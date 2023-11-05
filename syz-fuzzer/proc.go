// Copyright 2017 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package main

import (
	"bytes"
	"fmt"
	"io"
	"math/rand"
	"os"
	"os/exec"
	"runtime/debug"
	"sync/atomic"
	"syscall"
	"time"
	"unsafe"

	"github.com/google/syzkaller/pkg/cover"
	"github.com/google/syzkaller/pkg/hash"
	"github.com/google/syzkaller/pkg/ipc"
	"github.com/google/syzkaller/pkg/log"
	"github.com/google/syzkaller/pkg/osutil"
	"github.com/google/syzkaller/pkg/rpctype"
	"github.com/google/syzkaller/pkg/signal"
	"github.com/google/syzkaller/prog"
)

// Proc represents a single fuzzing process (executor).
type Proc struct {
	fuzzer          *Fuzzer
	pid             int
	env             *ipc.Env
	rnd             *rand.Rand
	execOpts        *ipc.ExecOpts
	execOptsCollide *ipc.ExecOpts
	execOptsCover   *ipc.ExecOpts
	execOptsComps   *ipc.ExecOpts
}
type ExecFlags uint64

type ExecOpts struct {
	Flags ExecFlags
}
type command struct {
	pid int
	//config   *Config
	timeout  time.Duration
	cmd      *exec.Cmd
	dir      string
	readDone chan []byte
	exited   chan error
	inrp     io.ReadCloser
	outwp    io.WriteCloser
	outmem   []byte
}
type executeReq struct {
	magic            uint64
	envFlags         uint64 // env flags
	execFlags        uint64 // exec flags
	pid              uint64
	syscallTimeoutMS uint64
	programTimeoutMS uint64
	slowdownScale    uint64
	progSize         uint64
	// This structure is followed by a serialized test program in encodingexec format.
	// Both when sent over a pipe or in shared memory.
}
type callReply struct {
	magic      uint32
	index      uint32 // call index in the program
	num        uint32 // syscall number (for cross-checking)
	errno      uint32
	flags      uint32 // see CallFlags
	signalSize uint32
	coverSize  uint32
	compsSize  uint32
	// signal/cover/comps follow
}
type executeReply struct {
	magic uint32
	// If done is 0, then this is call completion message followed by callReply.
	// If done is 1, then program execution is finished and status is set.
	done   uint32
	status uint32
}

const (
	statusFail = 67
	inMagic    = uint64(0xbadc0ffeebadface)
	outMagic   = uint32(0xbadf00d)
)

func newProc(fuzzer *Fuzzer, pid int) (*Proc, error) {
	env, err := ipc.MakeEnv(fuzzer.config, pid)
	if err != nil {
		return nil, err
	}
	rnd := rand.New(rand.NewSource(time.Now().UnixNano() + int64(pid)*1e12))
	execOptsCollide := *fuzzer.execOpts
	execOptsCollide.Flags &= ^ipc.FlagCollectSignal
	execOptsCover := *fuzzer.execOpts
	execOptsCover.Flags |= ipc.FlagCollectCover
	execOptsComps := *fuzzer.execOpts
	execOptsComps.Flags |= ipc.FlagCollectComps
	proc := &Proc{
		fuzzer:          fuzzer,
		pid:             pid,
		env:             env,
		rnd:             rnd,
		execOpts:        fuzzer.execOpts,
		execOptsCollide: &execOptsCollide,
		execOptsCover:   &execOptsCover,
		execOptsComps:   &execOptsComps,
	}
	return proc, nil
}

func (proc *Proc) loop() {
	generatePeriod := 100
	if proc.fuzzer.config.Flags&ipc.FlagSignal == 0 {
		// If we don't have real coverage signal, generate programs more frequently
		// because fallback signal is weak.
		generatePeriod = 2
	}
	for i := 0; ; i++ {
		item := proc.fuzzer.workQueue.dequeue()
		if item != nil {
			switch item := item.(type) {
			case *WorkTriage:
				proc.triageInput(item)
			case *WorkCandidate:
				//TODO: 修改执行的方式，或许参考manager是怎么和fuzzer通信的，然后复制到这里
				proc.execute(proc.execOpts, item.p, item.flags, StatCandidate)
			case *WorkSmash:
				proc.smashInput(item)
			default:
				log.SyzFatalf("unknown work type: %#v", item)
			}
			continue
		}

		ct := proc.fuzzer.choiceTable
		fuzzerSnapshot := proc.fuzzer.snapshot()
		if len(fuzzerSnapshot.corpus) == 0 || i%generatePeriod == 0 {
			// Generate a new prog.
			p := proc.fuzzer.target.Generate(proc.rnd, prog.RecommendedCalls, ct)
			log.Logf(1, "#%v: generated", proc.pid)
			proc.executeAndCollide(proc.execOpts, p, ProgNormal, StatGenerate)
		} else {
			// Mutate an existing prog.
			p := fuzzerSnapshot.chooseProgram(proc.rnd).Clone()
			p.Mutate(proc.rnd, prog.RecommendedCalls, ct, proc.fuzzer.noMutate, fuzzerSnapshot.corpus)
			log.Logf(1, "#%v: mutated", proc.pid)
			proc.executeAndCollide(proc.execOpts, p, ProgNormal, StatFuzz)
		}
	}
}

func (proc *Proc) triageInput(item *WorkTriage) {
	log.Logf(1, "#%v: triaging type=%x", proc.pid, item.flags)

	prio := signalPrio(item.p, &item.info, item.call)
	inputSignal := signal.FromRaw(item.info.Signal, prio)
	newSignal := proc.fuzzer.corpusSignalDiff(inputSignal)
	if newSignal.Empty() {
		return
	}
	callName := ".extra"
	logCallName := "extra"
	if item.call != -1 {
		callName = item.p.Calls[item.call].Meta.Name
		logCallName = fmt.Sprintf("call #%v %v", item.call, callName)
	}
	log.Logf(3, "triaging input for %v (new signal=%v)", logCallName, newSignal.Len())
	var inputCover cover.Cover
	const (
		signalRuns       = 3
		minimizeAttempts = 3
	)
	// Compute input coverage and non-flaky signal for minimization.
	notexecuted := 0
	rawCover := []uint32{}
	for i := 0; i < signalRuns; i++ {
		info := proc.executeRaw(proc.execOptsCover, item.p, StatTriage)
		if !reexecutionSuccess(info, &item.info, item.call) {
			// The call was not executed or failed.
			notexecuted++
			if notexecuted > signalRuns/2+1 {
				return // if happens too often, give up
			}
			continue
		}
		thisSignal, thisCover := getSignalAndCover(item.p, info, item.call)
		//fmt.Printf("sxq *** raw cover: %v\n", rawCover)
		if len(rawCover) == 0 && proc.fuzzer.fetchRawCover {
			rawCover = append([]uint32{}, thisCover...)
		}
		newSignal = newSignal.Intersection(thisSignal)
		// Without !minimized check manager starts losing some considerable amount
		// of coverage after each restart. Mechanics of this are not completely clear.
		if newSignal.Empty() && item.flags&ProgMinimized == 0 {
			return
		}
		inputCover.Merge(thisCover)
	}
	if item.flags&ProgMinimized == 0 {
		item.p, item.call = prog.Minimize(item.p, item.call, false,
			func(p1 *prog.Prog, call1 int) bool {
				for i := 0; i < minimizeAttempts; i++ {
					info := proc.execute(proc.execOpts, p1, ProgNormal, StatMinimize)
					if !reexecutionSuccess(info, &item.info, call1) {
						// The call was not executed or failed.
						continue
					}
					thisSignal, _ := getSignalAndCover(p1, info, call1)
					if newSignal.Intersection(thisSignal).Len() == newSignal.Len() {
						return true
					}
				}
				return false
			})
	}

	data := item.p.Serialize()
	sig := hash.Hash(data)

	log.Logf(2, "added new input for %v to corpus:\n%s", logCallName, data)
	proc.fuzzer.sendInputToManager(rpctype.Input{
		Call:     callName,
		CallID:   item.call,
		Prog:     data,
		Signal:   inputSignal.Serialize(),
		Cover:    inputCover.Serialize(),
		RawCover: rawCover,
	})

	proc.fuzzer.addInputToCorpus(item.p, inputSignal, sig)

	if item.flags&ProgSmashed == 0 {
		proc.fuzzer.workQueue.enqueue(&WorkSmash{item.p, item.call})
	}
}

func reexecutionSuccess(info *ipc.ProgInfo, oldInfo *ipc.CallInfo, call int) bool {
	if info == nil || len(info.Calls) == 0 {
		return false
	}
	if call != -1 {
		// Don't minimize calls from successful to unsuccessful.
		// Successful calls are much more valuable.
		if oldInfo.Errno == 0 && info.Calls[call].Errno != 0 {
			return false
		}
		return len(info.Calls[call].Signal) != 0
	}
	return len(info.Extra.Signal) != 0
}

func getSignalAndCover(p *prog.Prog, info *ipc.ProgInfo, call int) (signal.Signal, []uint32) {
	inf := &info.Extra
	if call != -1 {
		inf = &info.Calls[call]
	}
	return signal.FromRaw(inf.Signal, signalPrio(p, inf, call)), inf.Cover
}

func (proc *Proc) smashInput(item *WorkSmash) {
	if proc.fuzzer.faultInjectionEnabled && item.call != -1 {
		proc.failCall(item.p, item.call)
	}
	if proc.fuzzer.comparisonTracingEnabled && item.call != -1 {
		proc.executeHintSeed(item.p, item.call)
	}
	fuzzerSnapshot := proc.fuzzer.snapshot()
	for i := 0; i < 100; i++ {
		p := item.p.Clone()
		p.Mutate(proc.rnd, prog.RecommendedCalls, proc.fuzzer.choiceTable, proc.fuzzer.noMutate, fuzzerSnapshot.corpus)
		log.Logf(1, "#%v: smash mutated", proc.pid)
		proc.executeAndCollide(proc.execOpts, p, ProgNormal, StatSmash)
	}
}

func (proc *Proc) failCall(p *prog.Prog, call int) {
	for nth := 1; nth <= 100; nth++ {
		log.Logf(1, "#%v: injecting fault into call %v/%v", proc.pid, call, nth)
		newProg := p.Clone()
		newProg.Calls[call].Props.FailNth = nth
		info := proc.executeRaw(proc.execOpts, newProg, StatSmash)
		if info != nil && len(info.Calls) > call && info.Calls[call].Flags&ipc.CallFaultInjected == 0 {
			break
		}
	}
}

func (proc *Proc) executeHintSeed(p *prog.Prog, call int) {
	log.Logf(1, "#%v: collecting comparisons", proc.pid)
	// First execute the original program to dump comparisons from KCOV.
	info := proc.execute(proc.execOptsComps, p, ProgNormal, StatSeed)
	if info == nil {
		return
	}

	// Then mutate the initial program for every match between
	// a syscall argument and a comparison operand.
	// Execute each of such mutants to check if it gives new coverage.
	p.MutateWithHints(call, info.Calls[call].Comps, func(p *prog.Prog) {
		log.Logf(1, "#%v: executing comparison hint", proc.pid)
		proc.execute(proc.execOpts, p, ProgNormal, StatHint)
	})
}

func (proc *Proc) execute(execOpts *ipc.ExecOpts, p *prog.Prog, flags ProgTypes, stat Stat) *ipc.ProgInfo {
	fmt.Println("sxq *** execOpts: ", execOpts)
	fmt.Println("sxq *** p: ", p)
	fmt.Println("sxq *** flags: ", flags)
	fmt.Println("sxq *** stat: ", stat)
	info := proc.executeRaw(execOpts, p, stat)
	//info := proc.Run(execOpts, p, flags, stat)
	if info == nil {
		return nil
	}
	// 执行以后检查有没有新的signal，新的signal表示新的路径（？）
	calls, extra := proc.fuzzer.checkNewSignal(p, info)
	for _, callIndex := range calls {
		proc.enqueueCallTriage(p, flags, callIndex, info.Calls[callIndex])
	}
	if extra {
		proc.enqueueCallTriage(p, flags, -1, info.Extra)
	}
	fmt.Printf("sxq *** execute info: %v\n", info)
	return info
}

func (proc *Proc) enqueueCallTriage(p *prog.Prog, flags ProgTypes, callIndex int, info ipc.CallInfo) {
	// info.Signal points to the output shmem region, detach it before queueing.
	info.Signal = append([]uint32{}, info.Signal...)
	// None of the caller use Cover, so just nil it instead of detaching.
	// Note: triage input uses executeRaw to get coverage.
	info.Cover = nil
	proc.fuzzer.workQueue.enqueue(&WorkTriage{
		p:     p.Clone(),
		call:  callIndex,
		info:  info,
		flags: flags,
	})
}

func (proc *Proc) executeAndCollide(execOpts *ipc.ExecOpts, p *prog.Prog, flags ProgTypes, stat Stat) {
	proc.execute(execOpts, p, flags, stat)

	if proc.execOptsCollide.Flags&ipc.FlagThreaded == 0 {
		// We cannot collide syscalls without being in the threaded mode.
		return
	}
	const collideIterations = 2
	for i := 0; i < collideIterations; i++ {
		proc.executeRaw(proc.execOptsCollide, proc.randomCollide(p), StatCollide)
	}
}

func (proc *Proc) randomCollide(origP *prog.Prog) *prog.Prog {
	if proc.rnd.Intn(5) == 0 {
		// Old-style collide with a 20% probability.
		p, err := prog.DoubleExecCollide(origP, proc.rnd)
		if err == nil {
			return p
		}
	}
	if proc.rnd.Intn(4) == 0 {
		// Duplicate random calls with a 20% probability (25% * 80%).
		p, err := prog.DupCallCollide(origP, proc.rnd)
		if err == nil {
			return p
		}
	}
	p := prog.AssignRandomAsync(origP, proc.rnd)
	if proc.rnd.Intn(2) != 0 {
		prog.AssignRandomRerun(p, proc.rnd)
	}
	return p
}

func (proc *Proc) executeRaw(opts *ipc.ExecOpts, p *prog.Prog, stat Stat) *ipc.ProgInfo {
	proc.fuzzer.checkDisabledCalls(p)

	// Limit concurrency window and do leak checking once in a while.
	ticket := proc.fuzzer.gate.Enter()
	defer proc.fuzzer.gate.Leave(ticket)

	proc.logProgram(opts, p)
	fmt.Printf("sxq *** executeRaw opts.Flags: %v\n", opts.Flags) //{21} or {23}
	for try := 0; ; try++ {
		atomic.AddUint64(&proc.fuzzer.stats[stat], 1)
		output, info, hanged, err := proc.env.Exec(opts, p) //这里执行
		if err != nil {
			if err == prog.ErrExecBufferTooSmall {
				// It's bad if we systematically fail to serialize programs,
				// but so far we don't have a better handling than counting this.
				// This error is observed a lot on the seeded syz_mount_image calls.
				atomic.AddUint64(&proc.fuzzer.stats[StatBufferTooSmall], 1)
				return nil
			}
			if try > 10 {
				log.SyzFatalf("executor %v failed %v times: %v", proc.pid, try, err)
			}
			log.Logf(4, "fuzzer detected executor failure='%v', retrying #%d", err, try+1)
			debug.FreeOSMemory()
			time.Sleep(time.Second)
			continue
		}
		log.Logf(2, "result hanged=%v: %s", hanged, output) //查了下日志，这里输出的都是 result hanged=false:
		return info
	}
}

func (proc *Proc) logProgram(opts *ipc.ExecOpts, p *prog.Prog) {

	if proc.fuzzer.outputType == OutputNone {
		return
	}

	data := p.Serialize()

	// The following output helps to understand what program crashed kernel.
	// It must not be intermixed.
	switch proc.fuzzer.outputType {
	case OutputStdout:
		now := time.Now()
		proc.fuzzer.logMu.Lock()
		fmt.Printf("%02v:%02v:%02v executing program %v:\n%s\n",
			now.Hour(), now.Minute(), now.Second(),
			proc.pid, data)
		proc.fuzzer.logMu.Unlock()
	case OutputDmesg:
		fd, err := syscall.Open("/dev/kmsg", syscall.O_WRONLY, 0)
		if err == nil {
			buf := new(bytes.Buffer)
			fmt.Fprintf(buf, "syzkaller: executing program %v:\n%s\n",
				proc.pid, data)
			syscall.Write(fd, buf.Bytes())
			syscall.Close(fd)
		}
	case OutputFile:
		f, err := os.Create(fmt.Sprintf("%v-%v.prog", proc.fuzzer.name, proc.pid))
		if err == nil {
			f.Write(data)
			f.Close()
		}
	default:
		log.SyzFatalf("unknown output type: %v", proc.fuzzer.outputType)
	}
}

// 这四个函数是之前写的，主要是改了ipc里面的代码
func (c *command) wait() error {
	return <-c.exited
}
func (c *command) exec(opts *ExecOpts, progData []byte) (output []byte, hanged bool, err0 error) {
	// exec start
	req := &executeReq{
		magic:            13464654573481097934,
		envFlags:         0,
		execFlags:        0, // 假设 execOpts 已正确定义
		pid:              0,
		syscallTimeoutMS: 100,
		programTimeoutMS: 10000,
		slowdownScale:    1,
	}
	reqData := (*[unsafe.Sizeof(*req)]byte)(unsafe.Pointer(req))[:]
	if _, err := c.outwp.Write(reqData); err != nil {
		output = <-c.readDone
		err0 = fmt.Errorf("executor %v: failed to write control pipe: %w", c.pid, err)
		return
	}
	if progData != nil {
		if _, err := c.outwp.Write(progData); err != nil {
			output = <-c.readDone
			err0 = fmt.Errorf("executor %v: failed to write control pipe: %w", c.pid, err)
			return
		}
	}
	// At this point program is executing.

	done := make(chan bool)
	hang := make(chan bool)
	go func() {
		t := time.NewTimer(c.timeout)
		select {
		case <-t.C:
			c.cmd.Process.Kill()
			hang <- true
		case <-done:
			t.Stop()
			hang <- false
		}
	}()
	exitStatus := -1
	completedCalls := (*uint32)(unsafe.Pointer(&c.outmem[0]))
	outmem := c.outmem[4:]
	for {
		reply := &executeReply{}
		replyData := (*[unsafe.Sizeof(*reply)]byte)(unsafe.Pointer(reply))[:]
		if _, err := io.ReadFull(c.inrp, replyData); err != nil {
			break
		}
		if reply.magic != outMagic {
			fmt.Fprintf(os.Stderr, "executor %v: got bad reply magic 0x%x\n", c.pid, reply.magic)
			os.Exit(1)
		}
		if reply.done != 0 {
			exitStatus = int(reply.status)
			break
		}
		callReply := &callReply{}
		callReplyData := (*[unsafe.Sizeof(*callReply)]byte)(unsafe.Pointer(callReply))[:]
		if _, err := io.ReadFull(c.inrp, callReplyData); err != nil {
			break
		}
		if callReply.signalSize != 0 || callReply.coverSize != 0 || callReply.compsSize != 0 {
			// This is unsupported yet.
			fmt.Fprintf(os.Stderr, "executor %v: got call reply with coverage\n", c.pid)
			os.Exit(1)
		}
		copy(outmem, callReplyData)
		outmem = outmem[len(callReplyData):]
		*completedCalls++
	}
	close(done)
	if exitStatus == 0 {
		// Program was OK.
		<-hang
		return
	}
	c.cmd.Process.Kill()
	output = <-c.readDone
	err := c.wait()
	if err != nil {
		output = append(output, err.Error()...)
		output = append(output, '\n')
	}
	if <-hang {
		hanged = true
		return
	}
	if exitStatus == -1 {
		if c.cmd.ProcessState == nil {
			exitStatus = statusFail
		} else {
			exitStatus = osutil.ProcessExitStatus(c.cmd.ProcessState)
		}
	}
	// Ignore all other errors.
	// Without fork server executor can legitimately exit (program contains exit_group),
	// with fork server the top process can exit with statusFail if it wants special handling.
	if exitStatus == statusFail {
		err0 = fmt.Errorf("executor %v: exit status %d err %w\n%s", c.pid, exitStatus, err, output)
	}
	return
	// exec end
}

func (c *command) close() {
	if c.cmd != nil {
		c.cmd.Process.Kill()
		c.wait()
	}
	osutil.RemoveAll(c.dir)
	if c.inrp != nil {
		c.inrp.Close()
	}
	if c.outwp != nil {
		c.outwp.Close()
	}
}

// copy from /isolated.go and executor
// func (proc *Proc) Run(execOpts *ipc.ExecOpts, p *prog.Prog, flags ProgTypes, stat Stat) (
//
//	<-chan []byte, <-chan error, error, *ipc.ProgInfo) {
// func (proc *Proc) Run(execOpts *ipc.ExecOpts, p *prog.Prog, flags ProgTypes, stat Stat) *ipc.ProgInfo {
// 	// TODO：这里的初始化可以后面改写到config里面
// 	debug := true
// 	sshKey := "/home/sxq/.ssh/id_rsa"
// 	targetPort := 22
// 	sshUser := "root"
// 	targetAddr := "192.168.123.22"
// 	TargetDir := "/home/execdir"
// 	forwardPort := 8080
// 	args := append(vmimpl.SSHArgs(debug, sshKey, targetPort), sshUser+"@"+targetAddr)
// 	dmesg, err := vmimpl.OpenRemoteConsole("ssh", args...)
// 	if err != nil {
// 		fmt.Errorf("failed to open remote console: %v", err)
// 		return nil
// 	}
// 	// 设置一些makecommand需要的初始参数
// 	out := make([]byte, 4)
// 	for i := 0; i < 4; i++ {
// 		out[i] = 0
// 	}
// 	// var inf, outf *os.File
// 	//makecommand的部分
// 	tmpDirPath := "./"
// 	dir, err := os.MkdirTemp(tmpDirPath, "syzkaller-testdir")
// 	if err != nil {
// 		fmt.Errorf("failed to create temp dir: %w", err)
// 		return nil
// 	}
// 	dir = osutil.Abs(dir)

// 	c := &command{
// 		pid: 0,
// 		// config:  config,
// 		timeout: time.Hour,
// 		dir:     dir,
// 		outmem:  out,
// 	}
// 	if err := os.Chmod(dir, 0777); err != nil {
// 		fmt.Errorf("failed to chmod temp dir: %w", err)
// 		return nil
// 	}
// 	// Output capture pipe.
// 	rp, wp, err := os.Pipe()
// 	if err != nil {
// 		fmt.Errorf("failed to create pipe: %w", err)
// 		return nil
// 	}
// 	defer wp.Close()
// 	// executor->ssh command pipe.
// 	inrpipe, inwpipe, err := osutil.LongPipe()
// 	if err != nil {
// 		dmesg.Close()
// 		fmt.Errorf("failed to create pipe: %v", err)
// 		return nil
// 	}
// 	defer inwpipe.Close()
// 	c.inrp = inrpipe

// 	// ssh->executor command pipe.
// 	outrpipe, outwpipe, err := osutil.LongPipe() // outrp是command的输入
// 	if err != nil {
// 		dmesg.Close()
// 		fmt.Errorf("failed to create pipe: %v", err)
// 		return nil
// 	}
// 	defer outrpipe.Close()
// 	c.outwp = outwpipe

// 	c.readDone = make(chan []byte, 1)

// 	args = vmimpl.SSHArgsForward(debug, sshKey, targetPort, forwardPort)
// 	// if inst.cfg.Pstore {
// 	// 	args = append(args, "-o", "ServerAliveInterval=6")
// 	// 	args = append(args, "-o", "ServerAliveCountMax=5")
// 	// }

// 	// proc.fuzzer.checkDisabledCalls(p)

// 	// // 这个好像是控制并发进程数量的，先不管
// 	// // Limit concurrency window and do leak checking once in a while.
// 	// ticket := proc.fuzzer.gate.Enter()
// 	// defer proc.fuzzer.gate.Leave(ticket)

// 	// proc.logProgram(execOpts, p)
// 	// // 先不多次尝试了
// 	// // for try := 0; ; try++ {
// 	// // 	atomic.AddUint64(&proc.fuzzer.stats[stat], 1)
// 	// // 	output, info, hanged, err := proc.env.Exec(execOpts, p) //这里执行
// 	// // 	if err != nil {
// 	// // 		if err == prog.ErrExecBufferTooSmall {
// 	// // 			// It's bad if we systematically fail to serialize programs,
// 	// // 			// but so far we don't have a better handling than counting this.
// 	// // 			// This error is observed a lot on the seeded syz_mount_image calls.
// 	// // 			atomic.AddUint64(&proc.fuzzer.stats[StatBufferTooSmall], 1)
// 	// // 			return nil
// 	// // 		}
// 	// // 		if try > 10 {
// 	// // 			log.SyzFatalf("executor %v failed %v times: %v", proc.pid, try, err)
// 	// // 		}
// 	// // 		log.Logf(4, "fuzzer detected executor failure='%v', retrying #%d", err, try+1)
// 	// // 		//debug.FreeOSMemory()
// 	// // 		time.Sleep(time.Second)
// 	// // 		continue
// 	// // 	}
// 	// // 	log.Logf(2, "result hanged=%v: %s", hanged, output)
// 	// // 	return info
// 	// // }
// 	commands := "/home/fuzzdir/syz-executor"
// 	args = append(args, sshUser+"@"+targetAddr, "cd "+TargetDir+" && exec "+commands)
// 	log.Logf(0, "running commands: ssh %#v", args)

// 	cmd := osutil.Command("ssh", args...)
// 	cmd.Stdin = outrpipe
// 	cmd.Stdout = inwpipe
// 	cmd.Stderr = inwpipe
// 	cmd.Dir = dir
// 	// Tell ASAN to not mess with our NONFAILING.
// 	cmd.Env = append(append([]string{}, os.Environ()...), "ASAN_OPTIONS=handle_segv=0 allow_user_segv_handler=1")
// 	if err := cmd.Start(); err != nil {
// 		dmesg.Close()
// 		outrpipe.Close()
// 		outwpipe.Close()
// 		inrpipe.Close()
// 		inwpipe.Close()
// 		fmt.Errorf("failed to start commmand: %v", err)
// 		// return nil, nil, err, nil
// 		return nil
// 	}
// 	c.exited = make(chan error, 1)
// 	c.cmd = cmd
// 	go func(c *command) {
// 		err := c.cmd.Wait()
// 		c.exited <- err
// 		close(c.exited)
// 		// Avoid a livelock if cmd.Stderr has been leaked to another alive process.
// 		rp.SetDeadline(time.Now().Add(5 * time.Second))
// 	}(c)
// 	wp.Close()
// 	inwpipe.Close()
// 	// end makecommand
// 	output := []byte{}
// 	hanged := false
// 	err0 := error(nil)

// 	// 构造一下progData
// 	var progData []byte
// 	if !proc.fuzzer.config.UseShmem {
// 		progData = proc.env.in[:progSize]
// 	}

// 	output, hanged, err0 = c.exec(execOpts, progData)
// 	if err0 != nil {
// 		c.close()
// 		return nil
// 	}
// 	var info *ProgInfo
// 	info, err0 = parseOutput(p, opts)

// 	// 这里也暂时先不处理了
// 	// if info != nil {
// 	// 	addFallbackSignal(p, info)
// 	// }
// 	c.close()
// 	log.Logf(2, "result hanged=%v: %s", hanged, output)
// 	return info
// 	//return info

// 	// 似乎下面主要是用来监控命令实行的，暂时先没做。
// 	// var tee io.Writer
// 	// if debug {
// 	// 	tee = os.Stdout
// 	// }
// 	// merger := vmimpl.NewOutputMerger(tee)
// 	// merger.Add("dmesg", dmesg)
// 	// merger.Add("ssh", rpipe)
// 	// timeout := time.Hour
// 	// stop := make(chan bool)
// 	// closed := make(chan bool)
// 	// info := proc.executeRaw(execOpts, p, stat)
// 	// outc, errc, err := vmimpl.Multiplex(cmd, merger, dmesg, timeout, stop, closed, false)
// 	// if err != nil {
// 	// 	return nil, nil, err, nil
// 	// }
// 	// return outc, errc, err, info

// }
