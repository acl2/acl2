(in-package "X86ISA")

(include-book "tools/include-raw" :dir :system)
(include-book "../machine/x86" :ttags :all)

(defxdoc virtualization-for-validation
         :parents (model-validation)
         :short "Validating the model by comparing its behavior with a virtual
         machine"

         :long "<p>Our virtualization based model validation tool works by
         loading the state of the machine into KVM, Linux's hardware
         accelerated virtualization API. This means using it requires a Linux
         system with support for hardware accelerated virtualization. This has
         been tested on Intel processors with VMX and (very minimally) on QEMU
         with its tiny code generator (TCG) backend.</p>

         <p>This tool, at a high level, consists of a C program and some ACL2
         functions. We use the function @(tsee dump-virtualizable-state) to
         dump the model's state into a file. Then, we run the C program, which
         loads the model state from the file into a KVM virtual machine and
         opens a socket. Then, we call the @(tsee validate-insts) function,
         which connects to the socket causing the virtual machine to execute
         some instructions, executes the model until the instruction pointer
         matches the VM, and then compares the GPRs and RIP.</p>

         <p>It should be noted that this tool is <i>very</i> rough around the
         edges. It was built quickly to help track down bugs when attempting to
         get Linux to boot on the model. Additionally, it only works in the
         system-view mode, though if you have userspace Linux binary that you
         wish to use to test, you can do it by @(tsee booting-linux) and then
         running the program under Linux on the model. Of course, this won't
         catch bugs that only occur in app-view. This tool also requires
         including raw lisp and is unsound. It also requires using CCL.</p>

         <p>Before using this tool, you should probably read @(tsee
         virtualization-for-validation-limitations). Additionally, if you
         encounter issues, debugging tips are documented at @(tsee
         virtualization-for-validation-debugging).</p>

         <p>To use this tool, first compile the C program in
         @('books/projects/x86isa/virtualization/main.c') with the flag
         @('-DVALIDATE') (without it, the program simply executes a few
         instructions and logs some information). Since this uses Linux kernel
         APIs, to compile it you may need to make sure you have kernel headers
         installed. These can usually be downloaded from your Linux
         distribution's package manager. Refer the to the documentation of the
         Linux distribution you are using for help with this.</p>

         <p>Next, open ACL2 and include the model. Get it into whatever initial
         state you wish to use. Then, include the @('virtualization/top') book
         and call @(tsee dump-virtualizable-state) passing it the filename you
         wish to save to, the @('x86') stobj, and @('state'). Then, run the C
         program you compiled, making sure the file you just saved is in your
         current working directory and called @('state.virt'). To use it, you
         need to make sure you have permissions to open the @('/dev/kvm')
         device.</p>

         <p>Finally, in ACL2, execute @(tsee validate-insts) passing it the
         number of iterations (number of comparisons with the VM and model) you
         wish to execute and the @('x86') stobj. This will continue executing
         instructions until one of the following is met:</p>
         <ul>
           <li>The number of iterations has been exhausted.</li>
           <li>In the last iteration, we executed 30 instructions, but we
           weren't able to get to the same instruction pointer value as the
           VM.</li>
           <li>In the last iteration, we found a difference between the GPRs of
           the model and the GPRs of the VM.</li>
         </ul>")

(local (xdoc::set-default-parents virtualization-for-validation))

(defxdoc virtualization-for-validation-limitations
         :short "A note regarding the limitations of our virtualization based
         validation scheme."

         :long "<p>There are a number of limitations with the @(tsee
         virtualization-for-validation) system. Here, we document many of them.
The majority of them aren't inherent to the approach. Some wouldn't be too
difficult to fix, but weren't implemented since we didn't have need for
them.</p>

<ul>
<li>We only save the bottom 4 GB of memory to load into the VM. This is very
easy to change in the source for @(tsee dump-virtualizable-state)</li>
<li>We only compare the GPRs. Comparing other registers would be pretty easy.
Comparing memory is far harder since we can't just send all the memory down the
wire, but could be handled by doing some trickery by not mapping memory into
the VM and mapping memory into the process when we @('VMEXIT') because the
memory wasn't present.</li>
<li>We can't easily step exactly one instruction at a time. For some reason,
even with setting the single step option in KVM, it often steps a handful of
instructions. Usually, this is a small enough number of instructions it doesn't
matter much.</li>
<li>In KVM, we don't simulate the timer device, so if you take a timer
interrupt you will get out of sync.</li>
<li>I <i>think</i> some page faults don't result in the model getting out of
sync with the VM, but many do.</li>
<li>@('REP') prefixed string operations cause the validation to stop since it
thinks it didn't do anything because the instruction pointer didn't change. In
GCC, compiling with the flag @('-mstringop-strategy=loop') causes GCC not to
emit those instructions, which can be useful. Of course, if your bug is in the
@('REP') operations, this won't help you.</li>
</ul>")

(defxdoc virtualization-for-validation-debugging
         :short "Some tips on debugging the virtualization based validation tool."

         :long "<p>The virtualization based validation tool is pretty rough,
         and it isn't uncommon to run into issues. Here we document some
         debugging tips.</p>

         <h3>Segfault or other issue immediately after starting the C program</h3>
         <p>This is likely either because you don't have permissions to open
         @('/dev/kvm') or @('state.virt') doesn't exist. I recommend running
         the C program with @('strace') and check the return value for the
         @('open') syscalls. If they are @('-1'), you need to resolve why those
         files can't be opened.</p>

         <h3>@('VMEXIT') with @('exit_reason = KVM_EXIT_FAIL_ENTRY') and (on VMX,
         SVM has a different error code for a similar thing)
         @('hardware_entry_failure_reason = 0x80000021')</h3>
         <p>This is probably the most difficult to debug issue you can come
         across. Essentially what has happened is that the state of the virtual
         machine is invalid. KVM can't give you more information because this
         is all the information the processor gave it. The SDM says that this
         error code (see SDM Volume 3 Chapter 27.8) means that the state failed
         one of the check in Chapter 27.3.1.</p>

         <p>This part of the manual has a <i>ton</i> of different checks which
         may have failed, so it is basically useless. Here's a couple of
         suggestions on how to debug this. The first thing you should do is
         enable tracing of the KVM subsystem in Linux, enable dump invalid
         state, and then attempt to run the VM and look at the kernel log.
         Depending on the issue, you may notice something off in the log.
         Otherwise, move on to the following. It's pretty involved, but I have
         yet to find a better way.</p>

         <p>Build a copy of QEMU's @('qemu-system-x86_64') with @('-ggdb').
         Then, launch it with the tiny code generator @('TCG') backend (this
         is important, it won't work otherwise) in @('gdb'), set a breakpoint
         on the @('cpu_vmexit') function, and boot some Linux distro. Inside
         the VM, I run the validation C program (compiling it without
         @('-DVALIDATE') is useful for this) and it will likely @('VMEXIT') and
         trigger the breakpoint. Then, you can look at the backtrace to
         determine why it happened.</p>

         <p>Note: due to differences between VMX and SVM, it's possible that
         the behavior in QEMU doesn't match the behavior on an Intel processor.
         In my experience, it usually still fails, but in some other way. For
         example, in QEMU I had the VM triple fault instead. If you're getting
         some sort of exception, try setting breakpoints on some of the
         functions used to raise exceptions.</p>")

(define write-val1 (size)
  :mode :program
  (if (equal size 0)
      nil
      (cons `((mv ?val state) (b* ((state (write-byte$ (logand #xFF val) channel state)))
                                 (mv (ash val -8) state)))
            (write-val1 (- size 8)))))

(defmacro write-val (val size channel state)
  `(b* ((val ,val)
        (state ,state)
        (channel ,channel)
        ,@(write-val1 size))
       state))

(defmacro write-packed-struct (struct channel state)
  (if (not struct)
      state
      (b* (((list* (list size val) tail) struct))
          `(b* ((state (write-val ,val ,size ,channel ,state)))
               (write-packed-struct ,tail ,channel state)))))

(defmacro write-packed-struct-with-size (struct channel state)
  `(b* ((state (write-packed-struct ,struct ,channel ,state)))
       (mv state (+ ,@(strip-cars struct)))))

(define write-bytes (bytes channel state)
  :mode :program
  (b* (((when (not bytes)) state)
       ((cons b tail) bytes)
       (state (write-byte$ b channel state)))
      (write-bytes tail channel state)))

;; Ideally we'd use the machine/save-restore.lisp write-mem-to-channel, but
;; that writes the memory in reverse order, which means we can't mmap it
(define write-virtualizable-mem
  ((start :type (integer 0 #.*mem-size-in-bytes*))
   (end :type (integer 0 #.*mem-size-in-bytes*))
   (channel symbolp)
   x86
   state)
  :mode :program
  :short "Write the memory to a @('channel')."
  :guard (and (<= start end)
              (open-output-channel-p channel :byte state))
  (if (= start end)
    state
    (b* ((state (write-byte$ (memi start x86) channel state)))
        (write-virtualizable-mem (1+ start) end channel x86 state))))

(define dump-virtualizable-state (filename x86 state)
  :mode :program
  :short "Write the a subset of the model state to a file in a format that can
  be read by our @(tsee virtualization-for-validation) tools."
  (b* (((mv channel state) (open-output-channel filename :byte state))
       ;; This should match state_file in main.c
       ((mv state size) (write-packed-struct-with-size ((64 (rgfi 0 x86))
							(64 (rgfi 1 x86))
							(64 (rgfi 2 x86))
							(64 (rgfi 3 x86))
							(64 (rgfi 4 x86))
							(64 (rgfi 5 x86))
							(64 (rgfi 6 x86))
							(64 (rgfi 7 x86))
							(64 (rgfi 8 x86))
							(64 (rgfi 9 x86))
							(64 (rgfi 10 x86))
							(64 (rgfi 11 x86))
							(64 (rgfi 12 x86))
							(64 (rgfi 13 x86))
							(64 (rgfi 14 x86))
							(64 (rgfi 15 x86))
							(64 (rip x86))
							(32 (rflags x86))
							(16 (seg-visiblei *cs* x86))
							(64 (seg-hidden-basei *cs* x86))
							(32 (seg-hidden-limiti *cs* x86))
							(16 (seg-hidden-attri *cs* x86))
							(16 (seg-visiblei *ds* x86))
							(64 (seg-hidden-basei *ds* x86))
							(32 (seg-hidden-limiti *ds* x86))
							(16 (seg-hidden-attri *ds* x86))
							(16 (seg-visiblei *es* x86))
							(64 (seg-hidden-basei *es* x86))
							(32 (seg-hidden-limiti *es* x86))
							(16 (seg-hidden-attri *es* x86))
							(16 (seg-visiblei *fs* x86))
							(64 (seg-hidden-basei *fs* x86))
							(32 (seg-hidden-limiti *fs* x86))
							(16 (seg-hidden-attri *fs* x86))
							(16 (seg-visiblei *gs* x86))
							(64 (seg-hidden-basei *gs* x86))
							(32 (seg-hidden-limiti *gs* x86))
							(16 (seg-hidden-attri *gs* x86))
							(16 (seg-visiblei *ss* x86))
							(64 (seg-hidden-basei *ss* x86))
							(32 (seg-hidden-limiti *ss* x86))
							(16 (seg-hidden-attri *ss* x86))
							(16 (ssr-visiblei *tr* x86))
							(64 (ssr-hidden-basei *tr* x86))
							(32 (ssr-hidden-limiti *tr* x86))
							(16 (ssr-hidden-attri *tr* x86))
							(16 (ssr-visiblei *ldtr* x86))
							(64 (ssr-hidden-basei *ldtr* x86))
							(32 (ssr-hidden-limiti *ldtr* x86))
							(16 (ssr-hidden-attri *ldtr* x86))
							(80 (stri *gdtr* x86))
							(80 (stri *idtr* x86))
							(64 (ctri *cr0* x86))
							(64 (ctri *cr2* x86))
							(64 (ctri *cr3* x86))
							(64 (ctri *cr4* x86))
							(64 (ctri *cr8* x86))
							(64 (msri *ia32_efer-idx* x86))
							(64 (msri *ia32_fs_base-idx* x86))
							(64 (msri *ia32_gs_base-idx* x86)))
						       channel
						       state))
       (size (logtail 3 size)) ;; Get size in bytes
       (offset (+ size (logand (- size) (- #x1000 1))))
       (padding (- offset size))
       (state (write-bytes (acl2::repeat padding 0) channel state))
       (state (write-virtualizable-mem 0 (ash 1 32) channel x86 state))
       (state (close-output-channel channel state)))
      state))

(define validate-inst (x86)
  :short "Handles a single back and forth with the C program over the socket.
  Smashed in raw lisp."
  :mode :program
  (mv nil x86))

(define run-until-rip-or-n (rip n x86)
  :mode :program
  :short "Execute the model until we reach the given @('rip') address or have
  executed @('n') instructions."
  (if (or (= n 0)
	  (ms x86)
	  (fault x86)
	  (equal (rip x86) (i64 rip)))
    (mv (equal (rip x86) (i64 rip)) x86)
    (b* ((x86 (x86-fetch-decode-execute x86)))
	(run-until-rip-or-n rip (1- n) x86))))

(define validate-insts (n x86)
  :short "Validate the model until we have done @('n') iterations."
  :mode :program
  (b* (((when (equal n 0)) (mv t n x86))
       ((mv success? x86) (validate-inst x86))
       ((when (not success?)) (mv nil n x86)))
      (validate-insts (1- n) x86)))

(defttag :virtualization)
; (depends-on "virtualization-raw.lsp")
(include-raw "virtualization-raw.lsp")
