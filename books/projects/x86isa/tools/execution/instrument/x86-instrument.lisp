;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "../x86-init-page-tables" :ttags :all)
(include-book "std/strings/hex" :dir :system)

;; ==================================================================

(defxdoc dynamic-instrumentation
  :parents (program-execution model-validation)

  :short "Utilities to instrument a program run on the model"

  :long "<h5>Command Reference</h5>

<ul>

<li><p>Utilities to save the x86 state to a log file:</p>

<code>
(printing-x86-components x86 16 state) ;; 16 is the print-base.
</code>

<p>The current state of the general-purpose registers, instruction
pointer, and the flags will be stored in a log file, which is called
@('acl2-instrument.log') by default.  The log file's name can be
changed by the following:</p>

<code> (!log-file-name \"my-very-own-log-file.whoa\") </code>

</li>

<li><p>Utilities to print the x86 state in the ACL2 session \(and not log it into a file\):</p>

<p>The current state of the general-purpose registers, instruction
pointer, and the flags can be printed on screen by the following:</p>

<code>
(printing-x86-to-terminal x86 state)
</code>

<p>The following will print the current values of CF, PF, AF, ZF, SF,
and OF flags \(i.e., from the @('rflags') field in the x86
state\):</p>

<code>
(printing-flgs x86 state)
</code>

<p>The following will interpret its first argument \(100 in this
example\) as an @('rflags') value and print the values of CF, PF, AF,
ZF, SF, and OF flags.</p>

<code>
(printing-flg-val 100 state)
</code>

<p>To trace memory reads and writes, you can use the following:</p>

<code>
;; Trace rm08 and rm16.
(trace-read-memory (rm08 rm16))

;; The following is the same as
;; (trace-read-memory (rm08 rim08 rm16 rim16 rm32 rim32 rm64 rim64))
(trace-all-reads)

;; Trace wm32 and wm64.
(trace-write-memory (wm32 wm64))

;; The following is the same as
;; (trace-write-memory (wm08 wim08 wm16 wim16 wm32 wim32 wm64 wim64))
(trace-all-writes)
</code>

<p>You can send the output of these memory traces to file using the
ACL2 utility @(see open-trace-file).  Note that doing so will also
send the output of any other functions that you have traced to the
same file.</p>

</li>

<li>
<p>To step the interpreter once (like @('stepi') command of GDB):</p>
<code> (one_step) </code>

<p>@('one_step') logs the resulting state in the log file, which is
called @('acl2-instrument.log') by default, and can be changed via
@('!log-file-name').</p>

</li>

<li>
<p>To execute @('<n>') steps of a program \(or less if it halts or an
error occurs\):</p>
<code> (big_step @('<n>')) </code>

<p>@('big_step') logs the final state in the log file, which is called
@('acl2-instrument.log') by default, and can be changed via
@('!log-file-name').</p>

</li>

<li>

<p>To step the interpreter till a halt instruction \(#xF4\) is
encountered or an error occurs or \(2^60 - 1\) instructions \(you will
probably never want to execute these many instructions all at once\)
have been executed \(whatever comes first\):</p>

<code> (log_instr) </code>

<p>@('log_instr') logs the x86 state after <b>every</b> instruction in
the log file, which is called @('acl2-instrument.log') by default, and
can be changed via @('!log-file-name'). Note that if you are executing
a large number of instructions, @('log_instr') might be really slow
because of all the file output.</p>

</li>

<li>
<p>To set a breakpoint:</p>

<code>

(x86-break '(equal (rip x86) 10))
(x86-break '(equal (rgfi *rax* x86) 42))
(x86-break '(and (equal (rgfi *rsp* x86) 0)
		 (equal (rip x86) 12)))
</code>

<p>Any well-formed ACL2 expression that evaluates to a boolean is a
valid breakpoint.  Multiple breakpoints can be set using
@('x86-break') repeatedly.</p>

</li>

<li>
<p>See all active breakpoints:</p>
<code> (show-breakpoints) </code>
</li>

<li>
<p>To delete all breakpoints:</p>
<code>(delete-all-breakpoints)</code>
</li>

<li>
<p>To delete some breakpoints:</p>
<code> (delete-breakpoints '(0 2)) </code>

<p>@('delete-breakpoints') takes a list of the identifiers of the
breakpoints, where the identifiers are reported by
@('show-breakpoints').</p>
</li>

<li>
<p>Run the program when breakpoints are set:</p>

<code> (x86-debug) </code>

<p>Like GDB, <b>the first breakpoint encountered will stop the
 execution of the program</b>.  Of course, execution can also come to
 a stop if an error is encountered or if \(2^60 - 1\) instructions
 \(again, you probably never want to execute these many
 instructions!\) have been executed \(whatever comes first\).</p>

<p>To continue execution, see @('continue-debug') below.  Note that
 @('x86-debug') works only when at least one breakpoint is set.</p>

<p>@('x86-debug') logs the x86 state after every breakpoint in the log
file, which is called @('acl2-instrument.log') by default, and can be
changed via @('!log-file-name').</p>

<p>When @('x86-debug') stops when a breakpoint is reached, the @('ms')
field contains @('BREAKPOINT-REACHED'). This can be used to
differentiate between executions that stop because of an error or
those that stop when a breakpoint is reached.</p>

</li>

<li>
 <p>To continue execution of the program past a breakpoint:</p>
<code> (continue-debug) </code>
<p>Note that @('continue-debug') will set the contents of @('MS') to
 nil only if @('MS') contained @('breakpoint-reached'), then it will
 <i>step one instruction</i>, and then carry on with
 @('x86-debug').</p>

<p>Since @('continue-debug') essentially calls @('x86-debug'), it logs
the x86 state after every breakpoint in the log file, which is called
@('acl2-instrument.log') by default, and can be changed via
@('!log-file-name').</p>

<p>@('continue-debug') also sets @('ms') to @('BREAKPOINT-REACHED') if
it stops at a breakpoint.  @('ms') will be set to a legal halt message
when \(if\) @('continue-debug') finally leads the program to
completion.</p>

</li>

<li>
<p>To record the x86 state at a breakpoint and then continue:</p>
<code>(x86-debug!)</code>

<p>@('x86-debug!') logs the x86 state after every breakpoint in the
log file and continues execution till a halt or error is encountered
or if \(2^60 - 1\) instructions \(Do we need to say again that you
might never want to execute these many instructions?\) have been
executed \(whatever comes first\).</p>

</li>

</ul>
"
  )

;; ======================================================================
;; Printing and other utilities:

(defttag :instrument)

(defun !log-file-name-function (name state)
  (declare (xargs :stobjs (state)))
  (mv nil name state))

;; Smashing the definition of !log-file-name-function in raw Lisp...

(defmacro !log-file-name (name)
  `(!log-file-name-function ,name state))

(progn!
 (ACL2::set-raw-mode-on state)
 (defun !log-file-name-function (name state)
   (declare (ignorable state))
   (assign log-file-name name))
 ;; Default name of the ACL2 log file.
 (!log-file-name "acl2-instrument.log"))

(ACL2::remove-untouchable 'print-base nil)

(defun printing-x86-components (x86 base state)
  (declare (xargs :stobjs (x86 state))
	   (ignorable x86 base state))
  state)

;; Smashing the definition of printing-x86-components in raw Lisp...

(progn!
 (ACL2::set-raw-mode-on state)
 (defun printing-x86-components (x86 base state)
   (declare (xargs :stobjs (x86 state)))
   (with-open-file
    (*terminal-io* (@ log-file-name)
		   :direction :output
		   :if-exists :append
		   :if-does-not-exist :create)
    (b* ((rax (n64 (rgfi *rax* x86)))
	 (rbx (n64 (rgfi *rbx* x86)))
	 (rcx (n64 (rgfi *rcx* x86)))
	 (rdx (n64 (rgfi *rdx* x86)))
	 (rsi (n64 (rgfi *rsi* x86)))
	 (rdi (n64 (rgfi *rdi* x86)))
	 (rbp (n64 (rgfi *rbp* x86)))
	 (rsp (n64 (rgfi *rsp* x86)))
	 (r8  (n64 (rgfi *r8* x86)))
	 (r9  (n64 (rgfi *r9* x86)))
	 (r10 (n64 (rgfi *r10* x86)))
	 (r11 (n64 (rgfi *r11* x86)))
	 (r12 (n64 (rgfi *r12* x86)))
	 (r13 (n64 (rgfi *r13* x86)))
	 (r14 (n64 (rgfi *r14* x86)))
	 (r15 (n64 (rgfi *r15* x86)))
	 (flg (rflags x86))
	 (rip (n48 (rip x86)))
	 ((mv ?col state)
	  (fmt! "(@@GPR . ~%~
 ~tI((#.*RAX* . #x~s0)~%~
 ~tI (#.*RBX* . #x~s1)~%~
 ~tI (#.*RCX* . #x~s2)~%~
 ~tI (#.*RDX* . #x~s3)~%~
 ~tI (#.*RSI* . #x~s4)~%~
 ~tI (#.*RDI* . #x~s5)~%~
 ~tI (#.*RBP* . #x~s6)~%~
 ~tI (#.*RSP* . #x~s7)~%~
 ~tI (#.*R8*  . #x~s8)~%~
 ~tI (#.*R9*  . #x~s9)~%~
 ~tI (#.*R10* . #x~sA)~%~
 ~tI (#.*R11* . #x~sB)~%~
 ~tI (#.*R12* . #x~sC)~%~
 ~tI (#.*R13* . #x~sD)~%~
 ~tI (#.*R14* . #x~sE)~%~
 ~tI (#.*R15* . #x~sF))~%~
 @@)~%~
 (@@RFLAGS . ~%~tI#x~sG~%@@) ~%~
 (@@RIP . ~%~tI#x~sH~%@@)~%~%"
		(list (cons #\0 (str::natstr16 rax))
		      (cons #\1 (str::natstr16 rbx))
		      (cons #\2 (str::natstr16 rcx))
		      (cons #\3 (str::natstr16 rdx))
		      (cons #\4 (str::natstr16 rsi))
		      (cons #\5 (str::natstr16 rdi))
		      (cons #\6 (str::natstr16 rbp))
		      (cons #\7 (str::natstr16 rsp))
		      (cons #\8 (str::natstr16  r8))
		      (cons #\9 (str::natstr16  r9))
		      (cons #\A (str::natstr16 r10))
		      (cons #\B (str::natstr16 r11))
		      (cons #\C (str::natstr16 r12))
		      (cons #\D (str::natstr16 r13))
		      (cons #\E (str::natstr16 r14))
		      (cons #\F (str::natstr16 r15))
		      (cons #\G (str::natstr16 flg))
		      (cons #\H (str::natstr16 rip))
		      (cons #\I '8))
		*standard-co* state nil)))
	state))))

(push-untouchable 'print-base t)

(defun printing-x86-to-terminal (x86 state)
  (declare (xargs :stobjs (x86 state)
		  :mode :program))
  (b* ((rax (n64 (rgfi *rax* x86)))
       (rbx (n64 (rgfi *rbx* x86)))
       (rcx (n64 (rgfi *rcx* x86)))
       (rdx (n64 (rgfi *rdx* x86)))
       (rsi (n64 (rgfi *rsi* x86)))
       (rdi (n64 (rgfi *rdi* x86)))
       (rbp (n64 (rgfi *rbp* x86)))
       (rsp (n64 (rgfi *rsp* x86)))
       (r8  (n64 (rgfi *r8* x86)))
       (r9  (n64 (rgfi *r9* x86)))
       (r10 (n64 (rgfi *r10* x86)))
       (r11 (n64 (rgfi *r11* x86)))
       (r12 (n64 (rgfi *r12* x86)))
       (r13 (n64 (rgfi *r13* x86)))
       (r14 (n64 (rgfi *r14* x86)))
       (r15 (n64 (rgfi *r15* x86)))
       (flg (rflags x86))
       (rip (n48 (rip x86)))
       ((mv ?col state)
	(fmt! "(@@GPR . ~%~
 ~tI((#.*RAX* . #x~s0)~%~
 ~tI (#.*RBX* . #x~s1)~%~
 ~tI (#.*RCX* . #x~s2)~%~
 ~tI (#.*RDX* . #x~s3)~%~
 ~tI (#.*RSI* . #x~s4)~%~
 ~tI (#.*RDI* . #x~s5)~%~
 ~tI (#.*RBP* . #x~s6)~%~
 ~tI (#.*RSP* . #x~s7)~%~
 ~tI (#.*R8*  . #x~s8)~%~
 ~tI (#.*R9*  . #x~s9)~%~
 ~tI (#.*R10* . #x~sA)~%~
 ~tI (#.*R11* . #x~sB)~%~
 ~tI (#.*R12* . #x~sC)~%~
 ~tI (#.*R13* . #x~sD)~%~
 ~tI (#.*R14* . #x~sE)~%~
 ~tI (#.*R15* . #x~sF))~%~
 @@)~%~
 (@@RFLAGS . ~%~tI#x~sG~%@@) ~%~
 (@@RIP . ~%~tI#x~sH~%@@)~%~%"
	      (list (cons #\0 (str::natstr16 rax))
		    (cons #\1 (str::natstr16 rbx))
		    (cons #\2 (str::natstr16 rcx))
		    (cons #\3 (str::natstr16 rdx))
		    (cons #\4 (str::natstr16 rsi))
		    (cons #\5 (str::natstr16 rdi))
		    (cons #\6 (str::natstr16 rbp))
		    (cons #\7 (str::natstr16 rsp))
		    (cons #\8 (str::natstr16  r8))
		    (cons #\9 (str::natstr16  r9))
		    (cons #\A (str::natstr16 r10))
		    (cons #\B (str::natstr16 r11))
		    (cons #\C (str::natstr16 r12))
		    (cons #\D (str::natstr16 r13))
		    (cons #\E (str::natstr16 r14))
		    (cons #\F (str::natstr16 r15))
		    (cons #\G (str::natstr16 flg))
		    (cons #\H (str::natstr16 rip))
		    (cons #\I '8))
	      *standard-co* state nil)))
      state))

(defun printing-flgs (x86 state)
  (declare (xargs :stobjs (x86 state)
		  :mode :program))
  (b* ((cf  (flgi #.*cf* x86))
       (pf  (flgi #.*pf* x86))
       (af  (flgi #.*af* x86))
       (zf  (flgi #.*zf* x86))
       (sf  (flgi #.*sf* x86))
       (of  (flgi #.*of* x86))
       ((mv ?col state)
	(fmt!
	 "(@@FLGS . ~%~
~tI((CF . ~s0)~%~
~tI (PF . ~s1)~%~
~tI (AF . ~s2)~%~
~tI (ZF . ~s3)~%~
~tI (SF . ~s4)~%~
~tI (OF . ~s5))~%~
@@)~%~%"
	 (list (cons #\0 cf)
	       (cons #\1 pf)
	       (cons #\2 af)
	       (cons #\3 zf)
	       (cons #\4 sf)
	       (cons #\5 of)
	       (cons #\I '8))
	 *standard-co* state nil)))
      (mv x86 state)))

(defun printing-flg-val (eflags state)
  (declare (xargs :stobjs (state)
		  :mode :program))
  (b* ((cf  (rflags-slice :cf eflags))
       (pf  (rflags-slice :pf eflags))
       (af  (rflags-slice :af eflags))
       (zf  (rflags-slice :zf eflags))
       (sf  (rflags-slice :sf eflags))
       (of  (rflags-slice :of eflags))
       ((mv ?col state)
	(fmt! "(@@FLGS . ~%~
~tI((CF . ~s0)~%~
~tI (PF . ~s1)~%~
~tI (AF . ~s2)~%~
~tI (ZF . ~s3)~%~
~tI (SF . ~s4)~%~
~tI (OF . ~s5))~%~
@@)~%~%"
	      (list (cons #\0 cf)
		    (cons #\1 pf)
		    (cons #\2 af)
		    (cons #\3 zf)
		    (cons #\4 sf)
		    (cons #\5 of)
		    (cons #\I '8))
	      *standard-co* state nil)))
      state))

;; ======================================================================
;; Execution:

;; ======================================================================
;; "Big-Step" Execution:
;; ======================================================================

(defun big-step (n x86 state)
  (declare (xargs :guard (unsigned-byte-p 59 n)
		  :stobjs (x86 state)))
  (mv-let (steps x86 state)
	  (b* (((mv steps x86)
		(x86-run-steps n x86))
	       (state (printing-x86-components x86 16 state)))
	      (mv steps x86 state))
	  (mv (cw "Instructions Run: ~p0~%" steps) x86 state)))


(defmacro big_step (n)
  `(big-step ,n x86 state))

;; (time$ (big_step 100))

;; ======================================================================
;; "Small-Step" (one-step) Execution:
;; ======================================================================

(defun one-step (x86 state)
  (declare (xargs :stobjs (x86 state)))
  (b* ((x86 (x86-fetch-decode-execute x86))
       (state (printing-x86-components x86 16 state)))
      (mv x86 state)))

(defmacro one_step ()
  `(one-step x86 state))

;; (time$ (one_step x86 state))

;; ======================================================================
;; Printing state after each step:
;; ======================================================================

;; You can think of log-instr-fn, x86-run-debug1, and x86-debug!-fn1
;; as terminating only when #xF4 is encountered, which of course, may
;; never happen and so these functions may never terminate.  However,
;; in reality, in these functions, we are counting down from n (which
;; is set to a really large initial value) so that we can have an
;; argument for the termination of these functions and thus, they can
;; be in logic mode.  We could have these functions in program mode
;; too (which was the case previously) and in that case, we would not
;; have to worry about termination. But defining these functions in
;; program mode caused a problem.  Specifically, the constrained
;; function create-undef was being called, despite smashing its caller
;; undef-flg under the hood (so control should never have gone to
;; create-undef in the first place).  This problem was due to
;; "invariant-risk" (see :doc program-wrapper), which essentially
;; caused the *1* functions to be called instead of the Lisp
;; functions, thereby causing a slowdown, and in our case, allowed the
;; control to flow to create-undef.  We could have solved the problem
;; by doing the following:

;; From :doc program-wrapper:

;;     :q
;;     (setq *ignore-invariant-risk* t)
;;     (lp)

;; We chose to simply convert these functions to the logic mode instead.

(defun log-instr-fn (n x86 state)
  (declare (type (unsigned-byte 60) n)
	   (xargs :stobjs (x86 state)))
  (cond
   ((zp n)
    (mv "Out of time! See log file for the execution trace." x86 state))
   ((ms x86)
    (mv (ms x86) x86 state))
   (t
    (mv-let
     (erp val x86)
     (rm08 (rip x86) :r x86)
     (cond
      (erp (mv (cons erp "rm08 Error. See log file for the execution trace.")
	       x86 state))
      ((equal val #xF4)
       (let ((x86 (x86-fetch-decode-execute x86)))
	 (mv "Halt encountered. See log file for the execution trace." x86 state)))
      (t (b* (((mv x86 state) (one-step x86 state)))
	     (log-instr-fn (the (unsigned-byte 60) (1- n)) x86 state))))))))

(defun log-instr (x86 state)
  (declare (xargs :stobjs (x86 state)))
  (b* ((state ;; Print initial state
	(printing-x86-components x86 16 state)))
      (log-instr-fn (1- *2^60*) x86 state)))

(defmacro log_instr ()
  `(log-instr x86 state))

;; ======================================================================
;; Execution in "debug" mode:
;; ======================================================================

(defmacro x86-break (break-cond)
  `(table breakpoints
	  (let ((n (len (table-alist 'breakpoints world))))
	    n)
	  ,break-cond))

(defmacro get-breakpoints-1 ()
  `(let ((contents (table-alist 'breakpoints (w state))))
     (if (consp contents)
	 (cons 'or (strip-cdrs contents))
       (er hard 'get-breakpoints "No breakpoints set!"))))

(defmacro get-breakpoints ()
  (quote (get-breakpoints-1)))

(defn x86-run-debug-gen (stop-conds)
  `(defun x86-run-debug1 (n x86 state)
     (declare (xargs :guard (unsigned-byte-p 60 n)
		     :stobjs (x86 state)))
     (if (zp n)
	 (mv n x86 state)
       (let* ((state (set-print-base 16 state))
	      (state (set-print-radix t state)))
	 (cond ((ms x86)
		(let ((state (printing-x86-components x86 16 state)))
		  (mv n x86 state)))
	       (,stop-conds
		(let* ((x86 (!ms 'breakpoint-reached! x86))
		       (state (printing-x86-components x86 16 state)))
		  (mv n x86 state)))
	       (t (let ((x86 (x86-fetch-decode-execute x86)))
		    (x86-run-debug1 (1- n) x86 state))))))))

(defmacro x86-set-breakpoint ()
  `(make-event (x86-run-debug-gen
		;; Stop Conditions
		(get-breakpoints))))

(defmacro x86-run-debug ()
  `(b* (((mv n x86 state)
	 (x86-run-debug1
	  ,(1- *2^60*)
	  x86
	  state)))
       (mv (- (1- *2^60*) n) x86 state)))

;; ======================================================================

;; Some "make-event hackery" from Matt Kaufmann that defines x86-run-debug1 and
;; executes it with one top-level form called x86-debug.

(defmacro quiet-error ()
  '(ACL2::with-output :off (ACL2::error)
		      (defun f ())))

(defmacro x86-debug ()
  ;; Note that x86-debug results in an error.  If you want to use it with other
  ;; forms, you could do this:
  ;; (mv-let (erp val state)
  ;;         (x86-debug)
  ;;         (declare (ignore erp val))
  ;;         ....)
  `(ACL2::with-output :stack :push
		      :off (ACL2::error ACL2::summary)
		      (progn (ACL2::with-output :stack :pop
						:off (ACL2::summary)
						(x86-set-breakpoint))
			     (ACL2::with-output :stack :pop
						:off (ACL2::summary)
						(make-event
						 (ACL2::er-progn
						  (ACL2::trans-eval
						   '(x86-run-debug)
						   'top state t)
						  (ACL2::value
						   '(ACL2::value-triple nil)))))
			     (quiet-error))))

(defun continue-fn (x86)
  (declare (xargs :stobjs (x86)))
  (if (equal (ms x86) 'breakpoint-reached!)
      (b* ((x86 (!ms nil x86))
	   (x86 (x86-fetch-decode-execute x86)))
	  x86)
    x86))

(defmacro x86-debug-form ()
  `(b* (((mv ?erp ?val state)
	 (x86-debug)))
       state))

(defmacro continue-debug ()
  `(ACL2::er-progn
    (make-event (ACL2::er-progn
		 (ACL2::trans-eval '(continue-fn x86)
				   'top
				   state t)
		 (ACL2::value '(ACL2::value-triple nil))))
    (let* ((state (x86-debug-form)))
      (mv nil nil state))))

(defn x86-debug!-fn-gen (stop-conds)
  `(defun x86-debug!-fn1 (n x86 state)
     (declare (xargs :guard (unsigned-byte-p 60 n)
		     :stobjs (x86 state)))
     (if (zp n)
	 (mv n x86 state)
       (let* ((state (set-print-base 16 state))
	      (state (set-print-radix t state)))
	 (cond
	  (,stop-conds
	   (let* ((state (printing-x86-components x86 16 state))
		  (x86 (x86-fetch-decode-execute x86)))
	     (x86-debug!-fn1 (1- n) x86 state)))
	  ((ms x86)
	   (let ((state (printing-x86-components x86 16 state)))
	     (mv n x86 state)))
	  (t (let ((x86 (x86-fetch-decode-execute x86)))
	       (x86-debug!-fn1 (1- n) x86 state))))))))

(defmacro x86-set-breakpoint-x86-debug! ()
  `(make-event (x86-debug!-fn-gen
		;; Stop Conditions
		(get-breakpoints))))


(defmacro x86-debug!-fn ()
  `(b* (((mv n x86 state)
	 (x86-debug!-fn1
	  ,(1- *2^60*)
	  x86
	  state)))
       (mv (- (1- *2^60*) n) x86 state)))

(defmacro x86-debug! ()
  ;; Note that x86-debug! results in an error.  If you want to use it with other
  ;; forms, you could do this:
  ;; (mv-let (erp val state)
  ;;         (x86-debug!)
  ;;         (declare (ignore erp val))
  ;;         ....)
  `(ACL2::with-output :stack :push
		      :off (ACL2::error ACL2::summary)
		      (progn (ACL2::with-output :stack :pop
						:off (ACL2::summary)
						(x86-set-breakpoint-x86-debug!))
			     (ACL2::with-output
			      :stack :pop
			      :off (ACL2::summary)
			      (make-event
			       (ACL2::er-progn
				(ACL2::trans-eval '(x86-debug!-fn)
						  'top state t)
				(ACL2::value '(ACL2::value-triple nil)))))
			     (quiet-error))))

;; ======================================================================

;; Show breakpoints:

(defun display-table-contents (alst)
  (declare (xargs :guard (alistp alst)))
  (if (endp alst)
      nil
    (cons (cons (caar alst)
		(list (cdar alst)))
	  (display-table-contents (cdr alst)))))

(defmacro show-breakpoints ()
  `(let ((contents (table-alist 'breakpoints (w state))))
     (reverse (display-table-contents contents))))

;; Delete breakpoints:

(defmacro delete-all-breakpoints ()
  `(table breakpoints nil nil :clear))

(defun delete-breakpoint-fn (key-list breakpoints-lst)
  (declare (xargs :guard (and (nat-listp key-list)
			      (alistp breakpoints-lst))))
  (if (endp key-list)
      breakpoints-lst
    (delete-breakpoint-fn (cdr key-list)
			  (delete-assoc (car key-list)
					breakpoints-lst))))

(defmacro delete-breakpoint (key-list)
  `(table breakpoints nil
	  (delete-breakpoint-fn ,key-list
				(table-alist 'breakpoints world))
	  :clear))

;; ======================================================================

; Setting the guards on the table breakpoints (from Matt Kaufmann):

; Now we install a table guard.  Just to review, table guards are used roughly
; as follows.

; (let ((key 7) (val '(equal ..)) (world (w state)))
;   (breakpoints-check key val world))

(defun breakpoints-check (key val wrld)
  (declare (xargs :mode :program))
  (and (natp key)
       (mv-let (erp val bindings)
	       (ACL2::translate1-cmp val
				     '(nil)       ; stobjs-out
				     nil          ; bindings
				     '(x86 state) ; known-stobjs
				     'breakpoints ; ctx
				     wrld
				     (ACL2::default-state-vars :hons))
	       (declare (ignore bindings))
	       (cond (erp ; erp is a context; val is a message
		      (assert$
		       val ; message
		       (er hard erp
			   "~@0"
			   val)))
		     (t t)))))

(table breakpoints nil nil
       :guard
       (breakpoints-check ACL2::key ACL2::val world))

;; ======================================================================

;; Tracing memory:

(defun trace-read-memory-1 (fn)
  (let* ((numbytes
	  (case fn
	    ('rm08  1)
	    ('rim08 1)
	    ('rm16  2)
	    ('rim16 2)
	    ('rm32  4)
	    ('rim32 4)
	    ('rm64  8)
	    ('rim64 8))))
    (list
     `(trace! (,fn
	       :cond (and (equal ACL2::traced-fn (quote ,fn))
			  (not (equal (nth 1 ACL2::arglist) :x)))
	       :entry (:fmt! (msg "~%"))
	       :exit (:fmt! (msg "~x0: R ~x1 ~x2 ~x3"
				 (rip x86)
				 (nth 0 ACL2::arglist) ;; Linear address
				 ,numbytes             ;; Size
				 (nth 1 ACL2::values)  ;; Value read
				 )))))))

(defun create-trace-read-memory-1 (fn-lst)
  (if (endp fn-lst)
      nil
    (append (trace-read-memory-1 (car fn-lst))
	    (create-trace-read-memory-1 (cdr fn-lst)))))

(defun create-trace-read-memory (fn-lst)
  ;; (create-trace-read-memory '(rm08 rm16))
  (cons 'er-progn
	(create-trace-read-memory-1 fn-lst)))

(defmacro trace-read-memory (lst)
  ;; (trace-read-memory (rm08 rim08 rm16 rim16 rm32 rim32 rm64 rim64))
  (create-trace-read-memory lst))

(defmacro trace-all-reads ()
  `(trace-read-memory (rm08 rim08 rm16 rim16 rm32 rim32 rm64 rim64)))

(defun trace-write-memory-1 (fn)
  (let* ((numbytes
	  (case fn
	    ('wm08  1)
	    ('wim08 1)
	    ('wm16  2)
	    ('wim16 2)
	    ('wm32  4)
	    ('wim32 4)
	    ('wm64  8)
	    ('wim64 8))))
    (list
     `(trace! (,fn
	       :cond (equal ACL2::traced-fn (quote ,fn))
	       :entry (:fmt! (msg "~%"))
	       :exit (:fmt! (msg "~x0: W ~x1 ~x2 ~x3"
				 (rip x86)
				 (nth 0 ACL2::arglist) ;; Linear address
				 ,numbytes
				 (nth 1 ACL2::arglist) ;; Value written
				 )))))))

(defun create-trace-write-memory-1 (fn-lst)
  (if (endp fn-lst)
      nil
    (append (trace-write-memory-1 (car fn-lst))
	    (create-trace-write-memory-1 (cdr fn-lst)))))

(defun create-trace-write-memory (fn-lst)
  ;; (create-trace-write-memory '(wm08 wm16))
  (cons 'er-progn
	(create-trace-write-memory-1 fn-lst)))

(defmacro trace-write-memory (lst)
  ;; (trace-write-memory (wm08 wim08 wm16 wim16 wm32 wim32 wm64 wim64))
  (create-trace-write-memory lst))

(defmacro trace-all-writes ()
  `(trace-write-memory (wm08 wim08 wm16 wim16 wm32 wim32 wm64 wim64)))

(defmacro trace-to-file (file)
  `(open-trace-file ,file))

;; ======================================================================
