; An unrolling lifter xfor x86 code (based on Axe)
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Two approaches: 1. Use X86 as the only variable and get back a term
;; over the single variable X86 that captures the effect of the code.
;; 2. Introduce variables such as X and Y for the inputs and get back
;; a term over x86 and those variables.  This may make it easier to
;; state assumptions (since they can mention X and Y).  We use the
;; second approach here for now.

;; TODO: Add option to prune the DAG

;; TODO: Add support for a fixed or limited number of steps, for debugging

(include-book "kestrel/x86/tools/support-axe" :dir :system)
(include-book "kestrel/x86/tools/lifter-support" :dir :system)
(include-book "kestrel/x86/tools/conditions" :dir :system)
(include-book "kestrel/x86/tools/assumptions32" :dir :system)
(include-book "kestrel/x86/tools/assumptions64" :dir :system)
(include-book "kestrel/x86/tools/read-over-write-rules" :dir :system)
(include-book "kestrel/x86/tools/write-over-write-rules" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "../rules-in-rule-lists")
;(include-book "../rules2") ;for BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P-NON-CONST
;(include-book "../rules1") ;for ACL2::FORCE-OF-NON-NIL, etc.
(include-book "../rewriter") ;brings in skip-proofs, TODO: Consider using rewriter-basic (but it needs versions of simp-dag and simplify-terms-using-each-other)
;(include-book "../basic-rules")
(include-book "../step-increments")
(include-book "../dag-size")
(include-book "kestrel/lists-light/take" :dir :system)
(include-book "kestrel/lists-light/nthcdr" :dir :system)
(include-book "kestrel/lists-light/append" :dir :system)
(include-book "kestrel/arithmetic-light/less-than" :dir :system)
(include-book "kestrel/bv/arith" :dir :system) ;reduce?
(include-book "ihs/logops-lemmas" :dir :system) ;reduce? for logext-identity
(include-book "kestrel/arithmetic-light/mod" :dir :system)
(include-book "kestrel/bv/bvif2" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/progn" :dir :system)
(include-book "kestrel/x86/tools/rule-lists" :dir :system)
(include-book "kestrel/arithmetic-light/truncate" :dir :system)

(acl2::ensure-rules-known (lifter-rules32))
(acl2::ensure-rules-known (lifter-rules32-new))
(acl2::ensure-rules-known (lifter-rules64))
(acl2::ensure-rules-known (assumption-simplification-rules))

;; The type of an x86 executable
;; TODO: Add support for ELF
(defun executable-typep (type)
  (declare (xargs :guard t))
  (member-eq type '(:pe-32
                    :pe-64
                    :mach-o-32
                    :mach-o-64)))

;; We often want these for ACL2 proofs, but not for 64-bit examples
(deftheory 32-bit-reg-rules
  '(xw-becomes-set-eip
    xw-becomes-set-eax
    xw-becomes-set-ebx
    xw-becomes-set-ecx
    xw-becomes-set-edx
    xw-becomes-set-esp
    xw-becomes-set-ebp
    xr-becomes-eax
    xr-becomes-ebx
    xr-becomes-ecx
    xr-becomes-edx
    xr-becomes-ebp
    xr-becomes-esp)
  :redundant-okp t)

;; For safety:
(in-theory (disable (:executable-counterpart sys-call)))
(theory-invariant (not (active-runep '(:executable-counterpart sys-call))))

(defttag invariant-risk)
(set-register-invariant-risk nil) ;potentially dangerous but needed for execution speed

;; Repeatedly rewrite DAG to perform symbolic execution.  Perform
;; STEP-INCREMENT steps at a time, until the run finishes, STEPS-LEFT is
;; reduced to 0, or a loop or unsupported instruction is detected.  Returns (mv
;; erp result-dag state).
(defun repeatedly-run (steps-left step-increment dag rules assumptions rules-to-monitor use-internal-contextsp print print-base memoizep total-steps state)
  (declare (xargs :stobjs (state)
                  :guard (and (natp steps-left)
                              (acl2::step-incrementp step-increment)
                              (symbol-listp rules)
                              (pseudo-term-listp assumptions)
                              (symbol-listp rules-to-monitor)
                              (booleanp use-internal-contextsp)
                              ;; print
                              (member print-base '(10 16))
                              (booleanp memoizep)
                              (natp total-steps)
                              )
                  :mode :program)
           (irrelevant print) ;todo
           )
  (if (zp steps-left)
      (mv (erp-nil) dag state)
    (b* ((this-step-increment (acl2::this-step-increment step-increment total-steps))
         (steps-for-this-iteration (min steps-left this-step-increment))
         (old-dag dag)
         ((mv erp dag state)
          (acl2::simp-dag dag
                          :rules rules
                          :assumptions assumptions
                          :monitor rules-to-monitor
                          :use-internal-contextsp use-internal-contextsp
                          :print :brief ;nil ;print todo
;                             :print-interval 10000 ;todo: pass in
                          :limits (acons 'x86isa::x86-fetch-decode-execute-base steps-for-this-iteration nil)
                          :memoizep memoizep))
         ((when erp) (mv erp nil state))
         (dag-fns (acl2::dag-fns dag)))
      (if (not (member-eq 'run-until-rsp-greater-than dag-fns)) ;; stop if the run is done
          (prog2$ (cw "Note: The run has completed.~%")
                  (mv (erp-nil) dag state))
        (if (member-eq 'x86isa::x86-step-unimplemented dag-fns) ;; stop if we hit an unimplemented instruction
            (prog2$ (cw "WARNING: UNIMPLEMENTED INSTRUCTION.~%")
                    (mv (erp-nil) dag state))
          (if (acl2::equivalent-dags dag old-dag)
              (prog2$ (cw "Note: Stopping the run because nothing changed.~%")
                      (mv (erp-nil) dag state))
            (let* ((total-steps (+ steps-for-this-iteration total-steps))
                   (state ;; Print as a term unless it would be huge:
                    (if (< (acl2::dag-or-quotep-size dag) 1000)
                        (b* ((- (cw "(Term after ~x0 steps:~%" total-steps))
                             (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
                                        (set-print-base-radix print-base state)
                                      state))
                             (- (cw "~X01" (untranslate (dag-to-term dag) nil (w state)) nil))
                             (state (set-print-base-radix 10 state)) ;make event sets it to 10
                             (- (cw ")~%")))
                          state)
                      (b* ((- (cw "(DAG after ~x0 steps:~%" total-steps))
                           (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
                                      (set-print-base-radix print-base state)
                                    state))
                           (- (cw "~X01" dag nil))
                           (state (set-print-base-radix 10 state))
                           (- (cw ")~%")))
                        state))))
              (repeatedly-run (- steps-left steps-for-this-iteration)
                              step-increment
                              dag rules assumptions rules-to-monitor use-internal-contextsp print print-base memoizep
                              total-steps
                              state))))))))

;; Returns (mv erp event state). This function is
;; separate so we can call it directly in cases where we can't generate the
;; nice list of assumptions (e.g., no symbol table, or we only have a code
;; snippet).  TODO: Make a macro wrapper for this (todo, redundancy checking)
(defun def-unrolled-fn-aux (lifted-name
                            extra-rules
                            remove-rules
                            produce-theorem
                            prove-theorem ;whether to try to prove the theorem with ACL2 (rarely works)
                            output
                            assumptions
                            non-executable
                            restrict-theory
                            monitor
                            print
                            print-base
                            step-limit
                            step-increment
                            use-internal-contextsp
                            memoizep
                            executable-type
                            state)
  (declare (xargs :stobjs (state)
                  :guard (and (symbolp lifted-name)
                              (output-indicatorp output)
                              (booleanp non-executable)
                              (or (symbol-listp monitor)
                                  (eq :debug monitor))
                              (acl2::step-incrementp step-increment)
                              (member print-base '(10 16))
                              (executable-typep executable-type))
                  :mode :program))
  (b* ((assumptions (acl2::translate-terms assumptions 'def-unrolled-fn-aux (w state)))
       (- (and print (cw "(Unsimplified assumptions: ~x0)~%" assumptions)))
       (- (cw "(Simplifying assumptions...~%"))
       (lifter-rules (if (eq executable-type :pe-32)
                         (append (lifter-rules32)
                                 (lifter-rules32-new))
                       (if (eq executable-type :mach-o-32)
                           (append (lifter-rules32)
                                   (lifter-rules32-new) ; todo, may first need to implement standard-assumptions-mach-o-32
                                   )
                         (lifter-rules64))))
       (rules (append extra-rules lifter-rules))
       (- (let ((non-existent-remove-rules (set-difference-eq remove-rules rules)))
            (and non-existent-remove-rules
                 (cw "WARNING: The following rules in :remove-rules were not present: ~X01.~%" non-existent-remove-rules nil))))
       (rules (set-difference-eq rules remove-rules))
       ;; Next, we simplify the assumptions.  This allows us to state the
       ;; theorem about a lifted routine concisely, using an assumption
       ;; function that opens to a large conjunction before lifting is
       ;; attempted.  We need to assume some assumptions when simplifying the
       ;; others, because opening things like read64 involves testing
       ;; canonical-addressp (which we know from other assumptions is true):
       ((mv erp rule-alist)
        (acl2::make-rule-alist (assumption-simplification-rules) (w state)) ;todo: include the :extra-rules?
        )
       ((when erp) (mv erp nil state))
       ((mv erp assumptions state)
        (acl2::simplify-terms-using-each-other assumptions
                                               rule-alist
                                               :monitor '()
                                               ))
       ((when erp) (mv erp nil state))
       (assumptions (acl2::get-conjuncts-of-terms2 assumptions))
       (- (cw "Done simplifying assumptions)~%"))
       (- (and print (cw "(Simplified assumptions: ~x0)~%" assumptions)))
       ;; Do the symbolic simulation:
       (term-to-simulate '(run-until-return x86))
       (term-to-simulate (wrap-in-output-extractor output term-to-simulate)) ;TODO: delay this if lifting a loop?
       (- (cw "(Limiting the unrolling to ~x0 steps.)~%" step-limit))
       ;; Convert the term into a dag for passing to repeatedly-run:
       ((mv erp dag-to-simulate) (dagify-term term-to-simulate))
       ((when erp) (mv erp nil state))
       (rules-to-monitor (if (eq :debug monitor)
                             (debug-rules32)
                           monitor))
       ((mv erp result-dag state)
        (repeatedly-run step-limit step-increment dag-to-simulate rules assumptions rules-to-monitor use-internal-contextsp print print-base memoizep 0 state))
       ((when erp) (mv erp nil state))
       ;; could instead use dag-info (what was it called?) here to print the dag info:
       (- (and print (cw "Result DAG: ~x0~%" result-dag)))
       (result-dag-size (acl2::dag-or-quotep-size result-dag))
       (- (cw "(Result DAG size: ~x0)~%" result-dag-size))
       (result-dag-fns (acl2::dag-fns result-dag))
       (- (cw "(Result DAG functions: ~x0)~%" result-dag-fns))
       ;; Sometimes the presence of text-offset may indicate that something
       ;; wasn't resolved, but other times it's just needed to express some
       ;; junk left on the stack:
       (result-dag-vars (acl2::dag-vars result-dag))
       (- (cw "(Result DAG vars: ~x0)~%" result-dag-vars))
       ;; Do we want a check like this?
       ;; ((when (not (subsetp-eq result-vars '(x86 text-offset))))
       ;;  (mv t (er hard 'lifter "Unexpected vars, ~x0, in result DAG!" (set-difference-eq result-vars '(x86 text-offset))) state))
       ((when (intersection-eq result-dag-fns '(run-until-rsp-greater-than run-until-return)))
        (if (< result-dag-size 10000)
            (progn$ (cw "(Term:~%")
                    (cw "~X01" (untranslate (dag-to-term result-dag) nil (w state)) nil)
                    (cw ")~%"))
          (progn$ (cw "(DAG:~%")
                  (cw "~X01" result-dag nil)
                  (cw ")~%")))
        (mv t (er hard 'lifter "Lifter error: The run did not finish.") state))
       ;;TODO: consider untranslating this, or otherwise cleaning it up:
       (result-term (and (< result-dag-size 10000) ;avoids exploding
                         (acl2::dag-to-term result-dag)))
       (function-body (if (< result-dag-size 1000)
                          result-term
                        `(acl2::dag-val-with-axe-evaluator ',result-dag
                                                           ,(acl2::make-acons-nest result-dag-vars)
                                                           ',(acl2::make-interpreted-function-alist (acl2::get-non-built-in-supporting-fns-list result-dag-fns (w state)) (w state))
                                                           '0 ;array depth (not very important)
                                                           )))
       (function-body-untranslated (untranslate function-body nil (w state))) ;todo: is this unsound (e.g., because of user changes how untranslate works)?
       (function-body-retranslated (acl2::translate-term function-body-untranslated 'def-unrolled-fn-aux (w state)))
       ((when (not (equal function-body function-body-retranslated))) ;todo: make a safe-untranslate that does this check?
        (mv t (er hard 'lifter "Problem with function body.  Untranslating and the re-translating did not give original body.") state))

       ;; Print the term if small:
       (- (and print
               (< result-dag-size 10000)
               (cw "Result: ~x0" result-term)))
       ;;(- (cw "Runes used: ~x0" runes)) ;TODO: Have Axe return these?
       ;;use defun-nx by default because stobj updates are not all let-bound to x86
       (defun-variant (if non-executable 'defun-nx 'defun))
       (defun `(,defun-variant ,lifted-name (,@result-dag-vars)
                 (declare (xargs ,@(if (member-eq 'x86 result-dag-vars)
                                       `(:stobjs x86)
                                     nil)
                                 :verify-guards nil ;TODO
                                 ))
                 ,function-body-untranslated))
       (defthm `(defthm ,(acl2::pack$ lifted-name '-correct)
                  (implies (and ,@assumptions)
                           (equal (run-until-return x86)
                                  (,lifted-name ,@result-dag-vars)))
                  :hints ,(if restrict-theory
                              `(("Goal" :in-theory '(,lifted-name ;,@runes ;without the runes here, this won't work
                                                     )))
                            `(("Goal" :in-theory (enable ,@rules))))
                  :otf-flg t))
       (defthm (if prove-theorem
                   defthm
                 `(skip-proofs ,defthm)))
       (event `(progn ,defun
                      ,@(if produce-theorem (list defthm) nil))))
    (mv nil event state)))

;; Returns (mv erp event state)
(defun def-unrolled-fn (lifted-name
                        target
                        parsed-executable
                        stack-slots
                        extra-rules
                        remove-rules
                        whole-form
                        produce-theorem
                        prove-theorem ;whether to try to prove the theorem with ACL2 (rarely works)
                        output
                        assumptions
                        non-executable
                        restrict-theory
                        monitor
                        print
                        print-base
                        step-limit
                        step-increment
                        use-internal-contextsp
                        memoizep
                        suppress-assumptions
                        state)
  (declare (xargs :stobjs (state)
                  :guard (and (symbolp lifted-name)
                              (lifter-targetp target)
                              (natp stack-slots)
                              (output-indicatorp output)
                              (booleanp non-executable)
                              (or (symbol-listp monitor)
                                  (eq :debug monitor))
                              (booleanp memoizep)
                              (member print-base '(10 16))
                              (booleanp suppress-assumptions))
                  :mode :program))
  (b* ( ;; Check whether this call to the lifter has already been made:
       (previous-result (previous-lifter-result whole-form state))
       ((when previous-result)
        (mv nil '(value-triple :redundant) state))
       (executable-type (acl2::parsed-executable-type parsed-executable))
       (- (cw "(Executable type: ~x0.)~%" executable-type))
       ;;todo: finish adding support for :entry-point!
       ((when (and (eq :entry-point target)
                   (not (eq :pe-32 executable-type))))
        (er hard? 'def-unrolled-fn "Starting from the :entry-point is currently only supported for PE-32 files.")
        (mv t nil state))
       ((when (and (natp target)
                   (not (eq :pe-32 executable-type))))
        (er hard? 'def-unrolled-fn "Starting from a numeric offset is currently only supported for PE-32 files.")
        (mv t nil state))
       ;; assumptions (these get simplified below to put them into normal form):
       (assumptions (if suppress-assumptions
                        assumptions
                      (if (eq :mach-o-64 executable-type)
                          (cons `(standard-assumptions-mach-o-64 ',target
                                                                 ',parsed-executable
                                                                 ',stack-slots
                                                                 text-offset
                                                                 x86)
                                assumptions)
                        (if (eq :pe-64 executable-type)
                            (cons `(standard-assumptions-pe-64 ',target
                                                               ',parsed-executable
                                                               ',stack-slots
                                                               text-offset
                                                               x86)
                                  assumptions)
                          (if (eq :mach-o-32 executable-type)
                              (append (gen-standard-assumptions-mach-o-32 target
                                                                          parsed-executable
                                                                          stack-slots)
                                      assumptions)
                            (if (eq :pe-32 executable-type)
                                ;; todo: try without expanding this:
                                (append (gen-standard-assumptions-pe-32 target
                                                                        parsed-executable
                                                                        stack-slots)
                                        assumptions)
                              (prog2$ (cw "NOTE: Unsupported executable type: ~x0.~%" executable-type)
                                      assumptions)))))))
       ((mv erp event state)
        (def-unrolled-fn-aux lifted-name
          extra-rules
          remove-rules
          produce-theorem
          prove-theorem ;whether to try to prove the theorem with ACL2 (rarely works)
          output
          assumptions
          non-executable
          restrict-theory
          monitor
          print
          print-base
          step-limit
          step-increment
          use-internal-contextsp
          memoizep
          executable-type
          state))
       (event (acl2::extend-progn event `(table x86-lifter-table ',whole-form ',event))))
    (mv erp event state)))

;TODO: Add show- variant
;bad name?
;try defmacroq?
(defmacro def-unrolled (&whole whole-form
                               lifted-name ;name to use for the generated function
                               parsed-executable
                               &key
                               (stack-slots '100) ;; tells us what to assume about available stack space
                               (target ':entry-point) ;; where to start lifting (see lifter-targetp)
                               (extra-rules 'nil) ;Rules to use in addition to (lifter-rules32) or (lifter-rules64).
                               (remove-rules 'nil) ;Rules to turn off
                               (produce-theorem 't) ;whether to try to produce a theorem (possibly skip-proofed) about the result of the lifting
                               (prove-theorem 'nil) ;whether to try to prove the theorem with ACL2 (rarely works)
                               (output ':all)
                               (assumptions 'nil) ;extra assumptions in addition to the standard-assumptions (todo: rename to :extra-assumptions)
                               (non-executable 't)  ;since stobj updates will not be let-bound      ;allow :auto?  only use for :output :all ?
                               (restrict-theory 't)       ;todo: deprecate
                               (monitor 'nil)
                               (print 't)             ;how much to print
                               (print-base '10)       ; 10 or 16
                               (step-limit '1000000)
                               (step-increment '100)
                               (use-internal-contextsp 't)
                               (memoizep 't)
                               (suppress-assumptions 'nil) ;suppress the standard assumptions
                               )
  `(,(if print 'make-event 'acl2::make-event-quiet)
    (def-unrolled-fn
      ',lifted-name
      ,target
      ,parsed-executable
      ',stack-slots
      ,extra-rules             ;not quoted!
      ,remove-rules            ;not quoted!
      ',whole-form
      ',produce-theorem
      ',prove-theorem
      ',output
      ,assumptions
      ',non-executable
      ',restrict-theory
      ',monitor
      ',print
      ',print-base
      ',step-limit
      ',step-increment
      ',use-internal-contextsp
      ',memoizep
      ',suppress-assumptions
      state)))
