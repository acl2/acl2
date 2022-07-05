; An unrolling lifter xfor x86 code (based on Axe)
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2022 Kestrel Institute
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
(include-book "../dag-info")
(include-book "../prune")
(include-book "../print-levels")
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
;; erp result-dag-or-quotep state).
;; TODO: Handle returning a quotep?
(defun repeatedly-run (steps-left step-increment dag rules assumptions rules-to-monitor use-internal-contextsp prune print print-base memoizep total-steps state)
  (declare (xargs :guard (and (natp steps-left)
                              (acl2::step-incrementp step-increment)
                              (acl2::pseudo-dagp dag)
                              (symbol-listp rules)
                              (pseudo-term-listp assumptions)
                              (symbol-listp rules-to-monitor)
                              (booleanp use-internal-contextsp)
                              (or (eq nil prune)
                                  (eq t prune)
                                  (natp prune))
                              (acl2::axe-print-levelp print)
                              (member print-base '(10 16))
                              (booleanp memoizep)
                              (natp total-steps))
                  :mode :program
                  :stobjs (state)))
  (if (zp steps-left)
      (mv (erp-nil) dag state)
    (b* ((this-step-increment (acl2::this-step-increment step-increment total-steps))
         (steps-for-this-iteration (min steps-left this-step-increment))
         (old-dag dag)
         ((mv erp dag-or-quote state)
          (acl2::simp-dag dag
                          :rules rules
                          :assumptions assumptions
                          :monitor rules-to-monitor
                          :use-internal-contextsp use-internal-contextsp
                          ;; pass print, so we can cause rule hits to be printed:
                          :print print ; :brief ;nil
                          ;; :print-interval 10000 ;todo: pass in
                          :limits (acons 'x86isa::x86-fetch-decode-execute-base steps-for-this-iteration nil)
                          :memoizep memoizep))
         ((when erp) (mv erp nil state))
         ((when (quotep dag-or-quote))
          (mv (erp-nil) dag-or-quote state))
         (dag dag-or-quote)
         ;; Prune the DAG:
         ((mv erp dag state)
          (acl2::maybe-prune-dag-new prune ; if a natp, can help prevent explosion. todo: add some sort of DAG-based pruning)
                                     dag assumptions rules
                                     nil ; interpreted-fns
                                     rules-to-monitor
                                     t ;call-stp
                                     state))
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
                              dag rules assumptions rules-to-monitor use-internal-contextsp prune print print-base memoizep
                              total-steps
                              state))))))))

;; Returns (mv erp result-dag rules-used assumption-rules-used state).
(defun def-unrolled-fn-core (target
                             parsed-executable
                             assumptions ; todo: can these introduce vars for state components?  support that more directly?  could also replace register expressions with register names (vars)
                             suppress-assumptions
                             stack-slots
                             output
                             use-internal-contextsp
                             prune
                             extra-rules
                             remove-rules
                             extra-assumption-rules

                             step-limit
                             step-increment
                             memoizep
                             monitor
                             print
                             print-base
                             state)
  (declare (xargs :guard (and (lifter-targetp target)
                              ;; parsed-executable
                              ;; assumptions
                              (booleanp suppress-assumptions)
                              (natp stack-slots)
                              (output-indicatorp output)
                              (booleanp use-internal-contextsp)
                              (or (eq nil prune)
                                  (eq t prune)
                                  (natp prune))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp extra-assumption-rules)
                              (natp step-limit)
                              (acl2::step-incrementp step-increment)
                              (booleanp memoizep)
                              (or (symbol-listp monitor)
                                  (eq :debug monitor))
                              (acl2::axe-print-levelp print)
                              (member print-base '(10 16)))
                  :stobjs (state)
                  :mode :program))
  (b* ((- (cw "Lifting ~s0." target)) ;todo: print the executable name
       (executable-type (acl2::parsed-executable-type parsed-executable))
       (- (cw "(Executable type: ~x0.)~%" executable-type))
       ;;todo: finish adding support for :entry-point!
       ((when (and (eq :entry-point target)
                   (not (eq :pe-32 executable-type))))
        (er hard? 'def-unrolled-fn-core "Starting from the :entry-point is currently only supported for PE-32 files.")
        (mv :bad-entry-point nil nil nil state))
       ((when (and (natp target)
                   (not (eq :pe-32 executable-type))))
        (er hard? 'def-unrolled-fn-core "Starting from a numeric offset is currently only supported for PE-32 files.")
        (mv :bad-entry-point nil nil nil state))
       (- (and (stringp target)
               ;; Throws an error if the target doesn't exist:
               (acl2::ensure-target-exists-in-executable target parsed-executable)))
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
       (assumptions (acl2::translate-terms assumptions 'def-unrolled-fn-core (w state)))
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
       (assumption-rules (append extra-assumption-rules (assumption-simplification-rules)))
       ((mv erp rule-alist)
        (acl2::make-rule-alist assumption-rules (w state)))
       ((when erp) (mv erp nil nil nil state))
       ((mv erp assumptions state)
        (acl2::simplify-terms-using-each-other assumptions
                                               rule-alist
                                               :monitor '()
                                               ))
       ((when erp) (mv erp nil nil nil state))
       (assumptions (acl2::get-conjuncts-of-terms2 assumptions))
       (- (cw "Done simplifying assumptions)~%"))
       (- (and print (cw "(Simplified assumptions: ~x0)~%" assumptions)))
       ;; Prepare for symbolic execution:
       (term-to-simulate '(run-until-return x86))
       (term-to-simulate (wrap-in-output-extractor output term-to-simulate)) ;TODO: delay this if lifting a loop?
       (- (cw "(Limiting the unrolling to ~x0 steps.)~%" step-limit))
       ;; Convert the term into a dag for passing to repeatedly-run:
       ((mv erp dag-to-simulate) (dagify-term term-to-simulate))
       ((when erp) (mv erp nil nil nil state))
       (rules-to-monitor (if (eq :debug monitor)
                             (debug-rules32)
                           monitor))
       ;; Do the symbolic execution:
       ((mv erp result-dag ; result-dag-or-quotep ; FFIXME: Handle a quotep here
            state)
        (repeatedly-run step-limit step-increment dag-to-simulate rules assumptions rules-to-monitor use-internal-contextsp prune print print-base memoizep 0 state))
       ((when erp) (mv erp nil nil nil state))
       (- (if (quotep result-dag)
              (cw "Result is ~x0.~%" result-dag)
            (acl2::print-dag-info result-dag 'result t))))
    (mv (erp-nil) result-dag rules assumption-rules state)))

;; Returns (mv erp event state)
(defun def-unrolled-fn (lifted-name
                        target
                        parsed-executable
                        assumptions
                        suppress-assumptions
                        stack-slots
                        output
                        use-internal-contextsp
                        prune
                        extra-rules
                        remove-rules
                        extra-assumption-rules
                        step-limit
                        step-increment
                        memoizep
                        monitor
                        print
                        print-base
                        produce-function
                        non-executable
                        produce-theorem
                        prove-theorem ;whether to try to prove the theorem with ACL2 (rarely works)
                        restrict-theory
                        whole-form
                        state)
  (declare (xargs :guard (and (symbolp lifted-name)
                              (lifter-targetp target)
                              ;; parsed-executable
                              ;; assumptions
                              (booleanp suppress-assumptions)
                              (natp stack-slots)
                              (output-indicatorp output)
                              (booleanp use-internal-contextsp)
                              (or (eq nil prune)
                                  (eq t prune)
                                  (natp prune))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp extra-assumption-rules)
                              (natp step-limit)
                              (acl2::step-incrementp step-increment)
                              (booleanp memoizep)
                              (or (symbol-listp monitor)
                                  (eq :debug monitor))
                              (acl2::axe-print-levelp print)
                              (member print-base '(10 16))
                              (booleanp produce-function)
                              (booleanp non-executable)
                              (booleanp produce-theorem)
                              (booleanp prove-theorem)
                              (booleanp restrict-theory))
                  :stobjs (state)
                  :mode :program))
  (b* (;; Check whether this call to the lifter has already been made:
       (previous-result (previous-lifter-result whole-form state))
       ((when previous-result)
        (mv nil '(value-triple :redundant) state))
       ;; Lift the function to obtain the DAG:
       ((mv erp result-dag rules-used
            & ; assumption-rules-used
            state)
        (def-unrolled-fn-core target parsed-executable
          assumptions suppress-assumptions stack-slots
          output use-internal-contextsp prune extra-rules remove-rules extra-assumption-rules
          step-limit step-increment memoizep monitor print print-base state))
       ((when erp) (mv erp nil state))
       ;; TODO: Fully handle a quotep result here:
       (result-dag-size (acl2::dag-or-quotep-size result-dag))
       (result-dag-fns (acl2::dag-fns result-dag))
       ;; Sometimes the presence of text-offset may indicate that something
       ;; wasn't resolved, but other times it's just needed to express some
       ;; junk left on the stack
       (result-dag-vars (acl2::dag-vars result-dag))
       (defconst-name (pack-in-package-of-symbol lifted-name '* lifted-name '*))
       (defconst-form `(defconst ,defconst-name ',result-dag))
       (fn-formals result-dag-vars) ; we could include x86 here, even if the dag is a constant
       ;; Do we want a check like this?
       ;; ((when (not (subsetp-eq result-vars '(x86 text-offset))))
       ;;  (mv t (er hard 'lifter "Unexpected vars, ~x0, in result DAG!" (set-difference-eq result-vars '(x86 text-offset))) state))
       ;; TODO: Maybe move some of this to the -core function:
       ((when (intersection-eq result-dag-fns '(run-until-rsp-greater-than run-until-return)))
        (if (< result-dag-size 10000)
            (progn$ (cw "(Term:~%")
                    (cw "~X01" (untranslate (dag-to-term result-dag) nil (w state)) nil)
                    (cw ")~%"))
          (progn$ (cw "(DAG:~%")
                  (cw "~X01" result-dag nil)
                  (cw ")~%")))
        (mv t (er hard 'lifter "Lifter error: The run did not finish.") state))
       ;; Not valid if (not (< result-dag-size 10000)):
       (maybe-result-term (and (< result-dag-size 10000) ; avoids exploding
                               (acl2::dag-to-term result-dag)))
       ;; Print the result:
       (- (and print
               (if (< result-dag-size 10000)
                   (cw "(Result: ~x0)~%" maybe-result-term)
                 (progn$ (cw "(Result:~%")
                         (cw "~X01" result-dag nil)
                         (cw ")~%")))))
       ;; Possibly produce a defun:
       ((mv erp defuns) ; defuns is nil or a singleton list
        (if (not produce-function)
            (mv (erp-nil) nil)
          (b* (;;TODO: consider untranslating this, or otherwise cleaning it up:
               (function-body (if (< result-dag-size 1000)
                                  maybe-result-term
                                `(acl2::dag-val-with-axe-evaluator ',result-dag
                                                                   ,(acl2::make-acons-nest result-dag-vars)
                                                                   ',(acl2::make-interpreted-function-alist (acl2::get-non-built-in-supporting-fns-list result-dag-fns (w state)) (w state))
                                                                   '0 ;array depth (not very important)
                                                                   )))
               (function-body-untranslated (untranslate function-body nil (w state))) ;todo: is this unsound (e.g., because of user changes in how untranslate works)?
               (function-body-retranslated (acl2::translate-term function-body-untranslated 'def-unrolled-fn-core (w state)))
               ;; TODO: I've seen this check fail when (if x y t) got turned into (if (not x) (not x) y):
               ((when (not (equal function-body function-body-retranslated))) ;todo: make a safe-untranslate that does this check?
                (er hard? 'lifter "Problem with function body.  Untranslating and then re-translating did not give original body.  Body was ~X01" function-body nil)
                (mv :problem-with-function-body nil))
               ;;(- (cw "Runes used: ~x0" runes)) ;TODO: Have Axe return these?
               ;;use defun-nx by default because stobj updates are not all let-bound to x86
               (defun-variant (if non-executable 'defun-nx 'defun))
               (defun `(,defun-variant ,lifted-name (,@fn-formals)
                         (declare (xargs ,@(if (member-eq 'x86 fn-formals)
                                               `(:stobjs x86)
                                             nil)
                                         :verify-guards nil ;TODO
                                         )
                                  ,@(let ((ignored-vars (set-difference-eq fn-formals result-dag-vars)))
                                      (and ignored-vars
                                           `((ignore ,@ignored-vars)))))
                         ,function-body-untranslated)))
            (mv (erp-nil) (list defun)))))
       ((when erp) (mv erp nil state))
       (defthms ; either nil or a singleton list
         (if (not produce-theorem)
             nil
           (let* ((defthm `(defthm ,(acl2::pack$ lifted-name '-correct)
                             (implies (and ,@assumptions)
                                      (equal (run-until-return x86)
                                             (,lifted-name ,@fn-formals)))
                             :hints ,(if restrict-theory
                                         `(("Goal" :in-theory '(,lifted-name ;,@runes ;without the runes here, this won't work
                                                                )))
                                       `(("Goal" :in-theory (enable ,@rules-used
                                                                    ;; ,@assumption-rules-used ; todo consider this
                                                                    ))))
                             :otf-flg t))
                  (defthm (if prove-theorem
                              defthm
                            `(skip-proofs ,defthm))))
             (list defthm))))
       (event `(progn ,defconst-form
                      ,@defuns
                      ,@defthms))
       (event (acl2::extend-progn event `(table x86-lifter-table ',whole-form ',event))))
    (mv nil event state)))

;TODO: Add show- variant
;bad name?
;try defmacroq?
;; Creates some events to represent the unrolled computation, including a defconst for the DAG and perhaps a defun and a theorem.
(defmacro def-unrolled (&whole whole-form
                               lifted-name ;name to use for the generated function and constant (the latter surrounded by stars)
                               parsed-executable ; for example, a defconst created by defconst-x86
                               &key
                               (target ':entry-point) ;; where to start lifting (see lifter-targetp)
                               (assumptions 'nil) ;extra assumptions in addition to the standard-assumptions (todo: rename to :extra-assumptions)
                               (suppress-assumptions 'nil) ;suppress the standard assumptions
                               (stack-slots '100) ;; tells us what to assume about available stack space
                               (output ':all)
                               (use-internal-contextsp 't)
                               (prune '1000)
                               (extra-rules 'nil) ;Rules to use in addition to (lifter-rules32) or (lifter-rules64).
                               (remove-rules 'nil) ;Rules to turn off
                               (extra-assumption-rules 'nil) ; Extra rules to use when simplifying assumptions
                               (step-limit '1000000)
                               (step-increment '100)
                               (memoizep 't)
                               (monitor 'nil)
                               (print 't)             ;how much to print
                               (print-base '10)       ; 10 or 16
                               (produce-function 't) ;whether to produce a function, not just a constant dag, representing the result of the lifting
                               (non-executable 't)  ;since stobj updates will not be let-bound      ;allow :auto?  only use for :output :all ?
                               (produce-theorem 't) ;whether to try to produce a theorem (possibly skip-proofed) about the result of the lifting
                               (prove-theorem 'nil) ;whether to try to prove the theorem with ACL2 (rarely works)
                               (restrict-theory 't)       ;todo: deprecate
                               )
  `(,(if print 'make-event 'acl2::make-event-quiet)
    (def-unrolled-fn
      ',lifted-name
      ,target
      ,parsed-executable
      ,assumptions
      ',suppress-assumptions
      ',stack-slots
      ',output
      ',use-internal-contextsp
      ',prune
      ,extra-rules ; gets evaluated since not quoted
      ,remove-rules ; gets evaluated since not quoted
      ,extra-assumption-rules ; gets evaluated since not quoted
      ',step-limit
      ',step-increment
      ',memoizep
      ,monitor ; gets evaluated since not quoted
      ',print
      ',print-base
      ',produce-function
      ',non-executable
      ',produce-theorem
      ',prove-theorem
      ',restrict-theory
      ',whole-form
      state)))
