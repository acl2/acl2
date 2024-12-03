; An unrolling lifter xfor x86 code (based on Axe)
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
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

(include-book "x86-rules")
(include-book "../bitops-rules")
(include-book "../logops-rules-axe")
(include-book "kestrel/x86/if-lowering" :dir :system)
(include-book "kestrel/x86/read-over-write-rules" :dir :system)
(include-book "kestrel/x86/read-over-write-rules32" :dir :system)
(include-book "kestrel/x86/read-over-write-rules64" :dir :system)
(include-book "kestrel/x86/write-over-write-rules" :dir :system)
(include-book "kestrel/x86/write-over-write-rules32" :dir :system)
(include-book "kestrel/x86/write-over-write-rules64" :dir :system)
(include-book "kestrel/x86/x86-changes" :dir :system)
(include-book "kestrel/x86/tools/lifter-support" :dir :system)
(include-book "kestrel/x86/conditions" :dir :system)
(include-book "kestrel/x86/support" :dir :system)
(include-book "kestrel/x86/assumptions32" :dir :system)
(include-book "kestrel/x86/assumptions64" :dir :system)
(include-book "kestrel/x86/assumptions-new" :dir :system)
(include-book "kestrel/x86/floats" :dir :system)
(include-book "kestrel/x86/parsers/parse-executable" :dir :system)
(include-book "kestrel/x86/separate" :dir :system)
(include-book "kestrel/x86/rflags" :dir :system)
(include-book "kestrel/x86/rflags2" :dir :system)
(include-book "kestrel/x86/support-bv" :dir :system)
(include-book "rule-lists")
(include-book "kestrel/x86/run-until-return" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "../rules-in-rule-lists")
;(include-book "../rules2") ;for BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P-NON-CONST
;(include-book "../rules1") ;for ACL2::FORCE-OF-NON-NIL, etc.
(include-book "../equivalent-dags")
(include-book "../make-term-into-dag-basic")
;(include-book "../basic-rules")
(include-book "../step-increments")
(include-book "../dag-size")
(include-book "../dag-info")
(include-book "../prune-dag-precisely")
(include-book "../prune-dag-approximately")
(include-book "../arithmetic-rules-axe")
(include-book "../make-evaluator") ; for make-acons-nest ; todo: split out
(include-book "../supporting-functions") ; for get-non-built-in-supporting-fns-list
(include-book "../evaluator") ; todo: this book has skip-proofs
(include-book "rewriter-x86")
(include-book "kestrel/utilities/print-levels" :dir :system)
(include-book "kestrel/utilities/widen-margins" :dir :system)
(include-book "kestrel/utilities/if" :dir :system)
(include-book "kestrel/utilities/if-rules" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system) ; for print-to-hundredths
(include-book "kestrel/utilities/defmacrodoc" :dir :system)
(include-book "kestrel/booleans/booleans" :dir :system)
(include-book "kestrel/lists-light/take" :dir :system)
(include-book "kestrel/lists-light/nthcdr" :dir :system)
(include-book "kestrel/lists-light/append" :dir :system)
(include-book "kestrel/arithmetic-light/less-than" :dir :system)
(include-book "kestrel/arithmetic-light/fix" :dir :system)
(include-book "kestrel/bv/arith" :dir :system) ;reduce?
(include-book "kestrel/bv/intro" :dir :system)
(include-book "kestrel/bv/rtl" :dir :system)
(include-book "kestrel/bv/convert-to-bv-rules" :dir :system)
(include-book "ihs/logops-lemmas" :dir :system) ;reduce? for logext-identity
(include-book "kestrel/arithmetic-light/mod" :dir :system)
(include-book "kestrel/arithmetic-light/ash" :dir :system) ; for ash-of-0, mentioned in a rule-list
(include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system) ; for +-OF-+-OF---SAME
(include-book "kestrel/bv/bvif2" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/progn" :dir :system)
(include-book "kestrel/arithmetic-light/truncate" :dir :system)
(include-book "kestrel/utilities/real-time-since" :dir :system)
(local (include-book "kestrel/utilities/get-real-time" :dir :system))
(local (include-book "kestrel/utilities/doublet-listp" :dir :system))
(local (include-book "kestrel/utilities/greater-than-or-equal-len" :dir :system))

(in-theory (disable str::coerce-to-list-removal)) ;todo

(acl2::ensure-rules-known (lifter-rules32-all))
(acl2::ensure-rules-known (lifter-rules64-all))
(acl2::ensure-rules-known (assumption-simplification-rules))
(acl2::ensure-rules-known (step-opener-rules))

;move
;; We often want these for ACL2 proofs, but not for 64-bit examples
(deftheory 32-bit-reg-rules
  '(xw-becomes-set-eip
    xw-becomes-set-eax
    xw-becomes-set-ebx
    xw-becomes-set-ecx
    xw-becomes-set-edx
    xw-becomes-set-esp
    xw-becomes-set-ebp
    ;; introduce eip too?
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move this util

;; Recognizes an alist from functions to boolean-lists representing which arguments to print.
(defun elision-spec-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
      (let ((entry (first alist)))
        (and (consp entry)
             (symbolp (car entry))
             (boolean-listp (cdr entry))
             (elision-spec-alistp (rest alist))))))

(defthm elision-spec-alistp-forward-to-alistp
    (implies (elision-spec-alistp alist)
             (alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable elision-spec-alistp alistp))))

;; Replace with :elided any arg that corresponds with nil in the bools
(defun apply-elision-spec (args bools)
  (declare (xargs :guard (and (true-listp args)
                              (boolean-listp bools))))
  (if (endp args)
      nil
      (cons (if (first bools) (first args) :elided)
            (apply-elision-spec (rest args) (rest bools)))))

(defund print-term-elided (term firstp elision-specs)
  (declare (xargs :guard (elision-spec-alistp elision-specs)))
  (let ((elision-spec (and (consp term)
                           (acl2::lookup-eq (car term) elision-specs))))
    (if elision-spec
        ;; eliding:
        (if (not (true-listp term))
            (er hard? 'print-term-elided "Bad term.")
            (if (not (= (len (rest term)) (len elision-spec))) ; todo: optimize via same-lengthp
                (er hard? 'print-term-elided "Length mismatch in elision spec, ~x0, for ~x1." elision-spec (car term))
                (let ((elided-term (cons (car term) (apply-elision-spec (rest term) elision-spec))))
                  (if firstp
                      (cw "(~y0" elided-term)
                      (cw " ~y0" elided-term)))))
        ;; not eliding (todo: share code with the above):
        (if firstp
            (cw "(~y0" term)
            (cw " ~y0" term)))))

;; Prints each of the TERMS, each starting with a space and ending with a newline.
;tail recursive, to support printing a large list
(defund print-terms-elided-aux (terms elision-specs)
  (declare (xargs :guard (and (true-listp terms)
                              (elision-spec-alistp elision-specs))))
  (if (atom terms)
      nil
    (prog2$ (print-term-elided (first terms) nil elision-specs)
            (print-terms-elided-aux (rest terms) elision-specs))))

(defund print-terms-elided (terms elision-specs)
  (declare (xargs :guard (and (true-listp terms)
                              (elision-spec-alistp elision-specs))))
  (if (consp terms)
      (prog2$ (print-term-elided (first terms) t elision-specs) ;print the first element separately to put in an open paren
              (prog2$ (print-terms-elided-aux (rest terms) elision-specs)
                      (cw ")")))
    (cw "nil") ; or could do ()
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund remove-assumptions-about (fns-to-remove terms)
  (declare (xargs :guard (and (symbol-listp fns-to-remove)
                              (pseudo-term-listp terms))))
  (if (endp terms)
      nil
    (let* ((term (first terms))
           ;; strip a NOT if present:
           (term (if (and (consp term)
                          (eq 'not (ffn-symb term))
                          (= 1 (len (fargs term))))
                     (farg1 term)
                   term)))
      (if (and (consp term)
               (member-eq (ffn-symb term) fns-to-remove))
          (remove-assumptions-about fns-to-remove (rest terms))
        (cons term (remove-assumptions-about fns-to-remove (rest terms)))))))

(local
  (defthm pseudo-term-listp-of-remove-assumptions-about
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (remove-assumptions-about fns-to-remove terms)))
    :hints (("Goal" :in-theory (enable remove-assumptions-about)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: more?
(defconst *non-stp-assumption-functions*
  '(canonical-address-p$inline
    program-at
    separate
    x86p
    cr0bits-p$inline
    cr4bits-p$inline
    alignment-checking-enabled-p
    ))

;move
(defund untranslate-logic (term wrld state)
  (declare (xargs :guard (plist-worldp wrld)
                  :stobjs state))
  (magic-ev-fncall 'untranslate (list term nil wrld) state nil nil))

(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

(local (in-theory (disable set-print-base-radix
                           w
                           acl2::ilks-plist-worldp
                           acl2::myquotep
                           quotep
                           mv-nth)))

(local (in-theory (enable acl2::weak-dagp-when-pseudo-dagp
                          acl2::true-listp-when-symbol-listp-rewrite-unlimited)))

;move
(defthm w-of-set-print-base-radix
  (equal (w (set-print-base-radix base state))
         (w state))
  :hints (("Goal" :in-theory (enable set-print-base-radix w))))

(local
  (defthm not-quote-forward-to-not-myquotep
    (implies (not (quotep x))
             (not (myquotep x)))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable myquotep)))))

;; Repeatedly rewrite DAG to perform symbolic execution.  Perform
;; STEP-INCREMENT steps at a time, until the run finishes, STEPS-LEFT is
;; reduced to 0, or a loop or an unsupported instruction is detected.
;; Returns (mv erp result-dag-or-quotep state).
(defun repeatedly-run (steps-left step-increment dag rule-alist assumptions rules-to-monitor use-internal-contextsp prune print print-base untranslatep memoizep total-steps state)
  (declare (xargs :guard (and (natp steps-left)
                              (acl2::step-incrementp step-increment)
                              (acl2::pseudo-dagp dag)
                              (acl2::rule-alistp rule-alist)
                              (pseudo-term-listp assumptions)
                              (symbol-listp rules-to-monitor)
                              (booleanp use-internal-contextsp)
                              (or (eq nil prune)
                                  (eq t prune)
                                  (natp prune))
                              (acl2::print-levelp print)
                              (member print-base '(10 16))
                              (booleanp untranslatep)
                              (booleanp memoizep)
                              (natp total-steps)
                              (acl2::ilks-plist-worldp (w state)) ; why?
                              )
                  :measure (nfix steps-left)
                  :stobjs state))
  (if (zp steps-left)
      (mv (erp-nil) dag state)
    (b* ((this-step-increment (acl2::this-step-increment step-increment total-steps))
         (steps-for-this-iteration (min steps-left this-step-increment))
         ((when (not (posp steps-for-this-iteration))) ; use mbt?
          (er hard? 'repeatedly-run "Temination problem.")
          (mv :termination-problem nil state))
         (- (cw "(Running (up to ~x0 steps):~%" steps-for-this-iteration))
         ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
         (old-dag dag)
         ;; (- (and print (progn$ (cw "(DAG before stepping:~%")
         ;;                       (cw "~X01" dag nil)
         ;;                       (cw ")~%"))))
         (limits nil) ; todo: call this empty-rule-limits?
         (limits (acl2::add-limit-for-rules (step-opener-rules) steps-for-this-iteration limits)) ; don't recompute for each small run?
         ((mv erp dag-or-quote state)
          ;; (if (eq :legacy rewriter)
          ;;     (acl2::simp-dag dag ; todo: call the basic rewriter, but it needs to support :use-internal-contextsp
          ;;                     :exhaustivep t
          ;;                     :rule-alist rule-alist
          ;;                     :assumptions assumptions
          ;;                     :monitor rules-to-monitor
          ;;                     ;; :fns-to-elide '(program-at) ; not supported
          ;;                     :use-internal-contextsp use-internal-contextsp
          ;;                     ;; pass print, so we can cause rule hits to be printed:
          ;;                     :print print ; :brief ;nil
          ;;                     ;; :print-interval 10000 ;todo: pass in
          ;;                     :limits limits
          ;;                     :memoizep memoizep
          ;;                     :check-inputs nil)
            (mv-let (erp result)
              (acl2::simplify-dag-x86 dag
                                      assumptions
                                      rule-alist
                                      nil ; interpreted-function-alist
                                      (acl2::known-booleans (w state))
                                      limits
                                      t ; count-hints ; todo: think about this
                                      print
                                      rules-to-monitor
                                      '(program-at) ; fns-to-elide
                                      t             ; normalize-xors
                                      memoizep)
              (mv erp result state))
            ;)
            )
         ((when erp) (mv erp nil state))
         ((mv elapsed state) (acl2::real-time-since start-real-time state))
         (- (cw " This limited run took ")
            (acl2::print-to-hundredths elapsed) ; todo: could have real-time-since detect negative time
            (cw "s.)~%")) ; matches "(Running"
         ((when (quotep dag-or-quote)) (mv (erp-nil) dag-or-quote state))
         (- (and print ;(acl2::print-level-at-least-tp print)
                 (progn$ (cw "(DAG after this limited run:~%")
                         (cw "~X01" dag-or-quote nil)
                         (cw ")~%"))))
         (dag dag-or-quote) ; it wasn't a quotep
         ;; Prune the DAG quickly but possibly imprecisely:
         ((mv erp dag-or-quotep state) (acl2::prune-dag-approximately dag
                                                                      (remove-assumptions-about *non-stp-assumption-functions* assumptions)
                                                                      t ; check-fnsp
                                                                      print state))
         ((when erp) (mv erp nil state))
         ((when (quotep dag-or-quotep)) (mv (erp-nil) dag-or-quotep state))
         (dag dag-or-quotep) ; it wasn't a quotep
         ;; (- (and print (progn$ (cw "(DAG after first pruning:~%")
         ;;                       (cw "~X01" dag nil)
         ;;                       (cw ")~%"))))
         ;; Prune precisely if feasible:
         ;; TODO: Maybe don't prune if the run has completed (but do simplify in that case)?
         ((mv erp dag-or-quotep state)
          (acl2::maybe-prune-dag-precisely prune ; if a natp, can help prevent explosion.
                                           dag
                                           ;; the assumptions used during lifting (program-at, MXCSR assumptions, etc) seem unlikely
                                           ;; to be helpful when pruning, and user assumptions seem like they should be applied by the
                                           ;; rewriter duing lifting (TODO: What about assumptions only usable by STP?)
                                           nil ; assumptions
                                           :none
                                           rule-alist
                                           nil ; interpreted-fns
                                           rules-to-monitor
                                           t ;call-stp
                                           print
                                           state))
         ((when erp) (mv erp nil state))
         ((when (quotep dag-or-quotep)) (mv (erp-nil) dag-or-quotep state))
         (dag dag-or-quotep) ; it wasn't a quotep
         ;; TODO: Error if dag too big (must be able to add it to old dag, or make a version of equivalent-dagsp that signals an error):
         ;; (- (and print (progn$ (cw "(DAG after second pruning:~%")
         ;;                       (cw "~X01" dag nil)
         ;;                       (cw ")~%"))))
         ;; TODO: If pruning did something, consider doing another rewrite here (pruning may have introduced bvchop or bool-fix$inline).  But perhaps now there are enough rules used in pruning to handle that?
         (dag-fns (acl2::dag-fns dag))
         ;; Stop if we hit an unimplemented instruction (what if it's on an unreachable branch?):
         ((when (member-eq 'x86isa::x86-step-unimplemented dag-fns))
          (prog2$ (cw "WARNING: UNIMPLEMENTED INSTRUCTION.~%")
                  (mv (erp-nil) dag state))) ; todo: return an error?
         ((mv erp nothing-changedp) (acl2::equivalent-dagsp2 dag old-dag)) ; todo: can we test equivalence up to xor nest normalization?
         ((when erp) (mv erp nil state))
         ((when nothing-changedp)
          (cw "Note: Stopping the run because nothing changed.~%")
          (mv (erp-nil) dag state)) ; todo: return an error?
         (run-completedp (not (member-eq 'run-until-stack-shorter-than dag-fns))) ;; stop if the run is done
         (- (and run-completedp (cw "(The run has completed.)~%")))
         )
      (if run-completedp
          ;; Simplify one last time (since pruning may have done something -- todo: skip this if pruning did nothing):
          (b* ((- (cw "(Doing final simplification:~%"))
               ((mv erp dag-or-quote state)
                ;; (if (eq :legacy rewriter)
                ;;     (acl2::simp-dag dag ; todo: call the basic rewriter, but it needs to support :use-internal-contextsp
                ;;                     :exhaustivep t
                ;;                     :rule-alist rule-alist
                ;;                     :assumptions assumptions
                ;;                     :monitor rules-to-monitor
                ;;                     :use-internal-contextsp use-internal-contextsp
                ;;                     ;; pass print, so we can cause rule hits to be printed:
                ;;                     :print print ; :brief ;nil
                ;;                     ;; :print-interval 10000 ;todo: pass in
                ;;                     :limits limits
                ;;                     :memoizep memoizep
                ;;                     :check-inputs nil)
                  (mv-let (erp result)
                    (acl2::simplify-dag-x86 dag
                                            assumptions
                                            rule-alist
                                            nil ; interpreted-function-alist
                                            (acl2::known-booleans (w state))
                                            limits
                                            t ; count-hints ; todo: think about this
                                            print
                                            rules-to-monitor
                                            '(program-at code-segment-assumptions32-for-code) ; fns-to-elide
                                            t ; normalize-xors
                                            memoizep)
                    (mv erp result state))
                  ;)
                  )
               (- (cw " Done with final simplification.)~%")) ; balances "(Doing final simplification"
               ((when erp) (mv erp nil state)))
            (mv (erp-nil) dag-or-quote state))
        ;; Continue the symbolic execution:
        (let* ((total-steps (+ steps-for-this-iteration total-steps))
               (state ;; Print as a term unless it would be huge:
                 (if (acl2::print-level-at-least-tp print)
                     (if (acl2::dag-or-quotep-size-less-than dag 1000)
                         (b* ((- (cw "(Term after ~x0 steps:~%" total-steps))
                              (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
                                         (set-print-base-radix print-base state)
                                       state))
                              ((mv erp term)
                               (let ((term (dag-to-term dag)))
                                 (if untranslatep
                                     (untranslate-logic term (w state) state)
                                   (mv nil term))))
                              ((when erp)
                               (er hard? 'repeatedly-run "Error untranslating.")
                               state)
                              (- (cw "~X01" term nil))
                              (state (set-print-base-radix 10 state)) ;make event sets it to 10
                              (- (cw ")~%")))
                           state)
                       (b* ((- (cw "(DAG after ~x0 steps:~%" total-steps))
                            (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
                                       (set-print-base-radix print-base state)
                                     state))
                            (- (cw "~X01" dag nil))
                            (state (set-print-base-radix 10 state))
                            (- (cw "(DAG has ~x0 IF-branches.)~%" (acl2::count-top-level-if-branches-in-dag dag)))
                            (- (cw ")~%")))
                         state))
                   state)))
          (repeatedly-run (- steps-left steps-for-this-iteration)
                          step-increment
                          dag rule-alist assumptions rules-to-monitor use-internal-contextsp prune print print-base untranslatep memoizep
                          total-steps
                          state))))))

(local (in-theory (disable ;; reader-and-writer-intro-rules
                           ;; (:e reader-and-writer-intro-rules)
                           ;; assumption-simplification-rules
                           ;; (:e assumption-simplification-rules)
                           ;; lifter-rules64-new
                           ;; (:e lifter-rules64-new)
                    )))

;; Returns (mv erp assumptions assumption-rules state)
(defund simplify-assumptions (assumptions extra-assumption-rules 64-bitp state)
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (symbol-listp extra-assumption-rules)
                              (booleanp 64-bitp)
                              (acl2::ilks-plist-worldp (w state)))
                  :stobjs state))
  (b* ((- (cw "(Simplifying assumptions...~%"))
       ((mv assumption-simp-start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       ;; todo: optimize):
       (assumption-rules (append extra-assumption-rules
                                 (reader-and-writer-intro-rules)
                                 (assumption-simplification-rules)
                                 (if 64-bitp
                                     ;; needed to match the normal forms used during lifting:
                                     (lifter-rules64-new)
                                   nil ; todo: why not use (lifter-rules32-new)?
                                   )))
       ((mv erp assumption-rule-alist)
        (acl2::make-rule-alist assumption-rules (w state)))
       ((when erp) (mv erp nil nil state))
       ;; TODO: Option to turn this off, or to do just one pass:
       ((mv erp assumptions)
        (acl2::simplify-conjunction-basic ;simplify-terms-repeatedly
          assumptions
          assumption-rule-alist
          (acl2::known-booleans (w state))
          nil ;; rules-to-monitor ; do we want to monitor here?  What if some rules are not included?
          nil ; don't memoize (avoids time spent making empty-memoizations)
          t   ; todo: warn just once
          ))
       ((when erp) (mv erp nil nil state))
       (assumptions (acl2::get-conjuncts-of-terms2 assumptions)) ; should already be done above, when repeatedly simplifying?
       ((mv assumption-simp-elapsed state) (acl2::real-time-since assumption-simp-start-real-time state))
       (- (cw " (Simplifying assumptions took ") ; usually <= .01 seconds
          (acl2::print-to-hundredths assumption-simp-elapsed)
          (cw "s.)~%"))
       (- (cw " Done simplifying assumptions)~%")))
    (mv nil assumptions assumption-rules state)))


;; Returns (mv erp result-dag-or-quotep assumptions lifter-rules-used assumption-rules-used state).
;; This is also called by the formal unit tester.
(defun unroll-x86-code-core (target
                             parsed-executable
                             extra-assumptions ; todo: can these introduce vars for state components?  support that more directly?  could also replace register expressions with register names (vars)
                             suppress-assumptions
                             inputs-disjoint-from
                             stack-slots
                             position-independent
                             inputs
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
                             untranslatep
                             state)
  (declare (xargs :guard (and (lifter-targetp target)
                              ;; parsed-executable
                              (true-listp extra-assumptions) ; untranslated terms
                              (booleanp suppress-assumptions)
                              (member-eq inputs-disjoint-from '(nil :code :all))
                              (natp stack-slots)
                              (member-eq position-independent '(t nil :auto))
                              (or (eq :skip inputs) (names-and-typesp inputs))
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
                              (acl2::print-levelp print)
                              (member print-base '(10 16))
                              (booleanp untranslatep))
                  :stobjs state
                  :mode :program ; todo: need a magic wrapper for translate-terms
                  ))
  (b* ((- (cw "(Lifting ~s0.~%" target)) ;todo: print the executable name
       ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       (state (acl2::widen-margins state))
       ;; Get and check the executable-type:
       (executable-type (acl2::parsed-executable-type parsed-executable))
       (- (cw "Executable type: ~x0.~%" executable-type))
       (- (acl2::ensure-x86 parsed-executable))
       (- (and (acl2::print-level-at-least-tp print) (cw "(Executable type: ~x0.)~%" executable-type)))
       ;; Handle a :position-independent of :auto:
       (position-independentp (if (eq :auto position-independent)
                                  (if (eq executable-type :mach-o-64)
                                      t ; since clang seems to produce position-independent code by default ; todo: think about this
                                    (if (eq executable-type :elf-64)
                                        (let ((elf-type (acl2::parsed-elf-type parsed-executable)))
                                          (prog2$ (cw "ELF type: ~x0.~%" elf-type)
                                                  (if (acl2::parsed-elf-program-header-table parsed-executable)
                                                      ;; For ELF64, we treat :dyn and :rel as position-independent (addresses relative to the var base-address) and :exec as absolute:
                                                      (if (member-eq elf-type '(:rel :dyn)) t nil)
                                                    ;; TTODO: Get this to work:
                                                    nil)))
                                      ;; TODO: Think about the other cases:
                                      t))
                                position-independent))
       ((when (and (not position-independentp) ; todo: think about this:
                   (not (member-eq executable-type '(:mach-o-64 :elf-64)))))
        (er hard? 'unroll-x86-code-core "Non-position-independent lifting is currently only supported for ELF64 and MACHO64 files.")
        (mv :bad-options nil nil nil nil state))
       (- (if position-independentp (cw "Using position-independent lifting.~%") (cw "Using non-position-independent lifting.~%")))
       ;;todo: finish adding support for :entry-point!
       ((when (and (eq :entry-point target)
                   (not (eq :pe-32 executable-type))))
        (er hard? 'unroll-x86-code-core "Starting from the :entry-point is currently only supported for PE-32 files.")
        (mv :bad-entry-point nil nil nil nil state))
       ((when (and (natp target)
                   (not (eq :pe-32 executable-type))))
        (er hard? 'unroll-x86-code-core "Starting from a numeric offset is currently only supported for PE-32 files.")
        (mv :bad-entry-point nil nil nil nil state))
       (- (and (stringp target)
               ;; Throws an error if the target doesn't exist:
               (acl2::ensure-target-exists-in-executable target parsed-executable)))
       (64-bitp (member-equal executable-type '(:mach-o-64 :pe-64 :elf-64)))
       (debug-rules (if 64-bitp (debug-rules64) (debug-rules32)))
       (rules-to-monitor (maybe-add-debug-rules debug-rules monitor))
       ;; Generate assumptions:
       ((mv erp assumptions untranslated-assumptions
            assumption-rules ; drop? todo: includes rules that were not used, but we return these as an RV named assumption-rules-used
            state)
        (if (and (eq :elf-64 executable-type)
                 ;; todo: remove this, but we have odd, unlinked ELFs that put both the text and data segments at address 0 !
                 (acl2::parsed-elf-program-header-table parsed-executable) ; there are segments present (todo: improve the "new" behavior to use sections when there are no segments)
                 )
            ;; New assumption generation behavior, only for ELF64 (for now):
            (b* ((- (cw "Using new-style assumptions.~%"))
                 (code-address (acl2::get-elf-code-address parsed-executable))
                 (base-var 'base-address) ; only used if position-independentp
                 (text-offset-term (if position-independentp
                                       (symbolic-add-constant code-address base-var)
                                     code-address))
                 ((mv erp disjoint-chunk-addresses-and-lens)
                  (if (eq nil inputs-disjoint-from)
                      (mv nil nil)
                    (if (eq :all inputs-disjoint-from)
                        (if (not (eq :elf-64 executable-type))
                            (mv :unsupported
                                (er hard? 'unroll-x86-code-core "The :inputs-disjoint-from option is only supported for ELF64 executables.")) ;todo!
                          (elf64-segment-addresses-and-lens (acl2::parsed-elf-program-header-table parsed-executable)
                                                            position-independentp
                                                            base-var
                                                            (len (acl2::parsed-elf-bytes parsed-executable))
                                                            nil))
                      (mv nil (acons text-offset-term (len (acl2::get-elf-code parsed-executable)) nil)))))
                 ((when erp)
                  (er hard? 'unroll-x86-code-core "Error generating disjointnes assumptions for inputs: ~x0." erp)
                  (mv erp nil nil nil state))
                 ((mv erp automatic-assumptions)
                  (if suppress-assumptions
                      (mv nil nil) ; todo: this also suppresses input assumptions - should it?  the user can just not give inputs..
                    (assumptions-elf64-new target
                                           position-independentp ;(if (eq :auto position-independent) :auto position-independent) ; todo: clean up the handling of this
                                           stack-slots
                                           'x86
                                           base-var
                                           inputs
                                           disjoint-chunk-addresses-and-lens
                                           parsed-executable)))
                 ((when erp) (mv erp nil nil nil state))

                 (untranslated-assumptions (append automatic-assumptions extra-assumptions)) ; includes any user assumptions
                 ;; Translate all the assumptions:
                 (assumptions (acl2::translate-terms untranslated-assumptions 'unroll-x86-code-core (w state)))
                 ((mv erp assumptions assumption-rules state)
                  (if extra-assumptions
                      ;; If there are extra-assumptions, we need to simplify (e.g., an extra assumption could replace RSP with 10000, and then all assumptions about RSP need to mention 10000 instead):
                      (simplify-assumptions assumptions extra-assumption-rules 64-bitp state)
                    (mv nil assumptions nil state)))
                 ((when erp) (mv erp nil nil nil state)))
              (mv nil assumptions
                  untranslated-assumptions ; seems ok to use the original, unrewritten assumptions here
                  assumption-rules state))
          ;; legacy case (generate some assumptions and then simplify them):
          (b* ((text-offset
                 (and 64-bitp ; todo
                      (if (eq :mach-o-64 executable-type)
                          (if position-independentp 'text-offset `,(acl2::get-mach-o-code-address parsed-executable))
                        (if (eq :pe-64 executable-type)
                            'text-offset ; todo: match what we do for other executable types
                          (if (eq :elf-64 executable-type)
                              (if position-independentp 'text-offset `,(acl2::get-elf-code-address parsed-executable))
                            (if (eq :mach-o-32 executable-type)
                                nil ; todo
                              (if (eq :pe-32 executable-type)
                                  nil ; todo
                                ;; todo: add support for :elf-32
                                (er hard? 'unroll-x86-code-core "Unsupported executable type: ~x0.~%" executable-type))))))))
               (code-length
                 (and 64-bitp ; todo
                      (if (eq :mach-o-64 executable-type)
                          (len (acl2::get-mach-o-code parsed-executable))
                        (if (eq :pe-64 executable-type)
                            10000 ; fixme
                          (if (eq :elf-64 executable-type)
                              (len (acl2::get-elf-code parsed-executable))
                            (if (eq :mach-o-32 executable-type)
                                nil ; todo
                              (if (eq :pe-32 executable-type)
                                  nil ; todo
                                ;;todo: add support for :elf-32
                                (er hard? 'unroll-x86-code-core "Unsupported executable type: ~x0.~%" executable-type))))))))
               (standard-assumptions
                 (if suppress-assumptions
                     ;; Suppress tool-generated assumptions; use only the explicitly provided ones:
                     nil
                   (if (eq :mach-o-64 executable-type)
                       `((standard-assumptions-mach-o-64 ',target
                                                         ',parsed-executable
                                                         ',stack-slots
                                                         ,text-offset
                                                         x86))
                     (if (eq :pe-64 executable-type)
                         `((standard-assumptions-pe-64 ',target
                                                       ',parsed-executable
                                                       ',stack-slots
                                                       text-offset
                                                       x86))
                       (if (eq :elf-64 executable-type)
                           `((standard-assumptions-elf-64 ',target
                                                          ',parsed-executable
                                                          ',stack-slots
                                                          ,text-offset
                                                          x86))
                         (if (eq :mach-o-32 executable-type)
                             (gen-standard-assumptions-mach-o-32 target parsed-executable stack-slots)
                           (if (eq :pe-32 executable-type)
                               ;; todo: try without expanding this:
                               (gen-standard-assumptions-pe-32 target parsed-executable stack-slots)
                             ;;todo: add support for :elf-32
                             (er hard? 'unroll-x86-code-core "Unsupported executable type: ~x0.~%" executable-type))))))))
               ;; maybe we should check suppress-assumptions here, but if they gave an :inputs, they must want the assumptions:
               (input-assumptions (if (and 64-bitp ; todo
                                           (not (equal inputs :skip)) ; really means generate no assumptions
                                           )
                                      (assumptions-for-inputs inputs
                                                              ;; todo: handle zmm regs and values passed on the stack?!:
                                                              ;; handle structs that fit in 2 registers?
                                                              ;; See the System V AMD64 ABI
                                                              '((rdi x86) (rsi x86) (rdx x86) (rcx x86) (r8 x86) (r9 x86))
                                                              stack-slots
                                                              (acons text-offset code-length nil) ;; disjoint-chunk-addresses-and-lens
                                                              )
                                    nil))
               (assumptions (append standard-assumptions input-assumptions)) ; call these automatic-assumptions?
               (assumptions (append assumptions extra-assumptions))
               (assumptions-to-return assumptions) ; untranslated?
               (assumptions (acl2::translate-terms assumptions 'unroll-x86-code-core (w state))) ; perhaps don't translate the automatic-assumptions?
               (- (and (acl2::print-level-at-least-tp print) (progn$ (cw "(Unsimplified assumptions:~%")
                                                                     (print-terms-elided assumptions
                                                                                         '((standard-assumptions-elf-64 t nil t t t)
                                                                                           (standard-assumptions-mach-o-64 t nil t t t)
                                                                                           (standard-assumptions-pe-64 t nil t t t)
                                                                                           )) ; todo: more?
                                                                     (cw ")~%"))))
               ;; Next, we simplify the assumptions.  This allows us to state the
               ;; theorem about a lifted routine concisely, using an assumption
               ;; function that opens to a large conjunction before lifting is
               ;; attempted.  We need to assume some assumptions when simplifying the
               ;; others, because opening things like read64 involves testing
               ;; canonical-addressp (which we know from other assumptions is true):
               ((mv erp assumptions assumption-rules state)
                (simplify-assumptions assumptions extra-assumption-rules 64-bitp state))
               ((when erp) (mv erp nil nil nil state)))
            (mv nil assumptions assumptions-to-return assumption-rules state))))
       ((when erp)
        (er hard? 'unroll-x86-code-core "Error generating assumptions: ~x0." erp)
        (mv erp nil nil nil nil state))
       (- (and print (progn$ (cw "(Assumptions for lifting:~%") ; should we untranslate these?
                             (if (acl2::print-level-at-least-tp print)
                                 (acl2::print-list assumptions)
                               (print-terms-elided assumptions '((program-at t nil t) ; the program can be huge
                                                                )))
                             (cw ")~%"))))
       ;; Prepare for symbolic execution:
       (term-to-simulate '(run-until-return x86))
       (term-to-simulate (wrap-in-output-extractor output term-to-simulate)) ;TODO: delay this if lifting a loop?
       (- (cw "(Limiting the unrolling to ~x0 steps.)~%" step-limit))
       ;; Convert the term into a dag for passing to repeatedly-run:
       ((mv erp dag-to-simulate) (acl2::make-term-into-dag-basic term-to-simulate nil))
       ((when erp) (mv erp nil nil nil nil state))
       ((when (quotep dag-to-simulate))
        (er hard? 'unroll-x86-code-core "Unexpected quotep: ~x0." dag-to-simulate)
        (mv :unexpected-quotep nil nil nil nil state))
       ;; Choose the lifter rules to use:
       (lifter-rules (if 64-bitp (lifter-rules64-all) (lifter-rules32-all)))
       ;; Add any extra-rules:
       (lifter-rules (append extra-rules lifter-rules)) ; todo: use union?
       ;; Remove any remove-rules:
       (- (let ((non-existent-remove-rules (set-difference-eq remove-rules lifter-rules)))
            (and non-existent-remove-rules
                 (cw "WARNING: The following rules in :remove-rules were not present: ~X01.~%" non-existent-remove-rules nil))))
       (lifter-rules (set-difference-eq lifter-rules remove-rules))
       ((mv erp lifter-rule-alist)
        (acl2::make-rule-alist lifter-rules (w state))) ; todo: allow passing in the rule-alist (and don't recompute for each lifted function)
       ((when erp) (mv erp nil nil nil nil state))
       ;; Do the symbolic execution:
       ((mv erp result-dag-or-quotep state)
        (repeatedly-run step-limit step-increment dag-to-simulate lifter-rule-alist assumptions rules-to-monitor use-internal-contextsp prune print print-base untranslatep memoizep 0 state))
       ((when erp) (mv erp nil nil nil nil state))
       (state (acl2::unwiden-margins state))
       ((mv elapsed state) (acl2::real-time-since start-real-time state))
       (- (cw " (Lifting took ")
          (acl2::print-to-hundredths elapsed) ; todo: could have real-time-since detect negative time
          (cw "s.)~%"))
       ;; Print the result (todo: allow suppressing this):
       (- (if (quotep result-dag-or-quotep)
              (cw " Lifting produced the constant ~x0.)~%" result-dag-or-quotep) ; matches (Lifting...
            (progn$ (cw " Lifting produced a dag:~%")
                    (acl2::print-dag-info result-dag-or-quotep 'result t)
                    (cw ")~%") ; matches (Lifting...
                    ))))
    (mv (erp-nil) result-dag-or-quotep untranslated-assumptions lifter-rules assumption-rules state)))

;; Returns (mv erp event state)
(defun def-unrolled-fn (lifted-name
                        target
                        executable
                        extra-assumptions
                        suppress-assumptions
                        inputs-disjoint-from
                        stack-slots
                        position-independent
                        inputs
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
                        untranslatep
                        produce-function
                        non-executable
                        produce-theorem
                        prove-theorem ;whether to try to prove the theorem with ACL2 (rarely works)
                        restrict-theory
                        whole-form
                        state)
  (declare (xargs :guard (and (symbolp lifted-name)
                              (lifter-targetp target)
                              ;; executable
                              ;; extra-assumptions ; untranslated-terms
                              (booleanp suppress-assumptions)
                              (member-eq inputs-disjoint-from '(nil :code :all))
                              (natp stack-slots)
                              (member-eq position-independent '(t nil :auto))
                              (or (eq :skip inputs) (names-and-typesp inputs))
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
                              (acl2::print-levelp print)
                              (member print-base '(10 16))
                              (booleanp untranslatep)
                              (booleanp produce-function)
                              (member-eq non-executable '(t nil :auto))
                              (booleanp produce-theorem)
                              (booleanp prove-theorem)
                              (booleanp restrict-theory))
                  :stobjs state
                  :mode :program ; todo
                  ))
  (b* (;; Check whether this call to the lifter has already been made:
       (previous-result (previous-lifter-result whole-form state))
       ((when previous-result)
        (mv nil '(value-triple :redundant) state))
       ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       ((mv erp parsed-executable state)
        (if (stringp executable)
            ;; it's a filename, so parse the file:
            (acl2::parse-executable executable state)
          ;; it's already a parsed-executable:
          (mv nil executable state)))
       ((when erp)
        (er hard? 'def-unrolled-fn "Error (~x0) parsing executable: ~s1." erp executable)
        (mv t nil state))
       (executable-type (acl2::parsed-executable-type parsed-executable))
       ;; Lift the function to obtain the DAG:
       ((mv erp result-dag assumptions lifter-rules-used assumption-rules-used state)
        (unroll-x86-code-core target parsed-executable
          extra-assumptions suppress-assumptions inputs-disjoint-from stack-slots position-independent
          inputs output use-internal-contextsp prune extra-rules remove-rules extra-assumption-rules
          step-limit step-increment memoizep monitor print print-base untranslatep state))
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
       (64-bitp (member-equal executable-type '(:mach-o-64 :pe-64 :elf-64)))
       ;; Now sort the formals:
       (param-names (if (and 64-bitp
                             (not (equal :skip inputs)))
                        ;; The user gave names to the params, and those vars will be put in for the registers:
                        (strip-cars inputs) ; fixme: handle array and pointer values (just look at the dag vars?)
                      ;; The register names may be being introduced (todo: deprecate this?):
                      '(rdi rsi rdx rcx r8 r9))) ; todo: handle 32-bit calling convention
       (common-formals (append param-names '(x86))) ; todo: handle 32-bit calling convention
       ;; these will be ordered like common-formals:
       (expected-formals (intersection-eq common-formals fn-formals))
       (unexpected-formals (acl2::merge-sort-symbol< (set-difference-eq fn-formals common-formals))) ; todo: warn if inputs given?  maybe x86 will sometimes be needed?
       (fn-formals (append expected-formals unexpected-formals))
       ;; Do we want a check like this?
       ;; ((when (not (subsetp-eq result-vars '(x86 text-offset))))
       ;;  (mv t (er hard 'lifter "Unexpected vars, ~x0, in result DAG!" (set-difference-eq result-vars '(x86 text-offset))) state))
       ;; TODO: Maybe move some of this to the -core function:
       ;; (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
       ;;            (set-print-base-radix print-base state)
       ;;          state)) ; todo: do this better
       ((when (intersection-eq result-dag-fns '(run-until-stack-shorter-than run-until-return)))
        (if (< result-dag-size 100000) ; todo: make customizable
            (progn$ (cw "(Term:~%")
                    (cw "~X01" (let ((term (dag-to-term result-dag)))
                                 (if untranslatep
                                     (untranslate term nil (w state))
                                   term))
                        nil)
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
                                                                   ',(acl2::make-interpreted-function-alist (acl2::get-non-built-in-supporting-fns-list result-dag-fns acl2::*axe-evaluator-functions* (w state)) (w state))
                                                                   '0 ;array depth (not very important)
                                                                   )))
               (function-body-untranslated (if untranslatep (untranslate function-body nil (w state)) function-body)) ;todo: is this unsound (e.g., because of user changes in how untranslate works)?
               (function-body-retranslated (acl2::translate-term function-body-untranslated 'def-unrolled-fn (w state)))
               ;; TODO: I've seen this check fail when (if x y t) got turned into (if (not x) (not x) y):
               ((when (not (equal function-body function-body-retranslated))) ;todo: make a safe-untranslate that does this check?
                (er hard? 'lifter "Problem with function body.  Untranslating and then re-translating did not give original body.  Body was ~X01" function-body nil)
                (mv :problem-with-function-body nil))
               ;;(- (cw "Runes used: ~x0" runes)) ;TODO: Have Axe return these?
               ;;use defun-nx by default because stobj updates are not all let-bound to x86
               (non-executable (if (eq :auto non-executable)
                                   (if (member-eq 'x86 fn-formals) ; there may be writes to the stobj (perhaps with unresolved reads around them), so we use defun-nx (todo: do a more precise check)
                                       ;; (eq :all output) ; we use defun-nx since there is almost certainly a stobj update (and updates are not properly let-bound)
                                       t
                                     nil)
                                 non-executable))
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
       (produce-theorem (and produce-theorem
                             (if (not produce-function)
                                 ;; todo: do something better in this case?
                                 (prog2$ (cw "NOTE: Suppressing theorem because :produce-function is nil.~%")
                                         nil)
                               t)))
       (defthms ; either nil or a singleton list
         (and produce-theorem
              (let* ((defthm `(defthm ,(acl2::pack$ lifted-name '-correct)
                                (implies (and ,@assumptions)
                                         (equal (run-until-return x86)
                                                (,lifted-name ,@fn-formals)))
                                :hints ,(if restrict-theory
                                            `(("Goal" :in-theory '(,lifted-name ;,@runes ;without the runes here, this won't work
                                                                   )))
                                          `(("Goal" :in-theory (enable ,@lifter-rules-used
                                                                       ,@assumption-rules-used))))
                                :otf-flg t))
                     (defthm (if prove-theorem
                                 defthm
                               `(skip-proofs ,defthm))))
                (list defthm))))
       (events (cons defconst-form (append defuns defthms)))
       (event-names (acl2::strip-cadrs events))
       (event `(progn ,@events))
       (event (acl2::extend-progn event `(table x86-lifter-table ',whole-form ',event)))
       (event (acl2::extend-progn event `(value-triple '(,@event-names))))
       ((mv elapsed state) (acl2::real-time-since start-real-time state))
       (- (cw " (Unrolling ~x0 took " lifted-name)
          (acl2::print-to-hundredths elapsed)
          (cw "s, not including event submission.)~%")))
    (mv nil event state)))

;TODO: Add show- variant
;bad name?
;; TODO: :print nil is not fully respected
;; Creates some events to represent the unrolled computation, including a defconst for the DAG and perhaps a defun and a theorem.
(acl2::defmacrodoc def-unrolled (&whole whole-form
                                  lifted-name
                                  executable
                                  &key
                                  (target ':entry-point)
                                  (extra-assumptions 'nil)
                                  (suppress-assumptions 'nil)
                                  (inputs-disjoint-from ':code)
                                  (stack-slots '100)
                                  (position-independent ':auto)
                                  (inputs ':skip)
                                  (output ':all)
                                  (use-internal-contextsp 't)
                                  (prune '1000)
                                  (extra-rules 'nil)
                                  (remove-rules 'nil)
                                  (extra-assumption-rules 'nil)
                                  (step-limit '1000000)
                                  (step-increment '100)
                                  (memoizep 't)
                                  (monitor 'nil)
                                  (print ':brief)             ;how much to print
                                  (print-base '10)
                                  (untranslatep 't)
                                  (produce-function 't)
                                  (non-executable ':auto)
                                  (produce-theorem 'nil)
                                  (prove-theorem 'nil)
                                  (restrict-theory 't)       ;todo: deprecate
                                  )
  `(,(if (acl2::print-level-at-least-tp print) 'make-event 'acl2::make-event-quiet)
    (def-unrolled-fn
      ',lifted-name
      ,target
      ,executable ; gets evaluated
      ,extra-assumptions
      ',suppress-assumptions
      ',inputs-disjoint-from
      ',stack-slots
      ',position-independent
      ',inputs
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
      ',untranslatep
      ',produce-function
      ',non-executable
      ',produce-theorem
      ',prove-theorem
      ',restrict-theory
      ',whole-form
      state))
  :parents (lifters)
  :short "Lift an x86 binary function to create a DAG, unrolling loops as needed."
  :args ((lifted-name "The name to use for the generated function and constant (the latter surrounded by stars).")
         (executable "The x86 binary executable that contains the target function.  Usually a string (a filename), or this can be a parsed executable of the form created by defconst-x86.")
         (target "Where to start lifting (a numeric offset, the name of a subroutine (a string), or the symbol :entry-point)")
         (extra-assumptions "Extra assumptions for lifting, in addition to the standard-assumptions")
         (suppress-assumptions "Whether to suppress the standard assumptions.  This does not suppress any assumptions generated about the :inputs.")
         (inputs-disjoint-from "What to assume about the inputs (specified using the :inputs option) being disjoint from the sections/segments in the executable.  The value :all means assume the inputs are disjoint from all sections/segments.  The value :code means assume the inputs are disjoint from the code/text section.  The value nil means do not include any assumptions of this kind.")
         (stack-slots "How much available stack space to assume exists.") ; 4 or 8 bytes each?
         (position-independent "Whether to attempt the lifting without assuming that the binary is loaded at a particular position.")
         (inputs "Either the special value :skip (meaning generate no additional assumptions on the input) or a doublet list pairing input names with types.  Types include things like u32, u32*, and u32[2].")
         (output "An indication of which state component(s) will hold the result of the computation being lifted.  See output-indicatorp.")
         (use-internal-contextsp "Whether to use contextual information from ovararching conditionals when simplifying DAG nodes.")
         ;; todo: better name?  only for precise pruning:
         (prune "Whether to prune DAGs using precise contexts.  Either t or nil or a natural number representing an (exclusive) limit on the maximum size of the DAG if represented as a term.  This kind of pruning can blow up if attempted for DAGs that represent huge terms.")
         ;; todo: how do these affect assumption simp:
         (extra-rules "Rules to use in addition to (lifter-rules32-all) or (lifter-rules64-all).")
         (remove-rules "Rules to turn off.")
         (extra-assumption-rules "Extra rules to be used when simplifying assumptions.")
         (step-limit "Limit on the total number of model steps (instruction executions) to allow.")
         (step-increment "Number of model steps to allow before pausing to simplify the DAG and remove unused nodes.")
         (memoizep "Whether to memoize during rewriting (when not using contextual information -- as doing both would be unsound).")
         (monitor "Rule names (symbols) to be monitored when rewriting.") ; during assumptions too?
         (print "Verbosity level.") ; todo: values
         (print-base "Base to use when printing during lifting.  Must be either 10 or 16.")
         (untranslatep "Whether to untranslate term when printing.")
         (produce-function "Whether to produce a function, not just a constant DAG, representing the result of the lifting.")
         (non-executable "Whether to make the generated function non-executable, e.g., because stobj updates are not properly let-bound.  Either t or nil or :auto.")
         (produce-theorem "Whether to try to produce a theorem (possibly skip-proofed) about the result of the lifting.")
         (prove-theorem "Whether to try to prove the theorem with ACL2 (rarely works, since Axe's Rewriter is different and more scalable than ACL2's rewriter).")
         (restrict-theory "To be deprecated..."))
  :description ("Given an ax86 binary function, extract an equivalent term in DAG form, by symbolic execution including inlining all functions and unrolling all loops."
                "This event creates a @(see defconst) whose name is derived from the @('lifted-name') argument."
                "To inspect the resulting DAG, you can simply enter its name at the prompt to print it."))
