; An unrolling lifter xfor x86 code (based on Axe)
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

(include-book "kestrel/utilities/erp" :dir :system)
(include-book "kestrel/utilities/real-time-since" :dir :system)
(include-book "kestrel/utilities/widen-margins" :dir :system)
(include-book "kestrel/utilities/progn" :dir :system)
(include-book "kestrel/utilities/defmacrodoc" :dir :system)
(include-book "kestrel/x86/parsers/parse-executable" :dir :system)
(include-book "kestrel/x86/parsers/parsed-executable-tools" :dir :system)
(include-book "kestrel/bv/intro" :dir :system) ; reduce?
(include-book "kestrel/bv/std" :dir :system) ; reduce?
(include-book "kestrel/bv/rules3" :dir :system) ;for bvor-of-bvshl-and-bvshr-becomes-leftrotate, in core-rules-bv
(include-book "kestrel/bv/bvsx-rules" :dir :system)
(include-book "kestrel/bv/trim-elim-rules-bv" :dir :system)
(include-book "kestrel/axe/trim-intro-rules-axe" :dir :system)
(include-book "kestrel/axe/bv-intro-rules" :dir :system)
(include-book "kestrel/bv/leftrotate-rules" :dir :system)
(include-book "kestrel/bv/sbvdiv-rules" :dir :system)
(include-book "kestrel/bv/bvif2" :dir :system)
(include-book "kestrel/bv/bvequal-rules" :dir :system)
(include-book "kestrel/bv/putbits" :dir :system)
(include-book "kestrel/bv/ash" :dir :system)
(include-book "kestrel/axe/rules1" :dir :system)
(include-book "rewriter")
(include-book "../step-increments")
(include-book "../rule-limits")
(include-book "../rewriter-basic")
(include-book "../prune-dag-precisely")
(include-book "../prune-dag-approximately")
(include-book "../lifter-common")
(include-book "../equivalent-dags")
(include-book "../make-term-into-dag-basic")
(include-book "../bv-rules-axe0")
(include-book "../convert-to-bv-rules-axe")
(include-book "../bv-array-rules-axe") ;reduce?
(include-book "assumptions")
(include-book "run-until-return")
(include-book "pc")
(include-book "rule-lists")
(include-book "read-over-write-rules")
(include-book "write-over-write-rules")
(include-book "lifter-rules")
(include-book "kestrel/arithmetic-light/plus" :dir :system)
(include-book "kestrel/arithmetic-light/fix" :dir :system)
(include-book "kestrel/arithmetic-light/minus" :dir :system)
(include-book "kestrel/x86/parsers/elf-tools" :dir :system) ; for the user's convenience
(include-book "kestrel/axe/util2" :dir :system) ; for the user's convenience
(local (include-book "kestrel/utilities/get-real-time" :dir :system))
(local (include-book "kestrel/utilities/w" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The presence of any of these function in the DAG indicates that the symbolic
;; execution is incomplete:
(defconst *incomplete-run-fns* '(run-until-return-aux
                                 ;run-until-sp-is-above
                                 step32))

;; The presence of any of these function in the DAG indicates an error state
;; arising during lifting (perhaps only on one branch of the execution, and
;; perhaps we can prune away that branch later):
(defconst *error-fns* '(error32))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable myquotep ; todo: loop involving acl2::simplify-dag-basic-return-type-corollary-2
                           intersection-equal
                           acl2::myquotep-when-axe-treep
                           state-p
                           mv-nth
                           natp
                           string-append
                           string-append-lst)))

(local (in-theory (enable acl2::weak-dagp-when-pseudo-dagp
                          acl2::true-listp-when-symbol-listp-rewrite-unlimited)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
  ;; Create a term representing the extraction of the indicated output from TERM.
  ;; why "normal"?  maybe "component" ?  or non-trivial?
  ;; This can translate some parts of the output-indicator.
  (defun wrap-in-normal-output-extractor (output-indicator term wrld)
    (declare (xargs :guard (and ;; see above comment on output-indicator
                             (plist-worldp wrld))
                    :mode :program ; because of translate-term ; todo: do that outside this function, while also checking the output-indicator?
                     ))
    (if (symbolp output-indicator)
        (case output-indicator
          ;; Extract a 64-bit register:
          (:x0 `(x0 ,term)) ; odd, since this always gives 0
          (:x1 `(x1 ,term))
          ;; todo: more
          (:a0 `(a0 ,term)) ; return value 0
          (:a1 `(a1 ,term)) ; return value 1
          ;; todo: more

          ;; ;; (:eax (rax ,term))
          ;; (:xmm0 `(bvchop '128 (xr ':zmm '0 ,term)))
          ;; (:ymm0 `(bvchop '256 (xr ':zmm '0 ,term)))
          ;; (:zmm0 `(xr ':zmm '0 ,term)) ; seems to already be unsigned
          ;; ;; Extract a CPU flag: ; todo: more?
          ;; (:af `(get-flag ':af ,term)) ; todo: more
          ;; (:cf `(get-flag ':cf ,term))
          ;; (:of `(get-flag ':of ,term))
          ;; (:pf `(get-flag ':pf ,term))
          ;; (:sf `(get-flag ':sf ,term))
          ;; (:zf `(get-flag ':zf ,term))
          (t (er hard? 'wrap-in-normal-output-extractor "Unsupported output-indicator: ~x0." output-indicator)))
      (if (not (and (consp output-indicator)
                    (true-listp output-indicator)))
          (er hard? 'wrap-in-normal-output-extractor "Bad output-indicator: ~x0." output-indicator)
        (case (ffn-symb output-indicator)
          ;; ;; (:register <N>)
          ;; (:register (if (and (eql 1 (len (fargs output-indicator)))
          ;;                     (natp (farg1 output-indicator)) ;todo: what is the max allowed?
          ;;                     )
          ;;                `(xr ':rgf ',(farg1 output-indicator) ,term)
          ;;              (er hard? 'wrap-in-normal-output-extractor "Bad output-indicator: ~x0." output-indicator)))
          ;; ;;  (:register-bool <N>)
          ;; ;; TODO: Deprecate this case but the tester uses :register-bool
          ;; ;; On Linux with gcc, a C function that returns a boolean has been observed to only set the low byte of RAX
          ;; ;; TODO: Should we chop to a single bit?
          ;; (:register-bool (if (and (eql 1 (len (fargs output-indicator)))
          ;;                          (natp (farg1 output-indicator)) ;todo: what is the max allowed?
          ;;                          )
          ;;                     `(bvchop '8 (xr ':rgf ',(farg1 output-indicator) ,term))
          ;;                   (er hard? 'wrap-in-normal-output-extractor "Bad output-indicator: ~x0." output-indicator)))
          ;; ;; (:mem32 <ADDR-TERM>)
          ;; ;; TODO: Add other sizes of :memXXX
          ;; (:mem32 (if (eql 1 (len (fargs output-indicator)))
          ;;             `(read '4 ,(translate-term (farg1 output-indicator) 'wrap-in-normal-output-extractor wrld) ,term)
          ;;           (er hard? 'wrap-in-normal-output-extractor "Bad output-indicator: ~x0." output-indicator)))
          ;; ;; (:byte-array <ADDR-TERM> <LEN>) ; not sure what order is best for the args

          ;; (:read <N> <ADDR-TERM>)
          (:read (if (= 2 (len (fargs output-indicator)))
                     (translate-term `(read ,(farg1 output-indicator) ,(farg2 output-indicator) ,term) 'wrap-in-normal-output-extractor wrld)
                   (er hard? 'wrap-in-normal-output-extractor "Bad output-indicator: ~x0." output-indicator)))

          ;; (:byte-array <element-count> <addr-term>) ; not sure what order is best for the args
          (:byte-array (if (and (= 2 (len (fargs output-indicator)))
                                ;; (posp (farg2 output-indicator)) ; number of bytes to read
                                )
                           `(acl2::list-to-byte-array (read-bytes ,(translate-term (farg2 output-indicator) 'wrap-in-normal-output-extractor wrld) ; note the order
                                                                  ,(translate-term (farg1 output-indicator) 'wrap-in-normal-output-extractor wrld)
                                                                  ,term))
                         (er hard? 'wrap-in-normal-output-extractor "Bad output-indicator: ~x0." output-indicator)))

          ;; ;; (:array <bits-per-element> <element-count> <addr-term>) ; not sure what order is best for the args
          ;; (:array (if (and (eql 3 (len (fargs output-indicator)))
          ;;                  (posp (farg1 output-indicator))
          ;;                  (= 0 (mod (farg1 output-indicator) 8)) ; bits-per-element must be a multiple of 8
          ;;                  (natp (farg2 output-indicator)) ; or use posp?
          ;;                  )
          ;;             `(acl2::list-to-bv-array ',(farg1 output-indicator)
          ;;                                      (read-chunks ,(translate-term (farg3 output-indicator) 'wrap-in-normal-output-extractor wrld)
          ;;                                                   ',(farg2 output-indicator)
          ;;                                                   ',(/ (farg1 output-indicator) 8)
          ;;                                                  ,term))
          ;;           (er hard? 'wrap-in-normal-output-extractor "Bad output-indicator: ~x0." output-indicator)))
          ;; (:bv-list ;; (:bv-list <bits-per-element> <element-count> <addr-term>)
          ;;  (if (and (= 3 (len (fargs output-indicator)))
          ;;           (posp (farg1 output-indicator))
          ;;           (= 0 (mod (farg1 output-indicator) 8)) ; bits-per-element must be a multiple of 8
          ;;           (natp (farg2 output-indicator)) ; or use posp?
          ;;           )
          ;;      `(read-chunks ,(translate-term (farg3 output-indicator) 'wrap-in-normal-output-extractor wrld)
          ;;                    ',(farg2 output-indicator)
          ;;                    ',(/ (farg1 output-indicator) 8)
          ;;                    ,term)
          ;;    (er hard? 'wrap-in-normal-output-extractor "Bad output-indicator: ~x0." output-indicator)))
          ;; ;; (:tuple ... output-indicators ...)
          ;; todo: what if no args?
          (:tuple (acl2::make-cons-nest (wrap-in-normal-output-extractors (fargs output-indicator) term wrld)))
          (otherwise (er hard? 'wrap-in-normal-output-extractor "Bad output indicator: ~x0" output-indicator))
          ))))

  (defun wrap-in-normal-output-extractors (output-indicators term wrld)
    (declare (xargs :guard (and (true-listp output-indicators)
                                (plist-worldp wrld))
;;                    :mode :program ; because of translate-term
                    ))
    (if (endp output-indicators)
        nil
      (cons (wrap-in-normal-output-extractor (first output-indicators) term wrld)
            (wrap-in-normal-output-extractors (rest output-indicators) term wrld)))))

;; (local (acl2::make-flag wrap-in-normal-output-extractor))

;; (defthm-flag-wrap-in-normal-output-extractor
;;   (defthm pseudo-termp-of-wrap-in-normal-output-extractor
;;     (implies (and (pseudo-termp term)
;;                   (plist-worldp wrld))
;;              (pseudo-termp (wrap-in-normal-output-extractor output-indicator term wrld)))
;;     :flag wrap-in-normal-output-extractor)
;;   (defthm pseudo-term-listp-of--wrap-in-normal-output-extractors
;;     (implies (and (pseudo-termp term)
;;                   (true-listp output-indicators)
;;                   (plist-worldp wrld))
;;              (pseudo-term-listp (wrap-in-normal-output-extractors output-indicators term wrld)))
;;     :flag wrap-in-normal-output-extractors))

;; Wraps TERM as indicated by OUTPUT-INDICATOR.
;; todo: reorder args?
(defund wrap-in-output-extractor (output-indicator term wrld)
  (declare (xargs :guard (plist-worldp wrld)
                  :mode :program ; because of translate-term
                  ))
  (if (eq :all output-indicator)
      term
    (wrap-in-normal-output-extractor output-indicator term wrld)))

;; (defthm pseudo-termp-of-wrap-in-output-extractor
;;   (implies (and (pseudo-termp term)
;;                 (plist-worldp wrld))
;;            (pseudo-termp (wrap-in-output-extractor output-indicator term wrld)))
;;   :hints (("Goal" :in-theory (enable wrap-in-output-extractor))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-risc-v-lifter-table (state)
  (declare (xargs :stobjs state))
  (table-alist 'risc-v-lifter-table (w state)))

;TODO: Use the generic utility for redundancy checking
;WHOLE-FORM is a call to the lifter
(defun previous-lifter-result (whole-form state)
  (declare (xargs :stobjs state))
  (let* ((table-alist (get-risc-v-lifter-table state)))
    (if (not (alistp table-alist))
        (hard-error 'previous-lifter-result "Invalid table alist for risc-v-lifter-table: ~x0."
                    (acons #\0 table-alist nil))
      (let ((previous-result (lookup-equal whole-form table-alist)))
        (if previous-result
            (prog2$ (cw "NOTE: The call to the lifter ~x0 is redundant.~%" whole-form)
                    previous-result)
          nil)))))

;; Repeatedly rewrite DAG to perform symbolic execution.  Perform
;; STEP-INCREMENT steps at a time, until the run finishes, STEPS-LEFT is
;; reduced to 0, or a loop or an unsupported instruction is detected.
;; Returns (mv erp result-dag-or-quotep state).
;; WARNING: Keep in sync with the x86 version.
(defun repeatedly-run (steps-done step-limit step-increment
                                  dag ; the state may be wrapped in an output-extractor
                                  rule-alist pruning-rule-alist
                                  assumptions
                                  step-opener-rule ; the rule that gets limited
                                  rules-to-monitor
                                  prune-precise prune-approx
                                  normalize-xors count-hits print print-base untranslatep memoizep
                                  ;; could pass in the stop-pcs, if any
                                  state)
  (declare (xargs :guard (and (natp steps-done)
                              (natp step-limit)
                              (step-incrementp step-increment)
                              (pseudo-dagp dag)
                              (rule-alistp rule-alist)
                              (rule-alistp pruning-rule-alist)
                              (pseudo-term-listp assumptions)
                              (symbolp step-opener-rule)
                              (symbol-listp rules-to-monitor)
                              (or (eq nil prune-precise)
                                  (eq t prune-precise)
                                  (natp prune-precise))
                              (or (eq nil prune-approx)
                                  (eq t prune-approx)
                                  (natp prune-approx))
                              (normalize-xors-optionp normalize-xors)
                              (count-hits-argp count-hits)
                              (print-levelp print)
                              (member print-base '(10 16))
                              (booleanp untranslatep)
                              (booleanp memoizep))
                  :measure (nfix (+ 1 (- (nfix step-limit) (nfix steps-done))))
                  :stobjs state
                  :hints (("Goal" :in-theory (disable min)))
                  :guard-hints (("Goal" :in-theory (disable min)))))
  (if (or (not (mbt (and (natp steps-done)
                         (natp step-limit))))
          (<= step-limit steps-done))
      (mv (erp-nil) dag state)
    (b* (;; Decide how many steps to do this time:
         (this-step-increment (this-step-increment step-increment steps-done))
         (steps-for-this-iteration (min (- step-limit steps-done) this-step-increment))
         ((when (not (posp steps-for-this-iteration))) ; use mbt?
          (er hard? 'repeatedly-run "Temination problem.")
          (mv :termination-problem nil state))
         (- (cw "(Running (up to ~x0 steps):~%" steps-for-this-iteration))
         ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
         (old-dag dag) ; so we can see if anything changed
         ;; (- (and print (progn$ (cw "(DAG before stepping:~%")
         ;;                       (cw "~X01" dag nil)
         ;;                       (cw ")~%"))))
         ;; Limit the run to the given number of steps:
         (limits nil) ; todo: call this empty-rule-limits?
         (limits (add-limit-for-rules (list step-opener-rule)
                                            steps-for-this-iteration
                                            limits)) ; don't recompute for each small run?
         ;; Do the run:
         ((mv erp dag-or-constant limits
              state
              )
          (acl2::simplify-dag-risc-v dag
                                     assumptions
                                     rule-alist
                                     nil ; interpreted-function-alist
                                     (known-booleans (w state))
                                     normalize-xors
                                     limits
                                     memoizep
                                     count-hits
                                     print
                                     rules-to-monitor
                                     nil ; *no-warn-ground-functions*
                                     '(program-at) ; fns-to-elide ; todo: this is old
                                     state
                                     ))
         ((when erp) (mv erp nil state))
         ;; usually 0, unless we are done (can this ever be negative?):
         (remaining-limit ;; todo: clean this up: there is only a single rule:
           (limit-for-rule step-opener-rule
                                 limits))
         (steps-done-this-time (- steps-for-this-iteration (ifix remaining-limit))) ; todo: drop the ifix
         ((mv elapsed state) (real-time-since start-real-time state))
         (- (cw " (~x0 steps took " steps-done-this-time)
            (print-to-hundredths elapsed) ; todo: could have real-time-since detect negative time
            (cw "s.)"))
         (- (cw ")~%")) ; matches "(Running"
         ((when (quotep dag-or-constant))
          (cw "Result is a constant!~%")
          (mv (erp-nil) dag-or-constant state))
         (dag dag-or-constant) ; it wasn't a constant, so name it "dag"
         ;; TODO: Consider not pruning if this increment didn't create any new branches:
         ;; Prune the DAG quickly but possibly imprecisely (actually, I've seen this be quite slow!):
         ((mv erp dag-or-constant state) (maybe-prune-dag-approximately prune-approx
                                                                              dag
                                                                              (remove-assumptions-about *non-stp-assumption-functions* assumptions)
                                                                              print
                                                                              60000 ; todo: pass in
                                                                              state))
         ((when erp) (mv erp nil state))
         ((when (quotep dag-or-constant))
          (cw "Result is a constant!~%")
          (mv (erp-nil) dag-or-constant state))
         (dag dag-or-constant) ; it wasn't a constant, so name it "dag"
         ;; (- (and print (progn$ (cw "(DAG after first pruning:~%")
         ;;                       (cw "~X01" dag nil)
         ;;                       (cw ")~%"))))
         ;; Prune precisely if feasible:
         ;; TODO: Maybe don't prune if the run has completed (but do simplify in that case)?
         ((mv erp dag-or-constant state)
          (maybe-prune-dag-precisely prune-precise ; if a natp, can help prevent explosion.
                                           dag
                                           ;; the assumptions used during lifting (program-at, MXCSR assumptions, etc) seem unlikely
                                           ;; to be helpful when pruning, and user assumptions seem like they should be applied by the
                                           ;; rewriter duing lifting (TODO: What about assumptions only usable by STP?)
                                           nil ; assumptions ; todo: include assumptions about canonical?
                                           :none
                                           pruning-rule-alist
                                           nil ; interpreted-function-alist
                                           rules-to-monitor
                                           t ;call-stp
                                           print
                                           state))
         ((when erp) (mv erp nil state))
         ((when (quotep dag-or-constant))
          (cw "Result is a constant!~%")
          (mv (erp-nil) dag-or-constant state))
         (dag dag-or-constant) ; it wasn't a constant, so name it "dag"
         (- (and print ;(print-level-at-least-tp print)
                 (progn$ (cw "(DAG after this limited run:~%")
                         (cw "~X01" dag nil)
                         (cw ")~%"))))
         ;; TODO: Error if dag too big (must be able to add it to old dag, or make a version of equivalent-dagsp that signals an error):
         ;; (- (and print (progn$ (cw "(DAG after second pruning:~%")
         ;;                       (cw "~X01" dag nil)
         ;;                       (cw ")~%"))))
         ;; TODO: If pruning did something, consider doing another rewrite here (pruning may have introduced bvchop or bool-fix$inline).  But perhaps now there are enough rules used in pruning to handle that?
         (dag-fns (dag-fns dag))

         ;; TODO: Maybe don't prune if the run completed and there are no error branches?
         (run-completedp (not (intersection-eq *incomplete-run-fns* dag-fns))) ; todo: call contains-anyp-eq
         ((mv erp nothing-changedp) (if run-completedp
                                        (mv nil nil) ; we know something changed since the run is now complete
                                      (equivalent-dagsp2 dag old-dag))) ; todo: can we test equivalence up to xor nest normalization? ; todo: check using the returned limits whether any work was done (want if was simplification but not stepping?)?
         ((when erp) (mv erp nil state))

         ;; Stop if we hit an unimplemented instruction (it may be on an unreachable branch, but we've already pruned -- todo: prune harder?):
         ;; ((when ..)
         ;;  (progn$ (cw "WARNING: UNIMPLEMENTED INSTRUCTION.~%") ; todo: print the name of the instruction
         ;;          (cw "~%")
         ;;          (mv :unimplemented-instruction dag state)))

         ;; ((when nothing-changedp)
         ;;  (cw "Note: Stopping the run because nothing changed.~%") ; todo: check if one of the *incomplete-run-fns* remains (but what if we hit one of the stop-pcs?)
         ;;  ;; check how many steps used?
         ;;  ;; todo: check for the error-fns here
         ;;  (mv (erp-nil) dag state))
 ; todo: return an error?  or maybe this can happen if we hit one of the stop-pcs
         )
      (if (or run-completedp nothing-changedp)
          ;; stop if the run is done
          ;; Simplify one last time (since pruning may have done something -- todo: skip this if pruning did nothing):
          (b* ((- (if run-completedp
                      (cw " The run completed normally.~%")
                    (cw " The run completed abnormally (nothing changed).~%")))
               (- (cw "(Doing final simplification:~%"))
               ((mv erp dag-or-constant state) ; todo: check if it is a constant?
                (mv-let (erp result limits state)
                  (acl2::simplify-dag-risc-v dag
                                             assumptions
                                             rule-alist
                                             nil ; interpreted-function-alist
                                             (known-booleans (w state))
                                             normalize-xors
                                             limits
                                             memoizep
                                             count-hits
                                             print
                                             rules-to-monitor
                                             nil ; *no-warn-ground-functions*
                                             '(program-at code-segment-assumptions32-for-code) ; fns-to-elide
                                             state
                                             )
                  (declare (ignore limits)) ; todo: use the limits?
                  (mv erp result state)))
               ((when erp) (mv erp nil state))
               ;; todo: also prune here, if the simplfication does anything?
               (- (cw " Done with final simplification.)~%")) ; balances "(Doing final simplification"
               ;; Check for error branches (TODO: What if we could prune them away with more work?):
               (dag-fns (if (quotep dag-or-constant) nil (dag-fns dag-or-constant)))
               (error-branch-functions (intersection-eq *error-fns* dag-fns))
               (incomplete-run-functions (intersection-eq *incomplete-run-fns* dag-fns dag-fns))
               ((when error-branch-functions)
                (cw "~%")
                (print-dag-nicely dag) ; use the print-base?
                (er hard? 'repeatedly-run "Unresolved error branches are present (see calls of ~&0 in the term or DAG above)." error-branch-functions)
                (mv :unresolved-error-branches nil state))
               ;; Check for an incomplete run (TODO: What if we could prune away such branches with more work?):
               ((when incomplete-run-functions)
                (cw "~%")
                (print-dag-nicely dag) ; use the print-base?
                (er hard? 'repeatedly-run " Incomplete run (see calls of ~%0 the DAG above: ~&0 in the term or DAG above)." incomplete-run-functions)
                (mv :incomplete-run nil state)))
            (mv (erp-nil) dag-or-constant state))
        ;; Continue the symbolic execution:
        (b* ((steps-done (+ steps-for-this-iteration steps-done))
             (- (cw "(Steps so far: ~x0.)~%" steps-done))
             (state ;; Print as a term unless it would be huge:
               (if (print-level-at-least-tp print)
                   (print-dag-nicely-with-base dag (concatenate 'string "after " (nat-to-string steps-done) " steps") untranslatep print-base state)
                 state)))
          (repeatedly-run steps-done step-limit
                          step-increment
                          dag rule-alist pruning-rule-alist assumptions step-opener-rule rules-to-monitor prune-precise prune-approx normalize-xors count-hits print print-base untranslatep memoizep
                          state))))))

;; Returns (mv erp result-dag-or-quotep
;;                 ; assumptions input-assumption-vars lifter-rules-used assumption-rules-used term-to-simulate
;;                state).
;; This will also be called by the formal unit tester.
(defun unroll-risc-v-code-core (target
                                parsed-executable
                                extra-assumptions ; todo: can these introduce vars for state components?  now we have :inputs for that.  could also replace register expressions with register names (vars) -- see what do do for the Tester.
                                ;;suppress-assumptions
                                ;;inputs-disjoint-from
                                stack-slots
                                existing-stack-slots
                                position-independent
                                ;;inputs
                                ;;type-assumptions-for-array-varsp
                                output-indicator
                                prune-precise
                                prune-approx
                                extra-rules
                                remove-rules
                                ;; extra-assumption-rules ; todo: why "extra"?
                                ;; remove-assumption-rules
                                step-limit
                                step-increment
                                ;; stop-pcs
                                memoizep
                                monitor
                                normalize-xors
                                count-hits
                                print
                                print-base
                                untranslatep
                                state)
  (declare (xargs :guard (and (acl2::lifter-targetp target)
                              ;; parsed-executable ; todo: add a guard (even if it's weak for now)
                              (true-listp extra-assumptions) ; untranslated terms
                              ;;(booleanp suppress-assumptions)
                              ;; (member-eq inputs-disjoint-from '(nil :code :all))
                              (natp stack-slots)
                              (or (natp existing-stack-slots)
                                  (eq :auto existing-stack-slots))
                              (member-eq position-independent '(t nil ; :auto
                                                                ))
                              ;; (or (eq :skip inputs) (names-and-typesp inputs))
                              ;; (booleanp type-assumptions-for-array-varsp)
                              ;; no recognizer for output-indicator, we just call wrap-in-output-extractor and see if it returns an error
                              (or (eq nil prune-precise)
                                  (eq t prune-precise)
                                  (natp prune-precise))
                              (or (eq nil prune-approx)
                                  (eq t prune-approx)
                                  (natp prune-approx))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              ;; (symbol-listp extra-assumption-rules)
                              ;; (symbol-listp remove-assumption-rules)
                              (natp step-limit)
                              (step-incrementp step-increment)
                              ;; (nat-listp stop-pcs)
                              (booleanp memoizep)
                              (or (symbol-listp monitor)
                                  (eq :debug monitor))
                              (normalize-xors-optionp normalize-xors)
                              (count-hits-argp count-hits)
                              (print-levelp print)
                              (member print-base '(10 16))
                              (booleanp untranslatep))
                  :stobjs state
                  :mode :program ; todo: need a magic wrapper for translate-terms (must translate at least the user-supplied assumptions)
                  ))
  (b* ((- (cw "(Lifting ~s0.~%" target)) ;todo: print the executable name, also handle non-string targets better
       ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       (state (acl2::widen-margins state))
       ;; Get and check the executable-type:
       (executable-type (acl2::parsed-executable-type parsed-executable))
       ;; (64-bitp (member-equal executable-type *executable-types64*))
       (- (and (acl2::print-level-at-least-briefp print) (cw "(Executable type: ~x0.)~%" executable-type)))
       ;; Make sure it's a RISC-V executable:
       (- (acl2::ensure-risc-v parsed-executable))
       ;; Handle a :position-independent of :auto:

       (position-independentp position-independent)
       ;; (position-independentp (if (eq :auto position-independent)
       ;;                            (if (eq executable-type :mach-o-64)
       ;;                                t ; since clang seems to produce position-independent code by default ; todo: look at the PIE bit in the header.
       ;;                              (if (eq executable-type :elf-64)
       ;;                                  (let ((elf-type (parsed-elf-type parsed-executable)))
       ;;                                    (prog2$ (cw "ELF type: ~x0.~%" elf-type)
       ;;                                            (if (parsed-elf-program-header-table parsed-executable)
       ;;                                                ;; For ELF64, we treat :dyn and :rel as position-independent (addresses relative to the var base-address) and :exec as absolute:
       ;;                                                (if (member-eq elf-type '(:rel :dyn)) t nil)
       ;;                                              ;; TODO: Get this to work:
       ;;                                              nil)))
       ;;                                ;; TODO: Think about the other cases:
       ;;                                t))
       ;;                          ;; the user supplied a value for position-independent, so use it:
       ;;                          position-independent))

       (- (if position-independentp (cw " Using position-independent lifting.~%") (cw " Using non-position-independent lifting.~%")))
       ;; (new-style-elf-assumptionsp (and (eq :elf-64 executable-type)
       ;;                                  ;; todo: remove this, but we have some unlinked ELFs without sections.  we also have some unlinked ELFs that put both the text and data segments at address 0 !
       ;;                                  ;(parsed-elf-program-header-table parsed-executable) ; there are segments present (todo: improve the "new" behavior to use sections when there are no segments)
       ;;                                  ))
       ;; (new-canonicalp (or (eq :elf-64 executable-type)
       ;;                     (eq :mach-o-64 executable-type)
       ;;                     (eq :pe-64 executable-type) ; todo, also need to change the assumptions
       ;;                     ))


       ;; todo: update this for risc-v:
       (existing-stack-slots (if (eq :auto existing-stack-slots)
                                 0
                               ;; (if (eq :pe-64 executable-type)
                               ;;       5 ; 1 for the saved return address, and 4 for registers on the stack (todo: think more about this)
                               ;;     1 ; todo: think about the 32-bit cases
                               ;;     )
                               existing-stack-slots))
       ;; Generate assumptions:
       ((mv erp assumptions
            ;untranslated-assumptions
            ;assumption-rules ; drop? todo: includes rules that were not used, but we return these as an RV named assumption-rules-used
            ;input-assumption-vars
            ;state
            )
        (assumptions-elf32 parsed-executable stack-slots existing-stack-slots position-independent)
        ;; todo: do we need to simplify the assumptions (maybe to get disjointness claims into reduced form by cancelling constants, since that will happen during rewriting)
        ;; (assumptions-new target
        ;;                  parsed-executable
        ;;                  extra-assumptions
        ;;                  suppress-assumptions
        ;;                  inputs-disjoint-from
        ;;                  stack-slots
        ;;                  existing-stack-slots
        ;;                  inputs
        ;;                  type-assumptions-for-array-varsp
        ;;                  extra-assumption-rules
        ;;                  remove-assumption-rules
        ;;                  count-hits
        ;;                  print
        ;;                  executable-type
        ;;                  position-independentp
        ;;                  state)
        )
       ((when erp)
        (er hard? 'unroll-risc-v-code-core "Error generating assumptions: ~x0." erp)
        (mv erp nil ; nil nil nil nil nil
            state))
       ;; Decide where to start lifting:
       (target-offset (if (eq :entry-point target)
                          (acl2::parsed-elf-entry-point parsed-executable)
                        (if (natp target)
                            target ; explicit address given (relative iff position-independentp)
                          ;; target is the name of a function:
                          (prog2$ ;; Throws an error if the target doesn't exist:
                            (acl2::ensure-target-exists-in-executable target parsed-executable)
                            (acl2::subroutine-address-elf target parsed-executable)))))
       (target-address-term (if position-independentp
                                ;; Position-independent, so the target is the base-address-var plus the target-offset:
                                ;; We posulate that there exists some base var wrt which the executable is loaded.
                                (let ((base-address-var 'base-address))
                                  ;; When making assumptions for the regions, we will check that it is possible for them all to be canonical
                                  (if (= 0 target-offset)
                                      base-address-var ; avoids adding 0
                                    `(bvplus 32 ',target-offset ,base-address-var)))
                              ;; Not position-independent, so the target is a concrete address:
                              (acl2::enquote target-offset)))
       (assumptions (append  `((equal (pc stat) ,target-address-term)
                               (stat32ip stat)
                               )
                          assumptions))
       (assumptions (union-equal extra-assumptions assumptions))
       ;; (assumptions (set-difference-equal assumptions remove-assumptions))

       (- (and print (progn$ (cw "(Assumptions for lifting (~x0):~%" (len assumptions)) ; should we untranslate these?
                             (if (print-level-at-least-tp print)
                                 (acl2::print-list assumptions)
                               (acl2::print-terms-elided assumptions '(;(program-at t nil t) ; the program can be huge
                                                                 (equal t nil))))
                             (cw ")~%"))))
       ;; Prepare for symbolic execution:
       ;; (- (and stop-pcs (cw "Will stop execution when any of these PCs are reached: ~x0.~%" stop-pcs))) ; todo: print in hex?
       ;; (- (and stop-pcs
       ;;         position-independentp ; todo: make this work!
       ;;         (er hard? 'unroll-risc-v-code-core ":stop-pcs are not supported with position-independentp.")))
       (term-to-simulate '(run-subroutine stat))
       ;; (term-to-simulate (if stop-pcs
       ;;                       (if 64-bitp
       ;;                           `(run-until-return-or-reach-pc3 ',stop-pcs x86)
       ;;                         `(run-until-return-or-reach-pc4 ',stop-pcs x86))
       ;;                     (if 64-bitp
       ;;                         '(run-until-return3 x86)
       ;;                       '(run-until-return4 x86))))
       (term-to-simulate (wrap-in-output-extractor output-indicator term-to-simulate (w state))) ;TODO: delay this if lifting a loop?
       (- (cw "(Limiting the total steps to ~x0.)~%" step-limit))
       ;; Convert the term into a dag for passing to repeatedly-run:
       ((mv erp dag-to-simulate) (acl2::make-term-into-dag-basic term-to-simulate nil))
       ((when erp) (mv erp nil; nil nil nil nil nil
                       state))
       ((when (quotep dag-to-simulate))
        (er hard? 'unroll-risc-v-code-core "Unexpected quotep: ~x0." dag-to-simulate)
        (mv :unexpected-quotep nil ; nil nil nil nil nil
            state))
       ;; Choose the lifter rules to use:
       (lifter-rules (lifter-rules) ;(if 64-bitp (unroller-rules64) (unroller-rules32))
                     )
       (symbolic-execution-rules (symbolic-execution-rules))
       ;; (symbolic-execution-rules (if stop-pcs
       ;;                               (if 64-bitp
       ;;                                   (symbolic-execution-rules-with-stop-pcs64)
       ;;                                 (symbolic-execution-rules-with-stop-pcs32))
       ;;                             (if 64-bitp
       ;;                                 (symbolic-execution-rules64)
       ;;                               (symbolic-execution-rules32))))
       (lifter-rules (append symbolic-execution-rules lifter-rules))
       ;; Add any extra-rules:
       (- (let ((intersection (intersection-eq extra-rules lifter-rules))) ; todo: optimize (sort and then compare, and also use sorted lists below...)
            (and intersection
                 (cw "Warning: The extra-rules include these rules that are already present: ~X01.~%" intersection nil))))
       (lifter-rules (append extra-rules lifter-rules)) ; todo: use union?  sort by symbol first and merge (may break things)?
       ;; Remove any remove-rules:
       (- (let ((non-existent-remove-rules (set-difference-eq remove-rules lifter-rules)))
            (and non-existent-remove-rules
                 (cw "WARNING: The following rules in :remove-rules were not present: ~X01.~%" non-existent-remove-rules nil))))
       (lifter-rules (set-difference-eq lifter-rules remove-rules))
       ;; Make the rule-alist for lifting:
       ((mv erp lifter-rule-alist)
        (make-rule-alist lifter-rules (w state))) ; todo: allow passing in the rule-alist (and don't recompute for each lifted function)
       ((when erp) (mv erp nil ; nil nil nil nil nil
                       state))
       ;; Make the rule-alist for pruning (must exclude rules that require the x86 rewriter):
       (pruning-rules lifter-rules
                      ;(set-difference-eq lifter-rules (x86-rewriter-rules))
                      ) ; optimize?  should we pre-sort rule-lists?
       ((mv erp pruning-rule-alist)
        (make-rule-alist pruning-rules (w state)))
       ((when erp) (mv erp nil ; nil nil nil nil nil
                       state))
       ;; Decide which rules to monitor:
       (debug-rules (debug-rules) ; todo (if 64-bitp (debug-rules64) (debug-rules32))
                    )
       (rules-to-monitor (acl2::maybe-add-debug-rules debug-rules monitor))
       ;; Do the symbolic execution:
       ((mv erp result-dag-or-quotep state)
        (repeatedly-run 0 step-limit step-increment dag-to-simulate lifter-rule-alist pruning-rule-alist assumptions
                        'step32-opener
                        ;; (if 64-bitp
                        ;;     (first (step-opener-rules64))
                        ;;   (first (step-opener-rules32)))
                        rules-to-monitor prune-precise prune-approx normalize-xors count-hits print print-base untranslatep memoizep state))
       ((when erp) (mv erp nil ;nil nil nil nil nil
                       state))
       (state (acl2::unwiden-margins state))
       ((mv elapsed state) (real-time-since start-real-time state))
       (- (cw " (Lifting took ")
          (print-to-hundredths elapsed) ; todo: could have real-time-since detect negative time
          (cw "s.)~%"))
       ;; Print the result (todo: allow suppressing this):
       (- (if (quotep result-dag-or-quotep)
              (cw " Lifting produced the constant ~x0.)~%" result-dag-or-quotep) ; matches (Lifting...
            (progn$ (cw " Lifting produced a dag:~%")
                    (acl2::print-dag-info result-dag-or-quotep 'result t)
                    (cw ")~%") ; matches (Lifting...
                    ))))
    (mv (erp-nil) result-dag-or-quotep ; untranslated-assumptions input-assumption-vars lifter-rules assumption-rules term-to-simulate
        state)))

;; Returns (mv erp event state)
;; TODO: Consider using the current print-base (:auto value) by default.
(defun def-unrolled-fn (lifted-name
                        target
                        executable
                        ;;inputs
                        output-indicator
                        extra-assumptions
                        ;;suppress-assumptions
                        ;;inputs-disjoint-from
                        stack-slots
                        existing-stack-slots
                        position-independent
                        ;;type-assumptions-for-array-varsp
                        prune-precise
                        prune-approx
                        extra-rules
                        remove-rules
                        ;; extra-assumption-rules
                        ;; remove-assumption-rules
                        step-limit
                        step-increment
                        ;;stop-pcs
                        memoizep
                        monitor
                        normalize-xors
                        count-hits
                        print
                        print-base
                        untranslatep
                        ;;produce-function
                        ;;non-executable
                        ;;produce-theorem
                        ;;prove-theorem ;whether to try to prove the theorem with ACL2 (rarely works)
                        ;; restrict-theory
                        whole-form
                        state)
  (declare (xargs :guard (and (symbolp lifted-name)
                              (acl2::lifter-targetp target)
                              ;; executable
                              ;; (or (eq :skip inputs) (names-and-typesp inputs))
                              ;; (output-indicatorp output-indicator) ; no recognizer for this, we just call wrap-in-output-extractor and see if it returns an error
                              ;; extra-assumptions ; untranslated-terms
;;                              (booleanp suppress-assumptions)
                              ;; (member-eq inputs-disjoint-from '(nil :code :all))
                              (natp stack-slots)
                              (or (natp existing-stack-slots)
                                  (eq :auto existing-stack-slots))
                              (member-eq position-independent '(t nil :auto))
                              ;; (booleanp type-assumptions-for-array-varsp)
                              (or (eq nil prune-precise)
                                  (eq t prune-precise)
                                  (natp prune-precise))
                              (or (eq nil prune-approx)
                                  (eq t prune-approx)
                                  (natp prune-approx))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              ;; (symbol-listp extra-assumption-rules)
                              ;; (symbol-listp remove-assumption-rules)
                              (natp step-limit)
                              (acl2::step-incrementp step-increment)
                              ;; (nat-listp stop-pcs)
                              (booleanp memoizep)
                              (or (symbol-listp monitor)
                                  (eq :debug monitor))
                              (acl2::normalize-xors-optionp normalize-xors)
                              (acl2::count-hits-argp count-hits)
                              (acl2::print-levelp print)
                              (member print-base '(10 16))
                              (booleanp untranslatep)
                              ;; (booleanp produce-function)
                              ;; (member-eq non-executable '(t nil :auto))
                              ;; (booleanp produce-theorem)
                              ;; (booleanp prove-theorem)
                              ;; (booleanp restrict-theory)
                              )
                  :stobjs state
                  :mode :program ; todo
                  ))
  (b* (;; Check whether this call to the lifter is redundant:
       (previous-result (previous-lifter-result whole-form state))
       ((when previous-result)
        (mv nil '(value-triple :redundant) state))
       ;; Start timing:
       ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       ;; Check inputs:
       ((when (eq :none executable))
        (er hard? 'def-unrolled-fn "No :executable supplied (should usually be a string (file name or path).") ; todo: mention the parsed-executable option (need a predicate for that)
        (mv (erp-t) nil state))
       ;; Handle filename vs parsed-structure
       ((mv erp parsed-executable state)
        (if (stringp executable)
            ;; it's a filename, so parse the file:
            (acl2::parse-executable executable state)
          ;; it's already a parsed-executable: ; todo: can we deprecate this case?  could be de-obfuscated
          (mv nil executable state)))
       ((when erp)
        (er hard? 'def-unrolled-fn "Error (~x0) parsing executable: ~s1." erp executable)
        (mv t nil state))
       ;; Translate assumptions:
       (extra-assumptions (acl2::translate-terms extra-assumptions 'def-unrolled-fn (w state)))

       ;; Lift the function to obtain the DAG:
       ((mv erp result-dag ;assumptions assumption-vars lifter-rules-used assumption-rules-used term-to-simulate
            state)
        (unroll-risc-v-code-core target parsed-executable
                                 extra-assumptions ;;suppress-assumptions
                                 ;;inputs-disjoint-from
                                 stack-slots existing-stack-slots position-independent
                                 ;inputs type-assumptions-for-array-varsp
                                 output-indicator
                                 prune-precise prune-approx extra-rules remove-rules
                                 ;; extra-assumption-rules remove-assumption-rules
                                 step-limit step-increment
                                 ;;stop-pcs
                                 memoizep monitor normalize-xors count-hits print print-base untranslatep state))
       ((when erp) (mv erp nil state))
       ;; Extract info from the result-dag:
       (result-dag-size (dag-or-quotep-size result-dag))
       (result-dag-fns (dag-or-quotep-fns result-dag))
       ;; Sometimes the presence of text-offset may indicate that something
       ;; wasn't resolved, but other times it's just needed to express some
       ;; junk left on the stack
;;       (result-dag-vars (dag-or-quotep-vars result-dag))
       ;; Check for incomplete run:
       ;; Do we want a check like this?
       ;; ((when (not (subsetp-eq result-vars '(risc-v text-offset))))
       ;;  (mv t (er hard 'lifter "Unexpected vars, ~x0, in result DAG!" (set-difference-eq result-vars '(risc-v text-offset))) state))
       ;; TODO: Maybe move some of this to the -core function:
       ;; (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
       ;;            (set-print-base-radix print-base state)
       ;;          state)) ; todo: do this better
       ((when (intersection-eq result-dag-fns *incomplete-run-fns*))
        (if (< result-dag-size 100000) ; todo: make customizable
            (progn$ (cw "(Term:~%")
                    (cw "~X01" (let ((term (acl2::dag-or-quotep-to-term result-dag)))
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

       ;; Build the defconst that will contain the result DAG:
       (defconst-form `(defconst ,(acl2::pack-in-package-of-symbol lifted-name '* lifted-name '*) ',result-dag))

       ;; ;; Possibly produce a defun:

       ;; ;; (fn-formals result-dag-vars) ; we could include stat here, even if the dag is a constant
       ;; (executable-type (acl2::parsed-executable-type parsed-executable))
       ;; (64-bitp (member-equal executable-type '(:mach-o-64 :pe-64 :elf-64)))
       ;; ;; Build the defun that will contain the result of lifting:
       ;; ;; Create the list of formals for the function:
       ;; ;; todo: move some of this to after we check produce-function below
       ;; (param-names (if (and 64-bitp
       ;;                       (not (equal :skip inputs)))
       ;;                  ;; The user gave names to the params (and/or their components, etc), and those vars will be put in:
       ;;                  assumption-vars ; (strip-cars inputs) ; fixme: handle array and pointer values (just look at the dag vars?) -- done?
       ;;                ;; The register names may be being introduced (todo: deprecate this?):
       ;;                '(rdi rsi rdx rcx r8 r9))) ; todo: handle 32-bit calling convention
       ;; (common-formals (append param-names '(stat))) ; todo: handle 32-bit calling convention
       ;; ;; these will be ordered like common-formals:
       ;; (expected-formals (intersection-eq common-formals result-dag-vars))
       ;; (unexpected-formals (set-difference-eq result-dag-vars common-formals)) ; todo: warn if inputs given?  maybe stat will sometimes be needed?
       ;; (fn-formals (append expected-formals unexpected-formals))
       ;; ((mv erp defuns) ; defuns is nil or a singleton list
       ;;  (if (not produce-function)
       ;;      (mv (erp-nil) nil)
       ;;    (b* (;;TODO: consider untranslating this, or otherwise cleaning it up:
       ;;         (function-body (if (< result-dag-size 1000)
       ;;                            maybe-result-term
       ;;                          `(acl2::dag-val-with-axe-evaluator ',result-dag ; can't be a constant (the size would be < 1000)
       ;;                                                             ,(acl2::make-acons-nest result-dag-vars)
       ;;                                                             ',(acl2::make-interpreted-function-alist (acl2::get-non-built-in-supporting-fns-list result-dag-fns acl2::*axe-evaluator-functions* (w state)) (w state))
       ;;                                                             '0 ;array depth (not very important)
       ;;                                                             )))
       ;;         (function-body-untranslated (if untranslatep (untranslate function-body nil (w state)) function-body)) ;todo: is this unsound (e.g., because of user changes in how untranslate works)?
       ;;         (function-body-retranslated (acl2::translate-term function-body-untranslated 'def-unrolled-fn (w state)))
       ;;         ;; TODO: I've seen this check fail when (if x y t) got turned into (if (not x) (not x) y):
       ;;         ((when (not (equal function-body function-body-retranslated))) ;todo: make a safe-untranslate that does this check?
       ;;          (er hard? 'lifter "Problem with function body.  Untranslating and then re-translating did not give original body.  Body was ~X01.  Re-translated body was ~X23" function-body nil function-body-retranslated nil)
       ;;          (mv :problem-with-function-body nil))
       ;;         ;;(- (cw "Runes used: ~x0" runes)) ;TODO: Have Axe return these?
       ;;         ;;use defun-nx by default because stobj updates are not all let-bound to x86
       ;;         (non-executable (if (eq :auto non-executable)
       ;;                             (if (member-eq 'x86 fn-formals) ; there may be writes to the stobj (perhaps with unresolved reads around them), so we use defun-nx (todo: do a more precise check)
       ;;                                 ;; (eq :all output-indicator) ; we use defun-nx since there is almost certainly a stobj update (and updates are not properly let-bound)
       ;;                                 t
       ;;                               nil)
       ;;                           non-executable))
       ;;         (defun-variant (if non-executable 'defun-nx 'defun))
       ;;         (defun `(,defun-variant ,lifted-name (,@fn-formals)
       ;;                   (declare (xargs ,@(if (member-eq 'x86 fn-formals)
       ;;                                         `(:stobjs x86)
       ;;                                       nil)
       ;;                                   :verify-guards nil ;TODO
       ;;                                   )
       ;;                            ,@(let ((ignored-vars (set-difference-eq fn-formals result-dag-vars)))
       ;;                                (and ignored-vars
       ;;                                     `((ignore ,@ignored-vars)))))
       ;;                   ,function-body-untranslated)))
       ;;      (mv (erp-nil) (list defun)))))
       ;; ((when erp) (mv erp nil state))
       ;; (produce-theorem (and produce-theorem
       ;;                       (if (not produce-function)
       ;;                           ;; todo: do something better in this case?
       ;;                           (prog2$ (cw "NOTE: Suppressing theorem because :produce-function is nil.~%")
       ;;                                   nil)
       ;;                         t)))
       ;; (defthms ; either nil or a singleton list
       ;;   (and produce-theorem ; todo: what if we are not producing the function?
       ;;        (if stop-pcs
       ;;            (prog2$ (cw "Suppressing theorem because :stop-pcs were given.~%")
       ;;                    nil)
       ;;          t)
       ;;        (let* ((defthm `(defthm ,(acl2::pack$ lifted-name '-correct)
       ;;                          (implies (and ,@assumptions)
       ;;                                   (equal ,term-to-simulate
       ;;                                          (,lifted-name ,@fn-formals)))
       ;;                          :hints ,(if restrict-theory
       ;;                                      `(("Goal" :in-theory '(,lifted-name ;,@runes ;without the runes here, this won't work
       ;;                                                             )))
       ;;                                    `(("Goal" :in-theory (enable ,@lifter-rules-used
       ;;                                                                 ,@assumption-rules-used))))))
       ;;               (defthm (if prove-theorem
       ;;                           defthm
       ;;                         `(skip-proofs ,defthm))))
       ;;          (list defthm))))
       (events (cons defconst-form
                     nil ; (append defuns defthms)
                     ))
       (event-names (acl2::strip-cadrs events))
       (event `(progn ,@events))
       (event (acl2::extend-progn event `(table risc-v-lifter-table ',whole-form ',event)))
       (event (acl2::extend-progn event `(value-triple '(,@event-names))))
       ((mv elapsed state) (acl2::real-time-since start-real-time state))
       (- (cw " (Unrolling ~x0 took " lifted-name)
          (acl2::print-to-hundredths elapsed)
          (cw "s, not including event submission.)~%")))
    (mv nil event state)))

;TODO: Add show- variant?
;; TODO: :print nil is not fully respected
;; Creates some events to represent the unrolled computation, including a defconst for the DAG.  no:  and perhaps a defun and a theorem.
(defmacrodoc def-unrolled (&whole whole-form
                                  lifted-name
                                  &key
                                  (target ':entry-point)
                                  (executable ':none)
                                  ;;(inputs ':skip)
                                  (output ':all)
                                  (extra-assumptions 'nil)
;;                                  (suppress-assumptions 'nil)
                                  ;;(inputs-disjoint-from ':code)
                                  (stack-slots '100)
                                  (existing-stack-slots ':auto)
                                  (position-independent 'nil ;':auto
                                                        )
                                  ;;(type-assumptions-for-array-vars 't)
                                  (prune-precise '1000)
                                  (prune-approx 't)
                                  (extra-rules 'nil)
                                  (remove-rules 'nil)
;;                                  (extra-assumption-rules 'nil)
;;                                  (remove-assumption-rules 'nil)
                                  (step-limit '1000000)
                                  (step-increment '100)
                                  ;;(stop-pcs 'nil)
                                  (memoizep 't)
                                  (monitor 'nil)
                                  (normalize-xors 'nil)
                                  (count-hits 'nil)
                                  (print ':brief)             ;how much to print
                                  (print-base '10)
                                  (untranslatep 't)
                                  ;;(produce-function 't)
                                  ;;(non-executable ':auto)
                                  ;;(produce-theorem 'nil)
                                  ;;(prove-theorem 'nil)
                                  ;;(restrict-theory 't)       ;todo: deprecate
                                  )
  `(,(if (acl2::print-level-at-least-tp print) 'make-event 'acl2::make-event-quiet)
    (def-unrolled-fn
      ',lifted-name
      ,target
      ,executable ; gets evaluated
;;      ',inputs
      ',output
      ,extra-assumptions
;;      ',suppress-assumptions
;;      ',inputs-disjoint-from
      ',stack-slots
      ',existing-stack-slots
      ',position-independent
;;      ',type-assumptions-for-array-vars
      ',prune-precise
      ',prune-approx
      ,extra-rules ; gets evaluated since not quoted
      ,remove-rules ; gets evaluated since not quoted
;;      ,extra-assumption-rules ; gets evaluated since not quoted
;;      ,remove-assumption-rules ; gets evaluated since not quoted
      ',step-limit
      ',step-increment
;;      ,stop-pcs
      ',memoizep
      ,monitor ; gets evaluated since not quoted
      ',normalize-xors
      ',count-hits
      ',print
      ',print-base
      ',untranslatep
      ;; ',produce-function
      ;; ',non-executable
      ;; ',produce-theorem
      ;; ',prove-theorem
      ;; ',restrict-theory
      ',whole-form
      state))
  :parents (acl2::axe-risc-v acl2::axe-lifters)
  :short "A tool to lift RISC-V binary code into logic, unrolling loops as needed."
  :args ((lifted-name "A symbol, the name to use for the generated function.  The name of the generated constant is created by adding stars to the front and back of this symbol.")
         (executable "The risc-v binary executable that contains the target function.  Usually a string (a filename), or this can be a parsed executable of the form created by defconst-x86.") ; todo: defconst-risc-v?
         (target "Where to start lifting (a numeric offset, the name of a subroutine (a string), or the symbol :entry-point)")
         (extra-assumptions "Extra assumptions for lifting, in addition to the standard-assumptions")
;;         (suppress-assumptions "Whether to suppress the standard assumptions.  This does not suppress any assumptions generated about the :inputs.")
;;         (inputs-disjoint-from "What to assume about the inputs (specified using the :inputs option) being disjoint from the sections/segments in the executable.  The value :all means assume the inputs are disjoint from all sections/segments.  The value :code means assume the inputs are disjoint from the code/text section.  The value nil means do not include any assumptions of this kind.")
         (stack-slots "How much unused stack space to assume is available, in terms of the number of stack slots, which are 4 bytes for 32-bit executables and 8 bytes for 64-bit executables.  The stack will expand into this space during (symbolic) execution.")
         (existing-stack-slots "How much available stack space to assume exists.  Usually at least 1, for the saved return address.") ; 4 or 8 bytes each?
         (position-independent "Whether to attempt the lifting without assuming that the binary is loaded at a particular position.")
;;         (inputs "Either the special value :skip (meaning generate no additional assumptions on the input) or a doublet list pairing input names with types.  Types include things like u32, u32*, and u32[2].")
;;         (type-assumptions-for-array-vars "Whether to put in type assumptions for the variables that represent elements of input arrays.")
         (output "An indication of which state component(s) will hold the result of the computation being lifted.  After lifting, the indicated result is projected out so that the result of lifting only represented the indicated state component.  The value supplied for this option can be :all (meaning return the whole state) or one of the values allowed by wrap-in-normal-output-extractor.")
;;         (use-internal-contextsp "Whether to use contextual information from ovararching conditionals when simplifying DAG nodes.")
         ;; todo: better name?  only for precise pruning:
         (prune-precise "Whether to prune DAGs using precise contexts.  Either t or nil or a natural number representing the smallest dag size that we deem too large for pruning (where here the size is the number of nodes in the corresponding term).  This kind of pruning can blow up if attempted for DAGs that represent huge terms.")
         (prune-approx "Whether to prune DAGs using approximate contexts.  Either t or nil or a natural number representing the smallest dag size that we deem too large for pruning (where here the size is the number of nodes in the corresponding term).  This kind of pruning should not blow up but doesn't use fully precise contextual information.")
         ;; todo: how do these affect assumption simp:
         (extra-rules "Rules to use in addition to (unroller-rules32) or (unroller-rules64) plus a few others.")
         (remove-rules "Rules to turn off.")
         ;; (extra-assumption-rules "Extra rules to be used when simplifying assumptions.")
         ;; (remove-assumption-rules "Rules to be removed when simplifying assumptions.")
         (step-limit "Limit on the total number of symbolic executions steps to allow (total number of steps over all branches, if the simulation splits).")
         (step-increment "Number of model steps to allow before pausing to simplify the DAG and remove unused nodes.")
;;         (stop-pcs "A list of program counters (natural numbers) at which to stop the execution, for debugging.")
         (memoizep "Whether to memoize during rewriting (when not using contextual information -- as doing both would be unsound).")
         (monitor "Rule names (symbols) to be monitored when rewriting.") ; during assumptions too?
         (normalize-xors "Whether to normalize BITXOR and BVXOR nodes when rewriting (t, nil, or :compact).")
         (count-hits "Whether to count rule hits during rewriting (t means count hits for every rule, :total means just count the total number of hits, nil means don't count hits)")
         (print "Verbosity level.") ; todo: values
         (print-base "Base to use when printing during lifting.  Must be either 10 or 16.")
         (untranslatep "Whether to untranslate terms when printing.")
;;         (produce-function "Whether to produce a function, not just a constant DAG, representing the result of the lifting.")
;;         (non-executable "Whether to make the generated function non-executable, e.g., because stobj updates are not properly let-bound.  Either t or nil or :auto.")
;;         (produce-theorem "Whether to try to produce a theorem (possibly skip-proofed) about the result of the lifting.")
;;         (prove-theorem "Whether to try to prove the theorem with ACL2 (rarely works, since Axe's Rewriter is different and more scalable than ACL2's rewriter).")
         ;;         (restrict-theory "To be deprecated...")
         )
  :description ("Lift some risc-v binary code into an ACL2 representation, by symbolic execution including inlining all functions and unrolling all loops."
                "Usually, @('def-unrolled') creates both a function representing the lifted code (in term or DAG form, depending on the size) and a @(tsee defconst) whose value is the corresponding DAG (or, rarely, a quoted constant).  The function's name is @('lifted-name') and the @('defconst')'s name is created by adding stars around  @('lifted-name')."
                "To inspect the resulting DAG, you can simply enter its name at the prompt to print it."))
