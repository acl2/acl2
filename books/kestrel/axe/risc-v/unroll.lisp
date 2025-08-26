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
(include-book "kestrel/x86/parsers/parsed-executable-tools" :dir :system)
(include-book "../step-increments")
(include-book "../rule-limits")
(include-book "../rewriter-basic")
(include-book "../prune-dag-precisely")
(include-book "../prune-dag-approximately")
(include-book "../lifter-common")
(include-book "../equivalent-dags")
(include-book "assumptions")
(local (include-book "kestrel/utilities/get-real-time" :dir :system))
(local (include-book "kestrel/utilities/w" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

(defconst *incomplete-run-fns* '(run-until-sp-is-above))
(defconst *error-fns* '(error32))

(local (in-theory (disable myquotep ; todo: loop involving acl2::simplify-dag-basic-return-type-corollary-2
                           intersection-equal
                           acl2::myquotep-when-axe-treep
                           state-p
                           mv-nth
                           natp
                           string-append
                           string-append-lst)))

(local (in-theory (enable acl2::weak-dagp-when-pseudo-dagp
                          acl2::true-listp-when-symbol-listp-rewrite-unlimited
                          )))

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
              ;;state
              )
          (simplify-dag-basic ; acl2::simplify-dag-risc-v
                                  dag
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
                                  ;; state
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
                (mv-let (erp result limits ;state
                             )
                  (simplify-dag-basic ; simplify-dag-risc-v
                    dag
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
                                          ;; state
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun symbolic-execution-rules ()
  (declare (xargs :guard t))
  '(run-until-return
    run-subroutine
    sp-is-abovep
    run-until-sp-is-above-opener
    run-until-sp-is-above-base
    run-until-sp-is-above-of-if-arg2))

(defun lifter-rules ()
  (declare (xargs :guard t))
  '())

;; Returns (mv erp result-dag-or-quotep
;;                 ; assumptions input-assumption-vars lifter-rules-used assumption-rules-used term-to-simulate
;;                state).
;; This is also called by the formal unit tester.
;; (defun unroll-risc-v-code-core (target
;;                                 parsed-executable
;;                                 extra-assumptions ; todo: can these introduce vars for state components?  now we have :inputs for that.  could also replace register expressions with register names (vars) -- see what do do for the Tester.
;;                                 suppress-assumptions
;;                                 ;;inputs-disjoint-from
;;                                 stack-slots
;;                                 existing-stack-slots
;;                                 position-independent
;;                                 ;;inputs
;;                                 ;;type-assumptions-for-array-varsp
;;                                 ;;output-indicator ; todo
;;                                 prune-precise
;;                                 prune-approx
;;                                 extra-rules
;;                                 remove-rules
;;                                 extra-assumption-rules ; todo: why "extra"?
;;                                 remove-assumption-rules
;;                                 step-limit
;;                                 step-increment
;;                                 ;; stop-pcs
;;                                 memoizep
;;                                 monitor
;;                                 normalize-xors
;;                                 count-hits
;;                                 print
;;                                 print-base
;;                                 untranslatep
;;                                 state)
;;   (declare (xargs :guard (and (acl2::lifter-targetp target)
;;                               ;; parsed-executable ; todo: add a guard (even if it's weak for now)
;;                               (true-listp extra-assumptions) ; untranslated terms
;;                               (booleanp suppress-assumptions)
;;                               ;; (member-eq inputs-disjoint-from '(nil :code :all))
;;                               (natp stack-slots)
;;                               (or (natp existing-stack-slots)
;;                                   (eq :auto existing-stack-slots))
;;                               (member-eq position-independent '(t nil ; :auto
;;                                                                 ))
;;                               ;; (or (eq :skip inputs) (names-and-typesp inputs))
;;                               ;; (booleanp type-assumptions-for-array-varsp)
;;                               ;; no recognizer for output-indicator, we just call wrap-in-output-extractor and see if it returns an error
;;                               (or (eq nil prune-precise)
;;                                   (eq t prune-precise)
;;                                   (natp prune-precise))
;;                               (or (eq nil prune-approx)
;;                                   (eq t prune-approx)
;;                                   (natp prune-approx))
;;                               (symbol-listp extra-rules)
;;                               (symbol-listp remove-rules)
;;                               (symbol-listp extra-assumption-rules)
;;                               (symbol-listp remove-assumption-rules)
;;                               (natp step-limit)
;;                               (step-incrementp step-increment)
;;                               ;; (nat-listp stop-pcs)
;;                               (booleanp memoizep)
;;                               (or (symbol-listp monitor)
;;                                   (eq :debug monitor))
;;                               (normalize-xors-optionp normalize-xors)
;;                               (count-hits-argp count-hits)
;;                               (print-levelp print)
;;                               (member print-base '(10 16))
;;                               (booleanp untranslatep))
;;                   :stobjs state
;;                   :mode :program ; todo: need a magic wrapper for translate-terms (must translate at least the user-supplied assumptions)
;;                   ))
;;   (b* ((- (cw "(Lifting ~s0.~%" target)) ;todo: print the executable name, also handle non-string targets better
;;        ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
;;        (state (acl2::widen-margins state))
;;        ;; Get and check the executable-type:
;;        (executable-type (acl2::parsed-executable-type parsed-executable))
;;        ;; (64-bitp (member-equal executable-type *executable-types64*))
;;        (- (and (acl2::print-level-at-least-briefp print) (cw "(Executable type: ~x0.)~%" executable-type)))
;;        ;; Make sure it's a RISC-V executable:
;;        (- (acl2::ensure-risc-v parsed-executable))
;;        ;; Handle a :position-independent of :auto:

;;        (position-independentp position-independent)
;;        ;; (position-independentp (if (eq :auto position-independent)
;;        ;;                            (if (eq executable-type :mach-o-64)
;;        ;;                                t ; since clang seems to produce position-independent code by default ; todo: look at the PIE bit in the header.
;;        ;;                              (if (eq executable-type :elf-64)
;;        ;;                                  (let ((elf-type (parsed-elf-type parsed-executable)))
;;        ;;                                    (prog2$ (cw "ELF type: ~x0.~%" elf-type)
;;        ;;                                            (if (parsed-elf-program-header-table parsed-executable)
;;        ;;                                                ;; For ELF64, we treat :dyn and :rel as position-independent (addresses relative to the var base-address) and :exec as absolute:
;;        ;;                                                (if (member-eq elf-type '(:rel :dyn)) t nil)
;;        ;;                                              ;; TODO: Get this to work:
;;        ;;                                              nil)))
;;        ;;                                ;; TODO: Think about the other cases:
;;        ;;                                t))
;;        ;;                          ;; the user supplied a value for position-independent, so use it:
;;        ;;                          position-independent))

;;        (- (if position-independentp (cw " Using position-independent lifting.~%") (cw " Using non-position-independent lifting.~%")))
;;        ;; (new-style-elf-assumptionsp (and (eq :elf-64 executable-type)
;;        ;;                                  ;; todo: remove this, but we have some unlinked ELFs without sections.  we also have some unlinked ELFs that put both the text and data segments at address 0 !
;;        ;;                                  ;(parsed-elf-program-header-table parsed-executable) ; there are segments present (todo: improve the "new" behavior to use sections when there are no segments)
;;        ;;                                  ))
;;        ;; (new-canonicalp (or (eq :elf-64 executable-type)
;;        ;;                     (eq :mach-o-64 executable-type)
;;        ;;                     (eq :pe-64 executable-type) ; todo, also need to change the assumptions
;;        ;;                     ))
;;        (- (and (stringp target)
;;                ;; Throws an error if the target doesn't exist:
;;                (acl2::ensure-target-exists-in-executable target parsed-executable)))

;;        ;; todo: update this for risc-v:
;;        (existing-stack-slots (if (eq :auto existing-stack-slots)
;;                                  (if (eq :pe-64 executable-type)
;;                                      5 ; 1 for the saved return address, and 4 for registers on the stack (todo: think more about this)
;;                                    1 ; todo: think about the 32-bit cases
;;                                    )
;;                                existing-stack-slots))
;;        ;; Generate assumptions:
;;        ((mv erp assumptions
;;             ;untranslated-assumptions
;;             ;assumption-rules ; drop? todo: includes rules that were not used, but we return these as an RV named assumption-rules-used
;;             ;input-assumption-vars
;;             ;state
;;             )
;;         (assumptions-elf32 parsed-executable)
;;         ;; todo: do we need to simplify yhe assumptions
;;         ;; (assumptions-new target
;;         ;;                  parsed-executable
;;         ;;                  extra-assumptions
;;         ;;                  suppress-assumptions
;;         ;;                  inputs-disjoint-from
;;         ;;                  stack-slots
;;         ;;                  existing-stack-slots
;;         ;;                  inputs
;;         ;;                  type-assumptions-for-array-varsp
;;         ;;                  extra-assumption-rules
;;         ;;                  remove-assumption-rules
;;         ;;                  count-hits
;;         ;;                  print
;;         ;;                  executable-type
;;         ;;                  position-independentp
;;         ;;                  state)
;;         )
;;        ((when erp)
;;         (er hard? 'unroll-risc-v-code-core "Error generating assumptions: ~x0." erp)
;;         (mv erp nil ; nil nil nil nil nil
;;             state))
;;        (- (and print (progn$ (cw "(Assumptions for lifting (~x0):~%" (len assumptions)) ; should we untranslate these?
;;                              (if (print-level-at-least-tp print)
;;                                  (print-list assumptions)
;;                                (print-terms-elided assumptions '(;(program-at t nil t) ; the program can be huge
;;                                                                  (equal t nil))))
;;                              (cw ")~%"))))
;;        ;; Prepare for symbolic execution:
;;        ;; (- (and stop-pcs (cw "Will stop execution when any of these PCs are reached: ~x0.~%" stop-pcs))) ; todo: print in hex?
;;        ;; (- (and stop-pcs
;;        ;;         position-independentp ; todo: make this work!
;;        ;;         (er hard? 'unroll-risc-v-code-core ":stop-pcs are not supported with position-independentp.")))
;;        (term-to-simulate '(run-subroutine stat))
;;        ;; (term-to-simulate (if stop-pcs
;;        ;;                       (if 64-bitp
;;        ;;                           `(run-until-return-or-reach-pc3 ',stop-pcs x86)
;;        ;;                         `(run-until-return-or-reach-pc4 ',stop-pcs x86))
;;        ;;                     (if 64-bitp
;;        ;;                         '(run-until-return3 x86)
;;        ;;                       '(run-until-return4 x86))))
;; ;       (term-to-simulate (wrap-in-output-extractor output-indicator term-to-simulate 64-bitp (w state))) ;TODO: delay this if lifting a loop?
;;        (- (cw "(Limiting the total steps to ~x0.)~%" step-limit))
;;        ;; Convert the term into a dag for passing to repeatedly-run:
;;        ((mv erp dag-to-simulate) (make-term-into-dag-basic term-to-simulate nil))
;;        ((when erp) (mv erp nil nil nil nil nil nil state))
;;        ((when (quotep dag-to-simulate))
;;         (er hard? 'unroll-risc-v-code-core "Unexpected quotep: ~x0." dag-to-simulate)
;;         (mv :unexpected-quotep nil nil nil nil nil nil state))
;;        ;; Choose the lifter rules to use:
;;        (lifter-rules (lifter-rules) ;(if 64-bitp (unroller-rules64) (unroller-rules32))
;;                      )
;;        (symbolic-execution-rules (symbolic-execution-rules))
;;        ;; (symbolic-execution-rules (if stop-pcs
;;        ;;                               (if 64-bitp
;;        ;;                                   (symbolic-execution-rules-with-stop-pcs64)
;;        ;;                                 (symbolic-execution-rules-with-stop-pcs32))
;;        ;;                             (if 64-bitp
;;        ;;                                 (symbolic-execution-rules64)
;;        ;;                               (symbolic-execution-rules32))))
;;        (lifter-rules (append symbolic-execution-rules lifter-rules))
;;        ;; Add any extra-rules:
;;        (- (let ((intersection (intersection-eq extra-rules lifter-rules))) ; todo: optimize (sort and then compare, and also use sorted lists below...)
;;             (and intersection
;;                  (cw "Warning: The extra-rules include these rules that are already present: ~X01.~%" intersection nil))))
;;        (lifter-rules (append extra-rules lifter-rules)) ; todo: use union?  sort by symbol first and merge (may break things)?
;;        ;; Remove any remove-rules:
;;        (- (let ((non-existent-remove-rules (set-difference-eq remove-rules lifter-rules)))
;;             (and non-existent-remove-rules
;;                  (cw "WARNING: The following rules in :remove-rules were not present: ~X01.~%" non-existent-remove-rules nil))))
;;        (lifter-rules (set-difference-eq lifter-rules remove-rules))
;;        ;; Make the rule-alist for lifting:
;;        ((mv erp lifter-rule-alist)
;;         (make-rule-alist lifter-rules (w state))) ; todo: allow passing in the rule-alist (and don't recompute for each lifted function)
;;        ((when erp) (mv erp nil nil nil nil nil nil state))
;;        ;; Make the rule-alist for pruning (must exclude rules that require the x86 rewriter):
;;        (pruning-rules lifter-rules
;;                       ;(set-difference-eq lifter-rules (x86-rewriter-rules))
;;                       ) ; optimize?  should we pre-sort rule-lists?
;;        ((mv erp pruning-rule-alist)
;;         (make-rule-alist pruning-rules (w state)))
;;        ((when erp) (mv erp nil nil nil nil nil nil state))
;;        ;; Decide which rules to monitor:
;;        (debug-rules nil ; todo (if 64-bitp (debug-rules64) (debug-rules32))
;;                     )
;;        (rules-to-monitor (maybe-add-debug-rules debug-rules monitor))
;;        ;; Do the symbolic execution:
;;        ((mv erp result-dag-or-quotep state)
;;         (repeatedly-run 0 step-limit step-increment dag-to-simulate lifter-rule-alist pruning-rule-alist assumptions
;;                         (if 64-bitp
;;                             (first (step-opener-rules64))
;;                           (first (step-opener-rules32)))
;;                         rules-to-monitor prune-precise prune-approx normalize-xors count-hits print print-base untranslatep memoizep state))
;;        ((when erp) (mv erp nil nil nil nil nil nil state))
;;        (state (unwiden-margins state))
;;        ((mv elapsed state) (real-time-since start-real-time state))
;;        (- (cw " (Lifting took ")
;;           (print-to-hundredths elapsed) ; todo: could have real-time-since detect negative time
;;           (cw "s.)~%"))
;;        ;; Print the result (todo: allow suppressing this):
;;        (- (if (quotep result-dag-or-quotep)
;;               (cw " Lifting produced the constant ~x0.)~%" result-dag-or-quotep) ; matches (Lifting...
;;             (progn$ (cw " Lifting produced a dag:~%")
;;                     (print-dag-info result-dag-or-quotep 'result t)
;;                     (cw ")~%") ; matches (Lifting...
;;                     ))))
;;     (mv (erp-nil) result-dag-or-quotep untranslated-assumptions input-assumption-vars lifter-rules assumption-rules term-to-simulate state)))
