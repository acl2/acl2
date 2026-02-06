; Utilities used by multiple lifters
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-size")
(include-book "dag-to-term")
(include-book "count-branches")
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "std/system/untranslate-dollar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Prints as a term if the term is not too big.
;; todo: respect the print-base?
(defund print-dag-nicely (dag max-term-size)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (natp max-term-size))))
  (if (dag-or-quotep-size-less-than dag max-term-size)
      (cw "~X01" (dag-to-term dag) nil) ; todo: untranslate (see below)
    (cw "~X01" dag nil)))

;; Returns state.
;; restores the print-base to 10 (do better?)
(defund print-dag-nicely-with-base (dag max-term-size descriptor untranslatep print-base state)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (natp max-term-size)
                              (stringp descriptor)
                              (booleanp untranslatep)
                              (member print-base '(10 16)))
                  :stobjs state))
  (if (dag-or-quotep-size-less-than dag max-term-size) ; todo: drop the "-or-quotep"
      (b* ((- (cw "(Term ~x0:~%" descriptor))
           (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
                      (set-print-base-radix print-base state)
                    state))
           (term (dag-to-term dag))
           (term (if untranslatep (untranslate$ term nil state) term))
           (- (cw "~X01" term nil))
           (state (set-print-base-radix 10 state)) ;make-event sets it to 10
           (- (cw ")~%"))) ; matches "(Term after"
        state)
    (b* ((- (cw "(DAG ~x0:~%" descriptor))
         (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
                    (set-print-base-radix print-base state)
                  state))
         (- (cw "~X01" dag nil))
         (state (set-print-base-radix 10 state))
         (- (cw "(DAG has ~x0 IF-branches.)~%" (count-top-level-if-branches-in-dag dag))) ; todo: if 1, say "no ifs"
         (- (cw ")~%"))) ; matches "(DAG after"
      state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: move this util

;; Recognizes an alist from functions to boolean-lists representing which arguments to print.
;; TODO: Generalize this to terms, like (equal (read n ad x86) :elide).
;; Note that all of this machinery is less important now that verbose-monitorp is nil (but we can :redef verbose-monitorp).
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

;; Replace with :elided any large constant list arg that corresponds with nil in the bools.
;; todo: clarify the sense of t and nil (nil means maybe don't print)
(defund apply-elision-spec (args bools)
  (declare (xargs :guard (and (true-listp args)
                              (boolean-listp bools))))
  (if (endp args)
      nil
    (cons (if (and (not (first bools))
                   (let ((arg (first args)))
                     (and (myquotep arg)
                          (consp (unquote arg)) ; checks for a fairly long list
                          (<= 100 (len (unquote arg))))))
              :elided
            (first args))
          (apply-elision-spec (rest args) (rest bools)))))

(defund print-term-elided (term firstp elision-specs)
  (declare (xargs :guard (elision-spec-alistp elision-specs)))
  (let ((elision-spec (and (consp term)
                           (lookup-eq (car term) elision-specs))))
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

;; Removes all of the TERMS that are calls of one of the FNS-TO-REMOVE, or
;; negations of such calls.
(defund remove-assumptions-about (fns-to-remove terms)
  (declare (xargs :guard (and (symbol-listp fns-to-remove)
                              (pseudo-term-listp terms))))
  (if (endp terms)
      nil
    (let* ((term (first terms))
           ;; strip a NOT if present:
           (core-term (if (and (consp term)
                               (eq 'not (ffn-symb term))
                               (= 1 (len (fargs term))))
                          (farg1 term)
                        term)))
      (if (and (consp core-term)
               (member-eq (ffn-symb core-term) fns-to-remove))
          (remove-assumptions-about fns-to-remove (rest terms))
        (cons term (remove-assumptions-about fns-to-remove (rest terms)))))))

;; Sanity check:
(thm
  (subsetp-equal (remove-assumptions-about fns-to-remove terms)
                 terms)
  :hints (("Goal" :in-theory (enable remove-assumptions-about))))

(defthm pseudo-term-listp-of-remove-assumptions-about
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (remove-assumptions-about fns-to-remove terms)))
  :hints (("Goal" :in-theory (enable remove-assumptions-about))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A lifter target is either a numeric offset, the name of a subroutine (a string), or the symbol :entry-point.
(defun lifter-targetp (target)
  (declare (xargs :guard t))
  (or (natp target)
      (stringp target)
      (eq :entry-point target)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a symbol-list.
(defund maybe-add-debug-rules (debug-rules monitor)
  (declare (xargs :guard (and (or (eq :debug monitor)
                                  (symbol-listp monitor))
                              (symbol-listp debug-rules))))
  (if (eq :debug monitor)
      debug-rules
    (if (member-eq :debug monitor)
        ;; replace :debug in the list with all the debug-rules:
        (union-eq debug-rules (remove-eq :debug monitor))
      ;; no special treatment:
      monitor)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-repeatedly-run-function-fn (name simplify-dag-name)
  (declare (xargs :guard (and (symbolp name)
                              (symbolp simplify-dag-name))))
  ;; Repeatedly rewrite DAG to perform symbolic execution.  Perform
  ;; STEP-INCREMENT steps at a time, until the run finishes, STEPS-LEFT is
  ;; reduced to 0, or a loop or an unsupported instruction is detected.
  ;; Returns (mv erp result-dag-or-quotep hits state).
  `(defun ,name (steps-done step-limit step-increment
                 dag ; the state may be wrapped in an output-extractor
                 rule-alist pruning-rule-alist
                 assumptions
                 step-opener-rule ; the rule that gets limited
                 rules-to-monitor
                 prune-precise prune-approx
                 normalize-xors count-hits hits print print-base max-printed-term-size
                 no-warn-ground-functions fns-to-elide non-stp-assumption-functions incomplete-run-fns error-fns
                 untranslatep memoizep
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
                                 (hitsp hits)
                                 (print-levelp print)
                                 (member print-base '(10 16))
                                 (natp max-printed-term-size)
                                 (symbol-listp no-warn-ground-functions)
                                 (symbol-listp fns-to-elide)
                                 (symbol-listp non-stp-assumption-functions)
                                 (symbol-listp incomplete-run-fns)
                                 (symbol-listp error-fns)
                                 (booleanp untranslatep)
                                 (booleanp memoizep))
                     :measure (nfix (+ 1 (- (nfix step-limit) (nfix steps-done))))
                     :stobjs state
                     :hints (("Goal" :in-theory (disable min)))
                     :guard-hints (("Goal" :in-theory (disable min)))))
     (if (or (not (mbt (and (natp steps-done)
                            (natp step-limit))))
             (<= step-limit steps-done))
         (mv (erp-nil) dag hits state)
       (b* (;; Decide how many steps to do this time:
            (this-step-increment (this-step-increment step-increment steps-done))
            (steps-for-this-iteration (min (- step-limit steps-done) this-step-increment))
            ((when (not (posp steps-for-this-iteration))) ; use mbt?
             (er hard? ',name "Temination problem.")
             (mv :termination-problem nil nil state))
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
            ((mv erp dag-or-constant limits hits-this-time state)
             (,simplify-dag-name dag
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
                                 no-warn-ground-functions
                                 fns-to-elide
                                 state))
            ((when erp) (mv erp nil hits state))
            (hits (combine-hits hits hits-this-time))
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
             (mv (erp-nil) dag-or-constant hits state))
            (dag dag-or-constant) ; it wasn't a constant, so name it "dag"
            ;; TODO: Consider not pruning if this increment didn't create any new branches:
            ;; Prune the DAG quickly but possibly imprecisely (actually, I've seen this be quite slow!):
            ((mv erp dag-or-constant state) (maybe-prune-dag-approximately prune-approx
                                                                           dag
                                                                           (remove-assumptions-about non-stp-assumption-functions assumptions)
                                                                           no-warn-ground-functions
                                                                           print
                                                                           60000 ; todo: pass in
                                                                           state))
            ((when erp) (mv erp nil hits state))
            ((when (quotep dag-or-constant))
             (cw "Result is a constant!~%")
             (mv (erp-nil) dag-or-constant hits state))
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
                                        no-warn-ground-functions
                                        print
                                        state))
            ((when erp) (mv erp nil hits state))
            ((when (quotep dag-or-constant))
             (cw "Result is a constant!~%")
             (mv (erp-nil) dag-or-constant hits state))
            (dag dag-or-constant) ; it wasn't a constant, so name it "dag"
            (- (and print         ;(print-level-at-least-tp print)
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
            (run-completedp (not (intersection-eq
                                  incomplete-run-fns
                                  dag-fns))) ; todo: call contains-anyp-eq
            ((mv erp nothing-changedp) (if run-completedp
                                           (mv nil nil) ; we know something changed since the run is now complete
                                         (equivalent-dagsp2 dag old-dag))) ; todo: can we test equivalence up to xor nest normalization? ; todo: check using the returned limits whether any work was done (want if was simplification but not stepping?)?
            ((when erp) (mv erp nil hits state))

            ;; Stop if we hit an unimplemented instruction (it may be on an unreachable branch, but we've already pruned -- todo: prune harder?):
            ;; ((when ..)
            ;;  (progn$ (cw "WARNING: UNIMPLEMENTED INSTRUCTION.~%") ; todo: print the name of the instruction
            ;;          (cw "~%")
            ;;          (mv :unimplemented-instruction dag state)))

            ;; ((when nothing-changedp)
            ;;  (cw "Note: Stopping the run because nothing changed.~%") ; todo: check if one of the incomplete-run-fns remains (but what if we hit one of the stop-pcs?)
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
                  ((mv erp dag-or-constant & hits2 state) ; todo: check if it is a constant?  ; todo: use the limits?
                   (,simplify-dag-name dag
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
                                       no-warn-ground-functions
                                       fns-to-elide
                                       state))
                  ((when erp) (mv erp nil hits state))
                  (hits (combine-hits hits hits2))
                  ;; todo: also prune here, if the simplfication does anything?
                  (- (cw " Done with final simplification.)~%")) ; balances "(Doing final simplification"
                  ;; Check for error branches (TODO: What if we could prune them away with more work?):
                  (dag-fns (if (quotep dag-or-constant) nil (dag-fns dag-or-constant)))
                  (error-branch-functions (intersection-eq error-fns dag-fns))
                  (incomplete-run-functions (intersection-eq incomplete-run-fns dag-fns))
                  ((when error-branch-functions)
                   (cw "~%")
                   (print-dag-nicely dag max-printed-term-size) ; use the print-base?
                   (er hard? ',name "Unresolved error branches are present (see calls of ~&0 in the term or DAG above)." error-branch-functions)
                   (mv :unresolved-error-branches nil hits state))
                  ;; Check for an incomplete run (TODO: What if we could prune away such branches with more work?):
                  ((when incomplete-run-functions)
                   (cw "~%")
                   (print-dag-nicely dag max-printed-term-size) ; use the print-base?
                   (er hard? ',name " Incomplete run (see calls of ~&0 in the term or DAG above)." incomplete-run-functions)
                   (mv :incomplete-run nil hits state)))
               (mv (erp-nil) dag-or-constant hits state))
           ;; Continue the symbolic execution:
           (b* ((steps-done (+ steps-for-this-iteration steps-done))
                (- (cw "(Steps so far: ~x0.)~%" steps-done))
                (state ;; Print as a term unless it would be huge:
                 (if (print-level-at-least-tp print)
                     (print-dag-nicely-with-base dag max-printed-term-size (concatenate 'string "after " (nat-to-string steps-done) " steps") untranslatep print-base state)
                   state)))
             (,name steps-done step-limit
                    step-increment
                    dag rule-alist pruning-rule-alist assumptions step-opener-rule rules-to-monitor prune-precise prune-approx normalize-xors count-hits hits print print-base max-printed-term-size no-warn-ground-functions fns-to-elide non-stp-assumption-functions incomplete-run-fns error-fns untranslatep memoizep
                    state)))))))

(defmacro make-repeatedly-run-function (name simplify-dag-name)
  `(make-event (make-repeatedly-run-function-fn ',name ',simplify-dag-name)))
