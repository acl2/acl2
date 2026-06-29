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
(include-book "step-increments") ; or move that material here
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
      (cw "~X01" (dag2term dag) nil) ; todo: untranslate (see below)
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
           (term (dag2term dag))
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
                          (consp (unquote arg)) ; checks for a fairly long list ; todo: allow elision-spec to contain a number indicating the max size (not length) item to print
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

;; Creates a custom version of the repeatedly-run-function for each unrolling lifter.
(defun make-repeatedly-run-function-fn (name simplify-dag-name)
  (declare (xargs :guard (and (symbolp name)
                              (symbolp simplify-dag-name))))
  ;; Repeatedly rewrites DAG to perform symbolic execution.  Repeatedly
  ;; alternates between running some number of steps (indicated by
  ;; STEP-INCREMENT) and pruning the DAG (usually), until the run finishes,
  ;; STEPS-DONE reaches STEP-LIMIT, or a loop (really?) or an unsupported
  ;; instruction is detected.  Returns (mv erp result-dag-or-quotep hits state).
  `(encapsulate ()
     (local (include-book "kestrel/arithmetic-light/types" :dir :system))

     (defund ,name (steps-done
                    step-limit
                    step-increment ; not always just a number!
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
                       :hints (("Goal" :in-theory (enable min nfix ifix)))
                       :guard-hints (("Goal" :in-theory (e/d (acl2-numberp-when-natp) (min member-equal))))))
       (if (or (not (mbt (and (natp steps-done)
                              (natp step-limit))))
               (<= step-limit steps-done))
           (mv (erp-nil) dag hits state)
         (b* (;; Decide how many steps to do this time:
              (this-step-increment (this-step-increment step-increment steps-done))
              (desired-steps-for-this-iteration (min (- step-limit steps-done) this-step-increment))
              ((when (not (posp desired-steps-for-this-iteration))) ; todo: add MBT
               (er hard? ',name "Termination problem: Desired steps is ~x0." desired-steps-for-this-iteration)
               (mv :termination-problem nil nil state))
              (- (cw "(Running (up to ~x0 steps):~%" desired-steps-for-this-iteration))
              ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
              (old-dag dag) ; so we can see if anything changed
              ;; (- (and print (progn$ (cw "(DAG before stepping:~%")
              ;;                       (cw "~X01" dag nil)
              ;;                       (cw ")~%"))))
              ;; Limit the run to the given number of steps:
              (limits nil) ; todo: call this empty-rule-limits?
              (limits (add-limit-for-rules (list step-opener-rule)
                                           desired-steps-for-this-iteration
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
              (remaining-limit (limit-for-rule step-opener-rule limits))
              ((when (not remaining-limit)) ; todo: prove this can't happen
               (er hard? ',name "The limit for ~x0 disappeared." step-opener-rule)
               (mv :limit-error dag-or-constant hits state))
              (steps-done-this-time (- desired-steps-for-this-iteration remaining-limit))
              (steps-done (+ steps-done-this-time steps-done))
              ((mv elapsed state) (real-time-since start-real-time state))
              (- (cw " (~x0 steps took " steps-done-this-time)
                 (print-to-hundredths elapsed) ; todo: could have real-time-since detect negative time
                 (cw "s.)"))
              (- (cw ")~%")) ; matches "(Running"
              ((when (quotep dag-or-constant)) ; rare for it to be a constant
               (cw "Total steps: ~x0.~%" steps-done)
               (cw "Result is a constant!~%")
               (mv (erp-nil) dag-or-constant hits state))
              (dag dag-or-constant) ; it wasn't a constant, so name it "dag"
              (dag-before-pruning dag) ; remember this for comparison below
              ;; Prune the DAG quickly but possibly imprecisely (actually, I've seen this be quite slow!):
              ;; TODO: Consider not pruning if this run didn't create any new branches:
              ((mv erp dag-or-constant state) (maybe-prune-dag-approximately prune-approx
                                                                             dag
                                                                             (remove-assumptions-about non-stp-assumption-functions assumptions)
                                                                             no-warn-ground-functions
                                                                             print
                                                                             60000 ; todo: pass in
                                                                             state))
              ((when erp) (mv erp nil hits state))
              ((when (quotep dag-or-constant))
               (cw "Total steps: ~x0.~%" steps-done)
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
               (cw "Total steps: ~x0.~%" steps-done)
               (cw "Result is a constant!~%")
               (mv (erp-nil) dag-or-constant hits state))
              (dag dag-or-constant) ; it wasn't a constant, so name it "dag"
              (- (and print         ;(print-level-at-least-tp print)
                      (progn$ (cw "(DAG after this limited run:~%")
                              (cw "~X01" dag nil)
                              (cw ")~%"))))
              ;; (- (and print (progn$ (cw "(DAG after second pruning:~%")
              ;;                       (cw "~X01" dag nil)
              ;;                       (cw ")~%"))))
              ;; TODO: If pruning did something, consider doing another rewrite here (pruning may have introduced bvchop or bool-fix$inline).  But perhaps now there are enough rules used in pruning to handle that?
              (dag-fns (dag-fns dag)) ; todo: optimize to avoid making this whole list
              ;; Check for an incomplete run (TODO: What if we could prune away such branches with more work?):
              (remaining-incomplete-run-fns (intersection-eq incomplete-run-fns dag-fns))
              (run-completedp (not remaining-incomplete-run-fns)) ; todo: call contains-anyp-eq?
              )
           (if run-completedp
               ;; Stop, since the run is done (but maybe simplify one last time):
               (b* ((- (cw " The run completed.~%"))
                    (- (cw "Total steps: ~x0.~%" steps-done))
                    ;; Maybe simplify one last time:
                    ((mv erp dag-or-constant hits2 state)
                     (if (equal dag dag-before-pruning) ; could use equivalent-dagsp here but maybe not needed
                         (prog2$ ;; Pruning did nothing, so we don't need to simplify again:
                           (cw "Note: No need for final simplification.~%")
                           (mv (erp-nil) dag nil state))
                       (b* ((- (cw "(Doing final simplification:~%"))
                            ((mv erp dag-or-constant & hits2 state) ; ignore the limits
                             (,simplify-dag-name dag
                                                 assumptions
                                                 rule-alist ; todo: don't use the symbolic execution rules here?
                                                 nil ; interpreted-function-alist
                                                 (known-booleans (w state))
                                                 normalize-xors
                                                 limits ; todo: don't pass, since we are done running?  can non-run rule be limited?
                                                 memoizep
                                                 count-hits
                                                 print
                                                 rules-to-monitor
                                                 no-warn-ground-functions
                                                 fns-to-elide
                                                 state))
                            (- (cw " Done with final simplification.)~%")) ; balances "(Doing final simplification"
                            )
                         (mv erp dag-or-constant hits2 state))))
                    ((when erp) (mv erp nil hits state))
                    (hits (combine-hits hits hits2))
                    ((when (quotep dag-or-constant)) ; rare for it to be a constant
                     (cw "Result is a constant!~%")
                     (mv (erp-nil) dag-or-constant hits state))
                    (dag dag-or-constant) ; it wasn't a constant, so name it "dag"
                    ;; todo: also prune here, if the simplfication does anything?
                    ;; TODO: Maybe don't prune if the run completed and there are no error branches?

                    ;; Check for error branches (TODO: What if we could prune them away with more work?):
                    ;; This should probably never happen, since the run-until should remain wrapped around the error branch.
                    (dag-fns (dag-fns dag))
                    (error-branch-functions (intersection-eq error-fns dag-fns))
                    ((when error-branch-functions)
                     (cw "~%")
                     (print-dag-nicely dag max-printed-term-size) ; use the print-base?
                     (er hard? ',name "Unresolved error branches are present (see calls of ~&0 in the term or DAG above)." error-branch-functions)
                     (mv :unresolved-error-branches nil hits state)))
                 (mv (erp-nil) dag hits state))
             ;; The run did not complete:
             (b* (((mv erp nothing-changedp) (equivalent-dagsp2 dag old-dag)) ; todo: can we test equivalence up to xor nest normalization? ; todo: check using the returned limits whether any work was done (what if it was simplification but not stepping?)?
                  ((when erp) (mv erp nil hits state))
                  ;; Stop if we hit an unimplemented instruction (it may be on an unreachable branch, but we've already pruned -- todo: prune harder?):
                  ;; ((when ..)
                  ;;  (progn$ (cw "WARNING: UNIMPLEMENTED INSTRUCTION.~%") ; todo: print the name of the instruction
                  ;;          (cw "~%")
                  ;;          (mv :unimplemented-instruction dag state)))
                  ;;  )
                  )
               (if nothing-changedp ; we know from the check above that the run is not complete (what if we hit one of the stop-pcs?)
                   ;; todo: return an error?  or maybe this can happen if we hit one of the stop-pcs
                   (b* ((- (cw " The run did not complete, but nothing is changing.~%"))
                        (- (cw "Total steps: ~x0.~%" steps-done))
                        ;; No need to try a final simplification or pruning, I guess, because the simplification/pruning this time around didn't change anything.
                        ;; Check for error branches (TODO: What if we could prune them away with more work?):
                        (dag-fns (dag-fns dag)) ; done above?
                        (error-branch-functions (intersection-eq error-fns dag-fns))
                        ;; todo: consider printing both of these kinds of info:
                        ((when error-branch-functions)
                         (cw "~%")
                         (print-dag-nicely dag max-printed-term-size) ; use the print-base?
                         (er hard? ',name "Unresolved error branches are present (see calls of ~&0 in the term or DAG above)." error-branch-functions)
                         (mv :unresolved-error-branches nil hits state))
                        ((when remaining-incomplete-run-fns)
                         (cw "~%")
                         (print-dag-nicely dag max-printed-term-size) ; use the print-base?
                         (er hard? ',name " Incomplete run (see calls of ~&0 in the term or DAG above)." remaining-incomplete-run-fns)
                         (mv :incomplete-run nil hits state)))
                     (mv :error-incomplete-run ; is this case possible?
                         dag hits state))
                 ;; Something changed, so continue the symbolic execution:
                 (b* (((when (not (posp steps-done-this-time))) ; for termination
                       (er hard? ',name "No steps were done, but the run is not complete.")
                       (mv :no-steps-done dag hits state))
                      (- (cw "(Steps so far: ~x0.)~%" steps-done))
                      (state ;; Print as a term unless it would be huge:
                        (if (print-level-at-least-tp print)
                            (print-dag-nicely-with-base dag max-printed-term-size (concatenate 'string "after " (nat-to-string steps-done) " steps") untranslatep print-base state)
                          state)))
                   (,name steps-done step-limit step-increment
                          dag rule-alist pruning-rule-alist assumptions step-opener-rule rules-to-monitor prune-precise prune-approx normalize-xors count-hits hits print print-base max-printed-term-size no-warn-ground-functions fns-to-elide non-stp-assumption-functions incomplete-run-fns error-fns untranslatep memoizep
                          state))))))))))

(defmacro make-repeatedly-run-function (name simplify-dag-name)
  `(make-event (make-repeatedly-run-function-fn ',name ',simplify-dag-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; maybe extends acc
(defund add-lifter-event-name (event acc)
  (declare (xargs :guard (true-listp acc)))
  (if (not (and (consp event)
                (true-listp event)))
      (er hard? 'lifter-event-name "Bad event encountered: ~x0." event)
    (case (car event)
      ;; These events don't have names:
      ((include-book) acc)
      ((skip-proofs) (add-lifter-event-name (cadr event) acc))
      ;; probably anything local should be ignored?
      ((defconst defun defun-nx defund defund-nx defthm defthmd)
       (cons (cadr event) acc))
      (otherwise (er hard? 'lifter-event-name "Unhandled event type: ~x0." event)))))

;; These are passed to value-triple for printing as the 'return value' of the lifter.
(defund lifter-event-names (events acc)
  (declare (xargs :guard (and (true-listp events)
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable add-lifter-event-name)))))
  (if (endp events)
      (reverse acc)
    (lifter-event-names (rest events)
                        (add-lifter-event-name (first events) acc))))
