; Pruning irrelevant IF-branches
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Prune irrelevant if-then-else branches in terms and DAGs using rewriting and calls to STP.

;; TODO: Use counterexamples returned by STP to avoid later calls that will fail.

(include-book "rewriter-basic") ;because we call simplify-term-basic
(include-book "prove-with-stp")
(include-book "interpreted-function-alists")
(include-book "kestrel/utilities/subtermp" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/utilities/w" :dir :system))

;(in-theory (disable table-alist)) ;why?

(local (in-theory (disable symbol-listp
                           use-all-consp-for-car
                           ;; subsetp-car-member ; bad?
                           member-equal
                           use-all-consp ; bad?
                           use-all-consp-2 ; bad?
                           ;; GET-GLOBAL
                           ACL2-COUNT
                           default-car
                           default-cdr
                           CONSP-FROM-LEN-CHEAP
                           state-p
                           nth
                           consp-of-car-when-symbol-term-alistp-cheap
                           equal-constant-when-bvchop-equal-constant-false
                           pseudo-dagp-of-cdr-when-pseudo-dagp
                           ;; not sure if these help:
                           ;;pseudo-term-listp
                           ;;quotep
                           union-equal-when-not-consp-arg1-cheap
                           union-equal-when-not-consp-arg2-cheap
                           ;; todo: many of these should either not be imported or be at least disabled:
                           car-of-car-when-pseudo-dagp-aux consp-of-car-when-pseudo-dagp consp-of-car-when-pseudo-dagp-aux consp-of-car-when-pseudo-dagp-aux-2 ; todo: disable globally?
                           integerp-of-nth-when-all-natp
                           equal-of-non-natp-and-caar-when-when-bounded-natp-alistp
                           quote-lemma-for-bounded-darg-listp-gen-alt
                           true-listp-of-car-when-when-bounded-natp-alistp
                           len-when-dargp-cheap
                           )))

(local
  (defthm quotep-forward-to-consp
    (implies (quotep x)
             (consp x))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable quotep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund lookup-with-default (key alist default)
  (declare (xargs :guard (and (eqlablep key)
                              (alistp alist))))
  (let ((res (assoc key alist)))
    (if (not res)
        default
      (cdr res))))

(local
  (defthm natp-of-lookup-with-default-type
    (implies (and (nat-listp (strip-cdrs alist))
                  (natp default))
             (natp (lookup-with-default key alist default)))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable lookup-with-default assoc-equal strip-cdrs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund count-top-level-if-branches-in-rev-dag (rev-dag
                                                alist ; maps nodenums to the number of if-leaves they each represent
                                                )
  (declare (xargs :guard (and (weak-dagp rev-dag)
                              (alistp alist)
                              (nat-listp (strip-cdrs alist)))
                  :guard-hints (("Goal" :in-theory (enable consp-of-cdr-of-dargs-when-dag-exprp-iff
                                                           consp-of-dargs-when-dag-exprp-iff)))))
  (if (not (mbt (consp rev-dag)))
      (er hard? 'count-top-level-if-branches-in-rev-dag "Empty DAG.")
    (let* ((entry (first rev-dag))
           (expr (cdr entry))
           (leaf-count (if (and (call-of 'if expr)
                                (consp (cdr (cdr (dargs expr)))))
                           (let ((then (darg2 expr))
                                 (else (darg3 expr)))
                             ;; only counting leaves in the then and else branches, not the test:
                             (+ (if (consp then) ; check for quotep
                                    1
                                  (lookup-with-default then alist 1))
                                (if (consp else) ; check for quotep
                                    1
                                  (lookup-with-default else alist 1))))
                         1 ; level expr is not an IF
                         )))
      (if (endp (cdr rev-dag)) ; we've reached the top node
          leaf-count
        (count-top-level-if-branches-in-rev-dag (cdr rev-dag)
                                                (if (< 1 leaf-count)
                                                    ;; only store counts greater than 1:
                                                    (acons (car entry) leaf-count alist)
                                                  alist))))))

;; Does not look for MYIF or BVIF or anything like that, only IF.
;; TODO: Optimize by using a result array?
(defund count-top-level-if-branches-in-dag (dag)
  (declare (xargs :guard (pseudo-dagp dag)))
  (count-top-level-if-branches-in-rev-dag (reverse-list dag) nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Do not remove: justifies treatment of bool-fix below
(thm (equal (boolif test x x) (bool-fix x)))

;; Do not remove: justifies treatment of bvif below
(thm (equal (bvif size test x x) (bvchop size x)))

;; Fixup assumption when it will obviously loop when used as a directed equality.
;; could check for (equal <constant> <x>) here too, but Axe may be smart enough to reorient that
;; Returns a possibly-empty list.
(defund fixup-assumption (assumption print)
  (declare (xargs :guard (and (pseudo-termp assumption)
                              (print-levelp print))))
  (if (not (and (consp assumption)
                (eq 'equal (ffn-symb assumption))
                (eql 2 (len (fargs assumption))) ;for guards
                ))
      (list assumption)
    (if (subtermp (farg1 assumption) (farg2 assumption))
        (prog2$ (and (print-level-at-least-briefp print)
                     (cw "(Note: re-orienting equality assumption ~x0.)~%" assumption))
                `((equal ,(farg2 assumption) ,(farg1 assumption))))
      (if (quotep (farg1 assumption))
          (list assumption)
        (if (quotep (farg2 assumption))
            `((equal ,(farg1 assumption) ,(farg2 assumption)))
          (prog2$ (and (print-level-at-least-briefp print)
                       (cw "(Note: Dropping equality assumption ~x0.)~%" assumption))
                  nil))))))

(local
  (defthm pseudo-term-listp-of-fixup-assumption
    (implies (pseudo-termp assumption)
             (pseudo-term-listp (fixup-assumption assumption print)))
    :hints (("Goal" :in-theory (enable fixup-assumption)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reorder equalities that obviously loop (because a term is equated to a
;; superterm).  TODO: Perform a more thorough analysis of possible looping.
(defund fixup-assumptions (assumptions print)
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (print-levelp print))))
  (if (endp assumptions)
      nil
    (union-equal (fixup-assumption (first assumptions) print)
                 (fixup-assumptions (rest assumptions) print))))

(local
  (defthm pseudo-term-listp-of-fixup-assumptions
    (implies (pseudo-term-listp assumptions)
             (pseudo-term-listp (fixup-assumptions assumptions print)))
    :hints (("Goal" :in-theory (enable fixup-assumptions)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund get-equalities (assumptions)
  (declare (xargs :guard (pseudo-term-listp assumptions)))
  (if (endp assumptions)
      nil
    (let ((assumption (first assumptions)))
      (if (call-of 'equal assumption)
          (cons assumption (get-equalities (rest assumptions)))
        (get-equalities (rest assumptions))))))

(local
  (defthm pseudo-term-listp-of-get-equalities
    (implies (pseudo-term-listp assumptions)
             (pseudo-term-listp (get-equalities assumptions)))
    :hints (("Goal" :in-theory (enable get-equalities)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund make-bool-fix (arg)
  (declare (xargs :guard (pseudo-termp arg)))
  (if (quotep arg)
      (enquote (bool-fix (unquote arg)))
    `(bool-fix$inline ,arg)))

(local
  (defthm pseudo-termp-of-make-bool-fix
    (implies (pseudo-termp arg)
             (pseudo-termp (make-bool-fix arg)))
    :hints (("Goal" :in-theory (enable make-bool-fix)))))

(defund make-bvchop (size x)
  (declare (xargs :guard (and (pseudo-termp size)
                              (pseudo-termp x))))
  (if (and (quotep x) ; unusual, so we test this first
           (quotep size)
           (natp (unquote x))
           (natp (unquote size)))
      (enquote (bvchop (unquote size) (unquote x)))
    `(bvchop ,size ,x)))

(local
  (defthm pseudo-termp-of-make-bvchop
    (implies (and (pseudo-termp x)
                  (pseudo-termp size))
             (pseudo-termp (make-bvchop size x)))
    :hints (("Goal" :in-theory (enable make-bvchop)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tries to resolve the TEST assuming the ASSUMPTIONS and EQUALITY-ASSUMPTIONS.  Uses rewriting and STP.
;; Returns (mv erp result state) where RESULT is :true (meaning non-nil), :false, or :unknown.
;; (It may be the case that the test can be shown to be both true and false,
;; because the assumptions contradict, in which case the entire enclosing
;; IF/MYIF/BOOLIF/BVIF may be irrelevant.)
;; TODO: Allow STP to run longer (more conflicts) for IFs that are higher up in the term, since resolving such an IF throws away more stuff.
(defund try-to-resolve-test (test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)
  (declare (xargs :guard (and (pseudo-termp test)
                              (pseudo-term-listp assumptions)
                              (pseudo-term-listp equality-assumptions)
                              (symbol-listp monitored-rules)
                              (rule-alistp rule-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              (or (booleanp call-stp)
                                  (natp call-stp))
                              (print-levelp print))
                  :stobjs state))
  (b* ((- (and (print-level-at-least-verbosep print)
               (cw "(Attempting to resolve test using ~x0 assumptions and ~x1 equality assumptions.~%" (len assumptions) (len equality-assumptions))))
       ;; First apply the Axe Rewriter to the test:
       (- (and (print-level-at-least-verbosep print)
               (cw "(Simplifying test.~%")))
       ;; TODO: Consider first doing something faster than a DAG-producing
       ;; rewrite, such as evaluating ground terms, using assumptions, and
       ;; applying rules that don't expand the term size too much.
       ((mv erp simplified-dag-or-quotep)
        (simplify-term-basic test
                             assumptions ;no equality assumptions here to prevent loops (todo: think about this)
                             rule-alist
                             interpreted-function-alist
                             (known-booleans (w state))
                             nil ; normalize-xors
                             nil ; limits
                             nil ; memoizep
                             nil ; count-hits
                             nil ; print
                             monitored-rules
                             nil ; fns-to-elide
                             ))
       ((when erp)
        (cw "ERROR simplifying test.))~%")
        (mv erp nil state))
       ((when (quotep simplified-dag-or-quotep))
        ;; Resolved the test via rewriting:
        (and (print-level-at-least-verbosep print)
             (cw "Simplified to the constant ~x0.))~%" simplified-dag-or-quotep))
        (if (unquote simplified-dag-or-quotep)
            (mv nil :true state)
          (mv nil :false state)))
       ;; Test did not rewrite to a constant, so try other things:
       ;; (- (cw "(Simplified to ~X01.)~%" simplified-dag-or-quotep nil))
       (- (and (print-level-at-least-verbosep print)
               (cw "Test did not simplify to a constant.)~%")))
       ;; Is this needed, given that we simplified the test above using the assumptions?
       ;; TODO: Also look for an equality in the other order?:
       ((when (or (member-equal test assumptions)
                  (member-equal test equality-assumptions))) ;; In case the test is not a known boolean (so rewriting can't rewrite it to t). ;todo: use simplified-test-term here?
        (and (print-level-at-least-verbosep print)
             (cw "(The test is a known assumption.))") ; todo: look for negated assumptions too
             )
        (mv nil :true state)) ;a test that's in the assumptions is like a test that rewrites to t
       ;; TODO: What if the test is equal to an assumption but not identical to it (e.g., a disjunction with the disjuncts reordered?)
       ((when (not call-stp))
        (and (print-level-at-least-verbosep print)
             (cw "Failed to resolve test by rewriting and we have been told not to call STP.)"))
        (mv nil :unknown state)) ; give up if we are not allowed to call STP
       ;; TODO: Avoid turning the DAG into a term:
       (simplified-test-term (dag-to-term simplified-dag-or-quotep)) ;TODO: check that this is not huge (I suppose it could be if something gets unrolled)
       ;; TODO: Consider trying to be smart about whether to try the true proof or the false proof first (e.g., by running a test).
       (- (and (print-level-at-least-verbosep print)
               (cw "(Attempting to prove test true with STP:~%")))
       ((mv true-result state)
        (prove-term-implication-with-stp simplified-test-term
                                    (append assumptions equality-assumptions)
                                    nil         ;counterexamplep
                                    nil ; print-cex-as-signedp
                                    (if (natp call-stp) call-stp *default-stp-max-conflicts*)
                                    nil                ;print
                                    "PRUNE-PROVE-TRUE" ;todo: do better?
                                    state))
       ((when (eq *error* true-result))
        (prog2$ (er hard? 'try-to-resolve-test "Error calling STP")
                (mv :error-calling-stp :unknown state)))
       ((when (eq *valid* true-result)) ;; STP proved the test
        (prog2$ (and (print-level-at-least-verbosep print)
                     (cw "STP proved the test true.))~%"))
                (mv nil :true state)))
       (- (and (print-level-at-least-verbosep print)
               (cw "STP failed to prove the test true.)~%")))
       (- (and (print-level-at-least-verbosep print)
               (cw "(Attempting to prove test false with STP:~%")))
       ((mv false-result state)
        (prove-term-implication-with-stp `(not ,simplified-test-term)
                                    assumptions ;todo: this caused problems with an rlp example: (append assumptions equality-assumptions)
                                    nil         ;counterexamplep
                                    nil ; print-cex-as-signedp
                                    (if (natp call-stp) call-stp *default-stp-max-conflicts*)
                                    nil                 ;print
                                    "PRUNE-PROVE-FALSE" ;todo: do better?
                                    state))
       ((when (eq *error* false-result))
        (prog2$ (er hard? 'try-to-resolve-test "Error calling STP")
                (mv :error-calling-stp :unknown state)))
       ((when (eq *valid* false-result)) ;; STP proved the negation of the test
        (prog2$ (and (print-level-at-least-verbosep print)
                     (cw "STP proved the test false.))~%"))
                (mv nil :false state))))
    (prog2$ (and (print-level-at-least-verbosep print)
                 (cw "STP did not resolve the test.))~%"))
            (mv nil :unknown state))))

(local
  (defthm w-of-mv-nth-2-of-try-to-resolve-test
    (equal (w (mv-nth 2 (try-to-resolve-test test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)))
           (w state))
    :hints (("Goal" :in-theory (enable try-to-resolve-test)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
 ;; Returns (mv erp result-term state) where RESULT-TERM is equal
 ;; to TERM. Tries to rewrite each if/myif/boolif/bvif test using context from all overarching
 ;; tests (and any given assumptions).
 ;; TODO: Add an IFF flag and, if set, turn (if x t nil) into x and (if x nil t) into (not x)
 ;; TODO: Consider filtering out assumptions unusable by STP once instead of each time try-to-resolve-test is called (or perhaps improve STP to use the known-booleans machinery so it rejects many fewer assumptions).
 (defund prune-term-aux (term assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)
   (declare (xargs :guard (and (pseudo-termp term)
                               (pseudo-term-listp assumptions)
                               (pseudo-term-listp equality-assumptions) ;used only for looking up conditions
                               (symbol-listp monitored-rules)
                               (rule-alistp rule-alist)
                               (interpreted-function-alistp interpreted-function-alist)
                               (or (booleanp call-stp)
                                   (natp call-stp))
                               (print-levelp print))
                   :stobjs state
                   :verify-guards nil ; done below
                   ))
   (if (variablep term)
       (mv (erp-nil) term state) ; can't prune a var
     (let ((fn (ffn-symb term)))
       (case fn
         (quote (mv (erp-nil) term state)) ; can't prune a constant
         ((if myif) ;; (if/myif test then-branch else-branch)
          (b* ((test (farg1 term))
               ;; First prune the test:
               ((mv erp test state)
                (prune-term-aux test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state))
               ((when erp) (mv erp nil state))
               ;; Now try to resolve the pruned test:
               ((mv erp result ; :true, :false, or :unknown
                    state)
                ;; TODO: Consider having try-to-resolve-test return the simplified test, for use below
                (try-to-resolve-test test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state))
               ((when erp) (mv erp nil state)))
            (if (eq :true result)
                ;; Throw away the else-branch:
                (prune-term-aux (farg2 term) assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state) ;we could add the condition as an assumption here
              (if (eq :false result)
                  ;; Throw away the then-branch:
                  (prune-term-aux (farg3 term) assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state) ;we could add the negated condition as an assumption here
                ;; Could not resolve the test:
                (b* (;; Prune the then-branch, assuming the (pruned, but not simplified) test:
                     (then-branch (farg2 term))
                     ((mv erp then-branch state)
                      (if (quotep then-branch)
                          ;; special case (avoid fixing up assumptions, which can print a message when one gets reoriented):
                          (mv (erp-nil) then-branch state)
                        (let ((test-conjuncts (get-conjuncts-of-term2 test)))
                          (prune-term-aux then-branch
                                          (union-equal (fixup-assumptions test-conjuncts print) assumptions)
                                          (union-equal (get-equalities test-conjuncts) equality-assumptions)
                                          rule-alist interpreted-function-alist monitored-rules call-stp print state))))
                     ((when erp) (mv erp nil state))
                     ;; Print the else-branch, assuming the negation of the (pruned, but not simplified) test:
                     (else-branch (farg3 term))
                     ((mv erp else-branch state)
                      (if (quotep else-branch)
                          (mv (erp-nil) else-branch state)
                        ;; TODO: Perhaps call get-disjunction and handle a possible constant returned?:
                        (let ((negated-test-conjuncts (negate-disjuncts (get-disjuncts-of-term2 test))))
                          (prune-term-aux else-branch
                                          (union-equal (fixup-assumptions negated-test-conjuncts print) assumptions)
                                          (union-equal (get-equalities negated-test-conjuncts) equality-assumptions)
                                          rule-alist interpreted-function-alist monitored-rules call-stp print state))))
                     ((when erp) (mv erp nil state))
                     (new-term (if (equal then-branch else-branch)
                                   then-branch ; special case when both branches are the same
                                 ;; Can't be a ground term since test was not resolved:
                                 `(,fn ,test ,then-branch ,else-branch))))
                  (mv (erp-nil) new-term state))))))
         (boolif ;; (boolif test then-branch else-branch)
          (b* ((test (farg1 term))
               (then-branch (farg2 term))
               (else-branch (farg3 term))
               ;; First prune the test:
               ((mv erp test state)
                (prune-term-aux test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state))
               ((when erp) (mv erp nil state))
               ;; Now try to resolve the pruned test:
               ((mv erp result ;:true, :false, or :unknown
                    state)
                (try-to-resolve-test test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state))
               ((when erp) (mv erp nil state)))
            (if (eq :true result)
                ;; Throw away the else-branch:
                (mv-let (erp then-branch state)
                  ;; we could add the condition as an assumption here:
                  (prune-term-aux then-branch assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)
                  (if erp
                      (mv erp nil state)
                    (mv (erp-nil)
                        ;; todo: skip the bool-fix if known-boolean:
                        (make-bool-fix then-branch)
                        state)))
              (if (eq :false result)
                  ;; Throw away the then-branch:
                  (mv-let (erp else-branch state)
                    ;; we could add the negated condition as an assumption here:
                    (prune-term-aux else-branch assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)
                    (if erp
                        (mv erp nil state)
                      (mv (erp-nil)
                          ;; todo: skip the bool-fix if known-boolean:
                          (make-bool-fix else-branch)
                          state)))
                ;; Failed to resolve the test.
                (b* (;; Prune the then-branch, assuming the (pruned, but not simplified) test:
                     ((mv erp then-branch state)
                      (if (quotep then-branch)
                          (mv (erp-nil) then-branch state)
                        (let ((test-conjuncts (get-conjuncts-of-term2 test)))
                          (prune-term-aux then-branch
                                          (union-equal (fixup-assumptions test-conjuncts print) assumptions)
                                          (union-equal (get-equalities test-conjuncts) equality-assumptions)
                                          rule-alist interpreted-function-alist monitored-rules call-stp print state))))
                     ((when erp) (mv erp nil state))
                     ;; Prune the else-branch, assuming the negation of the (pruned, but not simplified) test:
                     ;; TODO: Perhaps call get-disjunction and handle a possible constant returned?:
                     ((mv erp else-branch state)
                      (if (quotep else-branch)
                          (mv (erp-nil) else-branch state)
                        (let ((negated-test-conjuncts (negate-disjuncts (get-disjuncts-of-term2 test))))
                          (prune-term-aux else-branch
                                          (union-equal (fixup-assumptions negated-test-conjuncts print) assumptions)
                                          (union-equal (get-equalities negated-test-conjuncts) equality-assumptions)
                                          rule-alist interpreted-function-alist monitored-rules call-stp print state))))
                     ((when erp) (mv erp nil state))
                     (new-term (if (equal then-branch else-branch)
                                   (make-bool-fix then-branch) ; special case when both branches are the same
                                 ;; Can't be a ground term since test was not resolved:
                                 `(boolif ,test ,then-branch ,else-branch))))
                  (mv (erp-nil) new-term state))))))
         (bvif ;; (bvif size test then-branch else-branch)
          (b* ((size (farg1 term)) ;todo: prune this (it will usually be a constant, so that will be quick)?
               (test (farg2 term))
               (then-branch (farg3 term))
               (else-branch (farg4 term))
               ;; First prune the test:
               ((mv erp test state)
                (prune-term-aux test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state))
               ((when erp) (mv erp nil state))
               ;; Now try to resolve the pruned test:
               ((mv erp result ;:true, :false, or :unknown
                    state)
                (try-to-resolve-test test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state))
               ((when erp) (mv erp nil state)))
            (if (eq :true result)
                ;; Throw away the else-branch:
                (mv-let (erp then-branch state)
                  ;; we could add the condition as an assumption here:
                  (prune-term-aux then-branch assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)
                  (if erp
                      (mv erp nil state)
                    (mv (erp-nil)
                        (make-bvchop size then-branch)
                        state)))
              (if (eq :false result)
                  ;; Throw away the then-branch:
                  (mv-let (erp else-branch state)
                    ;; we could add the negated condition as an assumption here:
                    (prune-term-aux else-branch assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)
                    (if erp
                        (mv erp nil state)
                      (mv (erp-nil)
                          (make-bvchop size else-branch)
                          state)))
                ;; Failed to resolve the test:
                (b* (;; Prune the then-branch, assuming the (pruned, but not simplified) test:
                     ((mv erp then-branch state)
                      (if (quotep then-branch)
                          (mv (erp-nil) then-branch state)
                        (let ((test-conjuncts (get-conjuncts-of-term2 test)))
                          (prune-term-aux then-branch
                                          (union-equal (fixup-assumptions test-conjuncts print) assumptions)
                                          (union-equal (get-equalities test-conjuncts) equality-assumptions)
                                          rule-alist interpreted-function-alist monitored-rules call-stp print state))))
                     ((when erp) (mv erp nil state))
                     ;; Recur on the else-branch, assuming the negation of the (pruned, but not simplified) test:
                     ;; TODO: Perhaps call get-disjunction and handle a possible constant returned?:
                     ((mv erp else-branch state)
                      (if (quotep else-branch)
                          (mv (erp-nil) else-branch state)
                        (let ((negated-test-conjuncts (negate-disjuncts (get-disjuncts-of-term2 test))))
                          (prune-term-aux else-branch
                                          (union-equal (fixup-assumptions negated-test-conjuncts print) assumptions)
                                          (union-equal (get-equalities negated-test-conjuncts) equality-assumptions)
                                          rule-alist interpreted-function-alist monitored-rules call-stp print state))))
                     ((when erp) (mv erp nil state))
                     (new-term (if (equal then-branch else-branch)
                                   (make-bvchop size then-branch) ; special case when both branches are the same
                                 ;; Can't be a ground term since test was not resolved:
                                 `(bvif ,size ,test ,then-branch ,else-branch))))
                  (mv (erp-nil) new-term state))))))
         (t ;; Anything other than if/myif/bvif/boolif:
          ;; TODO: Handle bv-array-if?
          ;; TODO: Handle boolor?
          ;; TODO: Handle booland?
          ;; Look this up in the assumptions (if boolean or if only iff must be preserved -- could pass in an iff flag)?
          ;; TODO: Just do this for tests?
          ;; Do this even when the node is an IF/MYIF/BOOLIF/BVIF ?
          (if (and (or (member-equal term assumptions)
                       (member-equal term equality-assumptions) ; todo: also look for it with the equality reoriented?
                       )
                   (member-eq (ffn-symb term) (known-booleans (w state)))) ;todo avoid repeated calls to known-booleans
              (mv (erp-nil) *t* state)
            ;; Prune branches in arguments:
            (b* ((args (fargs term))
                 ((mv erp new-args state) (prune-terms-aux args assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state))
                 ((when erp) (mv erp nil state))
                 ;; Try to evaluate a ground term:
                 ((mv erp evaluatedp val) ; val only meaningful if evaluatedp
                  (if (not (all-myquotep new-args))
                      (mv (erp-nil) nil nil) ; not a ground term
                    ;; ground term, so try to evaluate (may fail, but we may have a constant opener rule to apply later):
                    (b* (((mv erp val) (apply-axe-evaluator-basic-to-quoted-args fn new-args interpreted-function-alist)))
                      (if erp
                          (if (call-of :unknown-function erp)
                              (mv (erp-nil) nil nil) ; suppress error, but it didn't produce a value (todo: print a warning?)
                            ;; anything else non-nil is a true error:
                            (mv erp nil nil))
                        ;; normal case (evaluated to VAL):
                        (mv (erp-nil) t val)))))
                 ((when erp) (mv erp nil state))
                 (new-term (if evaluatedp
                               (enquote val)
                             ;; todo: any other simplifications to try?:
                             `(,fn ,@new-args))))
              (mv (erp-nil) new-term state))))))))

 ;; Returns (mv erp result-terms state) where, if ERP is nil, then the
 ;; RESULT-TERMS are equal to their corresponding TERMS, given the ASSUMPTIONS
 ;; and EQUALITY-ASSUMPTIONS.
 (defund prune-terms-aux (terms assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (pseudo-term-listp assumptions)
                               (pseudo-term-listp equality-assumptions)
                               (rule-alistp rule-alist)
                               (interpreted-function-alistp interpreted-function-alist)
                               (symbol-listp monitored-rules)
                               (or (booleanp call-stp)
                                   (natp call-stp))
                               (print-levelp print))
                   :stobjs state))
   (if (endp terms)
       (mv (erp-nil) nil state)
     (b* (((mv erp pruned-first state) (prune-term-aux (first terms) assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state))
          ((when erp) (mv erp nil state))
          ((mv erp pruned-rest state) (prune-terms-aux (rest terms) assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state))
          ((when erp) (mv erp nil state)))
       (mv (erp-nil) (cons pruned-first pruned-rest) state)))))

(local
  (make-flag prune-term-aux))

(local
  (defthm-flag-prune-term-aux
    (defthm len-of-mv-nth-1-of-prune-terms-aux
      (implies (not (mv-nth 0 (prune-terms-aux terms assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)))
               (equal (len (mv-nth 1  (prune-terms-aux terms assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)))
                      (len terms)))
      :flag prune-terms-aux)
    :skip-others t
    :hints (("Goal" :in-theory (enable prune-terms-aux)))))

;; todo: slow
(local
  (defthm-flag-prune-term-aux
    (defthm prune-term-aux-return-type
      (implies (and (pseudo-termp term)
                    (pseudo-term-listp assumptions)
                    (pseudo-term-listp equality-assumptions) ;used only for looking up conditions
                    (symbol-listp monitored-rules)
                    (rule-alistp rule-alist)
                    (interpreted-function-alistp interpreted-function-alist))
               (pseudo-termp (mv-nth 1 (prune-term-aux term assumptions equality-assumptions
                                                       rule-alist interpreted-function-alist
                                                       monitored-rules call-stp print state))))
      :flag prune-term-aux)
    (defthm prune-terms-aux-return-type
      (implies (and (pseudo-term-listp terms)
                    (pseudo-term-listp assumptions)
                    (pseudo-term-listp equality-assumptions)
                    (rule-alistp rule-alist)
                    (interpreted-function-alistp interpreted-function-alist)
                    (symbol-listp monitored-rules))
               (pseudo-term-listp (mv-nth 1  (prune-terms-aux terms assumptions equality-assumptions
                                                              rule-alist interpreted-function-alist
                                                              monitored-rules call-stp print state))))
      :flag prune-terms-aux)
    :hints (("Goal" :in-theory (e/d (prune-term-aux prune-terms-aux symbolp-when-member-equal-and-symbol-listp)
                                    (;pseudo-term-listp quotep
                                     ))))))

(verify-guards prune-term-aux :hints (("Goal" :in-theory (enable true-listp-when-pseudo-term-listp-2))))

(local
  (defthm-flag-prune-term-aux
    (defthm w-of-mv-nth-2-of-prune-term-aux
      (equal (w (mv-nth 2 (prune-term-aux term assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)))
             (w state))
      :flag prune-term-aux)
    (defthm w-of-mv-nth-2-of-prune-terms-aux
      (equal (w (mv-nth 2 (prune-terms-aux terms assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)))
             (w state))
      :flag prune-terms-aux)
    :hints (("Goal" :in-theory (enable prune-term-aux prune-terms-aux symbolp-when-member-equal-and-symbol-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp changep result-term state).
;; TODO: Print some stats about the pruning process?
;; TODO: Allow rewriting to be suppressed (just call STP)?
(defund prune-term (term assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-term-listp assumptions)
                              (rule-alistp rule-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              (symbol-listp monitored-rules)
                              (or (booleanp call-stp)
                                  (natp call-stp))
                              (print-levelp print))
                  :stobjs state))
  (b* ((- (and (print-level-at-least-tp print)
               (cw "(Pruning term (~x0 rules, ~x1 assumptions).~%" (count-rules-in-rule-alist rule-alist) (len assumptions))))
       ;; (- (cw "(Term: ~x0)~%" term))  ;; TODO: Print, but only if small (and thread through a print arg)
       ((mv erp new-term state)
        (prune-term-aux term
                        (fixup-assumptions assumptions print)
                        (get-equalities assumptions)
                        rule-alist
                        interpreted-function-alist
                        monitored-rules
                        call-stp
                        print
                        state))
       ((when erp) (mv erp nil nil state))
       (changep (not (equal term new-term)))
       (- (and (print-level-at-least-tp print)
               (not changep)
               (cw "No change!~%")))
       (- (and (print-level-at-least-tp print)
               (cw "Done pruning term.)~%"))))
    (mv (erp-nil) changep new-term state)))

(defthm pseudo-termp-of-mv-nth-2-of-prune-term
  (implies (and (pseudo-termp term)
                (pseudo-term-listp assumptions)
                (rule-alistp rule-alist)
                (interpreted-function-alistp interpreted-function-alist)
                (symbol-listp monitored-rules)
                (or (booleanp call-stp)
                    (natp call-stp)))
           (pseudo-termp (mv-nth 2 (prune-term term assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state))))
  :hints (("Goal" :in-theory (enable prune-term))))

(defthm w-of-mv-nth-3-of-prune-term
  (equal (w (mv-nth 3 (prune-term term assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)))
         (w state))
  :hints (("Goal" :in-theory (enable prune-term))))
