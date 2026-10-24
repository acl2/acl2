; Correctness of the ACL2 system functions that drop literals and tests
; contradicted by an equality with a constant
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; When ACL2 builds the clauses for guard proof obligations (in guard-clauses
;; and special-conjectures), it adds literals with ADD-LITERAL-SMART (in
;; history-management.lisp).  Adding a literal (NOT (EQUAL X 'C)) to a clause
;; lets it drop each literal of the clause that equates X with a different
;; constant, such as (EQUAL X 'D): where the new literal is false, X is C, so
;; such a literal is false too.  Similarly, when ACL2 builds the tests of a
;; termination or induction machine, it adds tests with ADD-TEST-SMART (in
;; induct.lisp), which drops each negated test (NOT (EQUAL X 'D)) when the new
;; test is (EQUAL X 'C): where the new test is true, such a test is true too.
;; The functions recognize equalities written with EQUAL, EQ, EQL, and =.
;;
;; This book proves that these functions, and the functions built on them, do
;; what they should, in terms of an evaluator.  The constants are compared
;; syntactically, so the literals and tests must be pseudo-terms: a malformed
;; quoted constant such as (QUOTE 1 2), whose value is 1, differs from '1 but
;; has the same value.

(include-book "clause-sets")
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "system/pseudo-termp-lemmas" :dir :system))

;; These functions are in :program mode in the sources.  We put them in
;; :logic mode here.
(verify-termination term-equated-to-constant)
(verify-termination simplify-clause-for-term-equal-const-1)
(verify-termination simplify-clause-for-term-equal-const)
(verify-termination add-literal-smart)
(verify-termination add-literals)
(verify-termination
  (add-segments-to-clause (declare (xargs :measure (if (null segments) 0 (+ 1 (acl2-count segments)))))))
(verify-termination term-equated-to-constant-in-termlist)
(verify-termination simplify-tests)
(verify-termination add-test-smart)

;; An evaluator that knows the functions that add-literal and the functions
;; in clause-sets.lisp treat specially, and the equality functions recognized
;; by term-equated-to-constant:
(defevaluator+ smart-eval
  if not equal iff hard-error integerp rationalp eq eql =)

;; A set of clauses is true if all of its clauses are.
(defund smart-clause-set-true (cl-set a)
  (if (endp cl-set)
      t
    (and (smart-eval (disjoin (car cl-set)) a)
         (smart-clause-set-true (cdr cl-set) a))))

(defthm smart-clause-set-true-when-not-consp
  (implies (not (consp cl-set))
           (smart-clause-set-true cl-set a))
  :hints (("Goal" :in-theory (enable smart-clause-set-true))))

(defthm smart-clause-set-true-of-cons
  (equal (smart-clause-set-true (cons cl cl-set) a)
         (and (smart-eval (disjoin cl) a)
              (smart-clause-set-true cl-set a)))
  :hints (("Goal" :in-theory (enable smart-clause-set-true))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The results of clause-sets.lisp, for this evaluator

(local (in-theory (disable smart-eval-of-disjoin add-literal disjoin-clauses
                           conjoin-clause-to-clause-set)))

(defthm add-literal-correct-for-smart-eval
  (implies (pseudo-termp lit)
           (iff (smart-eval (disjoin (add-literal lit cl at-end-flg)) a)
                (or (smart-eval lit a)
                    (smart-eval (disjoin cl) a))))
  :hints (("Goal" :in-theory (e/d (smart-eval-of-fncall-args)
                                  (smart-eval-of-fncall-args-back))
           :use (:functional-instance add-literal-correct
                                      (clause-set-eval smart-eval)
                                      (clause-set-eval-list smart-eval-list)))))

(defthm disjoin-clauses-correct-for-smart-eval
  (implies (pseudo-term-listp cl2)
           (iff (smart-eval (disjoin (disjoin-clauses cl1 cl2)) a)
                (or (smart-eval (disjoin cl1) a)
                    (smart-eval (disjoin cl2) a))))
  :hints (("Goal" :in-theory (e/d (smart-eval-of-fncall-args)
                                  (smart-eval-of-fncall-args-back))
           :use (:functional-instance disjoin-clauses-correct
                                      (clause-set-eval smart-eval)
                                      (clause-set-eval-list smart-eval-list)))))

(defthm conjoin-clause-to-clause-set-correct-for-smart-eval
  (iff (smart-clause-set-true (conjoin-clause-to-clause-set cl cl-set) a)
       (and (smart-eval (disjoin cl) a)
            (smart-clause-set-true cl-set a)))
  :hints (("Goal" :in-theory (e/d (smart-eval-of-fncall-args smart-clause-set-true)
                                  (smart-eval-of-fncall-args-back))
           :use (:functional-instance conjoin-clause-to-clause-set-correct
                                      (clause-set-eval smart-eval)
                                      (clause-set-eval-list smart-eval-list)
                                      (clause-set-true smart-clause-set-true)))))

(local (in-theory (enable smart-eval-of-disjoin)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; TERM-EQUATED-TO-CONSTANT

;; If term-equated-to-constant finds a term equated to a constant, the
;; constant is a quoted constant, and the equality holds exactly when the term
;; has the value of the constant.
(defthm quotep-of-mv-nth-1-of-term-equated-to-constant
  (implies (mv-nth 0 (term-equated-to-constant term))
           (quotep (mv-nth 1 (term-equated-to-constant term))))
  :hints (("Goal" :in-theory (enable term-equated-to-constant))))

(defthm smart-eval-when-term-equated-to-constant
  (implies (mv-nth 0 (term-equated-to-constant term))
           (equal (smart-eval term a)
                  (equal (smart-eval (mv-nth 0 (term-equated-to-constant term)) a)
                         (smart-eval (mv-nth 1 (term-equated-to-constant term)) a))))
  :hints (("Goal" :in-theory (enable term-equated-to-constant)
           :cases ((equal (car term) 'equal)
                   (equal (car term) 'eq)
                   (equal (car term) 'eql)
                   (equal (car term) '=)))))

(defthm pseudo-termp-of-mv-nth-0-of-term-equated-to-constant
  (implies (pseudo-termp term)
           (pseudo-termp (mv-nth 0 (term-equated-to-constant term))))
  :hints (("Goal" :in-theory (enable term-equated-to-constant))))

(defthm pseudo-termp-of-mv-nth-1-of-term-equated-to-constant
  (implies (pseudo-termp term)
           (pseudo-termp (mv-nth 1 (term-equated-to-constant term))))
  :hints (("Goal" :in-theory (enable term-equated-to-constant))))

;; Where VAR has the value of CONST, a literal that equates VAR with a
;; different constant is false.  (CONST and the literal must be pseudo-terms,
;; so that different quoted constants have different values.)
(defthm not-smart-eval-when-term-equated-to-other-constant
  (implies (and (mv-nth 0 (term-equated-to-constant lit))
                (equal var (mv-nth 0 (term-equated-to-constant lit)))
                (not (equal const (mv-nth 1 (term-equated-to-constant lit))))
                (equal (smart-eval var a) (smart-eval const a))
                (quotep const)
                (pseudo-termp const)
                (pseudo-termp lit))
           (not (smart-eval lit a)))
  :hints (("Goal" :in-theory (enable term-equated-to-constant)
           :cases ((equal (car lit) 'equal)
                   (equal (car lit) 'eq)
                   (equal (car lit) 'eql)
                   (equal (car lit) '=)))))

(local (in-theory (disable term-equated-to-constant)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; SIMPLIFY-CLAUSE-FOR-TERM-EQUAL-CONST and ADD-LITERAL-SMART

;; A literal that simplify-clause-for-term-equal-const drops: one that
;; equates VAR with a constant other than CONST.
(defund equates-to-other-constantp (var const lit)
  (mv-let (var2 const2)
    (term-equated-to-constant lit)
    (and (equal var var2)
         (not (equal const const2)))))

;; If simplify-clause-for-term-equal-const-1 says it did not change a
;; (non-empty) clause, it returns the clause itself, and if it says it did, it
;; returns a shorter clause.  So its first result says whether it dropped any
;; literals.
(defthm mv-nth-1-of-simplify-clause-for-term-equal-const-1-when-not-changedp
  (implies (not (mv-nth 0 (simplify-clause-for-term-equal-const-1 var const cl)))
           (equal (mv-nth 1 (simplify-clause-for-term-equal-const-1 var const cl))
                  (if (consp cl) cl nil)))
  :hints (("Goal" :in-theory (enable simplify-clause-for-term-equal-const-1))))

(local
 (defthm len-of-mv-nth-1-of-simplify-clause-for-term-equal-const-1-linear
   (<= (len (mv-nth 1 (simplify-clause-for-term-equal-const-1 var const cl)))
       (len cl))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable simplify-clause-for-term-equal-const-1)))))

(local
 (defthm len-of-mv-nth-1-of-simplify-clause-for-term-equal-const-1-when-changedp
   (implies (mv-nth 0 (simplify-clause-for-term-equal-const-1 var const cl))
            (< (len (mv-nth 1 (simplify-clause-for-term-equal-const-1 var const cl)))
               (len cl)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable simplify-clause-for-term-equal-const-1)))))

(defthm booleanp-of-car-of-simplify-clause-for-term-equal-const-1
  (booleanp (car (simplify-clause-for-term-equal-const-1 var const cl)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable simplify-clause-for-term-equal-const-1))))

(local
 (defthm simplify-clause-for-term-equal-const-1-when-not-consp
   (implies (not (consp cl))
            (equal (simplify-clause-for-term-equal-const-1 var const cl)
                   (mv nil nil)))
   :hints (("Goal" :in-theory (enable simplify-clause-for-term-equal-const-1)))))

(defthm simplify-clause-for-term-equal-const-1-changedp
  (implies (true-listp cl)
           (equal (mv-nth 0 (simplify-clause-for-term-equal-const-1 var const cl))
                  (not (equal (mv-nth 1 (simplify-clause-for-term-equal-const-1 var const cl))
                              cl))))
  :hints (("Goal" :cases ((consp cl))
           :use (len-of-mv-nth-1-of-simplify-clause-for-term-equal-const-1-when-changedp
                 mv-nth-1-of-simplify-clause-for-term-equal-const-1-when-not-changedp)
           :in-theory (disable len-of-mv-nth-1-of-simplify-clause-for-term-equal-const-1-when-changedp
                               mv-nth-1-of-simplify-clause-for-term-equal-const-1-when-not-changedp
                               simplify-clause-for-term-equal-const-1))))

;; Simplify-clause-for-term-equal-const drops exactly the literals that
;; equate VAR with a constant other than CONST.
(defthm member-equal-of-simplify-clause-for-term-equal-const-1
  (iff (member-equal x (mv-nth 1 (simplify-clause-for-term-equal-const-1 var const cl)))
       (and (member-equal x cl)
            (not (equates-to-other-constantp var const x))))
  :hints (("Goal" :in-theory (e/d (simplify-clause-for-term-equal-const-1
                                   equates-to-other-constantp)
                                  (simplify-clause-for-term-equal-const-1-changedp)))))

(defthm member-equal-of-simplify-clause-for-term-equal-const
  (iff (member-equal x (simplify-clause-for-term-equal-const var const cl))
       (and (member-equal x cl)
            (not (equates-to-other-constantp var const x))))
  :hints (("Goal" :in-theory (enable simplify-clause-for-term-equal-const))))

;; So the result is a subset of the clause.
(defthm subsetp-equal-of-simplify-clause-for-term-equal-const
  (subsetp-equal (simplify-clause-for-term-equal-const var const cl) cl))

;; Where VAR has the value of CONST, the literals that
;; simplify-clause-for-term-equal-const drops are false, so the clause it
;; returns is true exactly when the clause is.
(defthm all-eval-to-false-with-smart-eval-of-mv-nth-1-of-simplify-clause-for-term-equal-const-1
  (implies (and var
                (equal (smart-eval var a) (smart-eval const a))
                (quotep const)
                (pseudo-termp const)
                (pseudo-term-listp cl))
           (equal (all-eval-to-false-with-smart-eval
                   (mv-nth 1 (simplify-clause-for-term-equal-const-1 var const cl))
                   a)
                  (all-eval-to-false-with-smart-eval cl a)))
  :hints (("Goal" :in-theory (e/d (simplify-clause-for-term-equal-const-1)
                                  (simplify-clause-for-term-equal-const-1-changedp)))))

(defthm simplify-clause-for-term-equal-const-correct
  (implies (and var
                (equal (smart-eval var a) (smart-eval const a))
                (quotep const)
                (pseudo-termp const)
                (pseudo-term-listp cl))
           (iff (smart-eval (disjoin (simplify-clause-for-term-equal-const var const cl)) a)
                (smart-eval (disjoin cl) a)))
  :hints (("Goal" :in-theory (enable simplify-clause-for-term-equal-const))))

(local (in-theory (disable simplify-clause-for-term-equal-const)))

;; Adding a literal to a clause with add-literal-smart makes the disjunction
;; of the literal and the clause.
(defthm add-literal-smart-correct
  (implies (and (pseudo-termp lit)
                (pseudo-term-listp cl))
           (iff (smart-eval (disjoin (add-literal-smart lit cl at-end-flg)) a)
                (or (smart-eval lit a)
                    (smart-eval (disjoin cl) a))))
  :hints (("Goal" :in-theory (e/d (add-literal-smart)
                                  (smart-eval-of-disjoin add-literal
                                   smart-eval-when-term-equated-to-constant))
           :use (:instance smart-eval-when-term-equated-to-constant (term (cadr lit))))))

(local (in-theory (disable add-literal-smart)))

;; ADD-LITERALS adds each literal of CL1 to CL2.
(defthm add-literals-correct
  (implies (pseudo-term-listp cl1)
           (iff (smart-eval (disjoin (add-literals cl1 cl2)) a)
                (or (smart-eval (disjoin cl1) a)
                    (smart-eval (disjoin cl2) a))))
  :hints (("Goal" :in-theory (e/d (add-literals) (smart-eval-of-disjoin))
           :induct (add-literals cl1 cl2))))

;; ADD-SEGMENTS-TO-CLAUSE disjoins the clause to each segment, making the
;; disjunction of the clause and the conjunction of the segments.  It tests
;; for the end of SEGMENTS with NULL, so SEGMENTS must be a true list.
(defthm add-segments-to-clause-correct
  (implies (pseudo-term-list-listp segments)
           (iff (smart-clause-set-true (add-segments-to-clause clause segments) a)
                (or (smart-eval (disjoin clause) a)
                    (smart-clause-set-true segments a))))
  :hints (("Goal" :in-theory (e/d (add-segments-to-clause) (disjoin-clauses smart-eval-of-disjoin)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; SIMPLIFY-TESTS and ADD-TEST-SMART (from induct.lisp)

;; A test that simplify-tests drops: the negation of a literal that equates
;; VAR with a constant other than CONST.
(defund negated-equation-with-other-constantp (var const test)
  (and (ffn-symb-p test 'not)
       (equates-to-other-constantp var const (fargn test 1))))

(defthm mv-nth-1-of-simplify-tests-when-not-changedp
  (implies (not (mv-nth 0 (simplify-tests var const tests)))
           (equal (mv-nth 1 (simplify-tests var const tests))
                  (if (consp tests) tests nil)))
  :hints (("Goal" :in-theory (enable simplify-tests))))

(local
 (defthm len-of-mv-nth-1-of-simplify-tests-linear
   (<= (len (mv-nth 1 (simplify-tests var const tests)))
       (len tests))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable simplify-tests)))))

(local
 (defthm len-of-mv-nth-1-of-simplify-tests-when-changedp
   (implies (mv-nth 0 (simplify-tests var const tests))
            (< (len (mv-nth 1 (simplify-tests var const tests)))
               (len tests)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable simplify-tests)))))

(defthm booleanp-of-car-of-simplify-tests
  (booleanp (car (simplify-tests var const tests)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable simplify-tests))))

(local
 (defthm simplify-tests-when-not-consp
   (implies (not (consp tests))
            (equal (simplify-tests var const tests)
                   (mv nil nil)))
   :hints (("Goal" :in-theory (enable simplify-tests)))))

;; The first result of simplify-tests says whether it dropped any tests.
(defthm simplify-tests-changedp
  (implies (true-listp tests)
           (equal (mv-nth 0 (simplify-tests var const tests))
                  (not (equal (mv-nth 1 (simplify-tests var const tests))
                              tests))))
  :hints (("Goal" :cases ((consp tests))
           :use (len-of-mv-nth-1-of-simplify-tests-when-changedp
                 mv-nth-1-of-simplify-tests-when-not-changedp)
           :in-theory (disable len-of-mv-nth-1-of-simplify-tests-when-changedp
                               mv-nth-1-of-simplify-tests-when-not-changedp
                               simplify-tests))))

;; Simplify-tests drops exactly the tests that negate a literal that equates
;; VAR with a constant other than CONST.
(defthm member-equal-of-simplify-tests
  (iff (member-equal x (mv-nth 1 (simplify-tests var const tests)))
       (and (member-equal x tests)
            (not (negated-equation-with-other-constantp var const x))))
  :hints (("Goal" :in-theory (e/d (simplify-tests
                                   negated-equation-with-other-constantp
                                   equates-to-other-constantp)
                                  (simplify-tests-changedp)))))

(defthm subsetp-equal-of-simplify-tests
  (subsetp-equal (mv-nth 1 (simplify-tests var const tests)) tests))

;; Where VAR has the value of CONST, the tests that simplify-tests drops are
;; true, so the tests it returns are all true exactly when the tests are.
(defthm all-eval-to-true-with-smart-eval-of-mv-nth-1-of-simplify-tests
  (implies (and var
                (equal (smart-eval var a) (smart-eval const a))
                (quotep const)
                (pseudo-termp const)
                (pseudo-term-listp tests))
           (equal (all-eval-to-true-with-smart-eval
                   (mv-nth 1 (simplify-tests var const tests))
                   a)
                  (all-eval-to-true-with-smart-eval tests a)))
  :hints (("Goal" :in-theory (e/d (simplify-tests)
                                  (simplify-tests-changedp)))))

(defthm simplify-tests-correct
  (implies (and var
                (equal (smart-eval var a) (smart-eval const a))
                (quotep const)
                (pseudo-termp const)
                (pseudo-term-listp tests))
           (iff (smart-eval (conjoin (mv-nth 1 (simplify-tests var const tests))) a)
                (smart-eval (conjoin tests) a))))

;; Adding a test to a list of tests with add-test-smart makes the conjunction
;; of the test and the tests.
(defthm add-test-smart-correct
  (implies (and (pseudo-termp test)
                (pseudo-term-listp tests))
           (iff (smart-eval (conjoin (add-test-smart test tests)) a)
                (and (smart-eval test a)
                     (smart-eval (conjoin tests) a))))
  :hints (("Goal" :in-theory (e/d (add-test-smart)
                                  (smart-eval-when-term-equated-to-constant
                                   simplify-tests-changedp))
           :use (:instance smart-eval-when-term-equated-to-constant (term test)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; TERM-EQUATED-TO-CONSTANT-IN-TERMLIST, and its use with SIMPLIFY-TESTS

;; The first member of LST that equates a term with a constant.
(defund first-equated-term (lst)
  (if (endp lst)
      nil
    (mv-let (term const)
      (term-equated-to-constant (car lst))
      (declare (ignore const))
      (if term
          (car lst)
        (first-equated-term (cdr lst))))))

;; Term-equated-to-constant-in-termlist finds the term and constant equated by
;; the first member of LST that equates a term with a constant.
(defthm term-equated-to-constant-in-termlist-becomes-term-equated-to-constant
  (equal (term-equated-to-constant-in-termlist lst)
         (term-equated-to-constant (first-equated-term lst)))
  :hints (("Goal" :in-theory (enable term-equated-to-constant-in-termlist
                                     first-equated-term
                                     term-equated-to-constant))))

(defthm member-equal-of-first-equated-term
  (implies (mv-nth 0 (term-equated-to-constant (first-equated-term lst)))
           (member-equal (first-equated-term lst) lst))
  :hints (("Goal" :in-theory (enable first-equated-term term-equated-to-constant))))

(local
 (defthm not-equal-of-car-when-term-equated-to-constant
   (implies (mv-nth 0 (term-equated-to-constant term))
            (not (equal (car term) 'not)))
   :hints (("Goal" :in-theory (enable term-equated-to-constant)))))

(defthm pseudo-termp-of-first-equated-term
  (implies (pseudo-term-listp lst)
           (pseudo-termp (first-equated-term lst)))
  :hints (("Goal" :in-theory (enable first-equated-term))))

;; Simplify-tests never drops the test found, because it drops only negated
;; tests.
(defthm member-equal-of-first-equated-term-and-simplify-tests
  (implies (mv-nth 0 (term-equated-to-constant (first-equated-term tests)))
           (member-equal (first-equated-term tests)
                         (mv-nth 1 (simplify-tests var const tests))))
  :hints (("Goal" :in-theory (enable negated-equation-with-other-constantp))))

;; So, where the tests are all true, the term found by
;; term-equated-to-constant-in-termlist has the value of the constant.
(defthm term-equated-to-constant-in-termlist-correct
  (implies (and (all-eval-to-true-with-smart-eval lst a)
                (mv-nth 0 (term-equated-to-constant-in-termlist lst)))
           (equal (smart-eval (mv-nth 0 (term-equated-to-constant-in-termlist lst)) a)
                  (smart-eval (mv-nth 1 (term-equated-to-constant-in-termlist lst)) a)))
  :hints (("Goal" :use (:instance smart-eval-when-term-equated-to-constant
                                  (term (first-equated-term lst)))
           :in-theory (disable smart-eval-when-term-equated-to-constant))))

;; SIMPLIFY-TESTS-AND-CALLS (in induct.lisp) simplifies the tests of an
;; induction case by finding a test that equates a term with a constant and
;; dropping the tests that this test makes true.  That step leaves the
;; conjunction of the tests unchanged.  (The test that equates the term with
;; the constant is not dropped, so where it is false, the simplified tests are
;; false too.)
(defthm simplify-tests-of-term-equated-to-constant-in-termlist-correct
  (implies (pseudo-term-listp tests)
           (iff (smart-eval
                 (conjoin (mv-let (var const)
                            (term-equated-to-constant-in-termlist tests)
                            (if var
                                (mv-nth 1 (simplify-tests var const tests))
                              tests)))
                 a)
                (smart-eval (conjoin tests) a)))
  :hints (("Goal"
           :cases ((mv-nth 0 (term-equated-to-constant (first-equated-term tests))))
           :in-theory (disable smart-eval-when-term-equated-to-constant)
           :use ((:instance smart-eval-when-term-equated-to-constant
                            (term (first-equated-term tests)))
                 (:instance smart-eval-when-all-eval-to-true-with-smart-eval-and-member-equal
                            (term (first-equated-term tests))
                            (terms (mv-nth 1 (simplify-tests
                                              (mv-nth 0 (term-equated-to-constant (first-equated-term tests)))
                                              (mv-nth 1 (term-equated-to-constant (first-equated-term tests)))
                                              tests))))
                 (:instance smart-eval-when-all-eval-to-true-with-smart-eval-and-member-equal
                            (term (first-equated-term tests))
                            (terms tests))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The literals and tests must be pseudo-terms

;; Counterexamples showing that the clause and the tests must be pseudo-terms
;; (since a malformed constant such as (QUOTE 1 2) differs from '1 but has the
;; same value) are in add-literal-smart-tests.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; What the functions return, and well-formedness

(local (include-book "kestrel/terms-light/termp" :dir :system))

;; ADD-LITERAL-SMART returns the true clause or a subset of the clause with
;; the literal added.
(defthm add-literal-smart-cases
  (let ((result (add-literal-smart lit cl at-end-flg)))
    (or (equal result *true-clause*)
        (subsetp-equal result (cons lit cl))))
  :hints (("Goal" :in-theory (enable add-literal-smart)
           :use ((:instance add-literal-cases)
                 (:instance add-literal-cases
                            (cl (simplify-clause-for-term-equal-const
                                 (mv-nth 0 (term-equated-to-constant (cadr lit)))
                                 (mv-nth 1 (term-equated-to-constant (cadr lit)))
                                 cl))))))
  :rule-classes nil)

;; ADD-TEST-SMART returns the tests, minus some of them, with the test added
;; at the front.
(defthm add-test-smart-cases
  (let ((result (add-test-smart test tests)))
    (and (consp result)
         (equal (car result) test)
         (subsetp-equal (cdr result) tests)))
  :hints (("Goal" :in-theory (enable add-test-smart)))
  :rule-classes nil)

(defthm pseudo-term-listp-of-mv-nth-1-of-simplify-clause-for-term-equal-const-1
  (implies (pseudo-term-listp cl)
           (pseudo-term-listp (mv-nth 1 (simplify-clause-for-term-equal-const-1 var const cl))))
  :hints (("Goal" :in-theory (e/d (simplify-clause-for-term-equal-const-1)
                                  (simplify-clause-for-term-equal-const-1-changedp)))))

(defthm term-listp-of-mv-nth-1-of-simplify-clause-for-term-equal-const-1
  (implies (term-listp cl w)
           (term-listp (mv-nth 1 (simplify-clause-for-term-equal-const-1 var const cl)) w))
  :hints (("Goal" :in-theory (e/d (simplify-clause-for-term-equal-const-1)
                                  (simplify-clause-for-term-equal-const-1-changedp)))))

(defthm pseudo-term-listp-of-add-literal-smart
  (implies (and (pseudo-termp lit)
                (pseudo-term-listp cl))
           (pseudo-term-listp (add-literal-smart lit cl at-end-flg)))
  :hints (("Goal" :in-theory (enable add-literal-smart simplify-clause-for-term-equal-const))))

(defthm term-listp-of-add-literal-smart
  (implies (and (termp lit w)
                (term-listp cl w))
           (term-listp (add-literal-smart lit cl at-end-flg) w))
  :hints (("Goal" :in-theory (enable add-literal-smart simplify-clause-for-term-equal-const))))

(defthm pseudo-term-listp-of-add-literals
  (implies (and (pseudo-term-listp cl1)
                (pseudo-term-listp cl2))
           (pseudo-term-listp (add-literals cl1 cl2)))
  :hints (("Goal" :in-theory (enable add-literals))))

(defthm term-listp-of-add-literals
  (implies (and (term-listp cl1 w)
                (term-listp cl2 w))
           (term-listp (add-literals cl1 cl2) w))
  :hints (("Goal" :in-theory (enable add-literals))))

(defthm pseudo-term-list-listp-of-add-segments-to-clause
  (implies (and (pseudo-term-listp clause)
                (pseudo-term-list-listp segments))
           (pseudo-term-list-listp (add-segments-to-clause clause segments)))
  :hints (("Goal" :in-theory (enable add-segments-to-clause))))

(defthm term-list-listp-of-add-segments-to-clause
  (implies (and (term-listp clause w)
                (term-list-listp segments w))
           (term-list-listp (add-segments-to-clause clause segments) w))
  :hints (("Goal" :in-theory (enable add-segments-to-clause))))

(defthm pseudo-term-listp-of-mv-nth-1-of-simplify-tests
  (implies (pseudo-term-listp tests)
           (pseudo-term-listp (mv-nth 1 (simplify-tests var const tests))))
  :hints (("Goal" :in-theory (e/d (simplify-tests) (simplify-tests-changedp)))))

(defthm term-listp-of-mv-nth-1-of-simplify-tests
  (implies (term-listp tests w)
           (term-listp (mv-nth 1 (simplify-tests var const tests)) w))
  :hints (("Goal" :in-theory (e/d (simplify-tests) (simplify-tests-changedp)))))

(defthm pseudo-term-listp-of-add-test-smart
  (implies (and (pseudo-termp test)
                (pseudo-term-listp tests))
           (pseudo-term-listp (add-test-smart test tests)))
  :hints (("Goal" :in-theory (enable add-test-smart))))

(defthm term-listp-of-add-test-smart
  (implies (and (termp test w)
                (term-listp tests w))
           (term-listp (add-test-smart test tests) w))
  :hints (("Goal" :in-theory (enable add-test-smart))))
