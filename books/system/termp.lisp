; Verify Termination and Guards of Termp
; Copyright (C) 2015, ForrestHunt, Inc.
; Written by J Strother Moore, May, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "legal-variablep")

(verify-termination plist-worldp-with-formals)

(defthm plist-worldp-with-formals-forward-to-plist-worldp
  (implies (plist-worldp-with-formals wrld)
           (plist-worldp wrld))
  :rule-classes :forward-chaining)

(verify-termination arity
  (declare (xargs :guard (and (or (and (consp fn)
                                       (consp (cdr fn))
                                       (true-listp (cadr fn)))
                                  (symbolp fn))
                              (plist-worldp-with-formals w)))))

; Before we can verify the guards of termp we must prove that termp implies
; pseudo-termp.  The reason is that termp calls all-vars1 on the body of lambda
; expressions, after checking that the body is recursively a termp.  But
; all-vars1 has a pseudo-termp guard.  So we first introduce termp, then prove
; that it implies pseudo-termp, and then verify its guards.

(verify-termination
 (termp
  (declare (xargs :guard (plist-worldp-with-formals w)
                  :guard-hints (("Goal" :in-theory (disable member-eq)))
                  :verify-guards nil)))
 (term-listp
  (declare (xargs :guard (plist-worldp-with-formals w)
                  :guard-hints (("Goal" :in-theory (disable member-eq)))
                  :verify-guards nil))))

; The function LEGAL-VARIABLE-OR-CONSTANT-NAMEP uses two very large constants
; that can cause stack overflow if member-eq is allowed to expand on them.  One
; could disable member-eq, but that would endanger many simple proofs having
; nothing to do with syntax checking.  So we will disable
; LEGAL-VARIABLE-OR-CONSTANT-NAMEP -- a strategy that also eliminates a lot of
; case splits in proofs about syntax.  But we sometimes need the fact that
; legal variables and constants are symbols, so we prove that first, as a
; :rewrite rule phrased in the contrapositive so that it fires only if
; legal-variable-or-constant-namep is in the problem.

(defthm legal-variable-or-constant-namep-implies-symbolp
  (implies (not (symbolp x))
           (not (legal-variable-or-constant-namep x)))
  :hints (("Goal" :in-theory (e/d (legal-variable-or-constant-namep)
                                  (member-eq)))))

(in-theory (disable legal-variable-or-constant-namep))

; Below we prove that termp implies pseudo-termp (and term-listp implies
; pseudo-term-listp).  The development is ugly because we introduce a flagged
; version of pseudo-termp and use it as a stepping stone.  But we don't
; configure things to reason always about the flagged version because we just
; export the two main theorems about the mutually recursive functions.  We need
; a few lemmas about subroutines too.

(encapsulate
 nil
 (local
  (defun pseudo-termp/pseudo-term-listp (flg x)
    (if (eq flg 'pseudo-termp)
        (cond ((atom x) (symbolp x))
              ((eq (car x) 'quote)
               (and (consp (cdr x))
                    (null (cdr (cdr x)))))
              ((not (true-listp x)) nil)
              ((not (pseudo-termp/pseudo-term-listp 'pseudo-term-listp (cdr x)))
               nil)
              (t (or (symbolp (car x))
                     (and (true-listp (car x))
                          (equal (length (car x)) 3)
                          (eq (car (car x)) 'lambda)
                          (symbol-listp (cadr (car x)))
                          (pseudo-termp/pseudo-term-listp 'pseudo-termp
                                                          (caddr (car x)))
                          (equal (length (cadr (car x)))
                                 (length (cdr x)))))))
        (cond ((atom x) (equal x nil))
              (t (and (pseudo-termp/pseudo-term-listp 'pseudo-termp (car x))
                      (pseudo-termp/pseudo-term-listp 'pseudo-term-listp
                                                      (cdr x))))))))

; Two simple lemmas...
 (local
  (defthm term-listp-implies-true-listp
    (implies (term-listp x w)
             (true-listp x))
    :rule-classes :forward-chaining))

 (local
  (defthm arglistp1-implies-symbol-listp
    (implies (arglistp1 x) (symbol-listp x))
    :hints (("Goal" :in-theory (enable arglistp1)))
    :rule-classes :forward-chaining))

 (local
  (defthm step-1-lemma
    (equal (pseudo-termp/pseudo-term-listp flg x)
           (if (eq flg 'pseudo-termp)
               (pseudo-termp x)
               (pseudo-term-listp x)))))
 (local
  (defthm step-2-lemma
    (implies (if (eq flg 'pseudo-termp) (termp x w) (term-listp x w))
             (pseudo-termp/pseudo-term-listp flg x))
    :hints (("Goal" :in-theory (enable arglistp))
            ("Subgoal *1/4''"
             :expand (termp x w)))))

 (defthm termp-implies-pseudo-termp
   (implies (termp x w)
            (pseudo-termp x))
   :hints (("Goal"
            :use ((:instance step-2-lemma (flg 'pseudo-termp)))))
   :rule-classes (:rewrite :forward-chaining))

 (defthm term-listp-implies-pseudo-term-listp
   (implies (term-listp x w)
            (pseudo-term-listp x))
   :hints (("Goal"
            :use ((:instance step-2-lemma (flg 'pseudo-term-listp)))))
   :rule-classes (:rewrite :forward-chaining)))

; To verify the guards of termp we need to know that (all-vars1 body nil) is a
; true-listp, to establish the guard of length which is used in the checking of
; lambda expressions.  To prove that we need the flagged version of all-vars1,
; which is introduced in a local ENCAPSULATE in axioms.lisp as
; ALL-VARS1/ALL-VARS1-LST.  In fact that same encapsulate proves that the
; output of all-vars1 is a symbol-list which implies true-listp.  So we just
; include that local encapsulate (again) below.

(local
 (encapsulate
  ()

; We wish to prove symbol-listp-all-vars1, below, so that we can verify the
; guards on all-vars1.  But it is in a mutually recursive clique.  Our strategy
; is simple: (1) define the flagged version of the clique, (2) prove that it is
; equal to the given pair of official functions, (3) prove that it has the
; desired property and (4) then obtain the desired property of the official
; function by instantiation of the theorem proved in step 3, using the theorem
; proved in step 2 to rewrite the flagged flagged calls in that instance to the
; official ones.

; Note: It would probably be better to make all-vars1/all-vars1-lst local,
; since it's really not of any interest outside the guard verification of
; all-vars1.  However, since we are passing through this file more than once,
; that does not seem to be an option.

  (local
   (defun all-vars1/all-vars1-lst (flg lst ans)
     (if (eq flg 'all-vars1)
         (cond ((variablep lst) (add-to-set-eq lst ans))
               ((fquotep lst) ans)
               (t (all-vars1/all-vars1-lst 'all-vars-lst1 (cdr lst) ans)))
         (cond ((endp lst) ans)
               (t (all-vars1/all-vars1-lst
                   'all-vars-lst1 (cdr lst)
                   (all-vars1/all-vars1-lst 'all-vars1 (car lst) ans)))))))

  (local
   (defthm step-1-lemma
     (equal (all-vars1/all-vars1-lst flg lst ans)
            (if (equal flg 'all-vars1)
                (all-vars1 lst ans)
              (all-vars1-lst lst ans)))))

  (local
   (defthm step-2-lemma
     (implies (and (symbol-listp ans)
                   (if (equal flg 'all-vars1)
                       (pseudo-termp lst)
                       (pseudo-term-listp lst)))
              (symbol-listp (all-vars1/all-vars1-lst flg lst ans)))))

  (defthm symbol-listp-all-vars1
    (implies (and (symbol-listp ans)
                  (pseudo-termp lst))
             (symbol-listp (all-vars1 lst ans)))
    :hints (("Goal" :use (:instance step-2-lemma (flg 'all-vars1)))))))

; Essay On Why we Sometimes Must Reclassify :Forward-Chaining and :Rewrite
; Rules

; We sometimes have :forward-chaining rules that must be reclassified as
; :rewrite rules.  This problem arises often enough that I wanted to
; understand it.  So here I describe what is going on, in very generic
; terms.  Let a, b, and c be three successively weaker predicates on x,
; e.g., (keyword-listp x), (symbol-listp x), and (true-listp x).  So we have
; (a --> b) and (b --> c).  Suppose that you want to prove (a --> c).  But
; suppose (a --> b) is stored (only) as a :rewrite rule while (b --> c) is
; stored (only) as a :forward-chaining rule.  Then when the prover is trying
; to prove (a --> c), nothing suggests the consideration of b: we don't
; forward chain from a to b because (a --> b) is a :rewrite rule, and we
; don't backchain from c to b because (b --> c) is a :forward-chaining rule.
; To make the proof work, both have to be either :forward-chaining rules or
; :rewrite rules.  Now the situation is complicated by Tau.  Tau can chain
; together both rules, regardless of which :rule-classes they are.  But Tau
; only fires in preprocessing.  So if the inference that (a --> c) is needed
; outside preprocessing, the Tau proof is not found.  To make it even worse,
; if one of the predicates is not monadic then Tau doesn't treat it as a Tau
; predicate and so Tau doesn't catch these kinds of chains even though
; they're obvious.  For example, (term-listp x w) --> (pseudo-term-listp x)
; --> (true-listp x) but Tau can't prove the first implies the last.

; The following is proved in axioms under the name
; symbol-listp-forward-to-true-listp but stored only as a :forward-chaining
; lemma.  We need it as a :rewrite rule so we prove it again, locally.  It
; is an inefficient :rewrite rule.

(local
 (defthm symbol-listp-implies-true-listp
   (implies (symbol-listp x)
            (true-listp x))))

(local
 (defthm arglistp1-implies-true-listp
   (implies (arglistp1 x)
            (true-listp x))
   :hints (("Goal" :in-theory (enable arglistp1)))))

(verify-guards termp)

(verify-termination term-list-listp)

(verify-termination arities-okp)

(defthm arities-okp-implies-arity
  (implies (and (arities-okp user-table w)
                (assoc fn user-table))
           (equal (arity fn w) (cdr (assoc fn user-table)))))

(defthm arities-okp-implies-logicp
  (implies (and (arities-okp user-table w)
                (assoc fn user-table))
           (logicp fn w)))

(in-theory (disable arity arities-okp))

(verify-termination logic-fnsp) ; and guards
(verify-termination logic-termp) ; and guards
(verify-termination logic-term-listp) ; and guards
(verify-termination logic-fns-list-listp) ; and guards
(verify-termination logic-term-list-listp) ; and guards

