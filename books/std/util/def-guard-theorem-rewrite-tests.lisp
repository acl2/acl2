; Standard Utilities Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "def-guard-theorem-rewrite")

(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Reject conclusions that rewrite variables or constants, and reflexive
; equalities. Keep valid equalities, negations, and predicates unchanged.

(assert-event
 (b* (((mv erp terms state)
       (guard-theorem-rewrite-filter
        '(((not (consp x)) (equal x 'nil))
          ((not (consp x)) (equal '0 x))
          ((not (consp x)) (not x))
          ((not (consp x)) 't)
          ((not (consp x)) (equal (car x) (car x)))
          ((not (consp x)) (equal (car x) 'nil))
          ((not (consp x)) (not (cdr x)))
          ((not (consp x)) (natp (car x))))
        state)))
   (mv (and (not erp)
            (equal terms
                   '((implies (consp x) (equal (car x) 'nil))
                     (implies (consp x) (not (cdr x)))
                     (implies (consp x) (natp (car x))))))
       state))
 :stobjs-out '(nil state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A mixture of valid obligations and variable equalities from CAR/CDR guards.

(defun grw-nat-id (x)
  (declare (xargs :guard (natp x)))
  x)

(defun grw-inputp (x)
  (declare (xargs :guard t))
  (and (consp x) (natp (car x)) (natp (cdr x))))

(defun grw-flat (x)
  (declare (xargs :guard (grw-inputp x)))
  (cons (grw-nat-id (car x)) (grw-nat-id (cdr x))))

(def-guard-theorem-rewrite grw-flat-rules grw-flat)
(def-guard-theorem-rewrite grw-flat-unsimplified-rules grw-flat :simplify nil)

; Without the generated rules, this cannot be proved in an empty theory.
(must-fail
 (defthm grw-flat-negative-control
   (implies (grw-inputp x)
            (natp (car x)))
   :rule-classes nil
   :hints (("Goal" :in-theory nil :do-not '(preprocess) :do-not-induct t))))

; These proofs enable only the generated rules, with no :USE hint.
(defthm grw-flat-rewrite-only
  (implies (grw-inputp x)
           (and (natp (car x))
                (natp (cdr x))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(grw-flat-rules))))

(defthm grw-flat-unsimplified-rewrite-only
  (implies (grw-inputp x)
           (and (natp (car x))
                (natp (cdr x))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(grw-flat-unsimplified-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Branch conditions become hypotheses of the corresponding rules.

(defun grw-branchp (flag x y)
  (declare (xargs :guard t))
  (if flag (natp x) (natp y)))

(defun grw-branch (flag x y)
  (declare (xargs :guard (grw-branchp flag x y)))
  (if flag (grw-nat-id x) (grw-nat-id y)))

(def-guard-theorem-rewrite grw-branch-rules grw-branch)

(defthm grw-both-branches-rewrite-only
  (and (implies (and (grw-branchp flag x y)
                     flag)
                (natp x))
       (implies (and (grw-branchp flag x y)
                     (not flag))
                (natp y)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(grw-branch-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The LET encloses several obligations,
; represented by a conjunction of disjunctions
; inside the lambda body of the guard theorem.

(defun grw-let (x)
  (declare (xargs :guard (grw-inputp x)))
  (let ((a (car x)) (b (cdr x)))
    (cons (grw-nat-id a) (grw-nat-id b))))

(def-guard-theorem-rewrite grw-let-rules grw-let)

(defthm grw-let-rewrite-only
  (implies (grw-inputp x)
           (and (natp (car x))
                (natp (cdr x))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(grw-let-rules))))

(defun grw-nested-let (flag x)
  (declare (xargs :guard (grw-inputp x)))
  (let ((a (car x)))
    (if flag
        (let ((b (cdr x)))
          (cons (grw-nat-id a) (grw-nat-id b)))
      (grw-nat-id a))))

(def-guard-theorem-rewrite grw-nested-let-rules grw-nested-let)

; Clausification retains the CONSP path condition
; from the earlier CDR guard obligation,
; so it is also a hypothesis of these rewrite rules.
(defthm grw-nested-let-rewrite-only
  (implies (and (grw-inputp x)
                flag
                (consp x))
           (and (natp (car x))
                (natp (cdr x))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(grw-nested-let-rules))))

; An equality of a lambda-bound variable can become a valid rewrite rule
; after substitution. Do not reject it before expanding the lambda.

(defun grw-null-id (x)
  (declare (xargs :guard (equal x nil)))
  x)

(defun grw-singletonp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (equal (cdr x) nil)))

(defun grw-let-equality (x)
  (declare (xargs :guard (grw-singletonp x)))
  (let ((tail (cdr x)))
    (grw-null-id tail)))

(def-guard-theorem-rewrite grw-let-equality-rules grw-let-equality)

(defthm grw-let-equality-rewrite-only
  (implies (grw-singletonp x)
           (equal (cdr x) nil))
  :rule-classes nil
  :hints (("Goal" :in-theory '(grw-let-equality-rules))))

; Multiple values introduce nested lambda expressions and MV-NTH calls.

(defun grw-pair (x)
  (declare (xargs :guard (grw-inputp x)))
  (mv (car x) (cdr x)))

(defun grw-mv-let (x)
  (declare (xargs :guard (grw-inputp x)))
  (mv-let (a b) (grw-pair x)
    (cons (grw-nat-id a) (grw-nat-id b))))

(def-guard-theorem-rewrite grw-mv-let-rules grw-mv-let)

(defthm grw-mv-let-rewrite-only
  (implies (grw-inputp x)
           (and (natp (mv-nth 0 (grw-pair x)))
                (natp (mv-nth 1 (grw-pair x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(grw-mv-let-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The guard theorem of a mutually recursive function covers its whole clique,
; including formal variables that only occur in another member of the clique.

(defun grw-listp (xs)
  (declare (xargs :guard t))
  (true-listp xs))

(mutual-recursion
 (defun grw-even (xs)
   (declare (xargs :guard (grw-listp xs)))
   (if (endp xs) t (grw-odd (cdr xs))))
 (defun grw-odd (ys)
   (declare (xargs :guard (grw-listp ys)))
   (if (endp ys) nil (grw-even (cdr ys)))))

(def-guard-theorem-rewrite grw-clique-rules grw-even)

(defthm grw-recursion-rewrite-only
  (implies (and (grw-listp xs)
                (not (endp xs)))
           (grw-listp (cdr xs)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(grw-clique-rules))))

(assert-event
 (b* (((mv erp term1 state)
       (guard-theorem-rewrite-term 'grw-even :limited state))
      ((when erp) (mv nil state))
      ((mv erp formula1 state)
       (guard-theorem-rewrite-formula term1 state))
      ((when erp) (mv nil state))
      ((mv erp term2 state)
       (guard-theorem-rewrite-term 'grw-odd :limited state))
      ((when erp) (mv nil state))
      ((mv erp formula2 state)
       (guard-theorem-rewrite-formula term2 state)))
   (mv (and (not erp)
            (equal formula1 formula2))
       state))
 :stobjs-out '(nil state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Both an originally trivial guard theorem
; and one whose only conclusion is rejected
; must produce T, with no rewrite rules.

(defun grw-trivial (x)
  (declare (xargs :guard t))
  x)

(def-guard-theorem-rewrite grw-trivial-rules grw-trivial)

(defun grw-nilp (x)
  (declare (xargs :guard t))
  (equal x nil))

(defun grw-only-invalid (x)
  (declare (xargs :guard (grw-nilp x)))
  (grw-null-id x))

(def-guard-theorem-rewrite grw-only-invalid-rules grw-only-invalid)
(def-guard-theorem-rewrite grw-only-invalid-unsimplified-rules
  grw-only-invalid :simplify nil)

(assert-event
 (and (equal (getpropc 'grw-trivial-rules 'theorem nil (w state))
             *t*)
      (equal (getpropc 'grw-only-invalid-rules 'theorem nil (w state))
             *t*)
      (equal (getpropc 'grw-only-invalid-unsimplified-rules
                       'theorem
                       nil
                       (w state))
             *t*)
      (null (getpropc 'grw-trivial-rules 'classes nil (w state)))
      (null (getpropc 'grw-only-invalid-rules 'classes nil (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Another example.

(defun my-natp (x)
  (declare (xargs :guard t))
  (natp x))

(defun my-increment (x)
  (declare (xargs :guard (my-natp x)))
  (+ 1 x))

(def-guard-theorem-rewrite my-increment-guards my-increment)

(defthm my-increment-argument-numberp
  (implies (my-natp x) (acl2-numberp x))
  :hints (("Goal" :in-theory '(my-increment-guards))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Subsumption/replacement combines the identical obligations on both branches.
; Both generation and the :BY proof must do this even when the world's limit
; would prevent it. The resulting rule must not require a branch condition.

(defun grw-common-branches (xs x)
  (declare (xargs :guard (my-natp x)))
  (if (consp xs)
      (grw-nat-id x)
    (cons (grw-nat-id x) nil)))

(encapsulate
  ()
  (set-case-split-limitations '(0 7))

  (def-guard-theorem-rewrite grw-common-branches-rules
    grw-common-branches :simplify nil)

  (defthm grw-common-branches-rewrite-only
    (implies (my-natp x)
             (natp x))
    :rule-classes nil
    :hints (("Goal" :in-theory '(grw-common-branches-rules)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Repeated guard predicates make failed subsumption matches expensive.
; Distinct variable tags prevent the expensive variable permutations in :BY.

(defun grw-many-obligations (a b c d e f g h i j)
  (declare (xargs :guard (and (my-natp a)
                              (my-natp b)
                              (my-natp c)
                              (my-natp d)
                              (my-natp e)
                              (my-natp f)
                              (my-natp g)
                              (my-natp h)
                              (my-natp i)
                              (my-natp j)))
           (ignore a b c d e f g h i j))
  (list (grw-nat-id 1)
        (grw-nat-id 2)
        (grw-nat-id 3)
        (grw-nat-id 4)
        (grw-nat-id 5)
        (grw-nat-id 6)
        (grw-nat-id 7)
        (grw-nat-id 8)
        (grw-nat-id 9)
        (grw-nat-id 10)))

(def-guard-theorem-rewrite grw-many-obligations-rules
  grw-many-obligations :simplify nil)

; The tagging function and auxiliary theorem must remain local.

(assert-event
 (and (not (logical-namep 'grw-many-obligations-rules$tag (w state)))
      (not (logical-namep 'grw-many-obligations-rules$aux (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fresh helper names must avoid existing functions and theorems.

(defun grw-collision-rules$tag (tag x)
  (declare (xargs :guard t))
  (cons tag x))

(defthm grw-collision-rules$aux
  t
  :rule-classes nil)

(def-guard-theorem-rewrite grw-collision-rules grw-flat)

(defthm grw-collision-rewrite-only
  (implies (grw-inputp x)
           (and (natp (car x))
                (natp (cdr x))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(grw-collision-rules))))

(assert-event
 (and (not (logical-namep 'grw-collision-rules$tag$ (w state)))
      (not (logical-namep 'grw-collision-rules$aux$ (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; An unsimplified guard theorem can have obligations but no free variables.

(defun grw-constant ()
  (declare (xargs :guard t))
  (grw-nat-id 1))

(def-guard-theorem-rewrite grw-constant-rules grw-constant :simplify nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Invalid inputs.

(defun grw-unverified (x)
  (declare (xargs :guard (natp x) :verify-guards nil))
  (+ 1 x))

(defun grw-program (x)
  (declare (xargs :mode :program))
  x)

(must-fail (def-guard-theorem-rewrite grw-bad-rules grw-unverified))
(must-fail (def-guard-theorem-rewrite grw-bad-rules grw-program))
(must-fail (def-guard-theorem-rewrite grw-bad-rules grw-undefined))
(must-fail (def-guard-theorem-rewrite grw-bad-rules 17))
(must-fail (def-guard-theorem-rewrite 17 grw-flat))
(must-fail (def-guard-theorem-rewrite grw-bad-rules grw-flat :simplify t))
