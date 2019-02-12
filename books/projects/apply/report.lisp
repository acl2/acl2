; Copyright (C) 2017, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file contains the events mentioned in the Examples section of the paper
; under development, ``Limited Second Order Functionality in a First Order
; Setting''.

(in-package "ACL2")

(include-book "top")

(defun$ square (x) (* x x))

(defun$ cube (x) (* x (square x)))

(defun$ nats (n)
  (if (zp n)
      nil
      (cons n (nats (- n 1)))))

(defun$ rev (x)
  (if (endp x)
      nil
      (append (rev (cdr x)) (list (car x)))))

(defun$ flatten (x)
  (if (atom x)
      (list x)
      (append (flatten (car x))
              (flatten (cdr x)))))

(defun$ sum (fn lst)
  (cond ((endp lst) 0)
        (t (+ (apply$ fn (list (car lst)))
              (sum fn (cdr lst))))))

(defun$ filter (fn lst)
  (cond ((endp lst) nil)
        ((apply$ fn (list (car lst)))
         (cons (car lst) (filter fn (cdr lst))))
        (t (filter fn (cdr lst)))))

(defun$ foldr (lst fn init)
  (if (endp lst)
      init
      (apply$ fn
              (list (car lst)
                    (foldr (cdr lst) fn init)))))

(defun$ foldt (x fn init)
  (if (atom x)
      (apply$ fn (list x init))
      (apply$ fn (list x (foldt (car x) fn (foldt (cdr x) fn init))))))


(defun$ sum-squares (lst)
  (if (endp lst)
      0
      (+ (square (car lst))
         (sum-squares (cdr lst)))))

(defthm T1
  (implies (warrant square)
           (equal (sum-squares lst)
                  (sum 'square lst))))

(defthm T2
  (equal (sum fn (append a b))
         (+ (sum fn a) (sum fn b))))

(encapsulate nil
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm T3
    (implies (and (warrant square)
                  (natp n))
             (equal (sum 'SQUARE (nats n))
                    (/ (* n (+ n 1) (+ (* 2 n) 1))
                       6)))
    :hints (("Goal" :expand ((:free (x) (HIDE x)))))))

(defun$ sum-squares-of-evens (lst)
  (if (endp lst)
      0
      (if (evenp (car lst))
          (+ (square (car lst))
             (sum-squares-of-evens (cdr lst)))
          (sum-squares-of-evens (cdr lst)))))

(defthm T4
  (implies (warrant square)
           (equal (sum-squares-of-evens lst)
                  (sum 'square (filter 'evenp lst)))))

(defthm T5
  (equal (filter fn (append a b))
         (append (filter fn a) (filter fn b))))

(defthm T6
  (implies (warrant square)
           (equal (foldr lst
                         '(lambda (i a)
                            (if (evenp i)
                                (binary-+ (square i) a) ; <--- Discrepancy
                                a))
                         0)
                  (sum 'square (filter 'evenp lst)))))

(defthm T7
  (equal (foldr x 'cons y)
         (append x y)))

(defthm T8
  (implies (warrant foldr)
           (equal (foldr x
                         '(LAMBDA (X Y)
                                  (FOLDR Y 'CONS (CONS X 'NIL)))
                         nil)
                  (rev x))))

(defthm weird-little-lemma1
  (implies (and (tamep `(,fn X))
                (symbolp y))
           (tamep `(,fn ,y)))
  :hints (("Goal" :expand ((tamep `(,fn X)) (tamep `(,fn ,y))))))

(defthm weird-little-lemma2
  (implies (tamep `(,fn ,y))
           (not (equal fn 'IF))))

(defthm T9
  (implies (ok-fnp fn)
           (equal (foldr lst `(lambda (x y) (binary-+ (,fn x) y)) 0) ; <--- Discrepancy
                  (sum fn lst))))

(defthm T10
  (implies (ok-fnp fn)
           (equal (foldr lst `(lambda (x y) (if (,fn x) (cons x y) y)) nil)
                  (filter fn lst))))

(defthm T11-lemma
  (implies (and (ok-fnp fn)
                (ok-fnp gn)
                (acl2-numberp init))
           (equal (foldr lst `(lambda (x y) (if (,fn x) (binary-+ (,gn x) y) y)) init)
                  (+ init (sum gn (filter fn lst))))))

(defthm T11
  (implies (and (ok-fnp fn)
                (ok-fnp gn))
           (equal (foldr lst `(lambda (x y) (if (,fn x) (binary-+ (,gn x) y) y)) 0)
                  (sum gn (filter fn lst)))))

(defthm T12-lemma
  (equal (foldt x '(lambda (x y)
                     (if (consp x)
                         y
                         (cons x y)))
                z)
         (append (flatten x) z)))

(defthm T12
  (equal (foldt x  '(lambda (x y)
                      (if (consp x)
                          y
                          (cons x y))) nil)
         (flatten x)))

(defun$ russell (fn x)
  (not (apply$ fn (list x x))))

(defthm T13
  (equal (russell 'equal 'equal) nil)
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes nil)

; One might hope we could derive something about (russell 'russell 'russell),
; but nothing interesting can be proved about it.  Suppose we have the warrant
; for russell and consider (russell 'russell 'russell).  By the definitional
; equation for russell, this is equal to

; (not (apply$ 'russell '(russell russell)))

; The definition of apply$ reduces this to

; (not (apply$-userfn 'russell '(russell russell)))

; Only potential next step is to use the warrant.  But that just tells us the
; badge for russell and the fact:

;   (tamep-functionp (car args))
;  --> 
;   (apply$-userfn 'russell args) = (russell (car args) (cadr args))

; So to use the warrant we must prove (tamep-functionp (car '(russell
; russell))) which is (tamep-functionp 'russell) which is NIL.  Thus the
; warrant tells us nothing about this apply$-userfn and we can do no more.

; -----------------------------------------------------------------

; The following definitions and theorems are not explicitly discussed in the
; paper ``Limited Second Order Functionality in a First Order Setting''.  We
; prove that a few other mapping functions are expressible as FOLDR calls.
; These theorems are akin to T9 and T10 where we proved that SUM and FILTER are
; FOLDRs.  The discerning reader may notice however that in T9 and T10 we
; oriented the concluding equalities to suggest that the relevant FOLDR
; expressions could be rewritten to SUM or FILTER calls, whereas below we
; orient the equalities differently, suggesting that, say, COLLECT can be
; rewritten to a FOLDR.  Logically it makes no difference but The discerning
; reader may notice

(defun$ collect (fn lst)
  (cond ((endp lst) nil)
        (t (cons (apply$ fn (list (car lst)))
                 (collect fn (cdr lst))))))

; We'd use FORALL and EXISTS for ALL and XISTS below, but those names are
; already taken in Common Lisp.

(defun$ all (fn lst)
  (cond ((endp lst) t)
        (t (and (apply$ fn (list (car lst)))
                (all fn (cdr lst))))))

(defun$ xists (fn lst)
  (cond ((endp lst) nil)
        ((apply$ fn (list (car lst)))
         t)
        (t (xists fn (cdr lst)))))

(defun$ maxlist (fn lst)
  (cond ((endp lst) nil)
        ((endp (cdr lst)) (apply$ fn (list (car lst))))
        (t (max (apply$ fn (list (car lst)))
                (maxlist fn (cdr lst))))))

(defthm T14
  (implies (force (ok-fnp fn))
           (equal (foldr lst
                         `(LAMBDA (X Y)
                                  (CONS (,fn X) Y))
                         nil)
                  (collect fn lst))))

; T14 is like T9 and T10: it shows how FOLDR can do the job of another mapping
; function, in this case COLLECT.  Logically T14 just says that for any ``ok
; function'' fn, the FOLDR term is equal to the COLLECT term.  Operationally,
; after proving it, ACL2 stores this theorem as rewrite rule: any term matching
; the FOLDR is rewritten to the corresponding instance of the COLLECT term
; provided the (ok-fnp fn) hypothesis can be established.  FORCE, used in the
; hypothesis, is a logical identity function but operationally means: ``if you
; can't immediately establish this hypothesis (or show that it's false),
; proceed as if you'd proved it (i.e., do the rewrite), and when the entire
; proof is finished, work harder at proving (ok-fnp fn).''

; Rules like T9, T10, and T14 suffer operationally because their targets
; involve specific LAMBDA expressions with fixed formals, e.g., X and Y in T14.
; The following variation on T14 shows that we can handle slightly more general
; LAMBDAs:

(defthm T15
  (implies (and (ok-fnp fn)
                (symbolp x)
                (symbolp y)
                (not (eq x y)))
           (equal (foldr lst
                         `(lambda (,x ,y)
                            (cons (,fn ,x) ,y))
                         nil)
                  (collect fn lst)))
  :rule-classes nil)

; We don't store this as a rule but prove it to illustrate the point.  As a
; rewrite rule, this theorem would rewrite any FOLDR whose second argument is a
; quoted LAMBDA expression with any two distinct formals and the body shown.
; (Of course, the third argument of the FOLDR must be NIL.)  Even is not fully
; general since the body could be any term whose evaluation is equivalent to
; the body shown.

; Another point worth making here is that one might wish the theorems to be
; ``reversed,'' so that the stored rules rewrite the specific mapping function,
; e.g., COLLECT, to the more general one, e.g., FOLDR.  Which version of the
; rule is best depends on the user's proof strategy.  The reversed orientation
; would be useful if one developed a powerful set of rewrite rules for FOLDR
; and then reduced all other simple mapping functions to FOLDR terms.

; But this discussion of the operational effect of these theorems is beyond the
; scope of this work.  Right now we're just interested in showing that we can
; prove the key relations between mapping functions.

(defthm T16
  (implies (force (ok-fnp fn))
           (equal (foldr lst
                         `(LAMBDA (X Y)
                                  (IF (,fn X) Y 'NIL))
                         t)
                  (all fn lst))))

(defthm T17
  (implies (force (ok-fnp fn))
           (equal (foldr lst
                         `(LAMBDA (X Y)
                                  (IF (,fn X) 'T Y))
                         NIL)
                  (xists fn lst))))

; Maxlist cannot be expressed as a foldr without some additional hypotheses or
; special cases.  The problem is that maxlist never calls itself recursively on
; the empty list while foldr does.  That means maxlist never compares its
; ``initial value'' (i.e., its value on the empty list) to any of the values
; returned by fn.  But foldr does compare those two.  One can try to avoid that
; by special-casing the singleton list sort of like maxlist does, but in fact
; that idea doesn't work.  (Note the NOT in the conclusion; the theorem below
; provides a counterexample to the claimed equivalence.)

(defthm T18
  (let ((lst '(4 1))
        (fn (cons 'lambda '((x) (binary-* '-5 x)))))

; Note: The cons-expression above is just '(lambda (x) (binary-* '-5 x)).  That
; used to be legal (in ACL2 Version_8.0).  But in order to provide more
; convenient well-formedness checking and translation support, ACL2 now insists
; that quoted lambda expressions occur only in :fn slots.  This is not a :fn
; slot.  So we have to avoid the syntactic appearance of a quoted lambda.

    (implies (force (ok-fnp fn))
             (NOT (equal (maxlist fn lst)
                         (if (endp lst)
                             nil
                             (if (endp (cdr lst))
                                 (apply$ fn (list (car lst)))
                                 (foldr lst
                                        `(LAMBDA (X Y)
                                                 (MAX (,fn X) Y))
                                        nil)))))))
  :hints (("Goal" :expand ((:free (x) (HIDE x)))))
  :rule-classes nil)

; The maxlist above returns -5 but the foldr returns nil (which is bigger than
; all the negatives in ACL2's completion of the < operator).

; So if foldr always compares its value on the empty list to the values of fn
; on elements of its input list, we must have a way to tell whether the value
; being compared is the special one returned for the empty list.  But without
; some kind of restriction on what fn returns, we cannot designate a
; ``special'' value.

; If we posit that fn always returns a number (at least, over the elements in
; lst), then we can tell the difference between the initial value and any call
; of fn, and then we get a reasonable relationship.

(defthm T19 ; a lemma needed for T20
  (implies (and (force (ok-fnp fn))
                (all 'ACL2-NUMBERP (collect fn lst)))
           (iff (maxlist fn lst)
                (consp lst))))

(defthm T20
  (implies (and (force (ok-fnp fn))
                (all 'ACL2-NUMBERP (collect fn lst)))
           (equal (foldr lst `(LAMBDA (X Y)
                                (IF (EQUAL Y 'NIL) 
                                    (,fn X)
                                    (MAX (,fn X) Y)))
                         nil)
                  (maxlist fn lst))))


; T21 shows how to move a multiplicative constant out of sum's LAMBDA, i.e., so
; that (modulo our unsupported use of macros in this illustration), (sum
; '(LAMBDA (X) (* 2 ...b...)) lst) becomes (* 2 (sum '(LAMBDA (X) ...b...))).

(defthm T21
  (implies (tamep body)
           (equal (sum (lamb (list v) (list 'BINARY-* (list 'QUOTE const) body)) lst)
                  (* const (sum (lamb (list v) body) lst)))))

; T22 shows that (LAMBDA (x) x) is functionally equivalent to IDENTITY:

(defthm T22
  (implies (symbolp x)
           (fn-equal (lamb (list x) x) 'identity))
  :hints (("Goal" :in-theory (enable fn-equal))))

; T23 is a silly example that just shows T21 and T22 operating together.  The
; hint is provided only to show that the theorem is proved by rewriting, not
; induction.

(defthm T23
  (equal (sum (lamb '(U) '(BINARY-* '2 U)) (append aaa bbb))
         (+ (* 2 (sum 'IDENTITY aaa))
            (* 2 (sum 'IDENTITY bbb))))
  :hints (("Goal" :do-not-induct t :in-theory (disable lamb (:e lamb))))
  :rule-classes nil)

(defun$ collect* (fn lst)
  (if (endp lst)
      nil
      (cons (apply$ fn (car lst))
            (collect* fn (cdr lst)))))

; T24 is really just a computation, but done with the rewriter.  It shows that
; TAME functions, e.g., the LAMBDAS below, can be data, and that we can supply
; mapping functions to mapping functions (COLLECT is the :FN argument to
; COLLECT*).  However, because COLLECT is not tame translate would reject
; (COLLECT* 'COLLECT '(((LAMBDA (X) (CONS 'A X)) (1 2 3)) ...)) so we have
; to use the trick of defining a constant symbol to be COLLECT.

(defconst *collect* 'collect)

(defthm T24
  (implies (warrant collect)
           (equal (collect* *collect* ; trick = 'collect
                            '(((LAMBDA (X) (CONS 'A X)) (1 2 3))
                              ((LAMBDA (Z) (CONS 'B Z)) (4 5 6 7))
                              ((LAMBDA (Y) (CONS 'C Y)) (8 9))))
                  '(((A . 1)(A . 2)(A . 3))
                    ((B . 4) (B . 5) (B . 6) (B . 7))
                    ((C . 8) (C . 9)))))
  :hints
  (("Goal"
    :in-theory
    (disable (:executable-counterpart collect)
             (:executable-counterpart collect*)))))
