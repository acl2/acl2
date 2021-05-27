; Copyright (C) 2020, ForrestHunt, Inc.
; Written by J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Examples of Rewrite-Quoted-Constant Rules in Use
; J Strother Moore
; August, 2020

(in-package "ACL2")

; The following book provides four things we care about in this book:

; (1) set-equalp as an equivalence relation

; (2) drop-dups-and-sort, a function that preserves set-equalp; in fact,
;     drop-dups-and-sort converts any list into a duplicate-free true-list of
;     elements in ascending lexorder.

; (3) cardinality

; (3) that SET-EQUALP lists have EQUAL cardinalities, as a congruence rule.

; In this work, a ``set'' is just a list, possibly with duplicatations.  Some
; examples:

; * (drop-dups-and-sort '(4 1 2 2 3 . 77)) = '(1 2 3 4),

; * (set-equalp '(4 1 2 2 3 . 77) '(1 2 3 4)) = T

; * (cardinality '(4 1 2 2 3 . 77)) = (cardinality '(1 2 3 4)) = 4

; There are other concepts and rules introduced by this ``-lemmas'' book, but
; they are not important to understanding the examples here.

(include-book "rewrite-quoted-constant-examples-lemmas")
(include-book "std/testing/eval" :dir :system)

; We disable cardinality so we can't compute on constants.  We also disable the
; :rewrite rule (from the -lemmas book above) that rewrites (drop-dups-and-sort
; x) to x under set-equalp.

(in-theory (disable cardinality
                    (:executable-counterpart cardinality)
                    (:rewrite set-equalp-drop-dups-and-sort)))

; The following conjecture would be provable by computation alone, if
; cardinality or its executable counterpart were enabled.  Here we just
; demonstrate that we've blocked that simple proof.

(must-fail
 (defthm example0
   (equal (cardinality '(4 1 1 2 2 3 . 77))
          (cardinality '(1 2 3 4)))
   :rule-classes nil))

; But if we could rewrite the quoted constant on the left-hand side of the
; conjecture to its ``normal form'' as a set, we could prove it by (equal x x).
; So we'll prove an appropriate :rewrite-quoted-constant rule.  All of the
; examples in this book will be of this form and all of the proofs will be
; analogous to this one: apply a :rewrite-quoted-constant rule to the constant
; on the left and observe that the conjecture becomes an instance of (equal x
; x).

; So here is our first :rewrite-quoted-constant rule, a Form [1] rule.

(defthm form-1-rule
  (set-equalp '(4 1 1 2 2 3 . 77) '(1 2 3 4))
  :rule-classes :rewrite-quoted-constant)

; (BTW: The above is just proved by computation, since set-equalp is not
; disabled.)

; So now we prove the previously ``unprovable'' conjecture.

(defthm example1
  (equal (cardinality '(4 1 1 2 2 3 . 77))
         (cardinality '(1 2 3 4)))
  :rule-classes nil)

; :Rewrite-quoted-constant rules are NOT applied recursively to substructures
; within the quoted constant!  So if we bury the target constant, '(4 1 1 2 2 3
; . 77), in the cdr of another quoted constant (by consing 555 onto the target),
; our rule won't apply.

(must-fail
 (defthm example2
   (equal (cardinality '(555 4 1 1 2 2 3 . 77))
          (cardinality '(555 1 2 3 4)))
   :rule-classes nil))

; Now we develop a Form [2] rule.

(defthm form-2-rule
  (set-equalp (drop-dups-and-sort lst) lst)
  :hints (("Goal" :in-theory (enable (:rewrite set-equalp-drop-dups-and-sort))))
  :rule-classes :rewrite-quoted-constant)

; Of course, the above theorem is provable only because we've established (in
; our -lemmas book) that drop-dups-and-sort preserves set-equalp.

; Form [2] rules allow you to process a constant recursively with a function
; that explores it as you wish.

(defthm example3
  (equal (cardinality '(555 4 1 1 2 2 3 . 77))
         (cardinality '(1 2 3 4 555)))
  :rule-classes nil)

; Before moving on, we will disable this form-2-rule because it will normalize
; any quoted constant in a set-equalp slot, and we want to demonstrate how form
; [3] rules operate.

(in-theory (disable form-2-rule))

; And now for some Form [3] rules.

(defthm form-3-rule-1
  (set-equalp (cons x (cons y z)) (cons y (cons x z)))
  :rule-classes :rewrite-quoted-constant)

; (BTW: The rule above has an automatically created loop-stopper so that x and
; y are swapped only when y is a smaller term than x.)

(defthm example4
  (equal (cardinality '(2 1 4 3))
         (cardinality '(1 2 4 3)))
  :rule-classes nil)

; Note that Form [3] rules only apply at the top level.  So our form-3-rule-1
; swapped the 2 and 1, but did not dive down and swap the 4 and 3.  Again, if
; you want to do that, use a Form [2] rule.

; Unlike Form [1] and [2] rules, Form [3] rules can turn an explicit quoted
; constant into a non-quoted term.  To illustrate this, we'll first disable
; form-3-rule-1 so it doesn't interfere with what's about to happen.

(in-theory (disable form-3-rule-1))

; Now we'll introduce a synonym for cons.

(defun my-cons (x y) (cons x y))

(defthm form-3-rule-2
  (set-equalp (cons x y) (my-cons x y))
  :rule-classes :rewrite-quoted-constant)

(in-theory (disable my-cons (:executable-counterpart my-cons)))

(defthm example5
  (equal (cardinality '(2 1 4 3))
         (cardinality (my-cons '2 '(1 4 3))))
  :rule-classes nil)

; Note that after form-3-rule-2 applies, above, it introduces the term (my-cons
; '2 '(1 4 3)).  That raises the quoted constant '(1 4 3) to the top-level of a
; term.  So you might expect that the rule will apply again and rewrite that
; quoted constant to another my-cons expression.  But it doesn't.

(must-fail
 (defthm example6
   (equal (cardinality '(2 1 4 3))
          (cardinality (my-cons '2 (my-cons '1 '(4 3)))))
   :rule-classes nil))

; The reason is that we have not proved that set-equalp is a congruence
; relation for the second argument of my-cons.  So let's prove that.  (Of
; course, we have to expand my-cons to do that.)

(defcong set-equalp set-equalp (my-cons x y) 2
  :hints (("Goal" :in-theory (enable my-cons))))

; Now we can demonstrate the previously expected rewriting, all the way down to
; the bottom.  But remember: :rewrite-quoted-constant terms only apply to
; quoted constants!  The reason this rule looks like it's applied recursively
; is that at every step it lifts a previously ``hidden'' substructure into the
; top-level of a term.

(defthm example7
  (equal (cardinality '(2 1 4 3))
         (cardinality (my-cons '2 (my-cons '1 (my-cons '4 (my-cons '3 'nil))))))
  :rule-classes nil)

; You might note another facet of example7.  The rewriting occurs in repeated
; simplification steps, not all at once.  Here are the first two steps as
; reported by Version 8.4:

; This simplifies, using the :congruence rule
; SET-EQUALP-IMPLIES-EQUAL-CARDINALITY-1 and the :rewrite-quoted-constant
; rule FORM-3-RULE-2, to
;
; Goal'
; (EQUAL (CARDINALITY (MY-CONS 2 '(1 4 3)))
;        (CARDINALITY (MY-CONS 2
;                              (MY-CONS 1 (MY-CONS 4 (MY-CONS 3 NIL)))))).
;
; This simplifies, using the :congruence rule
; SET-EQUALP-IMPLIES-SET-EQUALP-MY-CONS-2 and the :rewrite-quoted-constant
; rule FORM-3-RULE-2, to
;
; Goal''
; (EQUAL (CARDINALITY (MY-CONS 2 (MY-CONS 1 '(4 3))))
;        (CARDINALITY (MY-CONS 2
;                              (MY-CONS 1 (MY-CONS 4 (MY-CONS 3 NIL)))))).
;
;

; That is, after rewriting '(2 1 4 3) to (my-cons '2 '(1 4 3)), we do not call
; the ACL2 rewriter again on that rewritten constant.  The next time
; simplification is called it will discover that newly exposed constant and
; rewrite it.  This design is a judgement call on our part.  Because
; :rewrite-quoted-constant rules are new we thought that users might benefit
; from seeing the steps -- and be able to detect and avoid infinite rewriting
; loops caused by improperly formulated rules.  In some future version of the
; system we may rewrite the rewritten result.


