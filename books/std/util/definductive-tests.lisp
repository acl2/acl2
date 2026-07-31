; Standard Utilities Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "definductive")

(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (defstub r (* *) => *)

 (definductive refl-trans-closure
   :preds ((r* a b))
   :irules ((base ((r x y))
                  (r* x y))
            (refl ()
                  (r* x x))
            (trans ((r* x y) (r* y z))
                   (r* x z))))

 (must-be-redundant
  (defthm r*-base
    (implies (r x y)
             (r* x y))))

 (must-be-redundant
  (defthm r*-refl
    (r* x x)))

 (must-be-redundant
  (defthm r*-trans
    (implies (and (r* x y)
                  (r* y z))
             (r* x z))))

 (must-be-redundant
  (defthm r*-alt-when-r*
    (implies (and (r*-alt-base-p)
                  (r*-alt-refl-p)
                  (r*-alt-trans-p)
                  (r* a b))
             (r*-alt a b))))

 (must-be-redundant
  (defthm r*-2-base
    (implies (r x y)
             (r*-2 x y))))

 (must-be-redundant
  (defthm r*-2-refl
    (r*-2 x x)))

 (must-be-redundant
  (defthm r*-2-trans
    (implies (and (r*-2 x y)
                  (r*-2 y z))
             (r*-2 x z))))

 (must-be-redundant
  (defthm r*-2-alt-when-r*-2
    (implies (and (r*-2-alt-base-p)
                  (r*-2-alt-refl-p)
                  (r*-2-alt-trans-p)
                  (r*-2 a b))
             (r*-2-alt a b))))

 (must-be-redundant
  (defthm r*-2-is-r*
    (equal (r*-2 a b)
           (r* a b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (definductive nil-trees
   :preds ((p a))
   :irules ((base ()
                  (p nil))
            (step ((p x)
                   (p y))
                  (p (cons x y)))))

 (must-be-redundant
  (defthm p-base
    (p nil)))

 (must-be-redundant
  (defthm p-step
    (implies (and (p x)
                  (p y))
             (p (cons x y)))))

 (must-be-redundant
  (defthm p-alt-when-p
    (implies (and (p-alt-base-p)
                  (p-alt-step-p)
                  (p a))
             (p-alt a))))

 (must-be-redundant
  (defthm p-2-base
    (p-2 nil)))

 (must-be-redundant
  (defthm p-2-step
    (implies (and (p-2 x)
                  (p-2 y))
             (p-2 (cons x y)))))

 (must-be-redundant
  (defthm p-2-alt-when-p-2
    (implies (and (p-2-alt-base-p)
                  (p-2-alt-step-p)
                  (p-2 a))
             (p-2-alt a))))

 (must-be-redundant
  (defthm p-2-is-p
    (equal (p-2 a)
           (p a)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (defstub gstub () => *)

 (definductive all-ground
   :preds ((gnd a))
   :irules ((ax ()
                (gnd 0))
            (step ((gnd 0))
                  (gnd 1))
            (ax2 ((gstub))
                 (gnd 2))))

 (must-be-redundant
  (defthm gnd-ax
    (gnd 0)))

 (must-be-redundant
  (defthm gnd-step
    (implies (gnd 0)
             (gnd 1))))

 (must-be-redundant
  (defthm gnd-ax2
    (implies (gstub)
             (gnd 2))))

 (must-be-redundant
  (defthm gnd-alt-when-gnd
    (implies (and (gnd-alt-ax-p)
                  (gnd-alt-step-p)
                  (gnd-alt-ax2-p)
                  (gnd a))
             (gnd-alt a))))

 (must-be-redundant
  (defthm gnd-2-ax
    (gnd-2 0)))

 (must-be-redundant
  (defthm gnd-2-step
    (implies (gnd-2 0)
             (gnd-2 1))))

 (must-be-redundant
  (defthm gnd-2-ax2
    (implies (gstub)
             (gnd-2 2))))

 (must-be-redundant
  (defthm gnd-2-alt-when-gnd-2
    (implies (and (gnd-2-alt-ax-p)
                  (gnd-2-alt-step-p)
                  (gnd-2-alt-ax2-p)
                  (gnd-2 a))
             (gnd-2-alt a))))

 (must-be-redundant
  (defthm gnd-2-is-gnd
    (equal (gnd-2 a)
           (gnd a)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (definductive bounded-nats
   :preds ((bn x))
   :irules ((base ()
                  (bn 0))
            (step ((bn x)
                   (<= x 5))
                  (bn (1+ x)))))

 (must-be-redundant
  (defthm bn-base
    (bn 0)))

 (must-be-redundant
  (defthm bn-step
    (implies (and (bn x)
                  (<= x 5))
             (bn (1+ x)))))

 (must-be-redundant
  (defthm bn-alt-when-bn
    (implies (and (bn-alt-base-p)
                  (bn-alt-step-p)
                  (bn x))
             (bn-alt x))))

 (must-be-redundant
  (defthm bn-2-base
    (bn-2 0)))

 (must-be-redundant
  (defthm bn-2-step
    (implies (and (bn-2 x)
                  (<= x 5))
             (bn-2 (1+ x)))))

 (must-be-redundant
  (defthm bn-2-alt-when-bn-2
    (implies (and (bn-2-alt-base-p)
                  (bn-2-alt-step-p)
                  (bn-2 x))
             (bn-2-alt x))))

 (must-be-redundant
  (defthm bn-2-is-bn
    (equal (bn-2 x)
           (bn x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (definductive duplicate-formals
   :preds ((p x x))
   :irules ((ax ()
                (p 0 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A non-recursive predicate is allowed:
; the generated proof validity function is not recursive,
; so it carries no measure and its theorems avoid induction.

(must-succeed*

 (definductive all-base-ground
   :preds ((p x))
   :irules ((ax ()
                (p 0))))

 (must-be-redundant
  (defthm p-ax
    (p 0)))

 (must-be-redundant
  (defthm p-alt-when-p
    (implies (and (p-alt-ax-p)
                  (p x))
             (p-alt x))))

 (must-be-redundant
  (defthm p-2-ax
    (p-2 0)))

 (must-be-redundant
  (defthm p-2-alt-when-p-2
    (implies (and (p-2-alt-ax-p)
                  (p-2 x))
             (p-2-alt x))))

 (must-be-redundant
  (defthm p-2-is-p
    (equal (p-2 x)
           (p x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (definductive all-base-premise
   :preds ((p x))
   :irules ((ax ((natp x))
                (p x))))

 (must-be-redundant
  (defthm p-ax
    (implies (natp x)
             (p x))))

 (must-be-redundant
  (defthm p-alt-when-p
    (implies (and (p-alt-ax-p)
                  (p x))
             (p-alt x))))

 (must-be-redundant
  (defthm p-2-ax
    (implies (natp x)
             (p-2 x))))

 (must-be-redundant
  (defthm p-2-alt-when-p-2
    (implies (and (p-2-alt-ax-p)
                  (p-2 x))
             (p-2-alt x))))

 (must-be-redundant
  (defthm p-2-is-p
    (equal (p-2 x)
           (p x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A non-recursive predicate with more than one rule
; and with premise-only (existentially quantified) variables:
; this exercises the multiple-proof-kind and witness-extraction paths
; of the non-recursive minimality proof.

(must-succeed*

 (defstub r (* *) => *)

 (definductive all-base-multivar
   :preds ((m a))
   :irules ((pair ((r x y))
                  (m (cons x y)))
            (proj ((r x y))
                  (m x))))

 (must-be-redundant
  (defthm m-pair
    (implies (r x y)
             (m (cons x y)))))

 (must-be-redundant
  (defthm m-proj
    (implies (r x y)
             (m x))))

 (must-be-redundant
  (defthm m-alt-when-m
    (implies (and (m-alt-pair-p)
                  (m-alt-proj-p)
                  (m a))
             (m-alt a))))

 (must-be-redundant
  (defthm m-2-pair
    (implies (r x y)
             (m-2 (cons x y)))))

 (must-be-redundant
  (defthm m-2-proj
    (implies (r x y)
             (m-2 x))))

 (must-be-redundant
  (defthm m-2-alt-when-m-2
    (implies (and (m-2-alt-pair-p)
                  (m-2-alt-proj-p)
                  (m-2 a))
             (m-2-alt a))))

 (must-be-redundant
  (defthm m-2-is-m
    (equal (m-2 a)
           (m a)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (definductive no-base-rule
   :preds ((p x))
   :irules ((step ((p x))
                  (p (cons x x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (definductive no-base-rule-multi
   :preds ((p x))
   :irules ((step1 ((p x))
                   (p (cons x x)))
            (step2 ((p x) (p y))
                   (p (cons x y))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two mutually recursive predicates, on two levels:
; EVEN is at level 0, because it has a rule with no premise predicates,
; while ODD is at level 1, because it is only derivable from EVEN.

(must-succeed*

 (definductive evenodd
   :preds ((even n)
           (odd n))
   :irules ((even-0 ()
                    (even 0))
            (even-step ((natp n)
                        (odd n))
                       (even (1+ n)))
            (odd-step ((natp n)
                       (even n))
                      (odd (1+ n)))))

 (must-be-redundant
  (defthm even-even-0
    (even 0)))

 (must-be-redundant
  (defthm even-even-step
    (implies (and (odd n)
                  (natp n))
             (even (1+ n)))))

 (must-be-redundant
  (defthm odd-odd-step
    (implies (and (even n)
                  (natp n))
             (odd (1+ n)))))

 (must-be-redundant
  (defthm even-alt-when-even
    (implies (and (even-alt-even-0-p)
                  (even-alt-even-step-p)
                  (odd-alt-odd-step-p)
                  (even n))
             (even-alt n))))

 (must-be-redundant
  (defthm odd-alt-when-odd
    (implies (and (even-alt-even-0-p)
                  (even-alt-even-step-p)
                  (odd-alt-odd-step-p)
                  (odd n))
             (odd-alt n))))

 (must-be-redundant
  (defthm even-2-even-0
    (even-2 0)))

 (must-be-redundant
  (defthm even-2-even-step
    (implies (and (odd-2 n)
                  (natp n))
             (even-2 (1+ n)))))

 (must-be-redundant
  (defthm odd-2-odd-step
    (implies (and (even-2 n)
                  (natp n))
             (odd-2 (1+ n)))))

 (must-be-redundant
  (defthm even-2-alt-when-even-2
    (implies (and (even-2-alt-even-0-p)
                  (even-2-alt-even-step-p)
                  (odd-2-alt-odd-step-p)
                  (even-2 n))
             (even-2-alt n))))

 (must-be-redundant
  (defthm odd-2-alt-when-odd-2
    (implies (and (even-2-alt-even-0-p)
                  (even-2-alt-even-step-p)
                  (odd-2-alt-odd-step-p)
                  (odd-2 n))
             (odd-2-alt n))))

 (must-be-redundant
  (defthm even-2-is-even
    (equal (even-2 n)
           (even n))))

 (must-be-redundant
  (defthm odd-2-is-odd
    (equal (odd-2 n)
           (odd n))))

 ; The predicates hold on some of the expected numbers.

 (defthm even-4
   (even 4)
   :rule-classes nil
   :hints (("Goal" :in-theory (enable even-even-0
                                      even-even-step
                                      odd-odd-step))))

 (defthm odd-5
   (odd 5)
   :rule-classes nil
   :hints (("Goal" :in-theory (enable even-even-0
                                      even-even-step
                                      odd-odd-step)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two mutually recursive predicates, with different arities,
; both at level 0, because each has a rule with no premise predicates.

(must-succeed*

 (definductive twolevel0
   :preds ((p x)
           (q x y))
   :irules ((p0 ()
                (p 0))
            (q0 ()
                (q 0 0))
            (pq ((q x x))
                (p x))
            (qp ((p x))
                (q x x))))

 (must-be-redundant
  (defthm p-p0
    (p 0)))

 (must-be-redundant
  (defthm q-q0
    (q 0 0)))

 (must-be-redundant
  (defthm p-pq
    (implies (q x x)
             (p x))))

 (must-be-redundant
  (defthm q-qp
    (implies (p x)
             (q x x))))

 (must-be-redundant
  (defthm p-alt-when-p
    (implies (and (p-alt-p0-p)
                  (q-alt-q0-p)
                  (p-alt-pq-p)
                  (q-alt-qp-p)
                  (p x))
             (p-alt x))))

 (must-be-redundant
  (defthm q-alt-when-q
    (implies (and (p-alt-p0-p)
                  (q-alt-q0-p)
                  (p-alt-pq-p)
                  (q-alt-qp-p)
                  (q x y))
             (q-alt x y))))

 (must-be-redundant
  (defthm p-2-p0
    (p-2 0)))

 (must-be-redundant
  (defthm q-2-q0
    (q-2 0 0)))

 (must-be-redundant
  (defthm p-2-pq
    (implies (q-2 x x)
             (p-2 x))))

 (must-be-redundant
  (defthm q-2-qp
    (implies (p-2 x)
             (q-2 x x))))

 (must-be-redundant
  (defthm p-2-alt-when-p-2
    (implies (and (p-2-alt-p0-p)
                  (q-2-alt-q0-p)
                  (p-2-alt-pq-p)
                  (q-2-alt-qp-p)
                  (p-2 x))
             (p-2-alt x))))

 (must-be-redundant
  (defthm q-2-alt-when-q-2
    (implies (and (p-2-alt-p0-p)
                  (q-2-alt-q0-p)
                  (p-2-alt-pq-p)
                  (q-2-alt-qp-p)
                  (q-2 x y))
             (q-2-alt x y))))

 (must-be-redundant
  (defthm p-2-is-p
    (equal (p-2 x)
           (p x))))

 (must-be-redundant
  (defthm q-2-is-q
    (equal (q-2 x y)
           (q x y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Every predicate must be in the conclusion of some rule.

(must-fail
 (definductive ruleless-pred
   :preds ((p x)
           (q x))
   :irules ((p0 ()
                (p 0))
            (p1 ((q x))
                (p x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two cliques, each a single recursive predicate,
; with the second one depending on the first one.

(must-succeed*

 (definductive two-rec-cliques
   :preds ((p x)
           (q x))
   :irules ((p0 ()
                (p nil))
            (pstep ((p x))
                   (p (cons x x)))
            (q0 ((p x))
                (q x))
            (qstep ((q x))
                   (q (cons x x)))))

 (must-be-redundant
  (defthm p-p0
    (p nil)))

 (must-be-redundant
  (defthm p-pstep
    (implies (p x)
             (p (cons x x)))))

 (must-be-redundant
  (defthm q-q0
    (implies (p x)
             (q x))))

 (must-be-redundant
  (defthm q-qstep
    (implies (q x)
             (q (cons x x)))))

 (must-be-redundant
  (defthm p-alt-when-p
    (implies (and (p-alt-p0-p)
                  (p-alt-pstep-p)
                  (q-alt-q0-p)
                  (q-alt-qstep-p)
                  (p x))
             (p-alt x))))

 (must-be-redundant
  (defthm q-alt-when-q
    (implies (and (p-alt-p0-p)
                  (p-alt-pstep-p)
                  (q-alt-q0-p)
                  (q-alt-qstep-p)
                  (q x))
             (q-alt x))))

 (must-be-redundant
  (defthm p-2-p0
    (p-2 nil)))

 (must-be-redundant
  (defthm p-2-pstep
    (implies (p-2 x)
             (p-2 (cons x x)))))

 (must-be-redundant
  (defthm q-2-q0
    (implies (p-2 x)
             (q-2 x))))

 (must-be-redundant
  (defthm q-2-qstep
    (implies (q-2 x)
             (q-2 (cons x x)))))

 (must-be-redundant
  (defthm p-2-alt-when-p-2
    (implies (and (p-2-alt-p0-p)
                  (p-2-alt-pstep-p)
                  (q-2-alt-q0-p)
                  (q-2-alt-qstep-p)
                  (p-2 x))
             (p-2-alt x))))

 (must-be-redundant
  (defthm q-2-alt-when-q-2
    (implies (and (p-2-alt-p0-p)
                  (p-2-alt-pstep-p)
                  (q-2-alt-q0-p)
                  (q-2-alt-qstep-p)
                  (q-2 x))
             (q-2-alt x))))

 (must-be-redundant
  (defthm p-2-is-p
    (equal (p-2 x)
           (p x))))

 (must-be-redundant
  (defthm q-2-is-q
    (equal (q-2 x)
           (q x))))

 (defthm q-of-nil
   (q nil)
   :rule-classes nil
   :hints (("Goal" :in-theory (enable p-p0 q-q0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two cliques, the first one a non-recursive predicate;
; since A is not recursive, the minimality theorem for it
; is proved without induction,
; while the one for B uses the one for A.

(must-succeed*

 (definductive nonrec-then-rec
   :preds ((a x)
           (b x))
   :irules ((a0 ()
                (a 0))
            (b0 ((a x))
                (b x))
            (bstep ((b x))
                   (b (cons x x)))))

 (must-be-redundant
  (defthm a-a0
    (a 0)))

 (must-be-redundant
  (defthm b-b0
    (implies (a x)
             (b x))))

 (must-be-redundant
  (defthm b-bstep
    (implies (b x)
             (b (cons x x)))))

 (must-be-redundant
  (defthm a-alt-when-a
    (implies (and (a-alt-a0-p)
                  (b-alt-b0-p)
                  (b-alt-bstep-p)
                  (a x))
             (a-alt x))))

 (must-be-redundant
  (defthm b-alt-when-b
    (implies (and (a-alt-a0-p)
                  (b-alt-b0-p)
                  (b-alt-bstep-p)
                  (b x))
             (b-alt x))))

 (must-be-redundant
  (defthm a-2-a0
    (a-2 0)))

 (must-be-redundant
  (defthm b-2-b0
    (implies (a-2 x)
             (b-2 x))))

 (must-be-redundant
  (defthm b-2-bstep
    (implies (b-2 x)
             (b-2 (cons x x)))))

 (must-be-redundant
  (defthm a-2-alt-when-a-2
    (implies (and (a-2-alt-a0-p)
                  (b-2-alt-b0-p)
                  (b-2-alt-bstep-p)
                  (a-2 x))
             (a-2-alt x))))

 (must-be-redundant
  (defthm b-2-alt-when-b-2
    (implies (and (a-2-alt-a0-p)
                  (b-2-alt-b0-p)
                  (b-2-alt-bstep-p)
                  (b-2 x))
             (b-2-alt x))))

 (must-be-redundant
  (defthm a-2-is-a
    (equal (a-2 x)
           (a x))))

 (must-be-redundant
  (defthm b-2-is-b
    (equal (b-2 x)
           (b x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two independent predicates, neither depending on the other.

(must-succeed*

 (definductive independent
   :preds ((c x)
           (d x))
   :irules ((c0 ()
                (c 0))
            (d0 ()
                (d 1))))

 (must-be-redundant
  (defthm c-c0
    (c 0)))

 (must-be-redundant
  (defthm d-d0
    (d 1)))

 (must-be-redundant
  (defthm c-alt-when-c
    (implies (and (c-alt-c0-p)
                  (d-alt-d0-p)
                  (c x))
             (c-alt x))))

 (must-be-redundant
  (defthm d-alt-when-d
    (implies (and (c-alt-c0-p)
                  (d-alt-d0-p)
                  (d x))
             (d-alt x))))

 (must-be-redundant
  (defthm c-2-c0
    (c-2 0)))

 (must-be-redundant
  (defthm d-2-d0
    (d-2 1)))

 (must-be-redundant
  (defthm c-2-alt-when-c-2
    (implies (and (c-2-alt-c0-p)
                  (d-2-alt-d0-p)
                  (c-2 x))
             (c-2-alt x))))

 (must-be-redundant
  (defthm d-2-alt-when-d-2
    (implies (and (c-2-alt-c0-p)
                  (d-2-alt-d0-p)
                  (d-2 x))
             (d-2-alt x))))

 (must-be-redundant
  (defthm c-2-is-c
    (equal (c-2 x)
           (c x))))

 (must-be-redundant
  (defthm d-2-is-d
    (equal (d-2 x)
           (d x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A clique of two mutually recursive predicates
; that depends on an earlier clique of a single predicate.

(must-succeed*

 (definductive nat-evenodd
   :preds ((nt x)
           (evn x)
           (odn x))
   :irules ((nt0 ()
                 (nt 0))
            (ntstep ((nt x))
                    (nt (1+ x)))
            (evn0 ((nt x))
                  (evn 0))
            (evnstep ((natp x)
                      (odn x))
                     (evn (1+ x)))
            (odnstep ((natp x)
                      (evn x))
                     (odn (1+ x)))))

 (must-be-redundant
  (defthm nt-nt0
    (nt 0)))

 (must-be-redundant
  (defthm nt-ntstep
    (implies (nt x)
             (nt (1+ x)))))

 (must-be-redundant
  (defthm evn-evn0
    (implies (nt x)
             (evn 0))))

 (must-be-redundant
  (defthm evn-evnstep
    (implies (and (odn x)
                  (natp x))
             (evn (1+ x)))))

 (must-be-redundant
  (defthm odn-odnstep
    (implies (and (evn x)
                  (natp x))
             (odn (1+ x)))))

 (must-be-redundant
  (defthm nt-alt-when-nt
    (implies (and (nt-alt-nt0-p)
                  (nt-alt-ntstep-p)
                  (evn-alt-evn0-p)
                  (evn-alt-evnstep-p)
                  (odn-alt-odnstep-p)
                  (nt x))
             (nt-alt x))))

 (must-be-redundant
  (defthm evn-alt-when-evn
    (implies (and (nt-alt-nt0-p)
                  (nt-alt-ntstep-p)
                  (evn-alt-evn0-p)
                  (evn-alt-evnstep-p)
                  (odn-alt-odnstep-p)
                  (evn x))
             (evn-alt x))))

 (must-be-redundant
  (defthm odn-alt-when-odn
    (implies (and (nt-alt-nt0-p)
                  (nt-alt-ntstep-p)
                  (evn-alt-evn0-p)
                  (evn-alt-evnstep-p)
                  (odn-alt-odnstep-p)
                  (odn x))
             (odn-alt x))))

 (must-be-redundant
  (defthm nt-2-nt0
    (nt-2 0)))

 (must-be-redundant
  (defthm nt-2-ntstep
    (implies (nt-2 x)
             (nt-2 (1+ x)))))

 (must-be-redundant
  (defthm evn-2-evn0
    (implies (nt-2 x)
             (evn-2 0))))

 (must-be-redundant
  (defthm evn-2-evnstep
    (implies (and (odn-2 x)
                  (natp x))
             (evn-2 (1+ x)))))

 (must-be-redundant
  (defthm odn-2-odnstep
    (implies (and (evn-2 x)
                  (natp x))
             (odn-2 (1+ x)))))

 (must-be-redundant
  (defthm nt-2-alt-when-nt-2
    (implies (and (nt-2-alt-nt0-p)
                  (nt-2-alt-ntstep-p)
                  (evn-2-alt-evn0-p)
                  (evn-2-alt-evnstep-p)
                  (odn-2-alt-odnstep-p)
                  (nt-2 x))
             (nt-2-alt x))))

 (must-be-redundant
  (defthm evn-2-alt-when-evn-2
    (implies (and (nt-2-alt-nt0-p)
                  (nt-2-alt-ntstep-p)
                  (evn-2-alt-evn0-p)
                  (evn-2-alt-evnstep-p)
                  (odn-2-alt-odnstep-p)
                  (evn-2 x))
             (evn-2-alt x))))

 (must-be-redundant
  (defthm odn-2-alt-when-odn-2
    (implies (and (nt-2-alt-nt0-p)
                  (nt-2-alt-ntstep-p)
                  (evn-2-alt-evn0-p)
                  (evn-2-alt-evnstep-p)
                  (odn-2-alt-odnstep-p)
                  (odn-2 x))
             (odn-2-alt x))))

 (must-be-redundant
  (defthm nt-2-is-nt
    (equal (nt-2 x)
           (nt x))))

 (must-be-redundant
  (defthm evn-2-is-evn
    (equal (evn-2 x)
           (evn x))))

 (must-be-redundant
  (defthm odn-2-is-odn
    (equal (odn-2 x)
           (odn x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Every predicate must be at some level:
; here P and Q are mutually recursive, but neither has a base case.

(must-fail
 (definductive no-level-multi
   :preds ((p x)
           (q x))
   :irules ((pq ((q x))
                (p (cons x x)))
            (qp ((p x))
                (q (cons x x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The variables of a rule become fields of the summand of the proof,
; for the second representation of proofs;
; so they must differ from the names that those events use
; for the arguments of the conclusion and for the proofs of the premises.
; The first of these two is the one that matters:
; without the check, the variable would shadow
; the formal of the proof validity predicate in the case for the rule,
; turning the equality for that argument of the conclusion
; into an equality of the field with itself,
; which would silently define the wrong relation.

(must-fail
 (definductive concl-var-clash
   :preds ((p a))
   :irules ((ax ((natp concl.a))
                (p concl.a)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The second of the two: a variable named after a premise field
; would clash with that field in the summand.

(must-fail
 (definductive prem-field-clash
   :preds ((q a))
   :irules ((base ()
                  (q 0))
            (step ((q premise1-proof))
                  (q (1+ premise1-proof))))))
