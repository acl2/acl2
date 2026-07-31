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
             (r*-alt a b)))))

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
             (p-alt a)))))

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
             (gnd-alt a)))))

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
             (bn-alt x)))))

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
             (p-alt x)))))

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
             (p-alt x)))))

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
             (m-alt a)))))

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
             (q-alt x y)))))

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
             (b-alt x)))))

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
             (d-alt x)))))

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
             (odn-alt x)))))

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
