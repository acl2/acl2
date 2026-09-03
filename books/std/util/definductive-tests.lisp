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

(include-book "kestrel/built-ins/disable" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The commented out MUST-BE-REDUNDANT forms should be eventually deleted.

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
  (defthm r*-alt-base
    (implies (r x y)
             (r*-alt x y))))

 (must-be-redundant
  (defthm r*-alt-refl
    (r*-alt x x)))

 (must-be-redundant
  (defthm r*-alt-trans
    (implies (and (r*-alt x y)
                  (r*-alt y z))
             (r*-alt x z))))

 (must-be-redundant
  (defthm r*-alt-when-r*
    (implies (r* a b)
             (r*-alt a b))))

 ; The ruleset has the validity predicates, in order.

 (assert-event
  (equal (get-ruleset 'refl-trans-closure-validp-defs (w state))
         '(r*-base-validp r*-refl-validp r*-trans-validp r*-proof-validp)))

 ; The rule theorems are stored without hints.

 (assert-event (not (member-eq :hints (get-event 'r*-base (w state)))))

 ; The generated induction scheme supports rule induction.

 (encapsulate
   (((f *) => *))
   (local (defun f (x) x))
   (defthm f-preserves
     (implies (r x y)
              (r (f x) (f y)))))

 ; A plain :INDUCT hint on a call of the predicate suffices,
 ; via the generated R*-INDUCTION rule; no proof tree is mentioned.

 (defthm r*-of-f
   (implies (r* a b)
            (r* (f a) (f b)))
   :hints (("Goal" :induct (r* a b)
                   :expand ((r* a b)
                            (r*-proof-validp (r*-proof a b) a b))
                   :in-theory (enable r*-base-validp
                                      r*-refl-validp
                                      r*-trans-validp
                                      r*-base
                                      r*-refl
                                      r*-trans
                                      r*-when-proof-validp)))))

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
  (defthm p-alt-base
    (p-alt nil)))

 (must-be-redundant
  (defthm p-alt-step
    (implies (and (p-alt x)
                  (p-alt y))
             (p-alt (cons x y)))))

 (must-be-redundant
  (defthm p-alt-when-p
    (implies (p a)
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
  (defthm gnd-alt-ax
    (gnd-alt 0)))

 (must-be-redundant
  (defthm gnd-alt-step
    (implies (gnd-alt 0)
             (gnd-alt 1))))

 (must-be-redundant
  (defthm gnd-alt-ax2
    (implies (gstub)
             (gnd-alt 2))))

 (must-be-redundant
  (defthm gnd-alt-when-gnd
    (implies (gnd a)
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
  (defthm bn-alt-base
    (bn-alt 0)))

 (must-be-redundant
  (defthm bn-alt-step
    (implies (and (bn-alt x)
                  (<= x 5))
             (bn-alt (1+ x)))))

 (must-be-redundant
  (defthm bn-alt-when-bn
    (implies (bn x)
             (bn-alt x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (definductive duplicate-formals
   :preds ((p x x))
   :irules ((ax ()
                (p 0 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (definductive duplicate-pred-names
   :preds ((p x)
           (p x y))
   :irules ((ax ()
                (p 0))
            (ax2 ()
                 (p 0 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (definductive duplicate-irule-names
   :preds ((p x))
   :irules ((ax ()
                (p 0))
            (ax ()
                (p 1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules with different conclusion predicates may have the same name.

(must-succeed*

 (definductive same-irule-names
   :preds ((p x)
           (q x))
   :irules ((ax ()
                (p 0))
            (ax ()
                (q 0))))

 (must-be-redundant
  (defthm p-ax
    (p 0)))

 (must-be-redundant
  (defthm q-ax
    (q 0)))

 (must-be-redundant
  (defthm p-alt-ax
    (p-alt 0)))

 (must-be-redundant
  (defthm q-alt-ax
    (q-alt 0))))

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
  (defthm p-alt-ax
    (p-alt 0)))

 (must-be-redundant
  (defthm p-alt-when-p
    (implies (p x)
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
  (defthm p-alt-ax
    (implies (natp x)
             (p-alt x))))

 (must-be-redundant
  (defthm p-alt-when-p
    (implies (p x)
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
  (defthm m-alt-pair
    (implies (r x y)
             (m-alt (cons x y)))))

 (must-be-redundant
  (defthm m-alt-proj
    (implies (r x y)
             (m-alt x))))

 (must-be-redundant
  (defthm m-alt-when-m
    (implies (m a)
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

; A recursive rule listed before the base rule of its predicate,
; with the built-in logic definitions disabled, as some books do.
; FTY tests for non-CONSP values only in the kind test of the base summand,
; so the termination of the fixing function for the summand of STEP
; needs the definition of ACL2-COUNT, which the generated fixtype enables.

(must-succeed*

 (disable-most-builtin-logic-defuns)

 (definductive rec-rule-first
   :preds ((p x))
   :irules ((step ((p x))
                  (p (cons x x)))
            (base ()
                  (p nil))))

 (must-be-redundant
  (defthm p-step
    (implies (p x)
             (p (cons x x)))))

 (must-be-redundant
  (defthm p-base
    (p nil)))

 (must-be-redundant
  (defthm p-alt-when-p
    (implies (p x)
             (p-alt x)))))

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
  (defthm even-alt-even-0
    (even-alt 0)))

 (must-be-redundant
  (defthm even-alt-even-step
    (implies (and (natp n)
                  (odd-alt n))
             (even-alt (1+ n)))))

 (must-be-redundant
  (defthm odd-alt-odd-step
    (implies (and (natp n)
                  (even-alt n))
             (odd-alt (1+ n)))))

 (must-be-redundant
  (defthm even-alt-when-even
    (implies (even n)
             (even-alt n))))

 (must-be-redundant
  (defthm odd-alt-when-odd
    (implies (odd n)
             (odd-alt n))))

 ; The ruleset has the validity predicates, in order.

 (assert-event
  (equal (get-ruleset 'evenodd-validp-defs (w state))
         '(even-even-0-validp
           even-even-step-validp
           odd-odd-step-validp
           even-proof-validp
           odd-proof-validp)))

 ; The rule theorems are stored without hints.

 (assert-event (not (member-eq :hints (get-event 'even-even-step (w state)))))

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
                                      odd-odd-step))))

 ; For a clique of two or more predicates,
 ; rule induction is via the flag macro:
 ; both predicates are proved together,
 ; with no proof tree mentioned in either statement.
 ; The validity predicates are enabled via the generated ruleset.

 (defthm-even-induction
   (defthm natp-when-even
     (implies (even n)
              (natp n))
     :flag even-induct)
   (defthm natp-when-odd
     (implies (odd n)
              (natp n))
     :flag odd-induct)
   :hints (("Goal" :expand ((even-proof-validp (even-proof n) n)
                            (odd-proof-validp (odd-proof n) n))
                   :in-theory (enable* even
                                       odd
                                       evenodd-validp-defs
                                       even-when-proof-validp
                                       odd-when-proof-validp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two mutually recursive predicates,
; where some rules have two premises with predicates of the clique:
; EVEN-SUM has two EVN premises,
; and MIXED-SUM has an EVN premise and an ODN premise.
; This kind of clique requires, in the generated proofs,
; the :EXPAND hints in the fixing equivalences of the validity functions
; and the flag equivalence theorem in the minimality theorems.

(must-succeed*

 (definductive evenodd-sums
   :preds ((evn n)
           (odn n))
   :irules ((zero ()
                  (evn 0))
            (even-step ((natp n)
                        (odn n))
                       (evn (1+ n)))
            (odd-step ((natp n)
                       (evn n))
                      (odn (1+ n)))
            (even-sum ((natp n)
                       (natp m)
                       (evn n)
                       (evn m))
                      (evn (+ n m)))
            (mixed-sum ((natp n)
                        (natp m)
                        (evn n)
                        (odn m))
                       (odn (+ n m)))))

 (must-be-redundant
  (defthm evn-zero
    (evn 0)))

 (must-be-redundant
  (defthm evn-even-step
    (implies (and (odn n)
                  (natp n))
             (evn (1+ n)))))

 (must-be-redundant
  (defthm odn-odd-step
    (implies (and (evn n)
                  (natp n))
             (odn (1+ n)))))

 (must-be-redundant
  (defthm evn-even-sum
    (implies (and (evn n)
                  (evn m)
                  (natp n)
                  (natp m))
             (evn (+ n m)))))

 (must-be-redundant
  (defthm odn-mixed-sum
    (implies (and (evn n)
                  (odn m)
                  (natp n)
                  (natp m))
             (odn (+ n m)))))

 (must-be-redundant
  (defthm evn-alt-zero
    (evn-alt 0)))

 (must-be-redundant
  (defthm evn-alt-even-step
    (implies (and (natp n)
                  (odn-alt n))
             (evn-alt (1+ n)))))

 (must-be-redundant
  (defthm odn-alt-odd-step
    (implies (and (natp n)
                  (evn-alt n))
             (odn-alt (1+ n)))))

 (must-be-redundant
  (defthm evn-alt-even-sum
    (implies (and (natp n)
                  (natp m)
                  (evn-alt n)
                  (evn-alt m))
             (evn-alt (+ n m)))))

 (must-be-redundant
  (defthm odn-alt-mixed-sum
    (implies (and (natp n)
                  (natp m)
                  (evn-alt n)
                  (odn-alt m))
             (odn-alt (+ n m)))))

 (must-be-redundant
  (defthm evn-alt-when-evn
    (implies (evn n)
             (evn-alt n))))

 (must-be-redundant
  (defthm odn-alt-when-odn
    (implies (odn n)
             (odn-alt n))))

 ; The predicates hold on some of the expected numbers.

 (defthm evn-4
   (evn 4)
   :rule-classes nil
   :hints (("Goal" :in-theory (enable evn-zero
                                      evn-even-step
                                      odn-odd-step))))

 (defthm evn-double
   (implies (and (evn n)
                 (natp n))
            (evn (+ n n)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable evn-even-sum)))))

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
  (defthm p-alt-p0
    (p-alt 0)))

 (must-be-redundant
  (defthm q-alt-q0
    (q-alt 0 0)))

 (must-be-redundant
  (defthm p-alt-pq
    (implies (q-alt x x)
             (p-alt x))))

 (must-be-redundant
  (defthm q-alt-qp
    (implies (p-alt x)
             (q-alt x x))))

 (must-be-redundant
  (defthm p-alt-when-p
    (implies (p x)
             (p-alt x))))

 (must-be-redundant
  (defthm q-alt-when-q
    (implies (q x y)
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
  (defthm p-alt-p0
    (p-alt nil)))

 (must-be-redundant
  (defthm p-alt-pstep
    (implies (p-alt x)
             (p-alt (cons x x)))))

 (must-be-redundant
  (defthm q-alt-q0
    (implies (p-alt x)
             (q-alt x))))

 (must-be-redundant
  (defthm q-alt-qstep
    (implies (q-alt x)
             (q-alt (cons x x)))))

 (must-be-redundant
  (defthm p-alt-when-p
    (implies (p x)
             (p-alt x))))

 (must-be-redundant
  (defthm q-alt-when-q
    (implies (q x)
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
  (defthm a-alt-a0
    (a-alt 0)))

 (must-be-redundant
  (defthm b-alt-b0
    (implies (a-alt x)
             (b-alt x))))

 (must-be-redundant
  (defthm b-alt-bstep
    (implies (b-alt x)
             (b-alt (cons x x)))))

 (must-be-redundant
  (defthm a-alt-when-a
    (implies (a x)
             (a-alt x))))

 (must-be-redundant
  (defthm b-alt-when-b
    (implies (b x)
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
  (defthm c-alt-c0
    (c-alt 0)))

 (must-be-redundant
  (defthm d-alt-d0
    (d-alt 1)))

 (must-be-redundant
  (defthm c-alt-when-c
    (implies (c x)
             (c-alt x))))

 (must-be-redundant
  (defthm d-alt-when-d
    (implies (d x)
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
  (defthm nt-alt-nt0
    (nt-alt 0)))

 (must-be-redundant
  (defthm nt-alt-ntstep
    (implies (nt-alt x)
             (nt-alt (1+ x)))))

 (must-be-redundant
  (defthm evn-alt-evn0
    (implies (nt-alt x)
             (evn-alt 0))))

 (must-be-redundant
  (defthm evn-alt-evnstep
    (implies (and (natp x)
                  (odn-alt x))
             (evn-alt (1+ x)))))

 (must-be-redundant
  (defthm odn-alt-odnstep
    (implies (and (natp x)
                  (evn-alt x))
             (odn-alt (1+ x)))))

 (must-be-redundant
  (defthm nt-alt-when-nt
    (implies (nt x)
             (nt-alt x))))

 (must-be-redundant
  (defthm evn-alt-when-evn
    (implies (evn x)
             (evn-alt x))))

 (must-be-redundant
  (defthm odn-alt-when-odn
    (implies (odn x)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The variables of a rule become fields of the summand of the proof,
; for the first representation of proofs;
; so they must differ from the names that those events use
; for the arguments of the conclusion, for the proofs of the premises,
; and for the variable of the fixtypes of proofs.
; The first of these three is the one that matters:
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

; The second of the three: a variable named after a premise field
; would clash with that field in the summand.

(must-fail
 (definductive prem-field-clash
   :preds ((q a))
   :irules ((base ()
                  (q 0))
            (step ((q premise1-proof))
                  (q (1+ premise1-proof))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The third of the three: a variable named after
; the variable of the fixtypes of proofs
; would make FTY reject the fixtype,
; since no field can have the same name as that variable.

(must-fail
 (definductive xvar-clash
   :preds ((r a))
   :irules ((ax ((natp proof$))
                (r proof$)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; XDOC is generated when :PARENTS, :SHORT, or :LONG is supplied.
; This exercises the XDOC of all the generated events,
; for a clique of a single predicate and for a clique of two.

(must-succeed
 (definductive rtc-xdoc
   :preds ((r* a b))
   :irules ((refl ()
                  (r* a a))
            (step ((r* a b))
                  (r* a b)))
   :parents (acl2::top)
   :short "Reflexive transitive closure."))

(must-succeed
 (definductive evenodd-xdoc
   :preds ((evn n)
           (odd n))
   :irules ((zero ()
                  (evn 0))
            (evn-step ((evn n))
                      (odd (1+ n)))
            (odd-step ((odd n))
                      (evn (1+ n))))
   :parents (acl2::top)
   :short "Even and odd natural numbers."))
