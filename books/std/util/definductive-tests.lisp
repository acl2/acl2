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
             (r*-2-alt a b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (definductive nil-trees
   :preds ((p a))
   :irules ((base ()
                  (p nil))
            (step ((p x) (p y))
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
             (p-2-alt a)))))

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
             (gnd-2-alt a)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (definductive bounded-nats
   :preds ((bn x))
   :irules ((base ()
                  (bn 0))
            (step ((bn x) (<= x 5))
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
             (bn-2-alt x)))))

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
             (p-2-alt x)))))

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
             (p-2-alt x)))))

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
             (m-2-alt a)))))

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
