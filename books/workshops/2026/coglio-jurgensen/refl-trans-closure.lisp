; ACL2-2026 Workshop Paper on DEFINDUCTIVE
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/definductive" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains details of the REFL-TRANS-CLOSURE example
; in Sections 4 and 5.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A given binary relation.

(defstub r (* *) => *)

; Reflexive and transitive closure.

(definductive refl-trans-closure
  :preds ((r* a b))
  :irules ((base ((r x y)) (r* x y))
           (refl () (r* x x))
           (trans ((r* x y) (r* y z)) (r* x z))))

; A derived inference rule, proved by rewriting with defining inference rules.

(defruled r*-trans-base-right
  (implies (and (r* x y)
                (r y z))
           (r* x z))
  :enable (r*-base r*-trans))

; A derived inference rule,
; which needs a :USE hint because of the way
; ACL2 handles free variables in rewrite rules.

(defruled r*-trans-base-left
  (implies (and (r x y)
                (r* y z))
           (r* x z))
  :use r*-base
  :enable r*-trans)

; Alternatively, one can define another inference rule...

(defruled r*-trans-swapped
  (implies (and (r* y z)
                (r* x y))
           (r* x z))
  :enable r*-trans)

; ... and then prove the earlier one just via rewriting.

(defruled r*-trans-base-left-alt-proof
  (implies (and (r x y)
                (r* y z))
           (r* x z))
  :enable (r*-base r*-trans-swapped))

; Given a function f that preserves r...

(encapsulate
  (((f *) => *))
  (local (defun f (x) x))
  (defthmd r-of-f
    (implies (r x y)
             (r (f x) (f y)))))

; ... the fact that f also preserves r* can be proved by rule induction.

(defruled r*-of-f
  (implies (r* a b)
           (r* (f a) (f b)))
  :induct (r* a b)
  :expand ((r* a b)
           (r*-proof-validp (r*-proof a b) a b))
  :enable (r-of-f
           r*-base
           r*-refl
           r*-trans
           r*-base-validp
           r*-refl-validp
           r*-trans-validp
           r*-when-proof-validp))

; The previous theorem can be also proved using the minimality of r*,
; via functional instantiation, whose obligations are exactly the rules.

(defruled r*-of-f-via-functional-instantiation
  (implies (r* a b)
           (r* (f a) (f b)))
  :disable ((:e tau-system)) ; prevent any uses of r*-of-f
  :use (:functional-instance r*-alt-when-r*
                             (r*-alt (lambda (a b) (r* (f a) (f b)))))
  :enable (r-of-f r*-base r*-refl r*-trans))
