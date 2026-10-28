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

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defund-sk" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains (the full details of) the material in Section 3,
; which defines the reflexive and transitive closure manually,
; i.e. not by calling DEFINDUCTIVE.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A given binary relation.

(defstub r (* *) => *)

; Proof trees.

(fty::deftagsum r*-proof
  (:base (x y))
  (:refl (x))
  (:trans (x y z (premise1-proof r*-proof) (premise2-proof r*-proof)))
  :pred r*-proofp
  :xvar proof)

; Validity of proof trees.

(defund r*-proof-validp (proof a b)
  (declare (xargs :guard (r*-proofp proof)
                  :measure (r*-proof-count proof)))
  (r*-proof-case
   proof
   :base (and (r proof.x proof.y)
              (equal a proof.x)
              (equal b proof.y))
   :refl (and (equal a proof.x)
              (equal b proof.x))
   :trans (and (equal a proof.x)
               (equal b proof.z)
               (r*-proof-validp proof.premise1-proof proof.x proof.y)
               (r*-proof-validp proof.premise2-proof proof.y proof.z))))

; Definition of reflexive and transitive closure.

(defund-sk r* (a b)
  (exists (proof)
          (and (r*-proofp proof)
               (r*-proof-validp proof a b))))

; Inference rules as theorems.

(defthmd r*-base
  (implies (r x y)
           (r* x y))
  :hints (("Goal"
           :in-theory (enable r*-proof-validp)
           :use (:instance r*-suff
                           (proof (r*-proof-base x y))
                           (a x)
                           (b y)))))

(defthmd r*-refl
  (r* x x)
  :hints (("Goal"
           :in-theory (enable r*-proof-validp)
           :use (:instance r*-suff
                           (proof (r*-proof-refl x))
                           (a x)
                           (b x)))))

(defthmd r*-trans
  (implies (and (r* x y)
                (r* y z))
           (r* x z))
  :hints (("Goal"
           :in-theory (enable r*-proof-validp)
           :expand ((r* x y)
                    (r* y z))
           :use (:instance r*-suff
                           (proof (r*-proof-trans x y z
                                                  (r*-witness x y)
                                                  (r*-witness y z)))
                           (a x)
                           (b z)))))

; Assume another relation satisfying the rules.

(encapsulate
  (((r*-alt * *) => *))

  (local (defun r*-alt (a b) (r* a b)))

  (defthmd r*-alt-base
    (implies (r x y)
             (r*-alt x y))
    :hints (("Goal" :use r*-base)))

  (defthmd r*-alt-refl
    (r*-alt x x)
    :hints (("Goal" :use r*-refl)))

  (defthmd r*-alt-trans
    (implies (and (r*-alt x y)
                  (r*-alt y z))
             (r*-alt x z))
    :hints (("Goal" :use r*-trans))))

; Then that other relation is not smaller than r*.

(defthmd r*-alt-when-r*-proof-validp
  (implies (r*-proof-validp proof a b)
           (r*-alt a b))
  :hints (("Goal"
           :induct t
           :in-theory (enable r*-proof-validp))
          '(:use ((:instance r*-alt-base
                             (x (r*-proof-base->x proof))
                             (y (r*-proof-base->y proof)))
                  (:instance r*-alt-refl
                             (x (r*-proof-refl->x proof)))
                  (:instance r*-alt-trans
                             (x (r*-proof-trans->x proof))
                             (y (r*-proof-trans->y proof))
                             (z (r*-proof-trans->z proof)))))))

(defthmd r*-alt-when-r*
  (implies (r* a b)
           (r*-alt a b))
  :hints (("Goal" :in-theory (enable r* r*-alt-when-r*-proof-validp))))
