; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-equivalence")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-equivalence-derived-rules
  :parents (static-semantics)
  :short "Derived inference rules for ispace equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "Like each defining inference rule has a proof tree constructor,
     from the proofs of the premises to the proof of the conclusion,
     each derived rule has one,
     defined in terms of the constructors of the defining rules.
     We introduce functions similar to
     the constructors of the proof tree fixtypes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim=-trans-swapped
  :short "Transitivity of dimension equivalence with the premises swapped."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proof constructor just swaps the premise proofs
     in a proof tree for the transitivity defining rule."))

  (defruled dim=-trans-swapped
    (implies (and (dim= d2 d3)
                  (dim= d1 d2))
             (dim= d1 d3))
    :use dim=-trans
    :enable dimp-when-dim=)

  (define dim=-proof-trans-swapped (d1
                                    d2
                                    d3
                                    (premise1-proof dim=-proofp)
                                    (premise2-proof dim=-proofp))
    :returns (proof dim=-proofp)
    :parents nil
    (make-dim=-proof-trans :d1 d1
                           :d2 d2
                           :d3 d3
                           :premise1-proof premise2-proof
                           :premise2-proof premise1-proof)

    ///

    (defret dim=-proof-validp-of-dim=-proof-trans-swapped
      (implies (and (dim=-proof-validp premise1-proof d2 d3)
                    (dim=-proof-validp premise2-proof d1 d2))
               (dim=-proof-validp proof d1 d3))
      :hints (("Goal"
               :expand ((dim=-proof-validp
                         (dim=-proof-trans d1 d2 d3
                                           premise2-proof premise1-proof)
                         d1 d3))
               :in-theory (enable dim=-trans-validp
                                  dimp-when-dim=-proof-validp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection shp=-trans-swapped
  :short "Transitivity of shape equivalence with the premises swapped."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee dim=-trans-swapped)."))

  (defruled shp=-trans-swapped
    (implies (and (shp= s2 s3)
                  (shp= s1 s2))
             (shp= s1 s3))
    :use shp=-trans
    :enable shapep-when-shp=)

  (define shp=-proof-trans-swapped (s1
                                    s2
                                    s3
                                    (premise1-proof shp=-proofp)
                                    (premise2-proof shp=-proofp))
    :returns (proof shp=-proofp)
    :parents nil
    (make-shp=-proof-trans :s1 s1
                           :s2 s2
                           :s3 s3
                           :premise1-proof premise2-proof
                           :premise2-proof premise1-proof)

    ///

    (defret shp=-proof-validp-of-shp=-proof-trans-swapped
      (implies (and (shp=-proof-validp premise1-proof s2 s3)
                    (shp=-proof-validp premise2-proof s1 s2))
               (shp=-proof-validp proof s1 s3))
      :hints (("Goal"
               :expand ((shp=-proof-validp
                         (shp=-proof-trans s1 s2 s3
                                           premise2-proof premise1-proof)
                         s1 s3))
               :in-theory (enable shp=-trans-validp
                                  shapep-when-shp=-proof-validp))))))
