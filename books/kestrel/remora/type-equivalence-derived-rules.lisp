; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "type-equivalence")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-equivalence-derived-rules
  :parents (static-semantics)
  :short "Derived inference rules for type equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(see ispace-equivalence-derived-rules):
     each derived rule comes with a proof tree constructor,
     defined in terms of the constructors of the defining rules,
     as well as a @('make-...') macro with keyword arguments;
     the derived rule is proved as a theorem
     from the validity theorem of the proof tree constructor,
     via the soundness theorem @(tsee type-eq-when-proof-validp)
     and the witness function @('type-eq-proof')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-eq-trans-swapped
  :short "Transitivity of type equivalence with the premises swapped."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee dim-eq-trans-swapped)."))

  (define type-eq-proof-trans-swapped (type1
                                       type2
                                       type3
                                       (premise1-proof type-eq-proofp)
                                       (premise2-proof type-eq-proofp))
    :returns (proof type-eq-proofp)
    :parents nil
    (make-type-eq-proof-trans :type1 type1
                              :type2 type2
                              :type3 type3
                              :premise1-proof premise2-proof
                              :premise2-proof premise1-proof)

    ///

    (defret type-eq-proof-validp-of-type-eq-proof-trans-swapped
      (implies (and (type-eq-proof-validp premise1-proof type2 type3)
                    (type-eq-proof-validp premise2-proof type1 type2))
               (type-eq-proof-validp proof type1 type3))
      :hints (("Goal"
               :expand ((type-eq-proof-validp
                         (type-eq-proof-trans type1 type2 type3
                                              premise2-proof premise1-proof)
                         type1 type3))
               :in-theory (enable type-eq-trans-validp
                                  typep-when-type-eq-proof-validp)))))

  (defruled type-eq-trans-swapped
    (implies (and (type-eq type2 type3)
                  (type-eq type1 type2))
             (type-eq type1 type3))
    :use ((:instance type-eq (type1 type2) (type2 type3))
          (:instance type-eq (type1 type1) (type2 type2))
          (:instance type-eq-when-proof-validp
                     (proof (type-eq-proof-trans-swapped
                             type1 type2 type3
                             (type-eq-proof type2 type3)
                             (type-eq-proof type1 type2)))
                     (concl.type1 type1)
                     (concl.type2 type3))))

  (defmacro make-type-eq-proof-trans-swapped (&key type1
                                                   type2
                                                   type3
                                                   premise1-proof
                                                   premise2-proof)
    `(type-eq-proof-trans-swapped
      ,type1 ,type2 ,type3 ,premise1-proof ,premise2-proof)))
