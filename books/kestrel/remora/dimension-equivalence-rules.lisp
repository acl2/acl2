; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defund-sk" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dimension-equivalence-rules
  :parents (static-semantics)
  :short "Inference rules for dimension equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is work in progress towards
     a higher-level definition of dimension equivalence
     than the executable definition in @(see ispace-equivalence).
     This higher-level definition is an inductive one, via inference rules.
     This is part of our plan to add
     higher-level inductive definitions, via inference rules,
     of the static and dynamic semantics of Remora.")
   (xdoc::p
    "We are separately working on a new ACL2 tool
     to concisely introduce inductive definitions via inference rules,
     within the first-order logic of ACL2.
     We plan to use those tools when ready,
     but we start with some initial manual definitions here,
     also to provide test cases for that new tool."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We provide an inductive definition, via the inference rules below,
; of a binary predicate DIMEQ on dimensions (i.e. ASTs of fixtype DIM)
; that says whether the two dimensions are equivalent,
; i.e. they always denote the same dimension value (i.e. natural number).

; --------------- refl
; (dimeq dim dim)

; TODO: more rules

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Assertions (DIMEQ DIM1 DIM2).

(fty::defprod dimeq-assertion
  ((dim1 dim)
   (dim2 dim))
  :pred dimeq-assertionp)

;;;;;;;;;;;;;;;;;;;;

; Proofs of assertions (DIMEQ DIM1 DIM2).

(fty::deftagsum dimeq-proof
  (:refl ((conclusion dimeq-assertion)))
  :pred dimeq-proofp)

;;;;;;;;;;;;;;;;;;;;

; Conclusion of a proof.

(define dimeq-proof->conclusion ((proof dimeq-proofp))
  :returns (concl dimeq-assertionp)
  (dimeq-proof-case
   proof
   :refl proof.conclusion))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Validity of the rules.

(define-sk dimeq-refl-validp ((concl dimeq-assertionp))
  (exists (dim)
          (and (dimp dim)
               (equal (dimeq-assertion-fix concl)
                      (dimeq-assertion dim dim)))))

;;;;;;;;;;;;;;;;;;;;

; Validity of proofs.

(define dimeq-proof-validp ((proof dimeq-proofp))
  (dimeq-proof-case
   proof
   :refl (dimeq-refl-validp proof.conclusion)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Definition via proof existence.

(define-sk dimeq ((dim1 dimp) (dim2 dimp))
  :returns (yes/no booleanp)
  (exists (proof)
          (and (dimeq-proofp proof)
               (dimeq-proof-validp proof)
               (equal (dimeq-proof->conclusion proof)
                      (dimeq-assertion dim1 dim2))))
  :skolem-name dimeq-proof)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Construct proofs for rules.

(define dimeq-proof-for-refl ((dim dimp))
  :returns (proof dimeq-proofp)
  (make-dimeq-proof-refl :conclusion (dimeq-assertion dim dim))
  ///
  (defret dimeq-proof-validp-of-dimeq-proof-for-refl
    (dimeq-proof-validp proof)
    :hyp (dimp dim)
    :hints (("Goal"
             :use (:instance dimeq-refl-validp-suff
                             (concl (dimeq-assertion dim dim)))
             :in-theory (enable dimeq-proof-validp))))
  (defret dimeq-proof->conclusion-of-dimeq-proof-for-refl
    (equal (dimeq-proof->conclusion proof)
           (dimeq-assertion dim dim))
    :hints (("Goal"
             :in-theory (enable dimeq-proof->conclusion))))
  (in-theory (disable dimeq-proof-validp-of-dimeq-proof-for-refl
                      dimeq-proof->conclusion-of-dimeq-proof-for-refl)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules as theorems.

(defruled dimeq-refl
  (implies (dimp dim)
           (dimeq dim dim))
  :use ((:instance dimeq-suff
                   (proof (dimeq-proof-for-refl dim))
                   (dim1 dim)
                   (dim2 dim))
        (:instance dimeq-proof-validp-of-dimeq-proof-for-refl))
  :enable (dimeq-proof-for-refl
           dimeq-proof->conclusion))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Proof of minimality.

(defstub dimeq-alt (* *) => *)

(defund-sk dimeq-alt-refl-p ()
  (forall (dim)
          (implies (dimp dim)
                   (dimeq-alt dim dim))))

(defruled dimeq-alt-when-proof-validp
  (implies (and (dimeq-alt-refl-p)
                (dimeq-proof-validp proof))
           (b* (((dimeq-assertion concl) (dimeq-proof->conclusion proof)))
             (dimeq-alt concl.dim1 concl.dim2)))
  :use (:instance dimeq-alt-refl-p-necc
                  (dim (dimeq-assertion->dim1
                        (dimeq-proof->conclusion proof))))
  :enable (dimeq-proof-validp
           dimeq-refl-validp
           dimeq-proof->conclusion))

(defruled dimeq-alt-when-dimeq
  (implies (and (dimp dim1)
                (dimp dim2)
                (dimeq-alt-refl-p)
                (dimeq dim1 dim2))
           (dimeq-alt dim1 dim2))
  :enable dimeq
  :use (:instance dimeq-alt-when-proof-validp
                  (proof (dimeq-proof dim1 dim2))))
