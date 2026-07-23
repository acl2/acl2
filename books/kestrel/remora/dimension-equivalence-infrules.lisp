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

(include-book "std/util/definductive" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dimension-equivalence-inference-rules
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
     of the static and dynamic semantics of Remora."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive dimeq-infrules
  :short "Equivalence of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The inference rules say that:")
   (xdoc::ul
    (xdoc::li
     "It is an equivalence relation,
      i.e. reflexive, symmetric, and transitive.")
    (xdoc::li
     "The addition of no dimensions is equivalent to the dimension 0.")
    (xdoc::li
     "The addition of one dimension is equivalent to that dimension."))
   (xdoc::p
    "More rules need to be added, obviously."))

  :preds ((dimeq dim1 dim2))

  :irules

  ((refl ((dimp dim))
         (dimeq dim dim))

   (symm ((dimp dim1)
          (dimp dim2)
          (dimeq dim1 dim2))
         (dimeq dim2 dim1))

   (trans ((dimp dim1)
           (dimp dim2)
           (dimp dim3)
           (dimeq dim1 dim2)
           (dimeq dim2 dim3))
          (dimeq dim1 dim3))

   (add0 ()
         (dimeq (dim-add nil)
                (dim-const 0)))

   (add1 ((dimp dim))
         (dimeq (dim-add (list dim))
                dim))

   ;; TODO: add more rules

   ))
