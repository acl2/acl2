; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-equivalence-derived-rules")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ shape-ordering
  :parents (static-semantics)
  :short "Ordering of shapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Shapes denote sequences of natural numbers.
     Dynamically, lifting involves calculating
     the least upper bound of such sequences of natural numbers,
     according to the prefix relation on them, which is a partial order.
     Statically, shapes may include (shape and dimension) variables,
     so the calculation of the least upper bound,
     as well as the notion of partial order,
     must be expressed in terms of shape equivalence."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk shape-ord ((shape1 shapep) (shape2 shapep))
  :returns (yes/no booleanp)
  :short "Check if two shapes are ordered."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the first shape denotes a prefix of
     the sequence denoted by the second shape.
     We express that by saying that there exists a third shape that,
     when concatenated after the first shape,
     yields a shape equivalent to the second shape.")
   (xdoc::p
    "This is a partial order modulo shape equivalence:
     it is reflexive and transitive (and thus a preorder),
     but it is antisymmetric only up to shape equivalence.")
   (xdoc::p
    "We still need to prove antisymmetry modulo shape equivalence."))
  (exists (shape3)
          (and (shapep shape3)
               (shape-eq (shp++ shape1 shape3)
                         (shape-fix shape2))))

  ///

  (fty::deffixequiv-sk shape-ord
    :args ((shape1 shapep) (shape2 shapep)))

  (defrule shape-ord-refl
    (shape-ord shape shape)
    :use (:instance lemma (shape (shape-fix shape)))
    :prep-lemmas
    ((defrule lemma
       (implies (shapep shape)
                (shape-ord shape shape))
       :use (:instance shape-ord-suff
                       (shape1 shape)
                       (shape2 shape)
                       (shape3 (shp++)))
       :enable shape-eq-append-id-right
       :disable ((:e shape-append)))))

  (defruled shape-ord-trans
    (implies (and (shape-ord shape1 shape2)
                  (shape-ord shape2 shape3))
             (shape-ord shape1 shape3))
    :use (:instance lemma
                    (shape1 (shape-fix shape1))
                    (shape2 (shape-fix shape2))
                    (shape3 (shape-fix shape3)))
    :prep-lemmas
    ((defrule lemma
       (implies (and (shapep shape1)
                     (shapep shape2)
                     (shapep shape3)
                     (shape-ord shape1 shape2)
                     (shape-ord shape2 shape3))
                (shape-ord shape1 shape3))
       :expand ((shape-ord shape1 shape2)
                (shape-ord shape2 shape3))
       :use (:instance shape-ord-suff
                       (shape1 shape1)
                       (shape2 shape3)
                       (shape3 (shp++ (shape-ord-witness shape1 shape2)
                                      (shape-ord-witness shape2 shape3))))
       :enable (shape-eq-append-extend-right
                shape-eq-trans-swapped)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk shape-ord-all-upper-bounds-p ((shape shapep)
                                         (shape1 shapep)
                                         (shape2 shapep))
  :returns (yes/no booleanp)
  :short "Check if a shape is below or equal to
          every upper bound of two shapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check that every shape @('shape-ub')
     that is above or equal to both @('shape1') and @('shape2')
     is also above or equal to @('shape').
     This is used in the definition of least upper bound below."))
  (forall (shape-ub)
          (implies (and (shapep shape-ub)
                        (shape-ord shape1 shape-ub)
                        (shape-ord shape2 shape-ub))
                   (shape-ord shape shape-ub)))

  ///

  (fty::deffixequiv-sk shape-ord-all-upper-bounds-p
    :args ((shape shapep) (shape1 shapep) (shape2 shapep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shape-lubp ((shape shapep) (shape1 shapep) (shape2 shapep))
  :returns (yes/no booleanp)
  :short "Check if a shape is the least upper bound of two shapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The shape must be an upper bound (i.e. above or equal to the shapes),
     and must be least among all upper bounds.")
   (xdoc::p
    "Two shapes may or may not have a least upper bound.
     For instance, the two concrete sequences @('[1 2]') and @('[1 3]')
     do not have any upper bound at all."))
  (and (shape-ord shape1 shape)
       (shape-ord shape2 shape)
       (shape-ord-all-upper-bounds-p shape shape1 shape2)))
