; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-constructors")

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
    "The rules say that the relation is an equivalence,
     and a congruence with respect to
     additions, subtractions, and multiplications.")
   (xdoc::p
    "The rules say that
     the addition of no dimensions is equivalent to the 0 dimension,
     the addition of one dimension is equivalent to that dimension,
     and that the addition of three or more dimensions is equivalent to
     a nest of additions of two elements each.
     Thus, the laws of addition can be stated on binary additions:
     commutativity, associativity, and identity.
     The addition of (two) constant dimensions
     is equivalent to a single dimension consisting of the calculated sum.")
   (xdoc::p
    "The rules for multiplication are quite analogous to addition.")
   (xdoc::p
    "The rules for subtraction are more complicated,
     because of the lack of symmetry (compared to addition and multiplication),
     and also to avoid creating negative dimensions in calculations.
     There are no explicit rules for the subtraction of no dimensions,
     because it is illegal in fact;
     it is only equivalent to itself, via reflexivity.
     There are rules for the subtraction of one dimension,
     for different forms of that one dimension,
     except for constants and variables:
     there is a rule for binary addition and one for binary multiplication
     (since non-binary ones can be reduced to binary,
     or to non-additions and non-multiplications);
     there is a rule for unary subtraction,
     and one for binary subtraction.
     A subtraction of two or more dimensions is equivalent to the subtraction
     between the first dimension and the addition of the remaining dimensions.
     A subtraction of two constant dimensions is equivalent to
     a constant dimension of the difference, provided it is not negative."))

  :preds ((dimeq dim1 dim2))

  :irules

  ((refl ((dimp x))
         (dimeq x x))

   (symm ((dimp x)
          (dimp y)
          (dimeq x y))
         (dimeq y x))

   (trans ((dimp x)
           (dimp y)
           (dimp z)
           (dimeq x y)
           (dimeq y z))
          (dimeq x z))

   (cong-add ((dimp x)
              (dimp y)
              (dim-listp ws)
              (dim-listp us)
              (dimeq x y))
             (dimeq (dim-add (append ws (list x) us))
                    (dim-add (append ws (list y) us))))

   (cong-sub ((dimp x)
              (dimp y)
              (dim-listp ws)
              (dim-listp us)
              (dimeq x y))
             (dimeq (dim-sub (append ws (list x) us))
                    (dim-sub (append ws (list y) us))))

   (cong-mul ((dimp x)
              (dimp y)
              (dim-listp ws)
              (dim-listp us)
              (dimeq x y))
             (dimeq (dim-mul (append ws (list x) us))
                    (dim-mul (append ws (list y) us))))

   (add0 ()
         (dimeq (dim+)
                (dim-const 0)))

   (add1 ((dimp x))
         (dimeq (dim+ x)
                x))

   (add3m ((dimp x)
           (dimp y)
           (dimp z)
           (dim-listp ws))
          (dimeq (dim-add (list* x y z ws))
                 (dim-add (cons (dim+ (dim+ x y) z) ws))))

   (add2-comm ((dimp x)
               (dimp y))
              (dimeq (dim+ x y)
                     (dim+ y x)))

   (add2-assoc ((dimp x)
                (dimp y)
                (dimp z))
               (dimeq (dim+ (dim+ x y) z)
                      (dim+ x (dim+ y z))))

   (add2-id ((dimp x))
            (dimeq (dim+ 0 x)
                   x))

   (add2-const ((natp d1)
                (natp d2))
               (dimeq (dim+ (dim-const d1) (dim-const d2))
                      (dim-const (+ d1 d2))))

   (mul0 ()
         (dimeq (dim*)
                (dim-const 1)))

   (mul1 ((dimp x))
         (dimeq (dim* x)
                x))

   (mul3m ((dimp x)
           (dimp y)
           (dimp z)
           (dim-listp ws))
          (dimeq (dim-mul (list* x y z ws))
                 (dim-mul (cons (dim* (dim* x y) z) ws))))

   (mul2-comm ((dimp x)
               (dimp y))
              (dimeq (dim* x y)
                     (dim* y x)))

   (mul2-assoc ((dimp x)
                (dimp y)
                (dimp z))
               (dimeq (dim* (dim* x y) z)
                      (dim* x (dim* y z))))

   (mul2-id ((dimp x))
            (dimeq (dim* 1 x)
                   x))

   (mul2-const ((natp d1)
                (natp d2))
               (dimeq (dim* (dim-const d1) (dim-const d2))
                      (dim-const (* d1 d2))))

   (mul-add-distr ((dimp x)
                   (dimp y)
                   (dimp z))
                  (dimeq (dim* x (dim+ y z))
                         (dim+ (dim* x y) (dim* x z))))

   (sub1-mul ((dimp x)
              (dimp y))
             (dimeq (dim- (dim* x y))
                    (dim* (dim- x) y)))

   (sub2 ((dimp x)
          (dimp y))
         (dimeq (dim- x y)
                (dim+ x (dim- y))))

   (sub2m ((dimp x)
           (dim-listp ys)
           (consp ys))
          (dimeq (dim-sub (cons x ys))
                 (dim- x (dim-add ys))))

   (sub2-const ((natp d1)
                (natp d2)
                (>= d1 d2))
               (dimeq (dim- (dim-const d1) (dim-const d2))
                      (dim-const (- d1 d2))))))
