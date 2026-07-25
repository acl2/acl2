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
    "The inference rules say that:")
   (xdoc::ul
    (xdoc::li
     "It is an equivalence relation,
      i.e. reflexive, symmetric, and transitive.")
    (xdoc::p
     "It is a congruence with respect to
      additions, subtractions, and multiplications.")
    (xdoc::li
     "The addition of no dimensions is equivalent to the dimension 0.")
    (xdoc::li
     "The addition of one dimension is equivalent to that dimension.")
    (xdoc::li
     "The addition of three or more dimensions is equivalent to
      left-nested additions of two dimensions.
      This reduces n-ary additions with three or more addends
      to binary additions, which the following rules are about.")
    (xdoc::li
     "The addition of dimensions is commutative and associative,
      and it has 0 as identity.")
    (xdoc::li
     "The addition of two constant dimensions reduces to their sum.")
    (xdoc::li
     "Multiplication is subject to rules analogous to addition."))
   (xdoc::p
    "We need to add rules for subtractio,
     in a way that does not require the production of negative dimensions."))

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
           (dimp x)
           (dimeq x y)
           (dimeq y z))
          (dimeq x z))

   (cong-add ((dimp x)
              (dimp y)
              (dim-listp pre)
              (dim-listp post)
              (dimeq x y))
             (dimeq (dim-add (append pre (list x) post))
                    (dim-add (append pre (list y) post))))

   (cong-sub ((dimp x)
              (dimp y)
              (dim-listp pre)
              (dim-listp post)
              (dimeq x y))
             (dimeq (dim-sub (append pre (list x) post))
                    (dim-sub (append pre (list y) post))))

   (cong-mul ((dimp x)
              (dimp y)
              (dim-listp pre)
              (dim-listp post)
              (dimeq x y))
             (dimeq (dim-mul (append pre (list x) post))
                    (dim-mul (append pre (list y) post))))

   (add0 ()
         (dimeq (dim+)
                (dim-const 0)))

   (add1 ((dimp x))
         (dimeq (dim+ x)
                x))

   (add3m ((dimp x)
           (dimp y)
           (dimp z)
           (dim-listp rest))
          (dimeq (dim-add (list* x y z rest))
                 (dim-add (cons (dim+ (dim+ x y) z) rest))))

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
                      (dim+ (dim-const (+ d1 d2)))))

   ;; TODO: subtraction rules

   (mul0 ()
         (dimeq (dim*)
                (dim-const 1)))

   (mul1 ((dimp x))
         (dimeq (dim* x)
                x))

   (mul3m ((dimp x)
           (dimp y)
           (dimp z)
           (dim-listp rest))
          (dimeq (dim-mul (list* x y z rest))
                 (dim-mul (cons (dim* (dim* x y) z) rest))))

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
            (dimeq (dim* 0 x)
                   x))

   (mul2-const ((natp d1)
                (natp d2))
               (dimeq (dim* (dim-const d1) (dim-const d2))
                      (dim* (dim-const (* d1 d2)))))))
