; Elliptic Curve Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "kestrel/isar/defisar" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk pfield-squarep (x p)
  :guard (and (integerp p) (fep x p))
  :returns (yes/no booleanp)
  :parents (elliptic-curves)
  :short "Check if a prime field element is a square."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is more general than elliptic curve libraries,
     but it finds some uses in elliptic curves over prime fields
     (perhaps this should be moved to the prime field library).
     We non-constructively check whether there exists
     a square root in the prime field.
     The witness function returns a root, if one exists."))
  (exists (r) (and (fep r p)
                   (equal (mul r r p) x)))
  :skolem-name pfield-square->root)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield-squarep-of-0
  (implies (posp p)
           (pfield-squarep 0 p))
  :enable fep
  :use (:instance pfield-squarep-suff (r 0) (x 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield-squarep-of-1
  (implies (and (posp p)
                (> p 1))
           (pfield-squarep 1 p))
  :enable fep
  :prep-books ((include-book "arithmetic-5/top" :dir :system))
  :use (:instance pfield-squarep-suff (r 1) (x 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule fep-of-pfield-square->root
  (implies (pfield-squarep x p)
           (fep (pfield-square->root x p) p))
  :enable pfield-squarep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule natp-of-pfield-square->root
  (implies (pfield-squarep x p)
           (natp (pfield-square->root x p)))
  :rule-classes (:type-prescription :rewrite)
  :enable pfield-squarep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Odd and even square roots.

(define-sk pfield-odd-squarep (x p)
  :guard (and (integerp p) (fep x p))
  :returns (yes/no booleanp)
  :parents (pfield-squarep)
  :short "Check if a prime field element is a square of an odd field element."
  :long
  (xdoc::topstring
   (xdoc::p
    "Same as pfield-squarep except restricts the root to be odd."))
  (exists (r) (and (fep r p)
                   (oddp r)
                   (equal (mul r r p) x)))
  :skolem-name pfield-square->odd-root)

(define-sk pfield-even-squarep (x p)
  :guard (and (integerp p) (fep x p))
  :returns (yes/no booleanp)
  :parents (pfield-squarep)
  :short "Check if a prime field element is a square of an even field element."
  :long
  (xdoc::topstring
   (xdoc::p
    "Same as pfield-squarep except restricts the root to be even."))
  (exists (r) (and (fep r p)
                   (evenp r)
                   (equal (mul r r p) x)))
  :skolem-name pfield-square->even-root)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield-squarep-of-inv
  :parents (pfield-squarep)
  :short "The inverse of @('x') is a prime field square iff @('x') is."
  (implies (and (rtl::primep p)
                (fep x p))
           (equal (pfield-squarep (inv x p) p)
                  (pfield-squarep x p)))
  :use (pfield-squarep-when-pfield-squarep-of-inv
        pfield-squarep-of-inv-when-pfield-squarep)

  :prep-lemmas

  (;; 'only if' part:

   (defruled pfield-squarep-when-pfield-squarep-of-inv
     (implies (and (rtl::primep p)
                   (fep x p)
                   (pfield-squarep (inv x p) p))
              (pfield-squarep x p))
     :cases ((equal x 0))

     :prep-lemmas

     ((defruled equal-of-inv-swap
        (implies (and (rtl::primep p)
                      (fep x p)
                      (fep y p)
                      (not (equal x 0))
                      (not (equal y 0)))
                 (equal (equal (inv x p) y)
                        (equal x (inv y p))))
        :prep-books
        ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

      (defruled inv-of-inv
        (implies (and (rtl::primep p)
                      (fep a p))
                 (equal (inv (inv a p) p)
                        a))
        :prep-books
        ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

      (acl2::defisar
       pfield-squarep-when-pfield-squarep-of-inv-and-not-zero
       (implies (and (rtl::primep p)
                     (fep x p)
                     (not (equal x 0))
                     (pfield-squarep (inv x p) p))
                (pfield-squarep x p))
       :proof
       ((:assume (:prime (rtl::primep p)))
        (:assume (:fep (fep x p)))
        (:assume (:nonzero (not (equal x 0))))
        (:assume (:inv-square (pfield-squarep (inv x p) p)))
        (:derive (:nonzero-inv (not (equal (inv x p) 0)))
         :from (:nonzero :prime :fep)
         :prep-books
         ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))
        (:let (r (pfield-square->root (inv x p) p)))
        (:derive (:1/x-is-rr (equal (inv x p) (mul r r p)))
         :from (:inv-square)
         :enable pfield-squarep)
        (:derive (:fep-root (fep r p))
         :from (:inv-square)
         :enable pfield-squarep)
        (:derive (:x-is-1/rr (equal x (inv (mul r r p) p)))
         :from (:1/x-is-rr :prime :fep :fep-root :nonzero :nonzero-inv)
         :use (:instance equal-of-inv-swap
               (y (mul (pfield-square->root (inv x p) p)
                       (pfield-square->root (inv x p) p)
                       p))))
        (:derive (:x-is-1/r-1/r (equal x (mul (inv r p) (inv r p) p)))
         :from (:1/x-is-rr :prime :fep :nonzero)
         :use (:instance pfield::inv-of-mul
               (x (pfield-square->root (inv x p) p))
               (y (pfield-square->root (inv x p) p))
               (p p))
         :enable inv-of-inv
         :disable (pfield::inv-of-mul pfield::inv-of-inv)
         :prep-books
         ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))
        (:derive (:conclusion (pfield-squarep x p))
         :from (:x-is-1/r-1/r :fep-root :prime)
         :use (:instance pfield-squarep-suff
               (r (inv (pfield-square->root (inv x p) p) p))))
        (:qed)))))

   ;; 'if' part:

   (defruled pfield-squarep-of-inv-when-pfield-squarep
     (implies (and (rtl::primep p)
                   (fep x p)
                   (pfield-squarep x p))
              (pfield-squarep (inv x p) p))
     :cases ((equal x 0))

     :prep-lemmas

     ((defrule pfield-squarep-of-inv-when-pfield-squarep-when-not-zero
        (implies (and (rtl::primep p)
                      (fep x p)
                      (not (equal x 0))
                      (pfield-squarep x p))
                 (pfield-squarep (inv x p) p))
        :expand (pfield-squarep x p)
        :use (:instance pfield-squarep-suff
              (x (inv x p))
              (r (inv (pfield-square->root x p) p)))
        :prep-books
        ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

      (defrule pfield-squarep-of-inv-of-0
        (implies (rtl::primep p)
                 (pfield-squarep (inv 0 p) p))
        :cases ((equal p 2))
        :prep-books
        ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))))))
