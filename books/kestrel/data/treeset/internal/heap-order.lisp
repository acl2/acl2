; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "kestrel/utilities/polarity" :dir :system)

(include-book "../hash-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/fixed-size-words/u32" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "../hash"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ heap<
  :parents (implementation)
  :short "A total order based on object hashes."
  :short "The total order used by @(tsee heapp)."
  :long
  (xdoc::topstring
    (xdoc::p
      "This order is determined primarily by the @(see hash) values of objects.
       Since the hashes may collide, we fall back to @(tsee <<) when the hashes
       are equal to ensure the order is total.")
    (xdoc::p
      "The goal of this order is to be largely uncorrelated with @(tsee <<).
       Therefore, it is important that the hash function (@(tsee hash::jenkins))
       does not collide frequently and exhibits a strong "
      (xdoc::a :href
               "https://en.wikipedia.org/wiki/Avalanche_effect"
               "avalanche effect")
      ".")
    (xdoc::@def "heap<$inline")
    (xdoc::@def "heap<"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define heap<-with-hashes
  (x
   y
   (hash-x (unsigned-byte-p 32 hash-x))
   (hash-y (unsigned-byte-p 32 hash-x)))
  :guard (mbe :logic (and (equal (hash x) hash-x)
                          (equal (hash y) hash-y))
              :exec (and (data::u32-equal (hash x) hash-x)
                         (data::u32-equal (hash y) hash-y)))
  (declare (type (unsigned-byte 32) hash-x hash-y)
           (xargs :type-prescription
                  (booleanp (heap<-with-hashes x y hash-x hash-y))))
  :short "Variant of @(tsee heap<) which uses pre-computed hashes."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically, this variant of @('heap<') just ignores the @('hash-x') and
      @('hash-y') arguments, but in execution, these hash values are used
      instead of calculated new hashe values. This may be more efficient when
      used to avoid recalculating hashes.")
   (xdoc::p
     "For instance, instead of @('(and (heap< x y) (heap< y z))'), one may
      do:")
   (xdoc::codeblock
     "(let ((hash-x (hash x))"
     "      (hash-y (hash y))"
     "      (hash-z (hash z)))"
     "  (and (heap< x y hash-x hash-y)"
     "       (heap< y z hash-y hash-z)))")
   (xdoc::p
     "This performs just one call of @('(hash y)') instead of two."))
  (mbe :logic (or (< (hash x) (hash y))
                  (and (equal (hash x) (hash y))
                       (<< x y)))
       :exec (or (< (the (unsigned-byte 32) hash-x)
                    (the (unsigned-byte 32) hash-y))
                 (and (data::u32-equal hash-x hash-y)
                      (<< x y))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal))))

(define heap< (x y)
  (declare (xargs :type-prescription (booleanp (heap< x y))))
  :parents nil
  (let ((hash-x (hash x))
        (hash-y (hash y)))
    (declare (type (unsigned-byte 32) hash-x hash-y))
    (heap<-with-hashes x y hash-x hash-y))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-irreflexive
  (not (heap< x x))
  :enable (heap<
           heap<-with-hashes
           data::<<-rules))

(defruled heap<-asymmetric
  (implies (heap< x y)
           (not (heap< y x)))
  :enable (heap<
           heap<-with-hashes
           data::<<-rules))

(defruled heap<-transitive
  (implies (and (heap< x y)
                (heap< y z))
           (heap< x z))
  :enable (heap<
           heap<-with-hashes
           data::<<-rules))

(defruled heap<-trichotomy
  (implies (and (not (heap< y x))
                (not (equal x y)))
           (heap< x y))
  :enable (heap<
           heap<-with-hashes
           data::<<-rules))

(defruled not-heap<-transitive
  (implies (and (not (heap< x y))
                (not (heap< y z)))
           (not (heap< x z)))
  :cases ((equal y z))
  :enable (heap<-transitive
           heap<-trichotomy))

;;;;;;;;;;;;;;;;;;;;

(defthy heap<-rules
  '(heap<-irreflexive
    heap<-asymmetric
    heap<-transitive
    heap<-trichotomy))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heap<-becomes-cases
  (equal (heap< x y)
         (and (not (equal x y))
              (not (heap< y x))))
  :use (:instance heap<-trichotomy
                  (x y)
                  (y x))
  :enable heap<-rules
  :disable heap<-trichotomy)

(defruled not-heap<-case-split
  (implies (syntaxp (acl2::want-to-strengthen (heap< x y)))
           ;; The LHS is misleading here. Using want-to-strengthen, we are
           ;; limiting ourselves to rewriting the negation of the LHS.
           (equal (heap< x y)
                  (and (not (equal x y))
                       (not (heap< y x)))))
  :by heap<-becomes-cases)

;;;;;;;;;;;;;;;;;;;;

(defthy heap<-expensive-rules
  '(heap<-rules
    not-heap<-case-split
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-with-hashes-becomes-heap<
  (equal (heap<-with-hashes x y hash-x hash-y)
         (heap< x y))
  :enable (heap<
           heap<-with-hashes))

(theory-invariant (incompatible! (:definition heap<$inline)
                                 (:rewrite heap<-with-hashes-becomes-heap<)))
