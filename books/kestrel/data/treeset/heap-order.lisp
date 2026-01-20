; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
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

(include-book "total-order")
(include-book "hash")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;; (local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable <<-rules)))

(std::make-define-config
  :no-function t)

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
       Therefore, it is important that the hash function (@(tsee jenkins-hash))
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


(define heap<-with-hashes (x y hash-x hash-y)
  :guard (and (unsigned-byte-p 32 hash-x)
              (unsigned-byte-p 32 hash-y)
              (int= (hash x) hash-x)
              (int= (hash y) hash-y))
  (declare (type (unsigned-byte 32) hash-x)
           (type (unsigned-byte 32) hash-y)
           (xargs :type-prescription
                  (booleanp (heap<-with-hashes x y hash-x hash-y)))
           (optimize (speed 3) (safety 0)))
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
                       ;; (if (equal (mod (hash x) 2) 0)
                       ;;     (<< x y)
                       ;;   (<< y x))
                       (<< x y)
                       ))
       :exec (or (< hash-x hash-y)
                 (and (int= hash-x hash-y)
                      ;; We could opt to change direction of << based on the
                      ;; hash value, but collisions occur so rarely that it
                      ;; does not seem to matter.
                      ;; (if (int= (mod hash-x 2) 0)
                      ;;     (<< x y)
                      ;;   (<< y x))
                      (<< x y)
                      )))
  :inline t)

(define heap< (x y)
  (declare (xargs :type-prescription (booleanp (heap< x y)))
           (optimize (speed 3) (safety 0)))
  :parents nil
  (let ((hash-x (hash x))
        (hash-y (hash y)))
    (declare (type (unsigned-byte 32) hash-x)
             (type (unsigned-byte 32) hash-y))
    (heap<-with-hashes x y hash-x hash-y))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-irreflexive
  (not (heap< x x))
  :enable (heap<
           heap<-with-hashes
           <<-rules))

(defruled heap<-asymmetric
  (implies (heap< x y)
           (not (heap< y x)))
  :enable (heap<
           heap<-with-hashes
           <<-rules))

(defruled heap<-transitive
  (implies (and (heap< x y)
                (heap< y z))
           (heap< x z))
  :enable (heap<
           heap<-with-hashes
           <<-rules))

(defruled heap<-trichotomy
  (implies (and (not (heap< y x))
                (not (equal x y)))
           (heap< x y))
  :enable (heap<
           heap<-with-hashes
           <<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-with-hashes-becomes-heap<
  (equal (heap<-with-hashes x y hash-x hash-y)
         (heap< x y))
  :enable (heap<
           heap<-with-hashes))

(theory-invariant (incompatible! (:definition heap<$inline)
                                 (:rewrite heap<-with-hashes-becomes-heap<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy heap<-rules
  '(heap<-irreflexive
    heap<-asymmetric
    heap<-transitive
    heap<-trichotomy))
