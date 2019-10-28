; Elliptic Curve Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "secp256k1-domain-parameters")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/utilities/bytes-as-digits" :dir :system)
(include-book "kestrel/std/util/deffixer" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ secp256k1-types
  :parents (elliptic-curves)
  :short "Types for the secp256k1 elliptic curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "The secp256k1 elliptic curve is specified in "
    (xdoc::a :href "http://www.secg.org/sec1-v2.pdf"
      "Standards for Efficient Cryptography 1 (SEC 1)")
    " and "
    (xdoc::a :href "http://www.secg.org/sec2-v2.pdf"
      "Standards for Efficient Cryptography 2 (SEC 2)")
    ".")
   (xdoc::p
    "Here we introduce "
    (xdoc::seetopic "fty::fty" "fixtypes")
    " for field elements, point, and keys,
     along with an operation to represent points as byte lists."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-field
  :short "Fixtype of the elements of the secp256k1 field."
  :long
  (xdoc::topstring-p
   "These are natural numbers below the prime @($p$).")

  (define secp256k1-fieldp (x)
    :returns (yes/no booleanp)
    :parents (secp256k1-field)
    :short "Recognizer for @(tsee secp256k1-field)."
    (integer-range-p 0 (secp256k1-prime) x)
    :no-function t
    ///

    (make-event ; to avoid expanding SECP256K1-PRIME manually
     `(defrule natp-and-below-prime-when-secp256k1-fieldp
        (implies (secp256k1-fieldp x)
                 (and (natp x)
                      (< x ,(secp256k1-prime))))
        :rule-classes :tau-system
        :enable secp256k1-prime)))

  (std::deffixer secp256k1-field-fix
    :pred secp256k1-fieldp
    :body-fix 0
    :parents (secp256k1-field)
    :short "Fixer for @(tsee secp256k1-field).")

  (fty::deffixtype secp256k1-field
    :pred secp256k1-fieldp
    :fix secp256k1-field-fix
    :equiv secp256k1-field-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod secp256k1-point
  :short "Fixtype of points on the secp256k1 curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "Points consist of two coordinates that are elements of the field.
     We do not require the point to be on the curve for now.")
   (xdoc::p
    "Since the point @($(0,0)$) does not satisfy the curve equation,
     it can be used to represent the point at infinity
     (see @(tsee secp256k1-point-infinityp)."))
  ((x secp256k1-field)
   (y secp256k1-field))
  :pred secp256k1-pointp
  :layout :list
  :xvar p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-point-infinityp ((point secp256k1-pointp))
  :returns (yes/no booleanp)
  :short "Check if a secp256k1 point is
          the point at infinity @($\\mathcal{O}$) of the curve."
  (and (equal (secp256k1-point->x point) 0)
       (equal (secp256k1-point->y point) 0))
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-point-generator ()
  :short "The generator point @($G$) of the group of the secp256k1 curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "This puts the two coordinates (defined as domain parameters)
     into a point."))
  (secp256k1-point
   (secp256k1-generator-x)
   (secp256k1-generator-y))
  :guard-hints (("Goal" :in-theory (enable secp256k1-generator-x
                                           secp256k1-generator-y)))
  :no-function t
  ///
  (assert-event
   (secp256k1-fieldp (secp256k1-point->x (secp256k1-point-generator))))
  (assert-event
   (secp256k1-fieldp (secp256k1-point->y (secp256k1-point-generator)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-priv-key
  :short "Fixtype of secp256k1 private keys."
  :long
  (xdoc::topstring-p
   "A private key is a positive integer below the order @($n$).")

  (define secp256k1-priv-key-p (x)
    :returns (yes/no booleanp)
    :parents (secp256k1-priv-key)
    :short "Recognizer for @(tsee secp256k1-priv-key)."
    (integer-range-p 1 (secp256k1-order) x)
    :no-function t
    ///

    (make-event ; to avoid expanding SECP256K1-ORDER manually
     `(defrule posp-and-below-order-when-secp256k1-priv-key-p
        (implies (secp256k1-priv-key-p privkey)
                 (and (posp privkey)
                      (< privkey ,(secp256k1-order))))
        :rule-classes :tau-system
        :enable secp256k1-order)))

  (std::deffixer secp256k1-priv-key-fix
    :pred secp256k1-priv-key-p
    :body-fix 1
    :parents (secp256k1-priv-key)
    :short "Fixer for @(tsee secp256k1-priv-key).")

  (fty::deffixtype secp256k1-priv-key
    :pred secp256k1-priv-key-p
    :fix secp256k1-priv-key-fix
    :equiv secp256k1-priv-key-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-pub-key
  :short "Fixtype of secp256k1 public keys."
  :long
  (xdoc::topstring-p
   "A public key is a point that is not the point at infinity.")

  (define secp256k1-pub-key-p (x)
    :returns (yes/no booleanp)
    :parents (secp256k1-pub-key)
    :short "Recognizer for @(tsee secp256k1-pub-key)."
    (and (secp256k1-pointp x)
         (not (secp256k1-point-infinityp x)))
    :no-function t
    ///

    (defrule secp256k1-pointp-when-secp256k1-pub-key-p
      (implies (secp256k1-pub-key-p x)
               (secp256k1-pointp x))))

  (std::deffixer secp256k1-pub-key-fix
    :pred secp256k1-pub-key-p
    :body-fix (secp256k1-point 1 1)
    :parents (secp256k1-pub-key)
    :short "Fixer for @(tsee secp256k1-pub-key).")

  (fty::deffixtype secp256k1-pub-key
    :pred secp256k1-pub-key-p
    :fix secp256k1-pub-key-fix
    :equiv secp256k1-pub-key-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-point-to-bytes ((point secp256k1-pointp)
                                  (compressp booleanp))
  :returns (bytes byte-listp)
  :short "Represent a secp256k1 point in compressed or uncompressed form."
  :long
  (xdoc::topstring-p
   "This is specified in Section 2.3.3 of SEC 1.")
  (b* (((secp256k1-point point) point))
    (cond ((secp256k1-point-infinityp point) (list 0))
          (compressp (cons (if (evenp point.y) 2 3)
                           (nat=>bebytes 32 point.x)))
          (t (cons 4 (append (nat=>bebytes 32 point.x)
                             (nat=>bebytes 32 point.y))))))
  :no-function t
  :hooks (:fix)
  ///

  (defrule len-of-secp256k1-point-to-bytes
    (equal (len (secp256k1-point-to-bytes point compressp))
           (cond ((secp256k1-point-infinityp point) 1)
                 (compressp 33)
                 (t 65)))))
