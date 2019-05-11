; Cryptography -- secp256k1 Placeholder
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/utilities/bytes-as-digits" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ secp256k1-placeholder
  :parents (placeholders)
  :short "Elliptic curve secp256k1 placeholder."
  :long
  (xdoc::topstring
   (xdoc::p
    "The secp256k1 elliptic curve is specified in
     <a href=\"http://www.secg.org/sec1-v2.pdf\"
     >Standards for Efficient Cryptography 1 (SEC 1)</a>
     and
     <a href=\"http://www.secg.org/sec2-v2.pdf\"
     >Standards for Efficient Cryptography 2 (SEC 2)</a>."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-prime ()
  :short "The prime @($p$) of the field of the curve."
  #xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
  :no-function t
  ///
  (assert-event (equal (integer-length (secp256k1-prime)) 256)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-field
  :short "Fixtype of the elements of the field."
  :long
  (xdoc::topstring-p
   "These are natural numbers below @($p$).")

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
        :rule-classes :tau-system)))

  (define secp256k1-field-fix ((x secp256k1-fieldp))
    :returns (fixed-x secp256k1-fieldp)
    :parents (secp256k1-field)
    :short "Fixer for @(tsee secp256k1-field)."
    (mbe :logic (if (secp256k1-fieldp x) x 0)
         :exec x)
    :no-function t
    ///

    (defrule secp256k1-field-fix-when-secp256k1-fieldp
      (implies (secp256k1-fieldp x)
               (equal (secp256k1-field-fix x)
                      x))))

  (fty::deffixtype secp256k1-field
    :pred secp256k1-fieldp
    :fix secp256k1-field-fix
    :equiv secp256k1-field-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod secp256k1-point
  :short "Fixtype of points on the curve."
  :long
  "<p>
   Points consist of two coordinates that are elements of the field.
   We do not require the point to be on the curve for now.
   </p>"
  ((x secp256k1-field)
   (y secp256k1-field))
  :pred secp256k1-pointp
  :layout :list
  :xvar p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-infinityp ((point secp256k1-pointp))
  :returns (yes/no booleanp)
  :short "Check if a point is
          the point at infinity @($\\mathcal{O}$) of the curve."
  (and (equal (secp256k1-point->x point) 0)
       (equal (secp256k1-point->y point) 0))
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-generator ()
  :short "The generator @($G$) of the group of the curve."
  (secp256k1-point
   #x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
   #x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
  :no-function t
  ///
  (assert-event (secp256k1-fieldp (secp256k1-point->x (secp256k1-generator))))
  (assert-event (secp256k1-fieldp (secp256k1-point->y (secp256k1-generator)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-order ()
  :short "The order @($n$) of the group of the curve."
  #xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
  :no-function t
  ///
  (assert-event (equal (integer-length (secp256k1-order)) 256)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-priv-key
  :short "Fixtype of private keys."
  :long
  (xdoc::topstring-p
   "A private key is a positive integer below @($n$).")

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
        :rule-classes :tau-system)))

  (define secp256k1-priv-key-fix ((x secp256k1-priv-key-p))
    :returns (fixed-x secp256k1-priv-key-p)
    :parents (secp256k1-priv-key)
    :short "Fixer for @(tsee secp256k1-priv-key)."
    (mbe :logic (if (secp256k1-priv-key-p x) x 1)
         :exec x)
    :no-function t
    ///

    (defrule secp256k1-priv-key-fix-when-secp256k1-priv-key-p
      (implies (secp256k1-priv-key-p x)
               (equal (secp256k1-priv-key-fix x)
                      x))))

  (fty::deffixtype secp256k1-priv-key
    :pred secp256k1-priv-key-p
    :fix secp256k1-priv-key-fix
    :equiv secp256k1-priv-key-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-pub-key
  :short "Fixtype of public keys."
  :long
  (xdoc::topstring-p
   "A public key is a point that is not the point at infinity.")

  (define secp256k1-pub-key-p (x)
    :returns (yes/no booleanp)
    :parents (secp256k1-pub-key)
    :short "Recognizer for @(tsee secp256k1-pub-key)."
    (and (secp256k1-pointp x)
         (not (secp256k1-infinityp x)))
    :no-function t
    ///

    (defrule secp256k1-pointp-when-secp256k1-pub-key-p
      (implies (secp256k1-pub-key-p x)
               (secp256k1-pointp x))))

  (define secp256k1-pub-key-fix ((x secp256k1-pub-key-p))
    :returns (fixed-x secp256k1-pub-key-p)
    :parents (secp256k1-pub-key)
    :short "Fixer for @(tsee secp256k1-pub-key)."
    (mbe :logic (if (secp256k1-pub-key-p x) x (secp256k1-point 1 1))
         :exec x)
    :no-function t
    ///

    (defrule secp256k1-pub-key-fix-when-secp256k1-pub-key-p
      (implies (secp256k1-pub-key-p x)
               (equal (secp256k1-pub-key-fix x)
                      x))))

  (fty::deffixtype secp256k1-pub-key
    :pred secp256k1-pub-key-p
    :fix secp256k1-pub-key-fix
    :equiv secp256k1-pub-key-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-add
  :short "Addition of two points on the curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not require the points to be on the curve,
     but just to be two points with coordinates in the field,
     as formalized by the guard.")
   (xdoc::p
    "We constrain this function to return a point unconditionally.")
   (xdoc::p
    "We also constrain this function to fix its arguments to points."))

  (encapsulate

    (((secp256k1-add * *) => *
      :formals (point1 point2)
      :guard (and (secp256k1-pointp point1)
                  (secp256k1-pointp point2))))

    (local
     (defun secp256k1-add (point1 point2)
       (declare (ignore point1 point2))
       (secp256k1-point 0 0)))

    (defrule secp256k1-pointp-of-secp256k1-add
      (secp256k1-pointp (secp256k1-add point1 point2)))

    (defrule secp256k1-fixes-input-point1
      (equal (secp256k1-add (secp256k1-point-fix point1) point2)
             (secp256k1-add point1 point2)))

    (defrule secp256k1-fixes-input-point2
      (equal (secp256k1-add point1 (secp256k1-point-fix point2))
             (secp256k1-add point1 point2))))

  (defcong secp256k1-point-equiv equal (secp256k1-add point1 point2) 1
    :hints (("Goal"
             :use (secp256k1-fixes-input-point1
                   (:instance secp256k1-fixes-input-point1
                    (point1 point1-equiv)))
             :in-theory (disable secp256k1-fixes-input-point1))))

  (defcong secp256k1-point-equiv equal (secp256k1-add point1 point2) 2
    :hints (("Goal"
             :use (secp256k1-fixes-input-point2
                   (:instance secp256k1-fixes-input-point2
                    (point2 point2-equiv)))
             :in-theory (disable secp256k1-fixes-input-point2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-mul
  :short "Multiplication of a point on the curve by a number."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not require the point to be on the curve,
     but just to have coordinates in the field,
     as formalized by the guard.")
   (xdoc::p
    "The number is a natural number, as formalized by the guard.")
   (xdoc::p
    "We constrain this function to return a point unconditionally.")
   (xdoc::p
    "We also constrain this function to fix its arguments
     to a natural number and to a point.")
   (xdoc::p
    "Furthermore, we constrain this function to return a public key
     (i.e. not the point at infinity)
     when the number is a private key and the point is the generator.
     This is because, since @($n$) is the order of the group
     and @($G$) is not the point at infinity,
     @($kG$) cannot be the point at infinity when @($0 < k < n$)."))

  (encapsulate

    (((secp256k1-mul * *) => *
      :formals (nat point)
      :guard (and (natp nat) (secp256k1-pointp point))))

    (local
     (defun secp256k1-mul (nat point)
       (declare (ignore nat point))
       (secp256k1-point 1 1)))

    (defrule secp256k1-pointp-of-secp256k1-mul
      (secp256k1-pointp (secp256k1-mul nat point)))

    (defrule secp256k1-fixes-input-nat
      (equal (secp256k1-mul (nfix nat) point)
             (secp256k1-mul nat point)))

    (defrule secp256k1-fixes-input-point
      (equal (secp256k1-mul nat (secp256k1-point-fix point))
             (secp256k1-mul nat point)))

    (defrule secp256k1-pub-key-p-of-mul-when-priv-key-p
      (implies (and (secp256k1-priv-key-p k)
                    (equal point (secp256k1-generator)))
               (secp256k1-pub-key-p (secp256k1-mul k point)))))

  (defcong nat-equiv equal (secp256k1-mul nat point) 1
    :event-name nat-equiv-implies-equal-secp256k1-mul-1
    :hints (("Goal"
             :use (secp256k1-fixes-input-nat
                   (:instance secp256k1-fixes-input-nat (nat nat-equiv)))
             :in-theory (disable secp256k1-fixes-input-nat))))

  (defcong secp256k1-point-equiv equal (secp256k1-mul nat point) 2
    :hints (("Goal"
             :use (secp256k1-fixes-input-point
                   (:instance secp256k1-fixes-input-point (point point-equiv)))
             :in-theory (disable secp256k1-fixes-input-point)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-priv-to-pub ((priv secp256k1-priv-key-p))
  :returns (pub secp256k1-pub-key-p)
  :short "Calculate a public key from a private key."
  :long
  (xdoc::topstring-p
   "This consists in multiplying the generator by the private key.")
  (b* ((priv (mbe :logic (secp256k1-priv-key-fix priv) :exec priv))
       (pub (secp256k1-mul priv (secp256k1-generator))))
    pub)
  :no-function t
  :hooks (:fix)
  ///
  (in-theory (disable (:e secp256k1-priv-to-pub))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-point-to-bytes ((point secp256k1-pointp)
                                  (compressp booleanp))
  :returns (bytes byte-listp)
  :short "Represent a point in compressed or uncompressed form."
  :long
  (xdoc::topstring-p
   "This is specified in Section 2.3.3 of SEC 1.")
  (b* (((secp256k1-point point) point))
    (cond ((secp256k1-infinityp point) (list 0))
          (compressp (cons (if (evenp point.y) 2 3)
                           (nat=>bebytes 32 point.x)))
          (t (cons 4 (append (nat=>bebytes 32 point.x)
                             (nat=>bebytes 32 point.y))))))
  :no-function t
  :hooks (:fix)
  ///

  (defrule len-of-secp256k1-point-to-bytes
    (equal (len (secp256k1-point-to-bytes point compressp))
           (cond ((secp256k1-infinityp point) 1)
                 (compressp 33)
                 (t 65)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-sign
  :short "Signature operation (ECDSA)."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we assume that this signing operation
     is deterministic (according to RFC 6979),
     operates on a hash (of a message),
     and returns a boolean to recover the public key.
     Other variants exist,
     but this is just a placeholder.")
   (xdoc::p
    "This constrained function takes as inputs
     a hash (a list of bytes) and a private key,
     as formalized by the guard.
     Since there are no additional inputs,
     the signature operation has to be deterministic.")
   (xdoc::p
    "The function returns as outputs:
     an error flag, constrained to be a boolean;
     a public key recovery flag, constrained to be a boolean;
     the signature value @($r$), constrained to be a field element;
     and the signature value @($s$), constrained to be a field element.
     The error flag is motivated by the fact that,
     given a deterministic choice of the ephemeral private key @($k$),
     the calculation of the signature may fail:
     the flag is @('t') if the operation fails, otherwise @('nil');
     in the former case, the other results have irrelevant values.
     The public key recovery flag is assumed to describe
     the parity of the @($y$) coordinate of the @($R$) point:
     @('t') if even, @('nil') if odd.
     The other two results are always
     non-zero natural numbers below the order @($n$) of the curve,
     but they also happen to be field elements,
     which is adequate for the purpose of this placeholder.")
   (xdoc::p
    "We constrain this function
     to return results of the types described above unconditionally.
     We also constrain it to fix its arguments to the guard types."))

  (encapsulate

    (((secp256k1-sign * *) => (mv * * * *)
      :formals (hash priv)
      :guard (and (byte-listp hash)
                  (secp256k1-priv-key-p priv))))

    (local
     (defun secp256k1-sign (hash priv)
       (declare (ignore hash priv))
       (mv nil t 1 1)))

    (defrule booleanp-of-mv-nth-0-secp256k1-sign
      (booleanp (mv-nth 0 (secp256k1-sign hash priv))))

    (defrule booleanp-of-mv-nth-1-secp256k1-sign
      (booleanp (mv-nth 1 (secp256k1-sign hash priv))))

    (defrule secp256k1-fieldp-of-mv-nth-2-secp256k1-sign
      (secp256k1-fieldp (mv-nth 2 (secp256k1-sign hash priv))))

    (defrule secp256k1-fieldp-of-mv-nth-3-secp256k1-sign
      (secp256k1-fieldp (mv-nth 3 (secp256k1-sign hash priv))))

    (defrule secp256k1-sign-fixes-input-hash
      (equal (secp256k1-sign (byte-list-fix hash) priv)
             (secp256k1-sign hash priv)))

    (defrule secp256k1-sign-fixes-input-priv
      (equal (secp256k1-sign hash (secp256k1-priv-key-fix priv))
             (secp256k1-sign hash priv))))

  (defcong byte-list-equiv equal (secp256k1-sign hash priv) 1
    :hints (("Goal"
             :use (secp256k1-sign-fixes-input-hash
                   (:instance secp256k1-sign-fixes-input-hash
                    (hash acl2::hash-equiv)))
             :in-theory (disable secp256k1-sign-fixes-input-hash))))

  (defcong secp256k1-priv-key-equiv equal (secp256k1-sign hash priv) 2
    :hints (("Goal"
             :use (secp256k1-sign-fixes-input-priv
                   (:instance secp256k1-sign-fixes-input-priv
                    (priv priv-equiv)))
             :in-theory (disable secp256k1-sign-fixes-input-priv)))))
