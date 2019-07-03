; Cryptographic Library
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

(defxdoc+ secp256k1-interface
  :parents (interfaces)
  :short "Elliptic curve secp256k1 interface."
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
    "Currently this interface actually includes several concrete definitions.
     Eventually these may be moved somewhere else,
     or replaced with more abstract, constrained functions."))
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
  (xdoc::topstring-p
   "Points consist of two coordinates that are elements of the field.
    We do not require the point to be on the curve for now.")
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
  :short "ECDSA deterministic signature with public key recovery."
  :long
  (xdoc::topstring
   (xdoc::p
    "ECDSA signatures are specified in "
    (xdoc::a :href "http://www.secg.org/sec1-v2.pdf"
      "Standards for Efficient Cryptography 1 (SEC 1)")
    " in general, and their deterministic version is specified in the "
    (xdoc::a :href "https://tools.ietf.org/html/rfc6979" "RFC 6979 standard")
    ". The public key recovery aspects are also described in SEC 1.")
   (xdoc::p
    "ECDSA, as specified in SEC 1, relies on
     a randomly generated ephemeral private key for each signature.
     RFC 6979 describes a procedure to generate
     a deterministic but unpredictable ephemeral private key
     (from the message and the signing key),
     which can be considered indistinguishable from a random one.
     The details of this are unimportant for the interface introduced here,
     but the point is that,
     since the ephemeral private key is deterministically generated,
     the constrained ACL2 function introduced here requires
     no additional inputs related to the random generation of
     the ephemeral private key.")
   (xdoc::p
    "ECDSA is parameterized over a hash function applied to the message
     prior to the creation of the signature.
     To avoid this explicit dependency in our ACL2 function,
     we have it take as input a hash of the message instead of the message:
     this sidesteps the choice of the hash function,
     providing the ability to sign messages
     that are hashed by external means.")
   (xdoc::p
    "According to RFC 6979,
     the same hash function is used as part of the procedure
     to deterministically generate the ephemeral private key.
     Mathematically speaking,
     one could well use a different hash function though.
     For now, our constrained ACL2 function is agnostic
     in regard to the RFC 6979 hash function,
     and can be in fact made executable via attachments
     that pick different hash functions.")
   (xdoc::p
    "An ECDSA signature consists of a pair @($(r,s)$)
     of positive integers below the order @($n$) of the curve.
     This suffices to verify the signature against a known public key.
     As explained in SEC 1 Section 4.1.6, given a signature @($(r,s)$),
     there is generally a small number of possible public keys,
     all of which can be inferred from the signature;
     for the secp256k1 curve, there are at most four possibilities.
     Thus, by enhancing the signature @($(r,s)$)
     with a little additional information,
     it is possible to recover the public key from the enhanced signature.
     This information can be structured as (see SEC 1 Section 4.1.6)
     (i) the index @($j$) of the @($x$) coordinate of the point @($R$) and
     (ii) the parity of the @($y$) coordinate of the point @($R$).
     So our constrained function returns these (see below).")
   (xdoc::p
    "An ECDSA signature may involve the generation of successive
     random or (random-looking) deterministic ephemeral private keys
     until valid @($(r,s)$) are found.
     This ``looping'' feature can be exploited
     to put additional constraints on the signature or recovery information.
     For instance,
     one could require the aforementioned recovery index @($j$) to be always 0,
     which is equivalent to saying that
     @($r$) is the @($x$) coordinate of @($R$)
     (in general it is @($x \mod n$));
     this condition is almost always satisfied,
     because there is a comparatively very small number of values
     between the order @($n$) and the prime @($p$).
     Thus, our constrained function has an additional input flag
     that says whether the @($x$) coordinate of @($R$) should be ``small'',
     i.e. below @($n$).")
   (xdoc::p
    "If @($(r,s)$) is a signature, @($(r,-s)$) is an equivalent signature,
     where the negation is modulo @($n$).
     This fact can be used by requiring that the @($s$) signature component
     be always below @($n/2$),
     which can be achieved simply by generating @($(r,s$))
     and then flipping @($s$) if needed.
     To support this use case,
     our constrained function has an additional input flag
     that says whether @($s$) should be ``small'', i.e. below @($n/2$).")
   (xdoc::p
    "To summarize, our constrained function takes as inputs
     a hash (a list of bytes), a private key, and two boolean flags,
     as formalized by the guard.")
   (xdoc::p
    "The function returns as outputs:
     an error flag, constrained to be a boolean;
     a public key recovery @($x$) index, constrained to be a natural number
     (this is always 0 if the @('small-x?') flag is @('t'),
     but we do not capture this constraint here);
     a public key recovery @($y$) parity, constrained to be a boolean;
     the signature value @($r$), constrained to be a field element;
     and the signature value @($s$), constrained to be a field element.
     The latter two results are always positive and below the order @($n$),
     but for now we use the field type for simplicity.
     The error flag is @('t') when the signature operation fails,
     due to the repeated inability of deterministically finding
     an ephemeral private key that produces valid results;
     this is believe essentially impossible
     with just a few repetitions available,
     but the mathematical possibility remains.
     If the error flag is @('t'), the other results are irrelevant.")
   (xdoc::p
    "We constrain this function
     to return results of the types described above unconditionally.
     We also constrain it to fix its arguments to the guard types."))

  (encapsulate

    (((secp256k1-sign * * * *) => (mv * * * * *)
      :formals (hash priv small-x? small-s?)
      :guard (and (byte-listp hash)
                  (secp256k1-priv-key-p priv)
                  (booleanp small-x?)
                  (booleanp small-s?))))

    (local
     (defun secp256k1-sign (hash priv small-x? small-s?)
       (declare (ignore hash priv small-x? small-s?))
       (mv nil 0 nil 1 1)))

    (defrule booleanp-of-mv-nth-0-secp256k1-sign
      (booleanp (mv-nth 0 (secp256k1-sign hash priv small-x? small-s?))))

    (defrule natp-of-mv-nth-1-secp256k1-sign
      (natp (mv-nth 1 (secp256k1-sign hash priv small-x? small-s?))))

    (defrule booleanp-of-mv-nth-2-secp256k1-sign
      (booleanp (mv-nth 2 (secp256k1-sign hash priv small-x? small-s?))))

    (defrule secp256k1-fieldp-of-mv-nth-3-secp256k1-sign
      (secp256k1-fieldp
       (mv-nth 3 (secp256k1-sign hash priv small-x? small-s?))))

    (defrule secp256k1-fieldp-of-mv-nth-4-secp256k1-sign
      (secp256k1-fieldp
       (mv-nth 4 (secp256k1-sign hash priv small-x? small-s?))))

    (defrule secp256k1-sign-fixes-input-hash
      (equal (secp256k1-sign (byte-list-fix hash) priv small-x? small-s?)
             (secp256k1-sign hash priv small-x? small-s?)))

    (defrule secp256k1-sign-fixes-input-priv
      (equal (secp256k1-sign hash (secp256k1-priv-key-fix priv)
                             small-x? small-s?)
             (secp256k1-sign hash priv small-x? small-s?)))

    (defrule secp256k1-sign-fixes-input-small-x?
      (equal (secp256k1-sign hash priv (bool-fix small-x?) small-s?)
             (secp256k1-sign hash priv small-x? small-s?)))

    (defrule secp256k1-sign-fixes-input-small-s?
      (equal (secp256k1-sign hash priv small-x? (bool-fix small-s?))
             (secp256k1-sign hash priv small-x? small-s?))))

  (defcong byte-list-equiv equal
    (secp256k1-sign hash priv small-x? small-s?) 1
    :hints (("Goal"
             :use (secp256k1-sign-fixes-input-hash
                   (:instance secp256k1-sign-fixes-input-hash
                    (hash acl2::hash-equiv)))
             :in-theory (disable secp256k1-sign-fixes-input-hash))))

  (defcong secp256k1-priv-key-equiv equal
    (secp256k1-sign hash priv small-x? small-s?) 2
    :hints (("Goal"
             :use (secp256k1-sign-fixes-input-priv
                   (:instance secp256k1-sign-fixes-input-priv
                    (priv priv-equiv)))
             :in-theory (disable secp256k1-sign-fixes-input-priv))))

  (defcong iff equal (secp256k1-sign hash priv small-x? small-s?) 3
    :hints (("Goal"
             :use (secp256k1-sign-fixes-input-small-x?
                   (:instance secp256k1-sign-fixes-input-small-x?
                    (small-x? acl2::small-x?-equiv)))
             :in-theory (disable secp256k1-sign-fixes-input-small-x?))))

  (defcong iff equal (secp256k1-sign hash priv small-x? small-s?) 4
    :hints (("Goal"
             :use (secp256k1-sign-fixes-input-small-s?
                   (:instance secp256k1-sign-fixes-input-small-s?
                    (small-s? acl2::small-s?-equiv)))
             :in-theory (disable secp256k1-sign-fixes-input-small-s?)))))
