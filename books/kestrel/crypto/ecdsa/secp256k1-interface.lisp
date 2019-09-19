; Elliptic Curve Digital Signature Algorithm Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECDSA")

(include-book "kestrel/crypto/ecurve/secp256k1-types" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ secp256k1-ecdsa-interface
  :parents (crypto::interfaces elliptic-curve-digital-signature-algorithm)
  :short (xdoc::topstring
          "ECDSA "
          (xdoc::seetopic "crypto::interfaces" "interface")
          " for the elliptic curve secp256k1.")
  :long
  (xdoc::topstring
   (xdoc::p
    "ECDSA signatures and the secp256k1 elliptic curve are specified in "
    (xdoc::a :href "http://www.secg.org/sec1-v2.pdf"
      "Standards for Efficient Cryptography 1 (SEC 1)")
    " and "
    (xdoc::a :href "http://www.secg.org/sec2-v2.pdf"
      "Standards for Efficient Cryptography 2 (SEC 2)")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-sign-det-rec
  :short "ECDSA deterministic signature with public key recovery for secp256k1."
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
     We also constrain it to fix its arguments to the guard types.")
   (xdoc::p
    "See also:"
    (xdoc::ul
     (xdoc::li (xdoc::seetopic "ecdsa::deterministic-ecdsa-secp256k1" "Deterministic ECDSA executable specification"))
     (xdoc::li (xdoc::seetopic "ecdsa::secp256k1-ecdsa-attachment" "attaching Deterministic ECDSA executable specification to this interface")))))

  (encapsulate

    (((secp256k1-sign-det-rec * * * *) => (mv * * * * *)
      :formals (hash priv small-x? small-s?)
      :guard (and (byte-listp hash)
                  (secp256k1-priv-key-p priv)
                  (booleanp small-x?)
                  (booleanp small-s?))))

    (local
     (defun secp256k1-sign-det-rec (hash priv small-x? small-s?)
       (declare (ignore hash priv small-x? small-s?))
       (mv nil 0 nil 1 1)))

    (defrule booleanp-of-mv-nth-0-secp256k1-sign-det-rec
      (booleanp
       (mv-nth 0 (secp256k1-sign-det-rec hash priv small-x? small-s?))))

    (defrule natp-of-mv-nth-1-secp256k1-sign-det-rec
      (natp (mv-nth 1 (secp256k1-sign-det-rec hash priv small-x? small-s?))))

    (defrule booleanp-of-mv-nth-2-secp256k1-sign-det-rec
      (booleanp
       (mv-nth 2 (secp256k1-sign-det-rec hash priv small-x? small-s?))))

    (defrule secp256k1-fieldp-of-mv-nth-3-secp256k1-sign-det-rec
      (secp256k1-fieldp
       (mv-nth 3 (secp256k1-sign-det-rec hash priv small-x? small-s?))))

    (defrule secp256k1-fieldp-of-mv-nth-4-secp256k1-sign-det-rec
      (secp256k1-fieldp
       (mv-nth 4 (secp256k1-sign-det-rec hash priv small-x? small-s?))))

    (defrule secp256k1-sign-det-rec-fixes-input-hash
      (equal (secp256k1-sign-det-rec (byte-list-fix hash) priv
                                     small-x? small-s?)
             (secp256k1-sign-det-rec hash priv small-x? small-s?)))

    (defrule secp256k1-sign-det-rec-fixes-input-priv
      (equal (secp256k1-sign-det-rec hash (secp256k1-priv-key-fix priv)
                                     small-x? small-s?)
             (secp256k1-sign-det-rec hash priv small-x? small-s?)))

    (defrule secp256k1-sign-det-rec-fixes-input-small-x?
      (equal (secp256k1-sign-det-rec hash priv (bool-fix small-x?) small-s?)
             (secp256k1-sign-det-rec hash priv small-x? small-s?)))

    (defrule secp256k1-sign-det-rec-fixes-input-small-s?
      (equal (secp256k1-sign-det-rec hash priv small-x? (bool-fix small-s?))
             (secp256k1-sign-det-rec hash priv small-x? small-s?))))

  (defcong byte-list-equiv equal
    (secp256k1-sign-det-rec hash priv small-x? small-s?) 1
    :hints (("Goal"
             :use (secp256k1-sign-det-rec-fixes-input-hash
                   (:instance secp256k1-sign-det-rec-fixes-input-hash
                    (hash hash-equiv)))
             :in-theory (disable secp256k1-sign-det-rec-fixes-input-hash))))

  (defcong secp256k1-priv-key-equiv equal
    (secp256k1-sign-det-rec hash priv small-x? small-s?) 2
    :hints (("Goal"
             :use (secp256k1-sign-det-rec-fixes-input-priv
                   (:instance secp256k1-sign-det-rec-fixes-input-priv
                    (priv priv-equiv)))
             :in-theory (disable secp256k1-sign-det-rec-fixes-input-priv))))

  (defcong iff equal (secp256k1-sign-det-rec hash priv small-x? small-s?) 3
    :hints (("Goal"
             :use (secp256k1-sign-det-rec-fixes-input-small-x?
                   (:instance secp256k1-sign-det-rec-fixes-input-small-x?
                    (small-x? small-x?-equiv)))
             :in-theory (disable secp256k1-sign-det-rec-fixes-input-small-x?))))

  (defcong iff equal (secp256k1-sign-det-rec hash priv small-x? small-s?) 4
    :hints (("Goal"
             :use (secp256k1-sign-det-rec-fixes-input-small-s?
                   (:instance secp256k1-sign-det-rec-fixes-input-small-s?
                    (small-s? small-s?-equiv)))
             :in-theory (disable
                         secp256k1-sign-det-rec-fixes-input-small-s?)))))
