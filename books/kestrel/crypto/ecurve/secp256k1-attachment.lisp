; Elliptic Curve Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "secp256k1-interface")
(include-book "secp256k1")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-attachment
  :parents (crypto::attachments elliptic-curves)
  :short (xdoc::topstring
          "Executable attachments for the "
          (xdoc::seetopic "secp256k1-interface"
                        "elliptic curve secp256k1 interface")
          ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "We define an executable definition of private-to-public key conversion,
     and attach it to the constrained function.")
   (xdoc::p
    "We define a wrapper of the curve group multiplication definition
     and attach the wrapper to the constrained function.
     The wrapper converts between the fixtype of points
     and the representation of points
     used by the definition of the curve group operations;
     it also ensures that the starting point is on the curve,
     as required by the guards of the defined curve group operation.")
   (xdoc::p
    "An executable attachment for curve group addition
     may be added in the future.")
   (xdoc::p
    "For executable formal specifications, see the "
     (xdoc::seetopic "ecurve::secp256k1" "library for the
     Short Weierstrass elliptic curve secp256k1") "."))

  (define secp256k1-priv-to-pub-exec ((priv secp256k1-priv-key-p))
    :returns (pub secp256k1-pub-key-p)
    (b* ((priv (mbe :logic (secp256k1-priv-key-fix priv) :exec priv))
         (pub (secp256k1-mul priv (secp256k1-point-generator))))
      pub)
    :no-function t
    :hooks (:fix))

  (defattach secp256k1-priv-to-pub secp256k1-priv-to-pub-exec)

  (define secp256k1-mul-wrapper ((nat natp) (point secp256k1-pointp))
    :returns (result secp256k1-pointp)
    (b* ((nat (mbe :logic (nfix nat) :exec nat))
         (point (mbe :logic (secp256k1-point-fix point) :exec point))
         (point-cons (cons (secp256k1-point->x point)
                           (secp256k1-point->y point)))
         ((unless (point-on-elliptic-curve-p point-cons
                                             (secp256k1-prime)
                                             (secp256k1-a)
                                             (secp256k1-b)))
          (secp256k1-point 1 1))
         (result-cons (secp256k1* nat point-cons))
         (result (secp256k1-point (car result-cons) (cdr result-cons)))
         ((when (and
                 (secp256k1-priv-key-p nat)
                 (equal point (secp256k1-point-generator))
                 (not (secp256k1-pub-key-p result)))) (secp256k1-point 1 1)))
      result)
    :hooks (:fix)
    :guard-hints (("Goal"
                   :in-theory (e/d (secp256k1-fieldp
                                    secp256k1-a
                                    secp256k1-b
                                    pointp
                                    point-in-pxp-p
                                    secp256k1-prime)
                                   (pointp-of-secp256k1*))
                   :use ((:instance pointp-of-secp256k1*
                          (s nat)
                          (point (cons (secp256k1-point->x point)
                                       (secp256k1-point->y point))))
                         (:instance point-in-pxp-p-of-secp256k1*
                          (s nat)
                          (point (cons (secp256k1-point->x point)
                                       (secp256k1-point->y point)))))))

    :prepwork
    ((defrulel verify-guards-lemma
       (rtl::primep
        115792089237316195423570985008687907853269984665640564039457584007908834671663)
       :use secp256k1-prime-is-prime
       :enable secp256k1-prime))

    ///

    (defrule secp256k1-mul-wrapper-yields-pub-from-priv
      (implies (and (secp256k1-priv-key-p nat)
                    (equal point (secp256k1-point-generator)))
               (secp256k1-pub-key-p (secp256k1-mul-wrapper nat point)))
      :enable secp256k1-pub-key-p
      :disable ((:e point-on-elliptic-curve-p))))

  (defattach secp256k1-mul secp256k1-mul-wrapper))
