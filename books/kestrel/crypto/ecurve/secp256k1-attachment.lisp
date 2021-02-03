; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "secp256k1-interface")
(include-book "secp256k1")
(include-book "secp256k1-point-conversions")

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
     as required by the guards of the defined curve group operation.
     Note that @('secp256k1+') is never expected to return (0, 0),
     because the point at infinity is represented as @(':infinity')
     and the point (0, 0) is not on the curve;
     to satisfy the guard of @(tsee pointp-to-secp256k1-point),
     we check that at run time, raising an error if the test should ever fail
     (which we never expect to).")
   (xdoc::p
    "We define a wrapper of the curve group addition definition
     and attach the wrapper to the constrained function.
     The wrapper converts between the fixtype of points
     and the representation of points
     used by the definition of the curve group operations;
     it also ensures that the starting points are on the curve,
     as required by the guards of the defined curve group operation.
     Note that @('secp256k1+') is never expected to return (0, 0),
     because the point at infinity is represented as @(':infinity')
     and the point (0, 0) is not on the curve;
     to satisfy the guard of @(tsee pointp-to-secp256k1-point),
     we check that at run time, raising an error if the test should ever fail
     (which we never expect to).
     If we multiply the secp256k1 generator point by a private key,
     we obtain a valid public key,
     i.e. not the point at infinity.
     At this time we do not have that theorem proved and available,
     so for now we insert a run-time check that is never expected to fail.")
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

  (define secp256k1-add-wrapper ((secp-point1 secp256k1-pointp)
                                 (secp-point2 secp256k1-pointp))
    :returns (secp-result secp256k1-pointp)
    (b* ((point1 (secp256k1-point-to-pointp secp-point1))
         (point2 (secp256k1-point-to-pointp secp-point2))
         ((unless (point-on-weierstrass-elliptic-curve-p point1
                                                         (secp256k1-field-prime)
                                                         (secp256k1-a)
                                                         (secp256k1-b)))
          (secp256k1-point 1 1))
         ((unless (point-on-weierstrass-elliptic-curve-p point2
                                                         (secp256k1-field-prime)
                                                         (secp256k1-a)
                                                         (secp256k1-b)))
          (secp256k1-point 1 1))
         (result (secp256k1+ point1 point2))
         ((when (equal result (cons 0 0)))
          (acl2::raise "Internal error: SECP256K1+ produced (0, 0).")
          (secp256k1-point 1 1))
         (secp-result (pointp-to-secp256k1-point result)))
      secp-result)
    :hooks (:fix)
    :guard-hints (("Goal" :in-theory (e/d (secp256k1-b fep)
                                          ((:e secp256k1-field-prime))))))

  (define secp256k1-mul-wrapper ((nat natp) (secp-point secp256k1-pointp))
    :returns (secp-result secp256k1-pointp)
    (b* ((nat (mbe :logic (nfix nat) :exec nat))
         (point (secp256k1-point-to-pointp secp-point))
         ((unless (point-on-weierstrass-elliptic-curve-p point
                                                         (secp256k1-field-prime)
                                                         (secp256k1-a)
                                                         (secp256k1-b)))
          (secp256k1-point 1 1))
         (result (secp256k1* nat point))
         ((when (equal result (cons 0 0)))
          (acl2::raise "Internal error: SECP256K1* produced (0, 0).")
          (secp256k1-point 1 1))
         (secp-result (pointp-to-secp256k1-point result))
         ((when (and (secp256k1-priv-key-p nat)
                     (secp256k1-point-equiv secp-point
                                            (secp256k1-point-generator))
                     (not (secp256k1-pub-key-p secp-result))))
          (acl2::raise "Internal error: ~
                        SECP256K1* on a private key and the generator ~
                        has produced ~x0, which is not a public key."
                       secp-result)
          (secp256k1-point 1 1)))
      secp-result)
    :hooks (:fix)
    :guard-hints (("Goal" :in-theory (e/d (secp256k1-b fep)
                                          ((:e secp256k1-field-prime)))))
    ///

    (defrule secp256k1-mul-wrapper-yields-pub-from-priv
      (implies (and (secp256k1-priv-key-p nat)
                    (equal point (secp256k1-point-generator)))
               (secp256k1-pub-key-p (secp256k1-mul-wrapper nat point)))
      :enable secp256k1-pub-key-p
      :disable ((:e point-on-weierstrass-elliptic-curve-p))))

  (defattach secp256k1-priv-to-pub secp256k1-priv-to-pub-exec)

  (defattach secp256k1-add secp256k1-add-wrapper)

  (defattach secp256k1-mul secp256k1-mul-wrapper))
