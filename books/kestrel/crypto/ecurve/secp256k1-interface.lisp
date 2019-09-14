; Elliptic Curve Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "kestrel/crypto/ecurve/secp256k1-types" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ secp256k1-interface
  :parents (crypto::interfaces elliptic-curves)
  :short (xdoc::topstring
          "Elliptic curve secp256k1 "
          (xdoc::seetopic "crypto::interfaces" "interface")
          ".")
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
    "See also:"
    (xdoc::ul
     (xdoc::li (xdoc::seetopic "ecurve::secp256k1" "library for the
     Short Weierstrass elliptic curve secp256k1"))
     (xdoc::li (xdoc::seetopic "ecurve::secp256k1-attachment"
     "executable attachments to this interface")))))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-priv-to-pub
  :short "Calculate a secp256k1 public key from a private key."
  :long
  (xdoc::topstring
   (xdoc::p
    "We constrain this function to return a public key unconditionally.")
   (xdoc::p
    "We also constrain this function to fix its argument to a private key."))

  (encapsulate

    (((secp256k1-priv-to-pub *) => *
      :formals (priv)
      :guard (secp256k1-priv-key-p priv)))

    (local
     (defun secp256k1-priv-to-pub (priv)
       (declare (ignore priv))
       (secp256k1-point 1 1)))

    (defrule secp256k1-pub-key-p-of-secp256k1-priv-to-pub
      (secp256k1-pub-key-p (secp256k1-priv-to-pub priv)))

    (defrule secp256k1-priv-to-pub-fixes-input-priv
      (equal (secp256k1-priv-to-pub (secp256k1-priv-key-fix priv))
             (secp256k1-priv-to-pub priv))))

  (defcong secp256k1-priv-key-equiv equal (secp256k1-priv-to-pub priv) 1
    :hints (("Goal"
             :use (secp256k1-priv-to-pub-fixes-input-priv
                   (:instance secp256k1-priv-to-pub-fixes-input-priv
                    (priv priv-equiv)))
             :in-theory (disable secp256k1-priv-to-pub-fixes-input-priv)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-add
  :short "Addition of two points on the secp256k1 curve."
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
  :short "Multiplication of a point on the secp256k1 curve by a number."
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
                    (equal point (secp256k1-point-generator)))
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
                   (:instance secp256k1-fixes-input-point
                    (point point-equiv)))
             :in-theory (disable secp256k1-fixes-input-point)))))
