; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Eric McCarthy (mccarthy@kestrel.edu)
;          Alessandro Coglio (coglio@kestrel.edu)
;          Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "kestrel/crypto/primes/bls12-377-prime" :dir :system)

(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bls12-377-domain-parameters
  :parents (elliptic-curves)
  :short "Domain parameters of the BLS12-377 elliptic curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "The BLS12-377 elliptic curve is called @($E_{BLS}$) in "
    (xdoc::a :href "https://eprint.iacr.org/2018/962.pdf"
             "Zexe: Enabling Decentralized Private Computation")
    ".")
   (xdoc::p
    "Here we introduce some of the parameters of this and of related
     elliptic curves, as described in Section 7 and in Figure 16 of that paper."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bls12-377-parameter-x ()
  :short "The parameter @($x$) for constructing the curve @($E_{BLS}$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The parameter @($x$) is"
    (xdoc::@[] "3\\cdot{}2^{46}\\cdot(7\\cdot{}13\\cdot{}499)+1"))
   (xdoc::p
    "This ensures that both of these requirements are satisfied:"
    (xdoc::@[] "x\\equiv{}1\\ mod\\ 3\\cdot{}2^{46}")
    (xdoc::@[] "x\\equiv{}1\\ mod\\ 3"))
   (xdoc::p
    "In decimal: @($x = 9586122913090633729$).")
   (xdoc::p
    "@($x$) is used to calculate the base field prime @($p$) and
     and the
     <see topic='@(url bls12-377-scalar-field-prime)'>scalar field prime r</see>."))
   9586122913090633729
   :no-function t
   ///

   (assert-event (posp (bls12-377-parameter-x)))

   (assert-event (equal (bls12-377-parameter-x)
                        (+ (* 3 (expt 2 46) 7 13 499)
                           1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; show that r was computed from x as stated
(assert-event
 (equal (bls12-377-scalar-field-prime)
        (let ((x (bls12-377-parameter-x)))
          (+ (- (expt x 4) (expt x 2)) 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:e bls12-377-scalar-field-prime)))
