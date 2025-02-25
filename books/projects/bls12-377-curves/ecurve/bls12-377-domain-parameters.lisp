; bls12-377-curves Library
;
; Copyright (C) 2020 Aleo Systems Inc. (https://www.aleo.org)
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "projects/bls12-377-curves/primes/top" :dir :system)

(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bls12-377-domain-parameters
  :parents (crypto::bls12-377-curves)
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
    "@($x$) is used to calculate the 
     <see topic='@(url primes::bls12-377-base-field-prime)'>base field prime q</see>
     and the
     <see topic='@(url primes::bls12-377-scalar-field-prime)'>scalar field prime r</see>."))
   9586122913090633729
   :no-function t
   ///

   (assert-event (posp (bls12-377-parameter-x)))

   (assert-event (equal (bls12-377-parameter-x)
                        (+ (* 3 (expt 2 46) 7 13 499)
                           1)))

   (assert-event (equal (mod (bls12-377-parameter-x) (* 3 (expt 2 46)))
                        1))
   (assert-event (equal (mod (bls12-377-parameter-x) 3)
                        1))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; show that r was computed from x as stated
(assert-event
 (equal (primes::bls12-377-scalar-field-prime)
        (let ((x (bls12-377-parameter-x)))
          (+ (- (expt x 4) (expt x 2)) 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; show that q was computed from x as stated
(assert-event
 (equal (primes::bls12-377-base-field-prime)
        (let ((x (bls12-377-parameter-x))
              (r (primes::bls12-377-scalar-field-prime)))
          (+ (/ (* (expt (- x 1) 2) r) 3) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:e primes::bls12-377-scalar-field-prime) (:e primes::bls12-377-base-field-prime)))
