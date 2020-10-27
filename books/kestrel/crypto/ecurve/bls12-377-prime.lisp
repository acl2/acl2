; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Authors: Alessandro Coglio (coglio@kestrel.edu)
;                       Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "projects/quadratic-reciprocity/euclid" :dir :system) ;for rtl::primep
(local (include-book "projects/quadratic-reciprocity/pratt" :dir :system))

(include-book "kestrel/crypto/ecurve/bls12-377-domain-parameters" :dir :system)

(in-theory (disable (:e rtl::primep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Pratt certificate for BLS-377 prime subgroup (scalar field) aka "r".

;; This book proves some properties of the prime r used in the curve BLS12-377
;; which is described in the Zexe paper,
;; https://eprint.iacr.org/2018/962.pdf

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; To prove that r is indeed a prime,
;; we use Russinoff's algorithm from the paper
;; "Pratt certification and the primality of 2^255 - 19",
;; where a Pratt certificate of n is a tree
;; (r' (p1 ... pn) (e1 ... en) (c1 ... cn))
;; such that
;; 1. r' is primitive root of n
;; 2. n - 1 = (p1^e1)...(pn^en)
;; 3. ci is a pratt certificate of pi.

;; The following certificate was generated using
;; sagecell.sagemath.org and wolframalpha.com
;; For example,
;; SageCellServer:
;;   k = GF(8444461749428370424248824938781546531375899335154063827935233455917409239041, modulus="primitive")
;;   k.gen()
;;   F = factor(8444461749428370424248824938781546531375899335154063827935233455917409239040)
;;   list(F)
;; See also Mathematica's FactorInteger and PrimitiveRoot.

(local
 (defconst *bls12-377-r-pratt-cert*
   '(22 (2 3 5 7 13 499 958612291309063373 9586122913090633729)
	(47 1 1 1 1 1 1 2)
	(() () () () () ()
	 ;; 958612291309063373
	 (2 (2 29 167 49484425527001)
	    (2  1   1  1)
	    (() () ()
	     ;; 49484425527001
	     (14 (2 3 5 1832756501)
		 (3 3 3 1)
		 (() () ()
		  ;; 1832756501
		  (2 (2 5 29 126397)
		     (2 3 1 1)
		     (() () () ()))))))
	 ;; 9586122913090633729
	 (11 (2 3 7 13 499)
	     (46 1 1 1 1)
	     (() () () () ()))))))

(defthm bls12-377-prime-is-prime
  (rtl::primep (bls12-377-scalar-field-prime))
  :hints (("Goal"
           :in-theory (enable bls12-377-scalar-field-prime
                              rtl::certify-prime)
           :use (:instance rtl::certification-theorem
                 (p (bls12-377-scalar-field-prime))
                 (c *bls12-377-r-pratt-cert*)))))
