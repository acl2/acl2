; Primes Library: Scalar Field prime for BLS-377
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

;; See also ../ecurve/bls-377-domain-parameters.lisp

(include-book "defprime")

(defprime bls12-377-scalar-field-prime
  #x12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001
  ;; The following certificate was generated using
  ;; sagecell.sagemath.org and wolframalpha.com
  ;; For example,
  ;; SageCellServer:
  ;;   k = GF(8444461749428370424248824938781546531375899335154063827935233455917409239041, modulus="primitive")
  ;;   k.gen()
  ;;   F = factor(8444461749428370424248824938781546531375899335154063827935233455917409239040)
  ;;   list(F)
  ;; See also Mathematica's FactorInteger and PrimitiveRoot.
  (22 (2 3 5 7 13 499 958612291309063373 9586122913090633729)
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
           (() () () () ())))))
