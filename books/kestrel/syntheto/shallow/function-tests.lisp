; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Testing the shallow embedding macros

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "functions")
(include-book "composite-types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(s-fun "reducePlus"
       :inputs (("l" (s-type-sequence (s-type-integer)))
                ("acc" (s-type-integer)))
       :outputs (("R" (s-type-integer)))
       :body (s-conditional (s-empty-p (s-var-ref "l"))
                            (s-var-ref "acc")
                            (s-call "reducePlus" (s-tail (s-var-ref "l"))
                                    (s-plus (s-var-ref "acc")
                                            (s-head (s-var-ref "l"))))))
(acl2::assert-equal (syndef::|reducePlus| '(1 2 3 4 5) 0)
                    15)


(make-product-type "intPair"
                   ("id" (s-type-integer))
                   ("val" (s-type-integer)))

(s-fun "findIntSeq"
       :inputs (("x" (s-type-integer))
                ("S" (s-type-sequence (s-type-ref "intPair"))))
       :outputs (("R" (s-type-option (s-type-integer))))
       :body (s-conditional (s-empty-p (s-var-ref "S"))
                            (s-none (s-type-option (s-type-integer)))
                            (s-let (("pair" (s-head (s-var-ref "S"))))
                                   (s-conditional (s-equal (s-var-ref "x")
                                                           (s-prod-field-get "intPair" "id" (s-var-ref "pair")))
                                                  (s-some (s-type-option (s-type-integer))
                                                          (s-prod-field-get "intPair" "val"
                                                                            (s-var-ref "pair")))
                                                  (s-call "findIntSeq"
                                                          (s-var-ref "x")
                                                          (s-tail (s-var-ref "S")))))))
(acl2::assert-equal (syndef::|findIntSeq| 2 (list (syndef::|intPair| 1 1)
                                                  (syndef::|intPair| 2 2)
                                                  (syndef::|intPair| 3 3)))
                    (syndef::option[int]-some 2))
(acl2::assert-equal (syndef::|findIntSeq| 4 (list (syndef::|intPair| 1 1)
                                                  (syndef::|intPair| 2 2)
                                                  (syndef::|intPair| 3 3)))
                    (syndef::option[int]-none))

(s-fun "firstSeqId"
       :inputs (("S" (s-type-sequence (s-type-ref "intPair"))))
       :outputs (("R" (s-type-integer)))
       :body (s-conditional (s-empty-p (s-var-ref "S"))
                            0
                            (s-let (("pair" (s-head (s-var-ref "S"))))
                                   (s-prod-field-get "intPair" "id" (s-var-ref "pair")))))
(acl2::assert-equal (syndef::|firstSeqId| (list (syndef::|intPair| 1 1)
                                                  (syndef::|intPair| 2 2)
                                                  (syndef::|intPair| 3 3)))
                    1)

;; Hand translation of examples/sort-rationals.lisp

(s-fun "myAbs"
       :inputs (("x" (s-type-integer)))
       :outputs (("a" (s-type-integer)))
       :ensures (s-gte (s-var-ref "a") 0)
       :body (s-conditional (s-gte (s-var-ref "x") 0)
                            (s-var-ref "x")
                            (s-negate (s-var-ref "x"))))

(acl2::assert-equal (syndef::|myAbs| 4) 4)
(acl2::assert-equal (syndef::|myAbs| -4) 4)

(local (include-book "arithmetic-5/top" :dir :system))

(s-fun "myGCD"
       :inputs (("x" (s-type-integer))
                ("y" (s-type-integer)))
       :assumes (s-and (s-gte (s-var-ref "x") 0)
                       (s-gte (s-var-ref "y") 0))
       :outputs (("z" (s-type-integer)))
       :measure (s-plus (s-var-ref "x") (s-var-ref "y"))
       :body (s-conditional (s-equal (s-var-ref "x") 0)
                            (s-var-ref "y")
                            (s-conditional (s-equal (s-var-ref "y") 0)
                                           (s-var-ref "x")
                                           (s-conditional (s-lt (s-var-ref "x") (s-var-ref "y"))
                                                          (s-call "myGCD"
                                                                  (s-var-ref "x")
                                                                  (s-rem (s-var-ref "y") (s-var-ref "x")))
                                                          (s-call "myGCD"
                                                                  (s-rem (s-var-ref "x") (s-var-ref "y"))
                                                                  (s-var-ref "y"))))))

(acl2::assert-equal (syndef::|myGCD| 144 60) 12)
(acl2::assert-equal (syndef::|myGCD| 1144 64) 8)

(make-subtype "Positive" (s-type-integer)
              "x" (s-gt (s-var-ref "x") 0)
              1)
(acl2::assert-equal (syndef::|Positive-P| 144) t)
(acl2::assert-equal (syndef::|Positive-P| 0) nil)
(acl2::assert-equal (syndef::|Positive-P| -144) nil)


(make-product-type "myRational"
                   ("numerator" (s-type-integer))
                   ("denominator" (s-type-ref "Positive"))
                   :invariant (s-equal (s-call "myGCD"
                                               (s-call "myAbs" (s-var-ref "numerator"))
                                               (s-call "myAbs" (s-var-ref "denominator")))
                                       1)
                   :fixvals (0 1))


;; Should be created as necessary
;(make-sequence-type "[myRational]" (s-type-ref "myRational"))

(s-fun "lteq"
       :inputs (("x" (s-type-ref "myRational")) ("y" (s-type-ref "myRational")))
       :outputs (("b" (s-type-boolean)))
       :body (s-lte (s-times (s-prod-field-get "myRational" "numerator" (s-var-ref "x"))
                             (s-prod-field-get "myRational" "denominator" (s-var-ref "y")))
                    (s-times (s-prod-field-get "myRational" "numerator" (s-var-ref "y"))
                             (s-prod-field-get "myRational" "denominator" (s-var-ref "x")))))

(acl2::assert-equal (e-term (s-call "lteq"
                                    (s-prod-make "myRational" "numerator" 4 "denominator" 5)
                                    (s-prod-make "myRational" "numerator" 5 "denominator" 6)))
                    t)
(acl2::assert-equal (e-term (s-call "lteq"
                                    (s-prod-make "myRational" "numerator" 5 "denominator" 6)
                                    (s-prod-make "myRational" "numerator" 4 "denominator" 5)))
                    nil)

(s-fun "ordered?"
       :inputs (("S" (s-type-sequence (s-type-ref "myRational"))))
       :outputs (("b" (s-type-boolean)))
       :body (s-or (s-empty-p (s-var-ref "S"))
                   (s-or (s-empty-p (s-tail (s-var-ref "S")))
                         (s-and (s-call "lteq"
                                        (s-head (s-var-ref "S"))
                                        (s-head (s-tail (s-var-ref "S"))))
                                (s-call "ordered?" (s-tail (s-var-ref "S")))))))
(acl2::assert-equal (e-term (s-call "ordered?"
                                    (s-literal-sequence
                                     (s-prod-make "myRational" "numerator" 4 "denominator" 5)
                                     (s-prod-make "myRational" "numerator" 5 "denominator" 6))))
                    t)
(acl2::assert-equal (e-term (s-call "ordered?"
                                    (s-literal-sequence
                                     (s-prod-make "myRational" "numerator" 5 "denominator" 6)
                                     (s-prod-make "myRational" "numerator" 4 "denominator" 5))))
                    nil)

(s-fun "member_MyRationalSeq"
        :inputs (("x" (s-type-ref "myRational"))
                 ("S" (s-type-sequence (s-type-ref "myRational"))))
       :outputs (("b" (s-type-boolean)))
       :body (s-conditional (s-empty-p (s-var-ref "S"))
                            (s-literal-false)
                            (s-or (s-equal (s-var-ref "x") (s-head (s-var-ref "S")))
                                  (s-call "member_MyRationalSeq"
                                          (s-var-ref "x")
                                          (s-tail (s-var-ref "S"))))))
(acl2::assert-equal (e-term (s-call "member_MyRationalSeq"
                                    (s-prod-make "myRational" "numerator" 5 "denominator" 6)
                                    (s-literal-sequence
                                     (s-prod-make "myRational" "numerator" 4 "denominator" 5)
                                     (s-prod-make "myRational" "numerator" 5 "denominator" 6))))
                    t)
(acl2::assert-equal (e-term (s-call "member_MyRationalSeq"
                                    (s-prod-make "myRational" "numerator" 1 "denominator" 6)
                                    (s-literal-sequence
                                     (s-prod-make "myRational" "numerator" 4 "denominator" 5)
                                     (s-prod-make "myRational" "numerator" 5 "denominator" 6))))
                    nil)

(s-fun "remove1_MyRationalSeq"
        :inputs (("x" (s-type-ref "myRational"))
                 ("S" (s-type-sequence (s-type-ref "myRational"))))
       :outputs (("S'" (s-type-sequence (s-type-ref "myRational"))))
       :body (s-conditional (s-empty-p (s-var-ref "S"))
                            (s-literal-sequence)
                            (s-conditional (s-equal (s-var-ref "x") (s-head (s-var-ref "S")))
                                           (s-tail (s-var-ref "S"))
                                           (s-cons (s-head (s-var-ref "S"))
                                                   (s-call "remove1_MyRationalSeq"
                                                           (s-var-ref "x")
                                                           (s-tail (s-var-ref "S")))))))
(acl2::assert-equal (e-term (s-call "remove1_MyRationalSeq"
                                    (s-prod-make "myRational" "numerator" 5 "denominator" 6)
                                    (s-literal-sequence
                                     (s-prod-make "myRational" "numerator" 4 "denominator" 5)
                                     (s-prod-make "myRational" "numerator" 5 "denominator" 6))))
                    (e-term (s-literal-sequence
                             (s-prod-make "myRational" "numerator" 4 "denominator" 5))))

(s-fun "permutation"
        :inputs (("S1" (s-type-sequence (s-type-ref "myRational")))
                 ("S2" (s-type-sequence (s-type-ref "myRational"))))
        :outputs (("b" (s-type-boolean)))
        :body (s-conditional (s-empty-p (s-var-ref "S1"))
                             (s-empty-p (s-var-ref "S2"))
                             (s-conditional (s-empty-p (s-var-ref "S2"))
                                            (s-literal-false)
                                            (s-and (s-call "member_MyRationalSeq"
                                                           (s-head (s-var-ref "S1"))
                                                           (s-var-ref "S2"))
                                                   (s-call "permutation"
                                                           (s-tail (s-var-ref "S1"))
                                                           (s-call "remove1_MyRationalSeq"
                                                                   (s-head (s-var-ref "S1"))
                                                                   (s-var-ref "S2")))))))
(acl2::assert-equal (e-term (s-call "permutation"
                                    (s-literal-sequence
                                     (s-prod-make "myRational" "numerator" 5 "denominator" 6)
                                     (s-prod-make "myRational" "numerator" 4 "denominator" 5))
                                    (s-literal-sequence
                                     (s-prod-make "myRational" "numerator" 4 "denominator" 5)
                                     (s-prod-make "myRational" "numerator" 5 "denominator" 6))))
                    t)
(acl2::assert-equal (e-term (s-call "permutation"
                                    (s-literal-sequence
                                     (s-prod-make "myRational" "numerator" 5 "denominator" 6)
                                     (s-prod-make "myRational" "numerator" 4 "denominator" 5))
                                    (s-literal-sequence
                                     (s-prod-make "myRational" "numerator" 1 "denominator" 5)
                                     (s-prod-make "myRational" "numerator" 5 "denominator" 6))))
                    nil)

;; Additional myRational tests
#| Doesn't guard check
(s-fun "r-plus"
       :inputs (("x" (s-type-ref "myRational")) ("y" (s-type-ref "myRational")))
       :outputs (("b" (s-type-ref "myRational")))
       :guard-debug t
       :body (s-let (("num_0" (s-plus (s-times (s-prod-field-get "myRational" "numerator" (s-var-ref "x"))
                                               (s-prod-field-get "myRational" "denominator" (s-var-ref "y")))
                                      (s-times (s-prod-field-get "myRational" "numerator" (s-var-ref "y"))
                                               (s-prod-field-get "myRational" "denominator" (s-var-ref "x")))))
                     ("den_0" (s-times (s-prod-field-get "myRational" "denominator" (s-var-ref "x"))
                                       (s-prod-field-get "myRational" "denominator" (s-var-ref "y")))))
                    (s-let (("gcd" (s-call "myGCD" (s-call "myAbs" (s-var-ref "num_0"))
                                           (s-call "myAbs" (s-var-ref "den_0")))))
                           (s-prod-make "myRational"
                                        "numerator" (s-div (s-var-ref "num_0") (s-var-ref "gcd"))
                                        "denominator" (s-div (s-var-ref "den_0") (s-var-ref "gcd"))))))
|#
