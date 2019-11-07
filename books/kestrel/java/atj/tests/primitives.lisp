; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../implementation" :ttags (:open-input-channel (:oslib) (:quicklisp) :quicklisp.osicat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the generation of Java code
; that manipulates Java primitive values.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; As explained in the ATJ user documentation,
; the tests passed to :TESTS may only involve
; the target functions explicitly passed to ATJ,
; which may not include the functions in *ATJ-PRIMITIVE-FNS*
; when :DEEP is NIL and :GUARDS is T.
; Thus, here we introduce wrappers for such functions,
; which are the ones that we want to test here.

(defun test-boolean-not (x)
  (declare (xargs :guard (java::boolean-value-p x)))
  (java::boolean-not x))

(defun test-boolean-and (x y)
  (declare (xargs :guard (and (java::boolean-value-p x)
                              (java::boolean-value-p y))))
  (java::boolean-and x y))

(defun test-boolean-xor (x y)
  (declare (xargs :guard (and (java::boolean-value-p x)
                              (java::boolean-value-p y))))
  (java::boolean-xor x y))

(defun test-boolean-ior (x y)
  (declare (xargs :guard (and (java::boolean-value-p x)
                              (java::boolean-value-p y))))
  (java::boolean-ior x y))

(defun test-boolean-eq (x y)
  (declare (xargs :guard (and (java::boolean-value-p x)
                              (java::boolean-value-p y))))
  (java::boolean-eq x y))

(defun test-boolean-neq (x y)
  (declare (xargs :guard (and (java::boolean-value-p x)
                              (java::boolean-value-p y))))
  (java::boolean-neq x y))

(defun test-int-plus (x)
  (declare (xargs :guard (java::int-value-p x)))
  (java::int-plus x))

(defun test-int-minus (x)
  (declare (xargs :guard (java::int-value-p x)))
  (java::int-minus x))

(defun test-int-not (x)
  (declare (xargs :guard (java::int-value-p x)))
  (java::int-not x))

(defun test-int-add (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-add x y))

(defun test-int-sub (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-sub x y))

(defun test-int-mul (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-mul x y))

(defun test-int-div (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y)
                              (not (equal (java::int-value->int y) 0)))))
  (java::int-div x y))

(defun test-int-rem (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y)
                              (not (equal (java::int-value->int y) 0)))))
  (java::int-rem x y))

(defun test-int-and (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-and x y))

(defun test-int-xor (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-xor x y))

(defun test-int-ior (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-ior x y))

(defun test-int-int-shiftl (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-int-shiftl x y))

(defun test-int-int-shiftr (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-int-shiftr x y))

(defun test-int-int-ushiftr (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-int-ushiftr x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; More functions over (ACL2 representations of) Java primitive values.

(defun f-boolean (x y)
  (declare (xargs :guard (and (java::boolean-value-p x)
                              (java::boolean-value-p y))))
  (java::boolean-and (java::boolean-xor x y)
                     (java::boolean-ior x y)))

(defun g-boolean (x y z)
  (declare (xargs :guard (and (java::boolean-value-p x)
                              (java::boolean-value-p y)
                              (java::boolean-value-p z))))
  (java::boolean-eq (java::boolean-not x)
                    (java::boolean-neq y z)))

(defun f-int (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-add (java::int-mul (java::int-value 2) x)
                 (java::int-mul y y)))

(defun g-int (x y z)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y)
                              (java::int-value-p z))))
  (java::int-int-shiftl (java::int-sub x
                                       (java::int-and y z))
                        (java::int-not z)))

(defun h-int (x)
  (declare (xargs :guard (and (java::int-value-p x))))
  (java::int-xor (java::int-div x (java::int-value 119))
                 (java::int-rem x (java::int-value -373))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests for the functions above, when :DEEP is NIL and :GUARDS is T.

(defconst *shallow-guarded-basic-tests*
  '(;; boolean negation:
    ("BooleanNotT" (test-boolean-not (java::boolean-value t)))
    ("BooleanNotF" (test-boolean-not (java::boolean-value nil)))
    ;; boolean conjunction:
    ("BooleanAndTT" (test-boolean-and (java::boolean-value t)
                                      (java::boolean-value t)))
    ("BooleanAndTF" (test-boolean-and (java::boolean-value t)
                                      (java::boolean-value nil)))
    ("BooleanAndFT" (test-boolean-and (java::boolean-value nil)
                                      (java::boolean-value t)))
    ("BooleanAndFF" (test-boolean-and (java::boolean-value nil)
                                      (java::boolean-value nil)))
    ;; boolean exclusive disjunction:
    ("BooleanXorTT" (test-boolean-xor (java::boolean-value t)
                                      (java::boolean-value t)))
    ("BooleanXorTF" (test-boolean-xor (java::boolean-value t)
                                      (java::boolean-value nil)))
    ("BooleanXorFT" (test-boolean-xor (java::boolean-value nil)
                                      (java::boolean-value t)))
    ("BooleanXorFF" (test-boolean-xor (java::boolean-value nil)
                                      (java::boolean-value nil)))
    ;; boolean inclusive disjunction:
    ("BooleanIorTT" (test-boolean-ior (java::boolean-value t)
                                      (java::boolean-value t)))
    ("BooleanIorTF" (test-boolean-ior (java::boolean-value t)
                                      (java::boolean-value nil)))
    ("BooleanIorFT" (test-boolean-ior (java::boolean-value nil)
                                      (java::boolean-value t)))
    ("BooleanIorFF" (test-boolean-ior (java::boolean-value nil)
                                      (java::boolean-value nil)))
    ;; boolean equality:
    ("BooleanEqTT" (test-boolean-eq (java::boolean-value t)
                                    (java::boolean-value t)))
    ("BooleanEqTF" (test-boolean-eq (java::boolean-value t)
                                    (java::boolean-value nil)))
    ("BooleanEqFT" (test-boolean-eq (java::boolean-value nil)
                                    (java::boolean-value t)))
    ("BooleanEqFF" (test-boolean-eq (java::boolean-value nil)
                                    (java::boolean-value nil)))
    ;; boolean non-equality:
    ("BooleanNeqTT" (test-boolean-neq (java::boolean-value t)
                                      (java::boolean-value t)))
    ("BooleanNeqTF" (test-boolean-neq (java::boolean-value t)
                                      (java::boolean-value nil)))
    ("BooleanNeqFT" (test-boolean-neq (java::boolean-value nil)
                                      (java::boolean-value t)))
    ("BooleanNeqFF" (test-boolean-neq (java::boolean-value nil)
                                      (java::boolean-value nil)))
    ;; int unary plus:
    ("IntPlus0" (test-int-plus (java::int-value 0)))
    ("IntPlus1" (test-int-plus (java::int-value 1)))
    ("IntPlus2" (test-int-plus (java::int-value 875753)))
    ("IntPlus3" (test-int-plus (java::int-value -16)))
    ("IntPlus4" (test-int-plus (java::int-value -1600000)))
    ;; int unary minus:
    ("IntMinus0" (test-int-minus (java::int-value 0)))
    ("IntMinus1" (test-int-minus (java::int-value 1)))
    ("IntMinus2" (test-int-minus (java::int-value 875753)))
    ("IntMinus3" (test-int-minus (java::int-value -16)))
    ("IntMinus4" (test-int-minus (java::int-value -1600000)))
    ;; int bitwise complement:
    ("IntNot0" (test-int-not (java::int-value 0)))
    ("IntNot1" (test-int-not (java::int-value 1)))
    ("IntNot2" (test-int-not (java::int-value 875753)))
    ("IntNot3" (test-int-not (java::int-value -16)))
    ("IntNot4" (test-int-not (java::int-value -1600000)))
    ;; int addition:
    ("IntAdd0" (test-int-add (java::int-value 2) (java::int-value 3)))
    ("IntAdd1" (test-int-add (java::int-value -2) (java::int-value -3)))
    ("IntAdd2" (test-int-add (java::int-value 2) (java::int-value -3)))
    ("IntAdd3" (test-int-add (java::int-value -2) (java::int-value 3)))
    ("IntAdd4" (test-int-add (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; int subtraction:
    ("IntSub0" (test-int-sub (java::int-value 2) (java::int-value 3)))
    ("IntSub1" (test-int-sub (java::int-value -2) (java::int-value -3)))
    ("IntSub2" (test-int-sub (java::int-value 2) (java::int-value -3)))
    ("IntSub3" (test-int-sub (java::int-value -2) (java::int-value 3)))
    ("IntSub4" (test-int-sub (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; int multiplication:
    ("IntMul0" (test-int-mul (java::int-value 2) (java::int-value 3)))
    ("IntMul1" (test-int-mul (java::int-value -2) (java::int-value -3)))
    ("IntMul2" (test-int-mul (java::int-value 2) (java::int-value -3)))
    ("IntMul3" (test-int-mul (java::int-value -2) (java::int-value 3)))
    ("IntMul4" (test-int-mul (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; int division:
    ("IntDiv0" (test-int-div (java::int-value 2) (java::int-value 3)))
    ("IntDiv1" (test-int-div (java::int-value -2) (java::int-value -3)))
    ("IntDiv2" (test-int-div (java::int-value 2) (java::int-value -3)))
    ("IntDiv3" (test-int-div (java::int-value -2) (java::int-value 3)))
    ("IntDiv4" (test-int-div (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; int remainder:
    ("IntRem0" (test-int-rem (java::int-value 2) (java::int-value 3)))
    ("IntRem1" (test-int-rem (java::int-value -2) (java::int-value -3)))
    ("IntRem2" (test-int-rem (java::int-value 2) (java::int-value -3)))
    ("IntRem3" (test-int-rem (java::int-value -2) (java::int-value 3)))
    ("IntRem4" (test-int-rem (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; int bitwise conjunction:
    ("IntAnd0" (test-int-and (java::int-value 2) (java::int-value 3)))
    ("IntAnd1" (test-int-and (java::int-value -2) (java::int-value -3)))
    ("IntAnd2" (test-int-and (java::int-value 2) (java::int-value -3)))
    ("IntAnd3" (test-int-and (java::int-value -2) (java::int-value 3)))
    ("IntAnd4" (test-int-and (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; int bitwise exclusive disjunction:
    ("IntXor0" (test-int-xor (java::int-value 2) (java::int-value 3)))
    ("IntXor1" (test-int-xor (java::int-value -2) (java::int-value -3)))
    ("IntXor2" (test-int-xor (java::int-value 2) (java::int-value -3)))
    ("IntXor3" (test-int-xor (java::int-value -2) (java::int-value 3)))
    ("IntXor4" (test-int-xor (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; int bitwise inclusive disjunction:
    ("IntIor0" (test-int-ior (java::int-value 2) (java::int-value 3)))
    ("IntIor1" (test-int-ior (java::int-value -2) (java::int-value -3)))
    ("IntIor2" (test-int-ior (java::int-value 2) (java::int-value -3)))
    ("IntIor3" (test-int-ior (java::int-value -2) (java::int-value 3)))
    ("IntIor4" (test-int-ior (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; int left shift by int distance:
    ("IntIntShiftl0" (test-int-int-shiftl (java::int-value 2)
                                          (java::int-value 3)))
    ("IntIntShiftl1" (test-int-int-shiftl (java::int-value -2)
                                          (java::int-value -3)))
    ("IntIntShiftl2" (test-int-int-shiftl (java::int-value 2)
                                          (java::int-value -3)))
    ("IntIntShiftl3" (test-int-int-shiftl (java::int-value -2)
                                          (java::int-value 3)))
    ("IntIntShiftl4" (test-int-int-shiftl (java::int-value 2372792)
                                          (java::int-value -8882289)))
    ;; int right shift by int distance:
    ("IntIntShiftr0" (test-int-int-shiftr (java::int-value 2)
                                          (java::int-value 3)))
    ("IntIntShiftr1" (test-int-int-shiftr (java::int-value -2)
                                          (java::int-value -3)))
    ("IntIntShiftr2" (test-int-int-shiftr (java::int-value 2)
                                          (java::int-value -3)))
    ("IntIntShiftr3" (test-int-int-shiftr (java::int-value -2)
                                          (java::int-value 3)))
    ("IntIntShiftr4" (test-int-int-shiftr (java::int-value 2372792)
                                          (java::int-value -8882289)))
    ;; int unsigned right shift by int distance:
    ("IntIntUshiftr0" (test-int-int-ushiftr (java::int-value 2)
                                            (java::int-value 3)))
    ("IntIntUshiftr1" (test-int-int-ushiftr (java::int-value -2)
                                            (java::int-value -3)))
    ("IntIntUshiftr2" (test-int-int-ushiftr (java::int-value 2)
                                            (java::int-value -3)))
    ("IntIntUshiftr3" (test-int-int-ushiftr (java::int-value -2)
                                            (java::int-value 3)))
    ("IntIntUshiftr4" (test-int-int-ushiftr (java::int-value 2372792)
                                            (java::int-value -8882289)))))

(defconst *shallow-guarded-more-tests*
  '(;; F-BOOLEAN:
    ("FbooleanTT" (f-boolean (java::boolean-value t)
                             (java::boolean-value t)))
    ("FbooleanTF" (f-boolean (java::boolean-value t)
                             (java::boolean-value nil)))
    ("FbooleanFT" (f-boolean (java::boolean-value nil)
                             (java::boolean-value t)))
    ("FbooleanFF" (f-boolean (java::boolean-value nil)
                             (java::boolean-value nil)))
    ;; G-BOOLEAN:
    ("GbooleanTTT" (g-boolean (java::boolean-value t)
                              (java::boolean-value t)
                              (java::boolean-value t)))
    ("GbooleanTTF" (g-boolean (java::boolean-value t)
                              (java::boolean-value t)
                              (java::boolean-value nil)))
    ("GbooleanTFT" (g-boolean (java::boolean-value t)
                              (java::boolean-value nil)
                              (java::boolean-value t)))
    ("GbooleanTFF" (g-boolean (java::boolean-value t)
                              (java::boolean-value nil)
                              (java::boolean-value nil)))
    ("GbooleanFTT" (g-boolean (java::boolean-value nil)
                              (java::boolean-value t)
                              (java::boolean-value t)))
    ("GbooleanFTF" (g-boolean (java::boolean-value nil)
                              (java::boolean-value t)
                              (java::boolean-value nil)))
    ("GbooleanFFT" (g-boolean (java::boolean-value nil)
                              (java::boolean-value nil)
                              (java::boolean-value t)))
    ("GbooleanFFF" (g-boolean (java::boolean-value nil)
                              (java::boolean-value nil)
                              (java::boolean-value nil)))
    ;; F-INT:
    ("Fint0" (f-int (java::int-value 8)
                    (java::int-value 15)))
    ("Fint1" (f-int (java::int-value -280)
                    (java::int-value 3971)))
    ("Fint2" (f-int (java::int-value 1000000)
                    (java::int-value 1000000)))
    ;; G-INT:
    ("Gint0" (g-int (java::int-value 8383)
                    (java::int-value -3)
                    (java::int-value 0)))
    ("Gint1" (g-int (java::int-value -111)
                    (java::int-value 1383)
                    (java::int-value 90000)))
    ;; H-INT:
    ("Hint0" (h-int (java::int-value 64738)))
    ("Hint1" (h-int (java::int-value -64738)))))

(defconst *shallow-guarded-tests*
  (append *shallow-guarded-basic-tests*
          *shallow-guarded-more-tests*))
