; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
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
; which cannot include the functions in *ATJ-JAVA-PRIMITIVE-FNS*
; when :DEEP is NIL and :GUARDS is T.
; Thus, here we introduce wrappers for such functions,
; which are the ones that we want to test here.

;; boolean operations:

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

;; integer operations:

(defun test-int-plus (x)
  (declare (xargs :guard (java::int-value-p x)))
  (java::int-plus x))

(defun test-long-plus (x)
  (declare (xargs :guard (java::long-value-p x)))
  (java::long-plus x))

(defun test-int-minus (x)
  (declare (xargs :guard (java::int-value-p x)))
  (java::int-minus x))

(defun test-long-minus (x)
  (declare (xargs :guard (java::long-value-p x)))
  (java::long-minus x))

(defun test-int-not (x)
  (declare (xargs :guard (java::int-value-p x)))
  (java::int-not x))

(defun test-long-not (x)
  (declare (xargs :guard (java::long-value-p x)))
  (java::long-not x))

(defun test-int-add (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-add x y))

(defun test-long-add (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-add x y))

(defun test-int-sub (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-sub x y))

(defun test-long-sub (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-sub x y))

(defun test-int-mul (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-mul x y))

(defun test-long-mul (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-mul x y))

(defun test-int-div (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y)
                              (not (equal (java::int-value->int y) 0)))))
  (java::int-div x y))

(defun test-long-div (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y)
                              (not (equal (java::long-value->int y) 0)))))
  (java::long-div x y))

(defun test-int-rem (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y)
                              (not (equal (java::int-value->int y) 0)))))
  (java::int-rem x y))

(defun test-long-rem (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y)
                              (not (equal (java::long-value->int y) 0)))))
  (java::long-rem x y))

(defun test-int-and (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-and x y))

(defun test-long-and (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-and x y))

(defun test-int-xor (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-xor x y))

(defun test-long-xor (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-xor x y))

(defun test-int-ior (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-ior x y))

(defun test-long-ior (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-ior x y))

(defun test-int-eq (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-eq x y))

(defun test-long-eq (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-eq x y))

(defun test-int-neq (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-neq x y))

(defun test-long-neq (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-neq x y))

(defun test-int-less (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-less x y))

(defun test-long-less (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-less x y))

(defun test-int-lesseq (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-lesseq x y))

(defun test-long-lesseq (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-lesseq x y))

(defun test-int-great (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-great x y))

(defun test-long-great (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-great x y))

(defun test-int-greateq (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-greateq x y))

(defun test-long-greateq (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-greateq x y))

(defun test-int-int-shiftl (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-int-shiftl x y))

(defun test-long-long-shiftl (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-long-shiftl x y))

(defun test-long-int-shiftl (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::int-value-p y))))
  (java::long-int-shiftl x y))

(defun test-int-long-shiftl (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::long-value-p y))))
  (java::int-long-shiftl x y))

(defun test-int-int-shiftr (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-int-shiftr x y))

(defun test-long-long-shiftr (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-long-shiftr x y))

(defun test-long-int-shiftr (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::int-value-p y))))
  (java::long-int-shiftr x y))

(defun test-int-long-shiftr (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::long-value-p y))))
  (java::int-long-shiftr x y))

(defun test-int-int-ushiftr (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-int-ushiftr x y))

(defun test-long-long-ushiftr (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-long-ushiftr x y))

(defun test-long-int-ushiftr (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::int-value-p y))))
  (java::long-int-ushiftr x y))

(defun test-int-long-ushiftr (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::long-value-p y))))
  (java::int-long-ushiftr x y))

;; widening conversions:

(defun test-byte-to-short (x)
  (declare (xargs :guard (java::byte-value-p x)))
  (java::byte-to-short x))

(defun test-byte-to-int (x)
  (declare (xargs :guard (java::byte-value-p x)))
  (java::byte-to-int x))

(defun test-byte-to-long (x)
  (declare (xargs :guard (java::byte-value-p x)))
  (java::byte-to-long x))

(defun test-short-to-int (x)
  (declare (xargs :guard (java::short-value-p x)))
  (java::short-to-int x))

(defun test-short-to-long (x)
  (declare (xargs :guard (java::short-value-p x)))
  (java::short-to-long x))

(defun test-int-to-long (x)
  (declare (xargs :guard (java::int-value-p x)))
  (java::int-to-long x))

(defun test-char-to-int (x)
  (declare (xargs :guard (java::char-value-p x)))
  (java::char-to-int x))

(defun test-char-to-long (x)
  (declare (xargs :guard (java::char-value-p x)))
  (java::char-to-long x))

;; narrowing conversions:

(defun test-short-to-byte (x)
  (declare (xargs :guard (java::short-value-p x)))
  (java::short-to-byte x))

(defun test-int-to-byte (x)
  (declare (xargs :guard (java::int-value-p x)))
  (java::int-to-byte x))

(defun test-long-to-byte (x)
  (declare (xargs :guard (java::long-value-p x)))
  (java::long-to-byte x))

(defun test-char-to-byte (x)
  (declare (xargs :guard (java::char-value-p x)))
  (java::char-to-byte x))

(defun test-int-to-short (x)
  (declare (xargs :guard (java::int-value-p x)))
  (java::int-to-short x))

(defun test-long-to-short (x)
  (declare (xargs :guard (java::long-value-p x)))
  (java::long-to-short x))

(defun test-char-to-short (x)
  (declare (xargs :guard (java::char-value-p x)))
  (java::char-to-short x))

(defun test-long-to-int (x)
  (declare (xargs :guard (java::long-value-p x)))
  (java::long-to-int x))

(defun test-short-to-char (x)
  (declare (xargs :guard (java::short-value-p x)))
  (java::short-to-char x))

(defun test-int-to-char (x)
  (declare (xargs :guard (java::int-value-p x)))
  (java::int-to-char x))

(defun test-long-to-char (x)
  (declare (xargs :guard (java::long-value-p x)))
  (java::long-to-char x))

;; widening and narrowing conversions:

(defun test-byte-to-char (x)
  (declare (xargs :guard (java::byte-value-p x)))
  (java::byte-to-char x))

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

(defun f-long (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-add (java::long-mul (java::long-value 2) x)
                  (java::long-mul y y)))

(defun g-long (x y z)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y)
                              (java::long-value-p z))))
  (java::long-long-shiftl (java::long-sub x
                                          (java::long-and y z))
                          (java::long-not z)))

(defun h-long (x)
  (declare (xargs :guard (and (java::long-value-p x))))
  (java::long-xor (java::long-div x (java::long-value 119))
                  (java::long-rem x (java::long-value -373))))

(defun f-float (x y z)
  (declare (xargs :guard (and (java::float-value-p x)
                              (java::float-value-p y)
                              (java::float-value-p z))))
  (java::float-add (java::float-mul x y) z))

(defun f-double (x y z)
  (declare (xargs :guard (and (java::double-value-p x)
                              (java::double-value-p y)
                              (java::double-value-p z))))
  (java::double-sub (java::double-div x y) z))

(defun f-conv (x y z)
  (declare (xargs :guard (and (java::byte-value-p x)
                              (java::short-value-p y)
                              (java::long-value-p z))))
  (java::int-mul (java::int-add (java::byte-to-int x)
                                (java::short-to-int y))
                 (java::long-to-int z)))

(defun g-conv (x y)
  (declare (xargs :guard (and (java::float-value-p x)
                              (java::double-value-p y))))
  (java::double-mul (java::float-to-double x)
                    (java::double-add (java::int-to-double (java::int-value 2))
                                      y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Wrap-around factorial over Java ints.

(define factorial-int ((n java::int-value-p))
  :guard (java::boolean-value->bool (java::int-greateq n (java::int-value 0)))
  :returns (result java::int-value-p)
  (if (mbt (and (java::int-value-p n)
                (java::boolean-value->bool
                 (java::int-greateq n (java::int-value 0)))))
      (if (java::boolean-value->bool (java::int-eq n (java::int-value 0)))
          (java::int-value 1)
        (java::int-mul n
                       (factorial-int (java::int-sub n
                                                     (java::int-value 1)))))
    (java::int-value 1))
  :measure (nfix (java::int-value->int n))
  :hints (("Goal" :in-theory (enable java::int-eq
                                     java::int-greateq
                                     java::int-sub
                                     sbyte32p)))
  :verify-guards nil ; done below
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))
  ///
  (verify-guards factorial-int
    :hints (("Goal" :in-theory (enable java::int-eq
                                       java::int-greateq
                                       java::int-sub
                                       java::int-value-p
                                       sbyte32p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Wrap-around factorial over Java longs.

(define factorial-long ((n java::long-value-p))
  :guard (java::boolean-value->bool (java::long-greateq n (java::long-value 0)))
  :returns (result java::long-value-p)
  (if (mbt (and (java::long-value-p n)
                (java::boolean-value->bool
                 (java::long-greateq n (java::long-value 0)))))
      (if (java::boolean-value->bool (java::long-eq n (java::long-value 0)))
          (java::long-value 1)
        (java::long-mul n
                        (factorial-long (java::long-sub n
                                                        (java::long-value 1)))))
    (java::long-value 1))
  :measure (nfix (java::long-value->int n))
  :hints (("Goal" :in-theory (enable java::long-eq
                                     java::long-greateq
                                     java::long-sub
                                     sbyte64p)))
  :verify-guards nil ; done below
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))
  ///
  (verify-guards factorial-long
    :hints (("Goal" :in-theory (enable java::long-eq
                                       java::long-greateq
                                       java::long-sub
                                       java::long-value-p
                                       sbyte64p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests for the functions above (except the ones involving floating-point),
; when :DEEP is NIL and :GUARDS is T.

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
    ;; long unary plus:
    ("LongPlus0" (test-long-plus (java::long-value 0)))
    ("LongPlus1" (test-long-plus (java::long-value 1)))
    ("LongPlus2" (test-long-plus (java::long-value 875753)))
    ("LongPlus3" (test-long-plus (java::long-value -16)))
    ("LongPlus4" (test-long-plus (java::long-value -1600000)))
    ;; int unary minus:
    ("IntMinus0" (test-int-minus (java::int-value 0)))
    ("IntMinus1" (test-int-minus (java::int-value 1)))
    ("IntMinus2" (test-int-minus (java::int-value 875753)))
    ("IntMinus3" (test-int-minus (java::int-value -16)))
    ("IntMinus4" (test-int-minus (java::int-value -1600000)))
    ;; long unary minus:
    ("LongMinus0" (test-long-minus (java::long-value 0)))
    ("LongMinus1" (test-long-minus (java::long-value 1)))
    ("LongMinus2" (test-long-minus (java::long-value 875753)))
    ("LongMinus3" (test-long-minus (java::long-value -16)))
    ("LongMinus4" (test-long-minus (java::long-value -1600000)))
    ;; int bitwise complement:
    ("IntNot0" (test-int-not (java::int-value 0)))
    ("IntNot1" (test-int-not (java::int-value 1)))
    ("IntNot2" (test-int-not (java::int-value 875753)))
    ("IntNot3" (test-int-not (java::int-value -16)))
    ("IntNot4" (test-int-not (java::int-value -1600000)))
    ;; long bitwise complement:
    ("LongNot0" (test-long-not (java::long-value 0)))
    ("LongNot1" (test-long-not (java::long-value 1)))
    ("LongNot2" (test-long-not (java::long-value 875753)))
    ("LongNot3" (test-long-not (java::long-value -16)))
    ("LongNot4" (test-long-not (java::long-value -1600000)))
    ;; int addition:
    ("IntAdd0" (test-int-add (java::int-value 2)
                             (java::int-value 3)))
    ("IntAdd1" (test-int-add (java::int-value -2)
                             (java::int-value -3)))
    ("IntAdd2" (test-int-add (java::int-value 2)
                             (java::int-value -3)))
    ("IntAdd3" (test-int-add (java::int-value -2)
                             (java::int-value 3)))
    ("IntAdd4" (test-int-add (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; long addition:
    ("LongAdd0" (test-long-add (java::long-value 2)
                               (java::long-value 3)))
    ("LongAdd1" (test-long-add (java::long-value -2)
                               (java::long-value -3)))
    ("LongAdd2" (test-long-add (java::long-value 2)
                               (java::long-value -3)))
    ("LongAdd3" (test-long-add (java::long-value -2)
                               (java::long-value 3)))
    ("LongAdd4" (test-long-add (java::long-value 2372792)
                               (java::long-value -8882289)))
    ;; int subtraction:
    ("IntSub0" (test-int-sub (java::int-value 2)
                             (java::int-value 3)))
    ("IntSub1" (test-int-sub (java::int-value -2)
                             (java::int-value -3)))
    ("IntSub2" (test-int-sub (java::int-value 2)
                             (java::int-value -3)))
    ("IntSub3" (test-int-sub (java::int-value -2)
                             (java::int-value 3)))
    ("IntSub4" (test-int-sub (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; long subtraction:
    ("LongSub0" (test-long-sub (java::long-value 2)
                               (java::long-value 3)))
    ("LongSub1" (test-long-sub (java::long-value -2)
                               (java::long-value -3)))
    ("LongSub2" (test-long-sub (java::long-value 2)
                               (java::long-value -3)))
    ("LongSub3" (test-long-sub (java::long-value -2)
                               (java::long-value 3)))
    ("LongSub4" (test-long-sub (java::long-value 2372792)
                               (java::long-value -8882289)))
    ;; int multiplication:
    ("IntMul0" (test-int-mul (java::int-value 2)
                             (java::int-value 3)))
    ("IntMul1" (test-int-mul (java::int-value -2)
                             (java::int-value -3)))
    ("IntMul2" (test-int-mul (java::int-value 2)
                             (java::int-value -3)))
    ("IntMul3" (test-int-mul (java::int-value -2)
                             (java::int-value 3)))
    ("IntMul4" (test-int-mul (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; long multiplication:
    ("LongMul0" (test-long-mul (java::long-value 2)
                               (java::long-value 3)))
    ("LongMul1" (test-long-mul (java::long-value -2)
                               (java::long-value -3)))
    ("LongMul2" (test-long-mul (java::long-value 2)
                               (java::long-value -3)))
    ("LongMul3" (test-long-mul (java::long-value -2)
                               (java::long-value 3)))
    ("LongMul4" (test-long-mul (java::long-value 2372792)
                               (java::long-value -8882289)))
    ;; int division:
    ("IntDiv0" (test-int-div (java::int-value 2)
                             (java::int-value 3)))
    ("IntDiv1" (test-int-div (java::int-value -2)
                             (java::int-value -3)))
    ("IntDiv2" (test-int-div (java::int-value 2)
                             (java::int-value -3)))
    ("IntDiv3" (test-int-div (java::int-value -2)
                             (java::int-value 3)))
    ("IntDiv4" (test-int-div (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; long division:
    ("LongDiv0" (test-long-div (java::long-value 2)
                               (java::long-value 3)))
    ("LongDiv1" (test-long-div (java::long-value -2)
                               (java::long-value -3)))
    ("LongDiv2" (test-long-div (java::long-value 2)
                               (java::long-value -3)))
    ("LongDiv3" (test-long-div (java::long-value -2)
                               (java::long-value 3)))
    ("LongDiv4" (test-long-div (java::long-value 2372792)
                               (java::long-value -8882289)))
    ;; int remainder:
    ("IntRem0" (test-int-rem (java::int-value 2)
                             (java::int-value 3)))
    ("IntRem1" (test-int-rem (java::int-value -2)
                             (java::int-value -3)))
    ("IntRem2" (test-int-rem (java::int-value 2)
                             (java::int-value -3)))
    ("IntRem3" (test-int-rem (java::int-value -2)
                             (java::int-value 3)))
    ("IntRem4" (test-int-rem (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; long remainder:
    ("LongRem0" (test-long-rem (java::long-value 2)
                               (java::long-value 3)))
    ("LongRem1" (test-long-rem (java::long-value -2)
                               (java::long-value -3)))
    ("LongRem2" (test-long-rem (java::long-value 2)
                               (java::long-value -3)))
    ("LongRem3" (test-long-rem (java::long-value -2)
                               (java::long-value 3)))
    ("LongRem4" (test-long-rem (java::long-value 2372792)
                               (java::long-value -8882289)))
    ;; int bitwise conjunction:
    ("IntAnd0" (test-int-and (java::int-value 2)
                             (java::int-value 3)))
    ("IntAnd1" (test-int-and (java::int-value -2)
                             (java::int-value -3)))
    ("IntAnd2" (test-int-and (java::int-value 2)
                             (java::int-value -3)))
    ("IntAnd3" (test-int-and (java::int-value -2)
                             (java::int-value 3)))
    ("IntAnd4" (test-int-and (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; long bitwise conjunction:
    ("LongAnd0" (test-long-and (java::long-value 2)
                               (java::long-value 3)))
    ("LongAnd1" (test-long-and (java::long-value -2)
                               (java::long-value -3)))
    ("LongAnd2" (test-long-and (java::long-value 2)
                               (java::long-value -3)))
    ("LongAnd3" (test-long-and (java::long-value -2)
                               (java::long-value 3)))
    ("LongAnd4" (test-long-and (java::long-value 2372792)
                               (java::long-value -8882289)))
    ;; int bitwise exclusive disjunction:
    ("IntXor0" (test-int-xor (java::int-value 2)
                             (java::int-value 3)))
    ("IntXor1" (test-int-xor (java::int-value -2)
                             (java::int-value -3)))
    ("IntXor2" (test-int-xor (java::int-value 2)
                             (java::int-value -3)))
    ("IntXor3" (test-int-xor (java::int-value -2)
                             (java::int-value 3)))
    ("IntXor4" (test-int-xor (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; long bitwise exclusive disjunction:
    ("LongXor0" (test-long-xor (java::long-value 2)
                               (java::long-value 3)))
    ("LongXor1" (test-long-xor (java::long-value -2)
                               (java::long-value -3)))
    ("LongXor2" (test-long-xor (java::long-value 2)
                               (java::long-value -3)))
    ("LongXor3" (test-long-xor (java::long-value -2)
                               (java::long-value 3)))
    ("LongXor4" (test-long-xor (java::long-value 2372792)
                               (java::long-value -8882289)))
    ;; int bitwise inclusive disjunction:
    ("IntIor0" (test-int-ior (java::int-value 2)
                             (java::int-value 3)))
    ("IntIor1" (test-int-ior (java::int-value -2)
                             (java::int-value -3)))
    ("IntIor2" (test-int-ior (java::int-value 2)
                             (java::int-value -3)))
    ("IntIor3" (test-int-ior (java::int-value -2)
                             (java::int-value 3)))
    ("IntIor4" (test-int-ior (java::int-value 2372792)
                             (java::int-value -8882289)))
    ;; long bitwise inclusive disjunction:
    ("LongIor0" (test-long-ior (java::long-value 2)
                               (java::long-value 3)))
    ("LongIor1" (test-long-ior (java::long-value -2)
                               (java::long-value -3)))
    ("LongIor2" (test-long-ior (java::long-value 2)
                               (java::long-value -3)))
    ("LongIor3" (test-long-ior (java::long-value -2)
                               (java::long-value 3)))
    ("LongIor4" (test-long-ior (java::long-value 2372792)
                               (java::long-value -8882289)))
    ;; int equality:
    ("IntEq0" (test-int-eq (java::int-value 2829)
                           (java::int-value 2829)))
    ("IntEq1" (test-int-eq (java::int-value -373)
                           (java::int-value 0)))
    ("IntEq2" (test-int-eq (java::int-value 20)
                           (java::int-value 10)))
    ;; long equality:
    ("LongEq0" (test-long-eq (java::long-value 2829)
                             (java::long-value 2829)))
    ("LongEq1" (test-long-eq (java::long-value -373)
                             (java::long-value 0)))
    ("LongEq2" (test-long-eq (java::long-value 20)
                             (java::long-value 10)))
    ;; int non-equality:
    ("IntNeq0" (test-int-neq (java::int-value 2829)
                             (java::int-value 2829)))
    ("IntNeq1" (test-int-neq (java::int-value -373)
                             (java::int-value 0)))
    ("IntNeq2" (test-int-neq (java::int-value 20)
                             (java::int-value 10)))
    ;; long non-equality:
    ("LongNeq0" (test-long-neq (java::long-value 2829)
                               (java::long-value 2829)))
    ("LongNeq1" (test-long-neq (java::long-value -373)
                               (java::long-value 0)))
    ("LongNeq2" (test-long-neq (java::long-value 20)
                               (java::long-value 10)))
    ;; int less-than:
    ("IntLess0" (test-int-less (java::int-value 2829)
                               (java::int-value 2829)))
    ("IntLess1" (test-int-less (java::int-value -373)
                               (java::int-value 0)))
    ("IntLess2" (test-int-less (java::int-value 20)
                               (java::int-value 10)))
    ;; long less-than:
    ("LongLess0" (test-long-less (java::long-value 2829)
                                 (java::long-value 2829)))
    ("LongLess1" (test-long-less (java::long-value -373)
                                 (java::long-value 0)))
    ("LongLess2" (test-long-less (java::long-value 20)
                                 (java::long-value 10)))
    ;; int less-than-or-equal-to:
    ("IntLesseq0" (test-int-lesseq (java::int-value 2829)
                                   (java::int-value 2829)))
    ("IntLesseq1" (test-int-lesseq (java::int-value -373)
                                   (java::int-value 0)))
    ("IntLesseq2" (test-int-lesseq (java::int-value 20)
                                   (java::int-value 10)))
    ;; long less-than-or-equal-to:
    ("LongLesseq0" (test-long-lesseq (java::long-value 2829)
                                     (java::long-value 2829)))
    ("LongLesseq1" (test-long-lesseq (java::long-value -373)
                                     (java::long-value 0)))
    ("LongLesseq2" (test-long-lesseq (java::long-value 20)
                                     (java::long-value 10)))
    ;; int greater-than:
    ("IntGreat0" (test-int-great (java::int-value 2829)
                                 (java::int-value 2829)))
    ("IntGreat1" (test-int-great (java::int-value -373)
                                 (java::int-value 0)))
    ("IntGreat2" (test-int-great (java::int-value 20)
                                 (java::int-value 10)))
    ;; long greater-than:
    ("LongGreat0" (test-long-great (java::long-value 2829)
                                   (java::long-value 2829)))
    ("LongGreat1" (test-long-great (java::long-value -373)
                                   (java::long-value 0)))
    ("LongGreat2" (test-long-great (java::long-value 20)
                                   (java::long-value 10)))
    ;; int greater-than-or-equal-to:
    ("IntGreateq0" (test-int-greateq (java::int-value 2829)
                                     (java::int-value 2829)))
    ("IntGreateq1" (test-int-greateq (java::int-value -373)
                                     (java::int-value 0)))
    ("IntGreateq2" (test-int-greateq (java::int-value 20)
                                     (java::int-value 10)))
    ;; long greater-than-or-equal-to:
    ("LongGreateq0" (test-long-greateq (java::long-value 2829)
                                       (java::long-value 2829)))
    ("LongGreateq1" (test-long-greateq (java::long-value -373)
                                       (java::long-value 0)))
    ("LongGreateq2" (test-long-greateq (java::long-value 20)
                                       (java::long-value 10)))
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
    ;; long left shift by long distance:
    ("LongLongShiftl0" (test-long-long-shiftl (java::long-value 2)
                                              (java::long-value 3)))
    ("LongLongShiftl1" (test-long-long-shiftl (java::long-value -2)
                                              (java::long-value -3)))
    ("LongLongShiftl2" (test-long-long-shiftl (java::long-value 2)
                                              (java::long-value -3)))
    ("LongLongShiftl3" (test-long-long-shiftl (java::long-value -2)
                                              (java::long-value 3)))
    ("LongLongShiftl4" (test-long-long-shiftl (java::long-value 2372792)
                                              (java::long-value -8882289)))
    ;; long left shift by int distance:
    ("LongIntShiftl0" (test-long-int-shiftl (java::long-value 2)
                                            (java::int-value 3)))
    ("LongIntShiftl1" (test-long-int-shiftl (java::long-value -2)
                                            (java::int-value -3)))
    ("LongIntShiftl2" (test-long-int-shiftl (java::long-value 2)
                                            (java::int-value -3)))
    ("LongIntShiftl3" (test-long-int-shiftl (java::long-value -2)
                                            (java::int-value 3)))
    ("LongIntShiftl4" (test-long-int-shiftl (java::long-value 2372792)
                                            (java::int-value -8882289)))
    ;; int left shift by long distance:
    ("IntLongShiftl0" (test-int-long-shiftl (java::int-value 2)
                                            (java::long-value 3)))
    ("IntLongShiftl1" (test-int-long-shiftl (java::int-value -2)
                                            (java::long-value -3)))
    ("IntLongShiftl2" (test-int-long-shiftl (java::int-value 2)
                                            (java::long-value -3)))
    ("IntLongShiftl3" (test-int-long-shiftl (java::int-value -2)
                                            (java::long-value 3)))
    ("IntLongShiftl4" (test-int-long-shiftl (java::int-value 2372792)
                                            (java::long-value -8882289)))
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
    ;; long right shift by long distance:
    ("LongLongShiftr0" (test-long-long-shiftr (java::long-value 2)
                                              (java::long-value 3)))
    ("LongLongShiftr1" (test-long-long-shiftr (java::long-value -2)
                                              (java::long-value -3)))
    ("LongLongShiftr2" (test-long-long-shiftr (java::long-value 2)
                                              (java::long-value -3)))
    ("LongLongShiftr3" (test-long-long-shiftr (java::long-value -2)
                                              (java::long-value 3)))
    ("LongLongShiftr4" (test-long-long-shiftr (java::long-value 2372792)
                                              (java::long-value -8882289)))
    ;; long right shift by int distance:
    ("LongIntShiftr0" (test-long-int-shiftr (java::long-value 2)
                                            (java::int-value 3)))
    ("LongIntShiftr1" (test-long-int-shiftr (java::long-value -2)
                                            (java::int-value -3)))
    ("LongIntShiftr2" (test-long-int-shiftr (java::long-value 2)
                                            (java::int-value -3)))
    ("LongIntShiftr3" (test-long-int-shiftr (java::long-value -2)
                                            (java::int-value 3)))
    ("LongIntShiftr4" (test-long-int-shiftr (java::long-value 2372792)
                                            (java::int-value -8882289)))
    ;; int right shift by long distance:
    ("IntLongShiftr0" (test-int-long-shiftr (java::int-value 2)
                                            (java::long-value 3)))
    ("IntLongShiftr1" (test-int-long-shiftr (java::int-value -2)
                                            (java::long-value -3)))
    ("IntLongShiftr2" (test-int-long-shiftr (java::int-value 2)
                                            (java::long-value -3)))
    ("IntLongShiftr3" (test-int-long-shiftr (java::int-value -2)
                                            (java::long-value 3)))
    ("IntLongShiftr4" (test-int-long-shiftr (java::int-value 2372792)
                                            (java::long-value -8882289)))
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
                                            (java::int-value -8882289)))
    ;; long unsigned right shift by long distance:
    ("LongLongUshiftr0" (test-long-long-ushiftr (java::long-value 2)
                                                (java::long-value 3)))
    ("LongLongUshiftr1" (test-long-long-ushiftr (java::long-value -2)
                                                (java::long-value -3)))
    ("LongLongUshiftr2" (test-long-long-ushiftr (java::long-value 2)
                                                (java::long-value -3)))
    ("LongLongUshiftr3" (test-long-long-ushiftr (java::long-value -2)
                                                (java::long-value 3)))
    ("LongLongUshiftr4" (test-long-long-ushiftr (java::long-value 2372792)
                                                (java::long-value -8882289)))
    ;; long unsigned right shift by int distance:
    ("LongIntUshiftr0" (test-long-int-ushiftr (java::long-value 2)
                                              (java::int-value 3)))
    ("LongIntUshiftr1" (test-long-int-ushiftr (java::long-value -2)
                                              (java::int-value -3)))
    ("LongIntUshiftr2" (test-long-int-ushiftr (java::long-value 2)
                                              (java::int-value -3)))
    ("LongIntUshiftr3" (test-long-int-ushiftr (java::long-value -2)
                                              (java::int-value 3)))
    ("LongIntUshiftr4" (test-long-int-ushiftr (java::long-value 2372792)
                                              (java::int-value -8882289)))
    ;; int unsigned right shift by long distance:
    ("IntLongUshiftr0" (test-int-long-ushiftr (java::int-value 2)
                                              (java::long-value 3)))
    ("IntLongUshiftr1" (test-int-long-ushiftr (java::int-value -2)
                                              (java::long-value -3)))
    ("IntLongUshiftr2" (test-int-long-ushiftr (java::int-value 2)
                                              (java::long-value -3)))
    ("IntLongUshiftr3" (test-int-long-ushiftr (java::int-value -2)
                                              (java::long-value 3)))
    ("IntLongUshiftr4" (test-int-long-ushiftr (java::int-value 2372792)
                                              (java::long-value -8882289)))
    ;; byte to short widening conversion:
    ("ByteToShort0" (test-byte-to-short (java::byte-value 0)))
    ("ByteToShort1" (test-byte-to-short (java::byte-value -100)))
    ("ByteToShort2" (test-byte-to-short (java::byte-value 100)))
    ;; byte to int widening conversion:
    ("ByteToInt0" (test-byte-to-int (java::byte-value 0)))
    ("ByteToInt1" (test-byte-to-int (java::byte-value -100)))
    ("ByteToInt2" (test-byte-to-int (java::byte-value 100)))
    ;; byte to long widening conversion:
    ("ByteToLong0" (test-byte-to-long (java::byte-value 0)))
    ("ByteToLong1" (test-byte-to-long (java::byte-value -100)))
    ("ByteToLong2" (test-byte-to-long (java::byte-value 100)))
    ;; short to int widening conversion:
    ("ShortToInt0" (test-short-to-int (java::short-value 0)))
    ("ShortToInt1" (test-short-to-int (java::short-value -100)))
    ("ShortToInt2" (test-short-to-int (java::short-value 100)))
    ("ShortToInt3" (test-short-to-int (java::short-value -10000)))
    ("ShortToInt4" (test-short-to-int (java::short-value 10000)))
    ;; short to long widening conversion:
    ("ShortToLong0" (test-short-to-long (java::short-value 0)))
    ("ShortToLong1" (test-short-to-long (java::short-value -100)))
    ("ShortToLong2" (test-short-to-long (java::short-value 100)))
    ("ShortToLong3" (test-short-to-long (java::short-value -10000)))
    ("ShortToLong4" (test-short-to-long (java::short-value 10000)))
    ;; int to long widening conversion:
    ("IntToLong0" (test-int-to-long (java::int-value 0)))
    ("IntToLong1" (test-int-to-long (java::int-value -100)))
    ("IntToLong2" (test-int-to-long (java::int-value 100)))
    ("IntToLong3" (test-int-to-long (java::int-value -10000)))
    ("IntToLong4" (test-int-to-long (java::int-value 10000)))
    ("IntToLong5" (test-int-to-long (java::int-value -10000000)))
    ("IntToLong6" (test-int-to-long (java::int-value 10000000)))
    ;; char to int widening conversion:
    ("CharToInt0" (test-char-to-int (java::char-value 0)))
    ("CharToInt1" (test-char-to-int (java::char-value 37)))
    ("CharToInt2" (test-char-to-int (java::char-value 100)))
    ("CharToInt3" (test-char-to-int (java::char-value 637)))
    ("CharToInt4" (test-char-to-int (java::char-value 10000)))
    ;; char to long widening conversion:
    ("CharToLong0" (test-char-to-long (java::char-value 0)))
    ("CharToLong1" (test-char-to-long (java::char-value 37)))
    ("CharToLong2" (test-char-to-long (java::char-value 100)))
    ("CharToLong3" (test-char-to-long (java::char-value 637)))
    ("CharToLong4" (test-char-to-long (java::char-value 10000)))
    ;; short to byte narrowing conversion:
    ("ShortToByte0" (test-short-to-byte (java::short-value 0)))
    ("ShortToByte1" (test-short-to-byte (java::short-value -100)))
    ("ShortToByte2" (test-short-to-byte (java::short-value 100)))
    ("ShortToByte3" (test-short-to-byte (java::short-value -10000)))
    ("ShortToByte4" (test-short-to-byte (java::short-value 10000)))
    ;; int to byte narrowing conversion:
    ("IntToByte0" (test-int-to-byte (java::int-value 0)))
    ("IntToByte1" (test-int-to-byte (java::int-value -100)))
    ("IntToByte2" (test-int-to-byte (java::int-value 100)))
    ("IntToByte3" (test-int-to-byte (java::int-value -10000)))
    ("IntToByte4" (test-int-to-byte (java::int-value 10000)))
    ("IntToByte5" (test-int-to-byte (java::int-value -10000000)))
    ("IntToByte6" (test-int-to-byte (java::int-value 10000000)))
    ;; long to byte narrowing conversion:
    ("LongToByte0" (test-long-to-byte (java::long-value 0)))
    ("LongToByte1" (test-long-to-byte (java::long-value -100)))
    ("LongToByte2" (test-long-to-byte (java::long-value 100)))
    ("LongToByte3" (test-long-to-byte (java::long-value -10000)))
    ("LongToByte4" (test-long-to-byte (java::long-value 10000)))
    ("LongToByte5" (test-long-to-byte (java::long-value -10000000)))
    ("LongToByte6" (test-long-to-byte (java::long-value 10000000)))
    ("LongToByte7" (test-long-to-byte (java::long-value -100000000000)))
    ("LongToByte8" (test-long-to-byte (java::long-value 100000000000)))
    ;; char to byte narrowing conversion:
    ("CharToByte0" (test-char-to-byte (java::char-value 0)))
    ("CharToByte1" (test-char-to-byte (java::char-value 37)))
    ("CharToByte2" (test-char-to-byte (java::char-value 100)))
    ("CharToByte3" (test-char-to-byte (java::char-value 637)))
    ("CharToByte4" (test-char-to-byte (java::char-value 10000)))
    ;; int to short narrowing conversion:
    ("IntToShort0" (test-int-to-short (java::int-value 0)))
    ("IntToShort1" (test-int-to-short (java::int-value -100)))
    ("IntToShort2" (test-int-to-short (java::int-value 100)))
    ("IntToShort3" (test-int-to-short (java::int-value -10000)))
    ("IntToShort4" (test-int-to-short (java::int-value 10000)))
    ("IntToShort5" (test-int-to-short (java::int-value -10000000)))
    ("IntToShort6" (test-int-to-short (java::int-value 10000000)))
    ;; long to short narrowing conversion:
    ("LongToShort0" (test-long-to-short (java::long-value 0)))
    ("LongToShort1" (test-long-to-short (java::long-value -100)))
    ("LongToShort2" (test-long-to-short (java::long-value 100)))
    ("LongToShort3" (test-long-to-short (java::long-value -10000)))
    ("LongToShort4" (test-long-to-short (java::long-value 10000)))
    ("LongToShort5" (test-long-to-short (java::long-value -10000000)))
    ("LongToShort6" (test-long-to-short (java::long-value 10000000)))
    ("LongToShort7" (test-long-to-short (java::long-value -100000000000)))
    ("LongToShort8" (test-long-to-short (java::long-value 100000000000)))
    ;; char to short narrowing conversion:
    ("CharToShort0" (test-char-to-short (java::char-value 0)))
    ("CharToShort1" (test-char-to-short (java::char-value 37)))
    ("CharToShort2" (test-char-to-short (java::char-value 100)))
    ("CharToShort3" (test-char-to-short (java::char-value 637)))
    ("CharToShort4" (test-char-to-short (java::char-value 10000)))
    ;; long to int narrowing conversion:
    ("LongToInt0" (test-long-to-int (java::long-value 0)))
    ("LongToInt1" (test-long-to-int (java::long-value -100)))
    ("LongToInt2" (test-long-to-int (java::long-value 100)))
    ("LongToInt3" (test-long-to-int (java::long-value -10000)))
    ("LongToInt4" (test-long-to-int (java::long-value 10000)))
    ("LongToInt5" (test-long-to-int (java::long-value -10000000)))
    ("LongToInt6" (test-long-to-int (java::long-value 10000000)))
    ("LongToInt7" (test-long-to-int (java::long-value -100000000000)))
    ("LongToInt8" (test-long-to-int (java::long-value 100000000000)))
    ;; short to char narrowing conversion:
    ("ShortToChar0" (test-short-to-char (java::short-value 0)))
    ("ShortToChar1" (test-short-to-char (java::short-value -100)))
    ("ShortToChar2" (test-short-to-char (java::short-value 100)))
    ("ShortToChar3" (test-short-to-char (java::short-value -10000)))
    ("ShortToChar4" (test-short-to-char (java::short-value 10000)))
    ;; int to char narrowing conversion:
    ("IntToChar0" (test-int-to-char (java::int-value 0)))
    ("IntToChar1" (test-int-to-char (java::int-value -100)))
    ("IntToChar2" (test-int-to-char (java::int-value 100)))
    ("IntToChar3" (test-int-to-char (java::int-value -10000)))
    ("IntToChar4" (test-int-to-char (java::int-value 10000)))
    ("IntToChar5" (test-int-to-char (java::int-value -10000000)))
    ("IntToChar6" (test-int-to-char (java::int-value 10000000)))
    ;; long to char narrowing conversion:
    ("LongToChar0" (test-long-to-char (java::long-value 0)))
    ("LongToChar1" (test-long-to-char (java::long-value -100)))
    ("LongToChar2" (test-long-to-char (java::long-value 100)))
    ("LongToChar3" (test-long-to-char (java::long-value -10000)))
    ("LongToChar4" (test-long-to-char (java::long-value 10000)))
    ("LongToChar5" (test-long-to-char (java::long-value -10000000)))
    ("LongToChar6" (test-long-to-char (java::long-value 10000000)))
    ("LongToChar7" (test-long-to-char (java::long-value -100000000000)))
    ("LongToChar8" (test-long-to-char (java::long-value 100000000000)))
    ;; byte to char widening and narrowing conversion:
    ("ByteToChar0" (test-byte-to-char (java::byte-value 0)))
    ("ByteToChar1" (test-byte-to-char (java::byte-value -100)))
    ("ByteToChar2" (test-byte-to-char (java::byte-value 100)))))

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
    ("Hint1" (h-int (java::int-value -64738)))
    ;; F-LONG:
    ("Flong0" (f-long (java::long-value 8)
                      (java::long-value 15)))
    ("Flong1" (f-long (java::long-value -280)
                      (java::long-value 3971)))
    ("Flong2" (f-long (java::long-value 1000000)
                      (java::long-value 1000000)))
    ;; G-LONG:
    ("Glong0" (g-long (java::long-value 8383)
                      (java::long-value -3)
                      (java::long-value 0)))
    ("Glong1" (g-long (java::long-value -111)
                      (java::long-value 1383)
                      (java::long-value 90000)))
    ;; H-LONG:
    ("Hlong0" (h-long (java::long-value 64738)))
    ("Hlong1" (h-long (java::long-value -64738)))
    ;; F-CONV
    ("Fconv0" (f-conv (java::byte-value 84)
                      (java::short-value 11887)
                      (java::long-value -29493203747628)))))

(defconst *shallow-guarded-factorial-int-tests*
  '(("FactorialInt0" (factorial-int (java::int-value 0)))
    ("FactorialInt1" (factorial-int (java::int-value 1)))
    ("FactorialInt2" (factorial-int (java::int-value 2)))
    ("FactorialInt3" (factorial-int (java::int-value 3)))
    ("FactorialInt4" (factorial-int (java::int-value 4)))
    ("FactorialInt5" (factorial-int (java::int-value 5)))
    ("FactorialInt10" (factorial-int (java::int-value 10)))
    ("FactorialInt100" (factorial-int (java::int-value 100)))
    ("FactorialInt1000" (factorial-int (java::int-value 1000)))
    ("FactorialInt10000" (factorial-int (java::int-value 10000)))
    ("FactorialInt100000" (factorial-int (java::int-value 100000)))
    ("FactorialInt1000000" (factorial-int (java::int-value 1000000)))))

(defconst *shallow-guarded-factorial-long-tests*
  '(("FactorialLong0" (factorial-long (java::long-value 0)))
    ("FactorialLong1" (factorial-long (java::long-value 1)))
    ("FactorialLong2" (factorial-long (java::long-value 2)))
    ("FactorialLong3" (factorial-long (java::long-value 3)))
    ("FactorialLong4" (factorial-long (java::long-value 4)))
    ("FactorialLong5" (factorial-long (java::long-value 5)))
    ("FactorialLong10" (factorial-long (java::long-value 10)))
    ("FactorialLong100" (factorial-long (java::long-value 100)))
    ("FactorialLong1000" (factorial-long (java::long-value 1000)))
    ("FactorialLong10000" (factorial-long (java::long-value 10000)))
    ("FactorialLong100000" (factorial-long (java::long-value 100000)))
    ("FactorialLong1000000" (factorial-long (java::long-value 1000000)))))

(defconst *shallow-guarded-tests*
  (append *shallow-guarded-basic-tests*
          *shallow-guarded-more-tests*
          *shallow-guarded-factorial-int-tests*
          *shallow-guarded-factorial-long-tests*))
