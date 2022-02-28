; Java Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../../language/primitive-operations")
(include-book "../../language/primitive-conversions")

(include-book "../atj" :ttags ((:open-output-channel!) (:oslib) (:quicklisp) :quicklisp.osicat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the generation of Java code
; that manipulates Java primitive values.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; As explained in the ATJ user documentation,
; the tests passed to :TESTS may only involve
; the target functions explicitly passed to ATJ,
; which cannot include the functions in *ATJ-JPRIM-FNS*
; when :DEEP is NIL and :GUARDS is T.
; Thus, here we introduce wrappers for such functions,
; which are the ones that we want to test here.
; We exclude the floating-point operations,
; since tests involving them are not supported yet.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; constructors:

(defun test-boolean-value (x)
  (declare (xargs :guard (booleanp x)))
  (java::boolean-value x))

(defun test-char-value (x)
  (declare (xargs :guard (ubyte16p x)))
  (java::char-value x))

(defun test-byte-value (x)
  (declare (xargs :guard (sbyte8p x)))
  (java::byte-value x))

(defun test-short-value (x)
  (declare (xargs :guard (sbyte16p x)))
  (java::short-value x))

(defun test-int-value (x)
  (declare (xargs :guard (sbyte32p x)))
  (java::int-value x))

(defun test-long-value (x)
  (declare (xargs :guard (sbyte64p x)))
  (java::long-value x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; deconstructors:

(defun test-boolean-value->bool (x)
  (declare (xargs :guard (java::boolean-valuep x)))
  (java::boolean-value->bool x))

(defun test-char-value->nat (x)
  (declare (xargs :guard (java::char-valuep x)))
  (java::char-value->nat x))

(defun test-byte-value->int (x)
  (declare (xargs :guard (java::byte-valuep x)))
  (java::byte-value->int x))

(defun test-short-value->int (x)
  (declare (xargs :guard (java::short-valuep x)))
  (java::short-value->int x))

(defun test-int-value->int (x)
  (declare (xargs :guard (java::int-valuep x)))
  (java::int-value->int x))

(defun test-long-value->int (x)
  (declare (xargs :guard (java::long-valuep x)))
  (java::long-value->int x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; unary operations:

;;;;;;;;;;;;;;;;;;;;

; boolean:

(defun test-boolean-not (x)
  (declare (xargs :guard (java::boolean-valuep x)))
  (java::boolean-not x))

;;;;;;;;;;;;;;;;;;;;

; integer:

(defun test-int-plus (x)
  (declare (xargs :guard (java::int-valuep x)))
  (java::int-plus x))

(defun test-long-plus (x)
  (declare (xargs :guard (java::long-valuep x)))
  (java::long-plus x))

(defun test-int-minus (x)
  (declare (xargs :guard (java::int-valuep x)))
  (java::int-minus x))

(defun test-long-minus (x)
  (declare (xargs :guard (java::long-valuep x)))
  (java::long-minus x))

(defun test-int-not (x)
  (declare (xargs :guard (java::int-valuep x)))
  (java::int-not x))

(defun test-long-not (x)
  (declare (xargs :guard (java::long-valuep x)))
  (java::long-not x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; binary operations:

;;;;;;;;;;;;;;;;;;;;

; boolean:

(defun test-boolean-and (x y)
  (declare (xargs :guard (and (java::boolean-valuep x)
                              (java::boolean-valuep y))))
  (java::boolean-and x y))

(defun test-boolean-xor (x y)
  (declare (xargs :guard (and (java::boolean-valuep x)
                              (java::boolean-valuep y))))
  (java::boolean-xor x y))

(defun test-boolean-ior (x y)
  (declare (xargs :guard (and (java::boolean-valuep x)
                              (java::boolean-valuep y))))
  (java::boolean-ior x y))

(defun test-boolean-eq (x y)
  (declare (xargs :guard (and (java::boolean-valuep x)
                              (java::boolean-valuep y))))
  (java::boolean-eq x y))

(defun test-boolean-neq (x y)
  (declare (xargs :guard (and (java::boolean-valuep x)
                              (java::boolean-valuep y))))
  (java::boolean-neq x y))

;;;;;;;;;;;;;;;;;;;;

; integer:

(defun test-int-add (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-add x y))

(defun test-long-add (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-add x y))

(defun test-int-sub (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-sub x y))

(defun test-long-sub (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-sub x y))

(defun test-int-mul (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-mul x y))

(defun test-long-mul (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-mul x y))

(defun test-int-div (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y)
                              (not (equal (java::int-value->int y) 0)))))
  (java::int-div x y))

(defun test-long-div (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y)
                              (not (equal (java::long-value->int y) 0)))))
  (java::long-div x y))

(defun test-int-rem (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y)
                              (not (equal (java::int-value->int y) 0)))))
  (java::int-rem x y))

(defun test-long-rem (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y)
                              (not (equal (java::long-value->int y) 0)))))
  (java::long-rem x y))

(defun test-int-and (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-and x y))

(defun test-long-and (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-and x y))

(defun test-int-xor (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-xor x y))

(defun test-long-xor (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-xor x y))

(defun test-int-ior (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-ior x y))

(defun test-long-ior (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-ior x y))

(defun test-int-eq (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-eq x y))

(defun test-long-eq (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-eq x y))

(defun test-int-neq (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-neq x y))

(defun test-long-neq (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-neq x y))

(defun test-int-less (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-less x y))

(defun test-long-less (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-less x y))

(defun test-int-lesseq (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-lesseq x y))

(defun test-long-lesseq (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-lesseq x y))

(defun test-int-great (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-great x y))

(defun test-long-great (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-great x y))

(defun test-int-greateq (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-greateq x y))

(defun test-long-greateq (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-greateq x y))

(defun test-int-int-shiftl (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-int-shiftl x y))

(defun test-long-long-shiftl (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-long-shiftl x y))

(defun test-long-int-shiftl (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::int-valuep y))))
  (java::long-int-shiftl x y))

(defun test-int-long-shiftl (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::long-valuep y))))
  (java::int-long-shiftl x y))

(defun test-int-int-shiftr (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-int-shiftr x y))

(defun test-long-long-shiftr (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-long-shiftr x y))

(defun test-long-int-shiftr (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::int-valuep y))))
  (java::long-int-shiftr x y))

(defun test-int-long-shiftr (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::long-valuep y))))
  (java::int-long-shiftr x y))

(defun test-int-int-ushiftr (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-int-ushiftr x y))

(defun test-long-long-ushiftr (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-long-ushiftr x y))

(defun test-long-int-ushiftr (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::int-valuep y))))
  (java::long-int-ushiftr x y))

(defun test-int-long-ushiftr (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::long-valuep y))))
  (java::int-long-ushiftr x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; conversions:

;;;;;;;;;;;;;;;;;;;;

; widening:

(defun test-byte-to-short (x)
  (declare (xargs :guard (java::byte-valuep x)))
  (java::byte-to-short x))

(defun test-byte-to-int (x)
  (declare (xargs :guard (java::byte-valuep x)))
  (java::byte-to-int x))

(defun test-byte-to-long (x)
  (declare (xargs :guard (java::byte-valuep x)))
  (java::byte-to-long x))

(defun test-short-to-int (x)
  (declare (xargs :guard (java::short-valuep x)))
  (java::short-to-int x))

(defun test-short-to-long (x)
  (declare (xargs :guard (java::short-valuep x)))
  (java::short-to-long x))

(defun test-int-to-long (x)
  (declare (xargs :guard (java::int-valuep x)))
  (java::int-to-long x))

(defun test-char-to-int (x)
  (declare (xargs :guard (java::char-valuep x)))
  (java::char-to-int x))

(defun test-char-to-long (x)
  (declare (xargs :guard (java::char-valuep x)))
  (java::char-to-long x))

;;;;;;;;;;;;;;;;;;;;

; narrowing:

(defun test-short-to-byte (x)
  (declare (xargs :guard (java::short-valuep x)))
  (java::short-to-byte x))

(defun test-int-to-byte (x)
  (declare (xargs :guard (java::int-valuep x)))
  (java::int-to-byte x))

(defun test-long-to-byte (x)
  (declare (xargs :guard (java::long-valuep x)))
  (java::long-to-byte x))

(defun test-char-to-byte (x)
  (declare (xargs :guard (java::char-valuep x)))
  (java::char-to-byte x))

(defun test-int-to-short (x)
  (declare (xargs :guard (java::int-valuep x)))
  (java::int-to-short x))

(defun test-long-to-short (x)
  (declare (xargs :guard (java::long-valuep x)))
  (java::long-to-short x))

(defun test-char-to-short (x)
  (declare (xargs :guard (java::char-valuep x)))
  (java::char-to-short x))

(defun test-long-to-int (x)
  (declare (xargs :guard (java::long-valuep x)))
  (java::long-to-int x))

(defun test-short-to-char (x)
  (declare (xargs :guard (java::short-valuep x)))
  (java::short-to-char x))

(defun test-int-to-char (x)
  (declare (xargs :guard (java::int-valuep x)))
  (java::int-to-char x))

(defun test-long-to-char (x)
  (declare (xargs :guard (java::long-valuep x)))
  (java::long-to-char x))

;;;;;;;;;;;;;;;;;;;;

; widening and narrowing:

(defun test-byte-to-char (x)
  (declare (xargs :guard (java::byte-valuep x)))
  (java::byte-to-char x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; More functions over (ACL2 representations of) Java primitive values.

(defun f-boolean (x y)
  (declare (xargs :guard (and (java::boolean-valuep x)
                              (java::boolean-valuep y))))
  (java::boolean-and (java::boolean-xor x y)
                     (java::boolean-ior x y)))

(defun g-boolean (x y z)
  (declare (xargs :guard (and (java::boolean-valuep x)
                              (java::boolean-valuep y)
                              (java::boolean-valuep z))))
  (java::boolean-eq (java::boolean-not x)
                    (java::boolean-neq y z)))

(defun f-int (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-add (java::int-mul (java::int-value 2) x)
                 (java::int-mul y y)))

(defun g-int (x y z)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y)
                              (java::int-valuep z))))
  (java::int-int-shiftl (java::int-sub x
                                       (java::int-and y z))
                        (java::int-not z)))

(defun h-int (x)
  (declare (xargs :guard (and (java::int-valuep x))))
  (java::int-xor (java::int-div x (java::int-value 119))
                 (java::int-rem x (java::int-value -373))))

(defun f-long (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-add (java::long-mul (java::long-value 2) x)
                  (java::long-mul y y)))

(defun g-long (x y z)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y)
                              (java::long-valuep z))))
  (java::long-long-shiftl (java::long-sub x
                                          (java::long-and y z))
                          (java::long-not z)))

(defun h-long (x)
  (declare (xargs :guard (and (java::long-valuep x))))
  (java::long-xor (java::long-div x (java::long-value 119))
                  (java::long-rem x (java::long-value -373))))

(defun f-float (x y z)
  (declare (xargs :guard (and (java::float-valuep x)
                              (java::float-valuep y)
                              (java::float-valuep z))))
  (java::float-add (java::float-mul x y) z))

(defun f-double (x y z)
  (declare (xargs :guard (and (java::double-valuep x)
                              (java::double-valuep y)
                              (java::double-valuep z))))
  (java::double-sub (java::double-div x y) z))

(defun f-conv (x y z)
  (declare (xargs :guard (and (java::byte-valuep x)
                              (java::short-valuep y)
                              (java::long-valuep z))))
  (java::int-mul (java::int-add (java::byte-to-int x)
                                (java::short-to-int y))
                 (java::long-to-int z)))

(defun g-conv (x y)
  (declare (xargs :guard (and (java::float-valuep x)
                              (java::double-valuep y))))
  (java::double-mul (java::float-to-double x)
                    (java::double-add (java::int-to-double (java::int-value 2))
                                      y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Wrap-around factorial over Java ints.

(define factorial-int ((n java::int-valuep))
  :guard (java::boolean-value->bool (java::int-greateq n (java::int-value 0)))
  :returns (result java::int-valuep)
  (if (mbt (and (java::int-valuep n)
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
                                       java::int-valuep
                                       sbyte32p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Wrap-around factorial over Java longs.

(define factorial-long ((n java::long-valuep))
  :guard (java::boolean-value->bool (java::long-greateq n (java::long-value 0)))
  :returns (result java::long-valuep)
  (if (mbt (and (java::long-valuep n)
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
                                       java::long-valuep
                                       sbyte64p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests for the functions above, when :DEEP is NIL and :GUARDS is T.

(defconst *shallow-guarded-basic-tests*
  '(;; boolean constructor:
    ("BooleanValueT" (test-boolean-value t))
    ("BooleanValueF" (test-boolean-value nil))
    ;; char constructor:
    ("CharValue0" (test-char-value 0))
    ("CharValue1" (test-char-value 60000))
    ("CharValue2" (test-char-value 256))
    ("CharValue3" (test-char-value 32))
    ("CharValue4" (test-char-value 65))
    ("CharValue5" (test-char-value 12345))
    ;; byte constructor:
    ("ByteValue0" (test-byte-value 0))
    ("ByteValue1" (test-byte-value -128))
    ("ByteValue2" (test-byte-value 127))
    ("ByteValue3" (test-byte-value -67))
    ("ByteValue4" (test-byte-value 88))
    ("ByteValue5" (test-byte-value 1))
    ;; short constructor:
    ("ShortValue0" (test-short-value 0))
    ("ShortValue1" (test-short-value -32768))
    ("ShortValue2" (test-short-value 32767))
    ("ShortValue3" (test-short-value 1001))
    ("ShortValue4" (test-short-value 78))
    ("ShortValue5" (test-short-value -1))
    ;; int constructor:
    ("IntValue0" (test-int-value 0))
    ("IntValue1" (test-int-value -2147483648))
    ("IntValue2" (test-int-value 2147483647))
    ("IntValue3" (test-int-value 736382))
    ("IntValue4" (test-int-value -22))
    ("IntValue5" (test-int-value 90000))
    ;; long constructor:
    ("LongValue0" (test-long-value 0))
    ("LongValue1" (test-long-value -9223372036854775808))
    ("LongValue2" (test-long-value 9223372036854775807))
    ("LongValue3" (test-long-value 882882929292))
    ("LongValue4" (test-long-value 27))
    ("LongValue5" (test-long-value -27777))
    ("LongValue6" (test-long-value -292999999999))
    ;; boolean deconstructor:
    ("BooleanValueBoolT" (test-boolean-value->bool (java::boolean-value t)))
    ("BooleanValueBoolF" (test-boolean-value->bool (java::boolean-value nil)))
    ;; char deconstructor:
    ("CharValueNat0" (test-char-value->nat (java::char-value 0)))
    ("CharValueNat1" (test-char-value->nat (java::char-value 60000)))
    ("CharValueNat2" (test-char-value->nat (java::char-value 256)))
    ("CharValueNat3" (test-char-value->nat (java::char-value 32)))
    ("CharValueNat4" (test-char-value->nat (java::char-value 65)))
    ("CharValueNat5" (test-char-value->nat (java::char-value 12345)))
    ;; byte deconstructor:
    ("ByteValueInt0" (test-byte-value->int (java::byte-value 0)))
    ("ByteValueInt1" (test-byte-value->int (java::byte-value -128)))
    ("ByteValueInt2" (test-byte-value->int (java::byte-value 127)))
    ("ByteValueInt3" (test-byte-value->int (java::byte-value -67)))
    ("ByteValueInt4" (test-byte-value->int (java::byte-value 88)))
    ("ByteValueInt5" (test-byte-value->int (java::byte-value 1)))
    ;; short deconstructor:
    ("ShortValueInt0" (test-short-value->int (java::short-value 0)))
    ("ShortValueInt1" (test-short-value->int (java::short-value -32768)))
    ("ShortValueInt2" (test-short-value->int (java::short-value 32767)))
    ("ShortValueInt3" (test-short-value->int (java::short-value 1001)))
    ("ShortValueInt4" (test-short-value->int (java::short-value 78)))
    ("ShortValueInt5" (test-short-value->int (java::short-value -1)))
    ;; int deconstructor:
    ("IntValueInt0" (test-int-value->int (java::int-value 0)))
    ("IntValueInt1" (test-int-value->int (java::int-value -2147483648)))
    ("IntValueInt2" (test-int-value->int (java::int-value 2147483647)))
    ("IntValueInt3" (test-int-value->int (java::int-value 736382)))
    ("IntValueInt4" (test-int-value->int (java::int-value -22)))
    ("IntValueInt5" (test-int-value->int (java::int-value 90000)))
    ;; long deconstructor:
    ("LongValueInt0" (test-long-value->int (java::long-value 0)))
    ("LongValueInt1" (test-long-value->int (java::long-value
                                            -9223372036854775808)))
    ("LongValueInt2" (test-long-value->int (java::long-value 9223372036854775807)))
    ("LongValueInt3" (test-long-value->int (java::long-value 882882929292)))
    ("LongValueInt4" (test-long-value->int (java::long-value 27)))
    ("LongValueInt5" (test-long-value->int (java::long-value -27777)))
    ("LongValueInt6" (test-long-value->int (java::long-value -292999999999)))
    ;; boolean negation:
    ("BooleanNotT" (test-boolean-not (java::boolean-value t)))
    ("BooleanNotF" (test-boolean-not (java::boolean-value nil)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize the input and output types of the tested functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; constructors:

(java::atj-main-function-type test-boolean-value (:aboolean) :jboolean)

(java::atj-main-function-type test-char-value (:ainteger) :jchar)

(java::atj-main-function-type test-byte-value (:ainteger) :jbyte)

(java::atj-main-function-type test-short-value (:ainteger) :jshort)

(java::atj-main-function-type test-int-value (:ainteger) :jint)

(java::atj-main-function-type test-long-value (:ainteger) :jlong)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; deconstructors:

(java::atj-main-function-type test-boolean-value->bool (:jboolean) :aboolean)

(java::atj-main-function-type test-char-value->nat (:jchar) :ainteger)

(java::atj-main-function-type test-byte-value->int (:jbyte) :ainteger)

(java::atj-main-function-type test-short-value->int (:jshort) :ainteger)

(java::atj-main-function-type test-int-value->int (:jint) :ainteger)

(java::atj-main-function-type test-long-value->int (:jlong) :ainteger)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; unary operations:

(java::atj-main-function-type test-boolean-not (:jboolean) :jboolean)

(java::atj-main-function-type test-int-plus (:jint) :jint)

(java::atj-main-function-type test-long-plus (:jlong) :jlong)

(java::atj-main-function-type test-int-minus (:jint) :jint)

(java::atj-main-function-type test-long-minus (:jlong) :jlong)

(java::atj-main-function-type test-int-not (:jint) :jint)

(java::atj-main-function-type test-long-not (:jlong) :jlong)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; binary operations:

(java::atj-main-function-type test-boolean-and (:jboolean :jboolean) :jboolean)

(java::atj-main-function-type test-boolean-xor (:jboolean :jboolean) :jboolean)

(java::atj-main-function-type test-boolean-ior (:jboolean :jboolean) :jboolean)

(java::atj-main-function-type test-boolean-eq (:jboolean :jboolean) :jboolean)

(java::atj-main-function-type test-boolean-neq (:jboolean :jboolean) :jboolean)

(java::atj-main-function-type test-int-add (:jint :jint) :jint)

(java::atj-main-function-type test-long-add (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-sub (:jint :jint) :jint)

(java::atj-main-function-type test-long-sub (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-mul (:jint :jint) :jint)

(java::atj-main-function-type test-long-mul (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-div (:jint :jint) :jint)

(java::atj-main-function-type test-long-div (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-rem (:jint :jint) :jint)

(java::atj-main-function-type test-long-rem (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-and (:jint :jint) :jint)

(java::atj-main-function-type test-long-and (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-xor (:jint :jint) :jint)

(java::atj-main-function-type test-long-xor (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-ior (:jint :jint) :jint)

(java::atj-main-function-type test-long-ior (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-eq (:jint :jint) :jboolean)

(java::atj-main-function-type test-long-eq (:jlong :jlong) :jboolean)

(java::atj-main-function-type test-int-neq (:jint :jint) :jboolean)

(java::atj-main-function-type test-long-neq (:jlong :jlong) :jboolean)

(java::atj-main-function-type test-int-less (:jint :jint) :jboolean)

(java::atj-main-function-type test-long-less (:jlong :jlong) :jboolean)

(java::atj-main-function-type test-int-lesseq (:jint :jint) :jboolean)

(java::atj-main-function-type test-long-lesseq (:jlong :jlong) :jboolean)

(java::atj-main-function-type test-int-great (:jint :jint) :jboolean)

(java::atj-main-function-type test-long-great (:jlong :jlong) :jboolean)

(java::atj-main-function-type test-int-greateq (:jint :jint) :jboolean)

(java::atj-main-function-type test-long-greateq (:jlong :jlong) :jboolean)

(java::atj-main-function-type test-int-int-shiftl (:jint :jint) :jint)

(java::atj-main-function-type test-long-long-shiftl (:jlong :jlong) :jlong)

(java::atj-main-function-type test-long-int-shiftl (:jlong :jint) :jlong)

(java::atj-main-function-type test-int-long-shiftl (:jint :jlong) :jint)

(java::atj-main-function-type test-int-int-shiftr (:jint :jint) :jint)

(java::atj-main-function-type test-long-long-shiftr (:jlong :jlong) :jlong)

(java::atj-main-function-type test-long-int-shiftr (:jlong :jint) :jlong)

(java::atj-main-function-type test-int-long-shiftr (:jint :jlong) :jint)

(java::atj-main-function-type test-int-int-ushiftr (:jint :jint) :jint)

(java::atj-main-function-type test-long-long-ushiftr (:jlong :jlong) :jlong)

(java::atj-main-function-type test-long-int-ushiftr (:jlong :jint) :jlong)

(java::atj-main-function-type test-int-long-ushiftr (:jint :jlong) :jint)

(java::atj-main-function-type f-boolean (:jboolean :jboolean) :jboolean)

(java::atj-main-function-type g-boolean
                              (:jboolean :jboolean :jboolean)
                              :jboolean)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; conversions:

(java::atj-main-function-type test-byte-to-short (:jbyte) :jshort)

(java::atj-main-function-type test-byte-to-int (:jbyte) :jint)

(java::atj-main-function-type test-byte-to-long (:jbyte) :jlong)

(java::atj-main-function-type test-short-to-int (:jshort) :jint)

(java::atj-main-function-type test-short-to-long (:jshort) :jlong)

(java::atj-main-function-type test-int-to-long (:jint) :jlong)

(java::atj-main-function-type test-char-to-int (:jchar) :jint)

(java::atj-main-function-type test-char-to-long (:jchar) :jlong)

(java::atj-main-function-type test-short-to-byte (:jshort) :jbyte)

(java::atj-main-function-type test-int-to-byte (:jint) :jbyte)

(java::atj-main-function-type test-long-to-byte (:jlong) :jbyte)

(java::atj-main-function-type test-char-to-byte (:jchar) :jbyte)

(java::atj-main-function-type test-int-to-short (:jint) :jshort)

(java::atj-main-function-type test-long-to-short (:jlong) :jshort)

(java::atj-main-function-type test-char-to-short (:jchar) :jshort)

(java::atj-main-function-type test-long-to-int (:jlong) :jint)

(java::atj-main-function-type test-short-to-char (:jshort) :jchar)

(java::atj-main-function-type test-int-to-char (:jint) :jchar)

(java::atj-main-function-type test-long-to-char (:jlong) :jchar)

(java::atj-main-function-type test-byte-to-char (:jbyte) :jchar)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; other functions:

(java::atj-main-function-type f-int (:jint :jint) :jint)

(java::atj-main-function-type g-int (:jint :jint :jint) :jint)

(java::atj-main-function-type h-int (:jint) :jint)

(java::atj-main-function-type f-long (:jlong :jlong) :jlong)

(java::atj-main-function-type g-long (:jlong :jlong :jlong) :jlong)

(java::atj-main-function-type h-long (:jlong) :jlong)

(java::atj-main-function-type f-float (:jfloat :jfloat :jfloat) :jfloat)

(java::atj-main-function-type f-double (:jdouble :jdouble :jdouble) :jdouble)

(java::atj-main-function-type f-conv (:jbyte :jshort :jlong) :jint)

(java::atj-main-function-type g-conv (:jfloat :jdouble) :jdouble)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; factorial:

(java::atj-main-function-type factorial-int (:jint) :jint)

(java::atj-main-function-type factorial-long (:jlong) :jlong)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the functions that manipulate Java primitive values.

(java::atj test-boolean-value
           test-char-value
           test-byte-value
           test-short-value
           test-int-value
           test-long-value
           test-boolean-value->bool
           test-char-value->nat
           test-byte-value->int
           test-short-value->int
           test-int-value->int
           test-long-value->int
           test-boolean-not
           test-int-plus
           test-long-plus
           test-int-minus
           test-long-minus
           test-int-not
           test-long-not
           test-boolean-and
           test-boolean-xor
           test-boolean-ior
           test-boolean-eq
           test-boolean-neq
           test-int-add
           test-long-add
           test-int-sub
           test-long-sub
           test-int-mul
           test-long-mul
           test-int-div
           test-long-div
           test-int-rem
           test-long-rem
           test-int-and
           test-long-and
           test-int-xor
           test-long-xor
           test-int-ior
           test-long-ior
           test-int-eq
           test-long-eq
           test-int-neq
           test-long-neq
           test-int-less
           test-long-less
           test-int-lesseq
           test-long-lesseq
           test-int-great
           test-long-great
           test-int-greateq
           test-long-greateq
           test-int-int-shiftl
           test-long-long-shiftl
           test-long-int-shiftl
           test-int-long-shiftl
           test-int-int-shiftr
           test-long-long-shiftr
           test-long-int-shiftr
           test-int-long-shiftr
           test-int-int-ushiftr
           test-long-long-ushiftr
           test-long-int-ushiftr
           test-int-long-ushiftr
           test-byte-to-short
           test-byte-to-int
           test-byte-to-long
           test-short-to-int
           test-short-to-long
           test-int-to-long
           test-char-to-int
           test-char-to-long
           test-short-to-byte
           test-int-to-byte
           test-long-to-byte
           test-char-to-byte
           test-int-to-short
           test-long-to-short
           test-char-to-short
           test-long-to-int
           test-short-to-char
           test-int-to-char
           test-long-to-char
           test-byte-to-char
           f-boolean
           g-boolean
           f-int
           g-int
           h-int
           f-long
           g-long
           h-long
           f-conv
           factorial-int
           factorial-long
           :deep t
           :guards nil
           :java-class "PrimitivesDeepUnguarded")

(java::atj test-boolean-value
           test-char-value
           test-byte-value
           test-short-value
           test-int-value
           test-long-value
           test-boolean-value->bool
           test-char-value->nat
           test-byte-value->int
           test-short-value->int
           test-int-value->int
           test-long-value->int
           test-boolean-not
           test-int-plus
           test-long-plus
           test-int-minus
           test-long-minus
           test-int-not
           test-long-not
           test-boolean-and
           test-boolean-xor
           test-boolean-ior
           test-boolean-eq
           test-boolean-neq
           test-int-add
           test-long-add
           test-int-sub
           test-long-sub
           test-int-mul
           test-long-mul
           test-int-div
           test-long-div
           test-int-rem
           test-long-rem
           test-int-and
           test-long-and
           test-int-xor
           test-long-xor
           test-int-ior
           test-long-ior
           test-int-eq
           test-long-eq
           test-int-neq
           test-long-neq
           test-int-less
           test-long-less
           test-int-lesseq
           test-long-lesseq
           test-int-great
           test-long-great
           test-int-greateq
           test-long-greateq
           test-int-int-shiftl
           test-long-long-shiftl
           test-long-int-shiftl
           test-int-long-shiftl
           test-int-int-shiftr
           test-long-long-shiftr
           test-long-int-shiftr
           test-int-long-shiftr
           test-int-int-ushiftr
           test-long-long-ushiftr
           test-long-int-ushiftr
           test-int-long-ushiftr
           test-byte-to-short
           test-byte-to-int
           test-byte-to-long
           test-short-to-int
           test-short-to-long
           test-int-to-long
           test-char-to-int
           test-char-to-long
           test-short-to-byte
           test-int-to-byte
           test-long-to-byte
           test-char-to-byte
           test-int-to-short
           test-long-to-short
           test-char-to-short
           test-long-to-int
           test-short-to-char
           test-int-to-char
           test-long-to-char
           test-byte-to-char
           f-boolean
           g-boolean
           f-int
           g-int
           h-int
           f-long
           g-long
           h-long
           f-conv
           factorial-int
           factorial-long
           :deep t
           :guards t
           :java-class "PrimitivesDeepGuarded")

(java::atj test-boolean-value
           test-char-value
           test-byte-value
           test-short-value
           test-int-value
           test-long-value
           test-boolean-value->bool
           test-char-value->nat
           test-byte-value->int
           test-short-value->int
           test-int-value->int
           test-long-value->int
           test-boolean-not
           test-int-plus
           test-long-plus
           test-int-minus
           test-long-minus
           test-int-not
           test-long-not
           test-boolean-and
           test-boolean-xor
           test-boolean-ior
           test-boolean-eq
           test-boolean-neq
           test-int-add
           test-long-add
           test-int-sub
           test-long-sub
           test-int-mul
           test-long-mul
           test-int-div
           test-long-div
           test-int-rem
           test-long-rem
           test-int-and
           test-long-and
           test-int-xor
           test-long-xor
           test-int-ior
           test-long-ior
           test-int-eq
           test-long-eq
           test-int-neq
           test-long-neq
           test-int-less
           test-long-less
           test-int-lesseq
           test-long-lesseq
           test-int-great
           test-long-great
           test-int-greateq
           test-long-greateq
           test-int-int-shiftl
           test-long-long-shiftl
           test-long-int-shiftl
           test-int-long-shiftl
           test-int-int-shiftr
           test-long-long-shiftr
           test-long-int-shiftr
           test-int-long-shiftr
           test-int-int-ushiftr
           test-long-long-ushiftr
           test-long-int-ushiftr
           test-int-long-ushiftr
           test-byte-to-short
           test-byte-to-int
           test-byte-to-long
           test-short-to-int
           test-short-to-long
           test-int-to-long
           test-char-to-int
           test-char-to-long
           test-short-to-byte
           test-int-to-byte
           test-long-to-byte
           test-char-to-byte
           test-int-to-short
           test-long-to-short
           test-char-to-short
           test-long-to-int
           test-short-to-char
           test-int-to-char
           test-long-to-char
           test-byte-to-char
           f-boolean
           g-boolean
           f-int
           g-int
           h-int
           f-long
           g-long
           h-long
           f-conv
           factorial-int
           factorial-long
           :deep nil
           :guards nil
           :java-class "PrimitivesShallowUnguarded")

(java::atj test-boolean-value
           test-char-value
           test-byte-value
           test-short-value
           test-int-value
           test-long-value
           test-boolean-value->bool
           test-char-value->nat
           test-byte-value->int
           test-short-value->int
           test-int-value->int
           test-long-value->int
           test-boolean-not
           test-int-plus
           test-long-plus
           test-int-minus
           test-long-minus
           test-int-not
           test-long-not
           test-boolean-and
           test-boolean-xor
           test-boolean-ior
           test-boolean-eq
           test-boolean-neq
           test-int-add
           test-long-add
           test-int-sub
           test-long-sub
           test-int-mul
           test-long-mul
           test-int-div
           test-long-div
           test-int-rem
           test-long-rem
           test-int-and
           test-long-and
           test-int-xor
           test-long-xor
           test-int-ior
           test-long-ior
           test-int-eq
           test-long-eq
           test-int-neq
           test-long-neq
           test-int-less
           test-long-less
           test-int-lesseq
           test-long-lesseq
           test-int-great
           test-long-great
           test-int-greateq
           test-long-greateq
           test-int-int-shiftl
           test-long-long-shiftl
           test-long-int-shiftl
           test-int-long-shiftl
           test-int-int-shiftr
           test-long-long-shiftr
           test-long-int-shiftr
           test-int-long-shiftr
           test-int-int-ushiftr
           test-long-long-ushiftr
           test-long-int-ushiftr
           test-int-long-ushiftr
           test-byte-to-short
           test-byte-to-int
           test-byte-to-long
           test-short-to-int
           test-short-to-long
           test-int-to-long
           test-char-to-int
           test-char-to-long
           test-short-to-byte
           test-int-to-byte
           test-long-to-byte
           test-char-to-byte
           test-int-to-short
           test-long-to-short
           test-char-to-short
           test-long-to-int
           test-short-to-char
           test-int-to-char
           test-long-to-char
           test-byte-to-char
           f-boolean
           g-boolean
           f-int
           g-int
           h-int
           f-long
           g-long
           h-long
           f-float
           f-double
           f-conv
           g-conv
           factorial-int
           factorial-long
           :deep nil
           :guards t
           :java-class "PrimitivesShallowGuarded"
           :tests *shallow-guarded-tests*)
