; Java Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../atj" :ttags ((:open-output-channel!) (:oslib) (:quicklisp) :quicklisp.osicat))

(include-book "../java-primitive-arrays")
(include-book "../../language/primitive-operations")
(include-book "../../language/primitive-conversions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the generation of Java code
; that manipulates Java primitive arrays.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; As explained in the ATJ user documentation,
; the tests passed to :TESTS may only involve
; the target functions explicitly passed to ATJ,
; which cannot include the functions in *ATJ-JPRIMARR-FNS*
; when :DEEP is NIL and :GUARDS is T.
; Thus, here we introduce wrappers for such functions,
; which are the ones that we want to test here.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; read:

(defun test-boolean-array-read (a i)
  (declare
   (xargs :guard (and (java::boolean-arrayp a)
                      (java::int-valuep i)
                      (java::boolean-array-index-in-range-p a i))))
  (java::boolean-array-read a i))

(defun test-char-array-read (a i)
  (declare
   (xargs :guard (and (java::char-arrayp a)
                      (java::int-valuep i)
                      (java::char-array-index-in-range-p a i))))
  (java::char-array-read a i))

(defun test-byte-array-read (a i)
  (declare
   (xargs :guard (and (java::byte-arrayp a)
                      (java::int-valuep i)
                      (java::byte-array-index-in-range-p a i))))
  (java::byte-array-read a i))

(defun test-short-array-read (a i)
  (declare
   (xargs :guard (and (java::short-arrayp a)
                      (java::int-valuep i)
                      (java::short-array-index-in-range-p a i))))
  (java::short-array-read a i))

(defun test-int-array-read (a i)
  (declare
   (xargs :guard (and (java::int-arrayp a)
                      (java::int-valuep i)
                      (java::int-array-index-in-range-p a i))))
  (java::int-array-read a i))

(defun test-long-array-read (a i)
  (declare
   (xargs :guard (and (java::long-arrayp a)
                      (java::int-valuep i)
                      (java::long-array-index-in-range-p a i))))
  (java::long-array-read a i))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; length:

(defun test-boolean-array-length (a)
  (declare (xargs :guard (java::boolean-arrayp a)))
  (java::boolean-array-length a))

(defun test-char-array-length (a)
  (declare (xargs :guard (java::char-arrayp a)))
  (java::char-array-length a))

(defun test-byte-array-length (a)
  (declare (xargs :guard (java::byte-arrayp a)))
  (java::byte-array-length a))

(defun test-short-array-length (a)
  (declare (xargs :guard (java::short-arrayp a)))
  (java::short-array-length a))

(defun test-int-array-length (a)
  (declare (xargs :guard (java::int-arrayp a)))
  (java::int-array-length a))

(defun test-long-array-length (a)
  (declare (xargs :guard (java::long-arrayp a)))
  (java::long-array-length a))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; write:

(defun test-boolean-array-write (a i e)
  (declare
   (xargs :guard (and (java::boolean-arrayp a)
                      (java::int-valuep i)
                      (java::boolean-array-index-in-range-p a i)
                      (java::boolean-valuep e))))
  (java::boolean-array-write a i e))

(defun test-char-array-write (a i e)
  (declare
   (xargs :guard (and (java::char-arrayp a)
                      (java::int-valuep i)
                      (java::char-array-index-in-range-p a i)
                      (java::char-valuep e))))
  (java::char-array-write a i e))

(defun test-byte-array-write (a i e)
  (declare
   (xargs :guard (and (java::byte-arrayp a)
                      (java::int-valuep i)
                      (java::byte-array-index-in-range-p a i)
                      (java::byte-valuep e))))
  (java::byte-array-write a i e))

(defun test-short-array-write (a i e)
  (declare
   (xargs :guard (and (java::short-arrayp a)
                      (java::int-valuep i)
                      (java::short-array-index-in-range-p a i)
                      (java::short-valuep e))))
  (java::short-array-write a i e))

(defun test-int-array-write (a i e)
  (declare
   (xargs :guard (and (java::int-arrayp a)
                      (java::int-valuep i)
                      (java::int-array-index-in-range-p a i)
                      (java::int-valuep e))))
  (java::int-array-write a i e))

(defun test-long-array-write (a i e)
  (declare
   (xargs :guard (and (java::long-arrayp a)
                      (java::int-valuep i)
                      (java::long-array-index-in-range-p a i)
                      (java::long-valuep e))))
  (java::long-array-write a i e))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; creation with length:

(defun test-boolean-array-new-len (l)
  (declare (xargs :guard (and (java::int-valuep l)
                              (<= 0 (java::int-value->int l)))))
  (java::boolean-array-new-len l))

(defun test-char-array-new-len (l)
  (declare (xargs :guard (and (java::int-valuep l)
                              (<= 0 (java::int-value->int l)))))
  (java::char-array-new-len l))

(defun test-byte-array-new-len (l)
  (declare (xargs :guard (and (java::int-valuep l)
                              (<= 0 (java::int-value->int l)))))
  (java::byte-array-new-len l))

(defun test-short-array-new-len (l)
  (declare (xargs :guard (and (java::int-valuep l)
                              (<= 0 (java::int-value->int l)))))
  (java::short-array-new-len l))

(defun test-int-array-new-len (l)
  (declare (xargs :guard (and (java::int-valuep l)
                              (<= 0 (java::int-value->int l)))))
  (java::int-array-new-len l))

(defun test-long-array-new-len (l)
  (declare (xargs :guard (and (java::int-valuep l)
                              (<= 0 (java::int-value->int l)))))
  (java::long-array-new-len l))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; creation with initializer:

;;;;;;;;;;;;;;;;;;;;

; initializer with 0 components:

(defun test-boolean-array-new-init-0 ()
  (java::boolean-array-new-init nil))

(defun test-char-array-new-init-0 ()
  (java::char-array-new-init nil))

(defun test-byte-array-new-init-0 ()
  (java::byte-array-new-init nil))

(defun test-short-array-new-init-0 ()
  (java::short-array-new-init nil))

(defun test-int-array-new-init-0 ()
  (java::int-array-new-init nil))

(defun test-long-array-new-init-0 ()
  (java::long-array-new-init nil))

;;;;;;;;;;;;;;;;;;;;

; initializer with 1 component:

(defun test-boolean-array-new-init-1 (x)
  (declare (xargs :guard (java::boolean-valuep x)))
  (java::boolean-array-new-init (list x)))

(defun test-char-array-new-init-1 (x)
  (declare (xargs :guard (java::char-valuep x)))
  (java::char-array-new-init (list x)))

(defun test-byte-array-new-init-1 (x)
  (declare (xargs :guard (java::byte-valuep x)))
  (java::byte-array-new-init (list x)))

(defun test-short-array-new-init-1 (x)
  (declare (xargs :guard (java::short-valuep x)))
  (java::short-array-new-init (list x)))

(defun test-int-array-new-init-1 (x)
  (declare (xargs :guard (java::int-valuep x)))
  (java::int-array-new-init (list x)))

(defun test-long-array-new-init-1 (x)
  (declare (xargs :guard (java::long-valuep x)))
  (java::long-array-new-init (list x)))

;;;;;;;;;;;;;;;;;;;;

; initializer with 2 components:

(defun test-boolean-array-new-init-2 (x y)
  (declare (xargs :guard (and (java::boolean-valuep x)
                              (java::boolean-valuep y))))
  (java::boolean-array-new-init (list x y)))

(defun test-char-array-new-init-2 (x y)
  (declare (xargs :guard (and (java::char-valuep x)
                              (java::char-valuep y))))
  (java::char-array-new-init (list x y)))

(defun test-byte-array-new-init-2 (x y)
  (declare (xargs :guard (and (java::byte-valuep x)
                              (java::byte-valuep y))))
  (java::byte-array-new-init (list x y)))

(defun test-short-array-new-init-2 (x y)
  (declare (xargs :guard (and (java::short-valuep x)
                              (java::short-valuep y))))
  (java::short-array-new-init (list x y)))

(defun test-int-array-new-init-2 (x y)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y))))
  (java::int-array-new-init (list x y)))

(defun test-long-array-new-init-2 (x y)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y))))
  (java::long-array-new-init (list x y)))

;;;;;;;;;;;;;;;;;;;;

; initializer with 3 components:

(defun test-boolean-array-new-init-3 (x y z)
  (declare (xargs :guard (and (java::boolean-valuep x)
                              (java::boolean-valuep y)
                              (java::boolean-valuep z))))
  (java::boolean-array-new-init (list x y z)))

(defun test-char-array-new-init-3 (x y z)
  (declare (xargs :guard (and (java::char-valuep x)
                              (java::char-valuep y)
                              (java::char-valuep z))))
  (java::char-array-new-init (list x y z)))

(defun test-byte-array-new-init-3 (x y z)
  (declare (xargs :guard (and (java::byte-valuep x)
                              (java::byte-valuep y)
                              (java::byte-valuep z))))
  (java::byte-array-new-init (list x y z)))

(defun test-short-array-new-init-3 (x y z)
  (declare (xargs :guard (and (java::short-valuep x)
                              (java::short-valuep y)
                              (java::short-valuep z))))
  (java::short-array-new-init (list x y z)))

(defun test-int-array-new-init-3 (x y z)
  (declare (xargs :guard (and (java::int-valuep x)
                              (java::int-valuep y)
                              (java::int-valuep z))))
  (java::int-array-new-init (list x y z)))

(defun test-long-array-new-init-3 (x y z)
  (declare (xargs :guard (and (java::long-valuep x)
                              (java::long-valuep y)
                              (java::long-valuep z))))
  (java::long-array-new-init (list x y z)))

;;;;;;;;;;;;;;;;;;;;

; conversion to list:

(defun test-boolean-array-to-boolean-list (array)
  (declare (xargs :guard (java::boolean-arrayp array)))
  (java::boolean-array-to-boolean-list array))

(defun test-char-array-to-ubyte16-list (array)
  (declare (xargs :guard (java::char-arrayp array)))
  (java::char-array-to-ubyte16-list array))

(defun test-byte-array-to-sbyte8-list (array)
  (declare (xargs :guard (java::byte-arrayp array)))
  (java::byte-array-to-sbyte8-list array))

(defun test-short-array-to-sbyte16-list (array)
  (declare (xargs :guard (java::short-arrayp array)))
  (java::short-array-to-sbyte16-list array))

(defun test-int-array-to-sbyte32-list (array)
  (declare (xargs :guard (java::int-arrayp array)))
  (java::int-array-to-sbyte32-list array))

(defun test-long-array-to-sbyte64-list (array)
  (declare (xargs :guard (java::long-arrayp array)))
  (java::long-array-to-sbyte64-list array))

;;;;;;;;;;;;;;;;;;;;

; conversion from list:

(defun test-boolean-array-from-boolean-list (list)
  (declare (xargs :guard (and (boolean-listp list)
                              (< (len list) (expt 2 31)))))
  (java::boolean-array-from-boolean-list list))

(defun test-char-array-from-ubyte16-list (list)
  (declare (xargs :guard (and (ubyte16-listp list)
                              (< (len list) (expt 2 31)))))
  (java::char-array-from-ubyte16-list list))

(defun test-byte-array-from-sbyte8-list (list)
  (declare (xargs :guard (and (sbyte8-listp list)
                              (< (len list) (expt 2 31)))))
  (java::byte-array-from-sbyte8-list list))

(defun test-short-array-from-sbyte16-list (list)
  (declare (xargs :guard (and (sbyte16-listp list)
                              (< (len list) (expt 2 31)))))
  (java::short-array-from-sbyte16-list list))

(defun test-int-array-from-sbyte32-list (list)
  (declare (xargs :guard (and (sbyte32-listp list)
                              (< (len list) (expt 2 31)))))
  (java::int-array-from-sbyte32-list list))

(defun test-long-array-from-sbyte64-list (list)
  (declare (xargs :guard (and (sbyte64-listp list)
                              (< (len list) (expt 2 31)))))
  (java::long-array-from-sbyte64-list list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; More functions over (ACL2 representations of) Java primitive arrays.

(defun f (array i j)
  (declare
   (xargs :guard (and
                  (java::int-arrayp array)
                  (java::int-valuep i)
                  (java::int-valuep j)
                  (java::int-array-index-in-range-p array i)
                  (java::int-array-index-in-range-p array j))))
  (java::int-add (java::int-array-read array i)
                 (java::int-array-read array j)))

(defun g (bytearray shortarray)
  (declare (xargs :guard (and (java::byte-arrayp bytearray)
                              (java::short-arrayp shortarray))))
  (java::int-add (java::byte-array-length bytearray)
                 (java::short-array-length shortarray)))

(defun h (length)
  (declare (xargs :guard (and (java::byte-valuep length)
                              (>= (java::byte-value->int length) 0))
                  :guard-hints (("Goal" :in-theory (enable java::byte-to-short
                                                           java::short-to-int
                                                           sbyte16-fix
                                                           sbyte32-fix)))))
  (b* ((length (java::byte-to-short length))
       (length (java::short-to-int length)))
    (java::char-array-new-len length)))

(defun i (floatarray doublearray i j)
  (declare
   (xargs :guard (and (java::float-arrayp floatarray)
                      (java::double-arrayp doublearray)
                      (java::int-valuep i)
                      (java::int-valuep j)
                      (java::float-array-index-in-range-p floatarray i)
                      (java::double-array-index-in-range-p doublearray j))))
  (java::double-rem (java::float-to-double
                     (java::float-array-read floatarray i))
                    (java::double-array-read doublearray j)))

(defun j (bytes1 bytes2 i1 i2)
  (declare (xargs :guard (and (java::byte-arrayp bytes1)
                              (java::byte-arrayp bytes2)
                              (java::int-valuep i1)
                              (java::int-valuep i2)
                              (java::byte-array-index-in-range-p bytes1 i1)
                              (java::byte-array-index-in-range-p bytes2 i2))))
  (let* ((x1 (java::byte-array-read bytes1 i1))
         (x2 (java::byte-array-read bytes2 i2))
         (bytes1 (java::byte-array-write bytes1 i1 x2))
         (bytes2 (java::byte-array-write bytes2 i2 x1)))
    (mv bytes1 bytes2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests for the functions above (except the ones involving floating-point),
; when :DEEP is NIL and :GUARDS is T.

(defconst *shallow-guarded-basic-tests*
  '(;; read:
    ("BooleanArrayRead" (test-boolean-array-read
                         (java::boolean-array-new-init
                          (list (java::boolean-value t)
                                (java::boolean-value nil)
                                (java::boolean-value nil)))
                         (java::int-value 2)))
    ("CharArrayRead" (test-char-array-read
                      (java::char-array-new-init
                       (list (java::char-value 722)
                             (java::char-value 9990)
                             (java::char-value 1)))
                      (java::int-value 1)))
    ("ByteArrayRead" (test-byte-array-read
                      (java::byte-array-new-init
                       (list (java::byte-value -100)
                             (java::byte-value 100)))
                      (java::int-value 0)))
    ("ShortArrayRead" (test-short-array-read
                       (java::short-array-new-init
                        (list (java::short-value -100)
                              (java::short-value 100)
                              (java::short-value 32001)
                              (java::short-value -5000)))
                       (java::int-value 2)))
    ("IntArrayRead" (test-int-array-read
                     (java::int-array-new-init
                      (list (java::int-value 1000000000)))
                     (java::int-value 0)))
    ("LongArrayRead" (test-long-array-read
                      (java::long-array-new-init
                       (list (java::long-value 1000000000)
                             (java::long-value 1000000000000000000)))
                      (java::int-value 1)))
    ;; length:
    ("BooleanArrayLength" (test-boolean-array-length
                           (java::boolean-array-new-init
                            (list (java::boolean-value t)
                                  (java::boolean-value nil)
                                  (java::boolean-value nil)))))
    ("CharArrayLength" (test-char-array-length
                        (java::char-array-new-init
                         (list (java::char-value 722)
                               (java::char-value 9990)
                               (java::char-value 1)))))
    ("ByteArrayLength" (test-byte-array-length
                        (java::byte-array-new-init
                         (list (java::byte-value -100)
                               (java::byte-value 100)))))
    ("ShortArrayLength" (test-short-array-length
                         (java::short-array-new-init
                          (list (java::short-value -100)
                                (java::short-value 100)
                                (java::short-value 32001)
                                (java::short-value -5000)))))
    ("IntArrayLength" (test-int-array-length
                       (java::int-array-new-init
                        (list (java::int-value 1000000000)))))
    ("LongArrayLength" (test-long-array-length
                        (java::long-array-new-init
                         (list (java::long-value 1000000000)
                               (java::long-value 1000000000000000000)))))
    ;; write:
    ("BooleanArrayWrite" (test-boolean-array-write
                          (java::boolean-array-new-init
                           (list (java::boolean-value t)
                                 (java::boolean-value nil)
                                 (java::boolean-value nil)))
                          (java::int-value 2)
                          (java::boolean-value t)))
    ("CharArrayWrite" (test-char-array-write
                       (java::char-array-new-init
                        (list (java::char-value 722)
                              (java::char-value 9990)
                              (java::char-value 1)))
                       (java::int-value 1)
                       (java::char-value 88)))
    ("ByteArrayWrite" (test-byte-array-write
                       (java::byte-array-new-init
                        (list (java::byte-value -100)
                              (java::byte-value 100)))
                       (java::int-value 0)
                       (java::byte-value -10)))
    ("ShortArrayWrite" (test-short-array-write
                        (java::short-array-new-init
                         (list (java::short-value -100)
                               (java::short-value 100)
                               (java::short-value 32001)
                               (java::short-value -5000)))
                        (java::int-value 2)
                        (java::short-value 1)))
    ("IntArrayWrite" (test-int-array-write
                      (java::int-array-new-init
                       (list (java::int-value 1000000000)))
                      (java::int-value 0)
                      (java::int-value -100000)))
    ("LongArrayWrite" (test-long-array-write
                       (java::long-array-new-init
                        (list (java::long-value 1000000000)
                              (java::long-value 1000000000000000000)))
                       (java::int-value 1)
                       (java::long-value -55555555555555555)))
    ;; creation with length:
    ("BooleanArrayNewLen0" (test-boolean-array-new-len
                            (java::int-value 0)))
    ("BooleanArrayNewLen1" (test-boolean-array-new-len
                            (java::int-value 80)))
    ("CharArrayNewLen0" (test-char-array-new-len
                         (java::int-value 8)))
    ("CharArrayNewLen1" (test-char-array-new-len
                         (java::int-value 19)))
    ("ByteArrayNewLen0" (test-byte-array-new-len
                         (java::int-value 73)))
    ("ByteArrayNewLen1" (test-byte-array-new-len
                         (java::int-value 1)))
    ("ShortArrayNewLen0" (test-short-array-new-len
                          (java::int-value 7)))
    ("ShortArrayNewLen1" (test-short-array-new-len
                          (java::int-value 111)))
    ("IntArrayNewLen0" (test-int-array-new-len
                        (java::int-value 0)))
    ("IntArrayNewLen1" (test-int-array-new-len
                        (java::int-value 9)))
    ("LongArrayNewLen0" (test-long-array-new-len
                         (java::int-value 20)))
    ("LongArrayNewLen1" (test-long-array-new-len
                         (java::int-value 23)))
    ;; creation with initializer of 0 components:
    ("BooleanArrayNewInit0" (test-boolean-array-new-init-0))
    ("CharArrayNewInit0" (test-char-array-new-init-0))
    ("ByteArrayNewInit0" (test-byte-array-new-init-0))
    ("ShortArrayNewInit0" (test-short-array-new-init-0))
    ("IntArrayNewInit0" (test-int-array-new-init-0))
    ("LongArrayNewInit0" (test-long-array-new-init-0))
    ;; creation with initializer of 1 component:
    ("BooleanArrayNewInit1" (test-boolean-array-new-init-1
                             (java::boolean-value t)))
    ("CharArrayNewInit1" (test-char-array-new-init-1
                          (java::char-value 8888)))
    ("ByteArrayNewInit1" (test-byte-array-new-init-1
                          (java::byte-value -1)))
    ("ShortArrayNewInit1" (test-short-array-new-init-1
                           (java::short-value 8000)))
    ("IntArrayNewInit1" (test-int-array-new-init-1
                         (java::int-value 2000000000)))
    ("LongArrayNewInit1" (test-long-array-new-init-1
                          (java::long-value -8000000000000000000)))
    ;; creation with initializer of 2 components:
    ("BooleanArrayNewInit2" (test-boolean-array-new-init-2
                             (java::boolean-value t)
                             (java::boolean-value nil)))
    ("CharArrayNewInit2" (test-char-array-new-init-2
                          (java::char-value 736)
                          (java::char-value 18000)))
    ("ByteArrayNewInit2" (test-byte-array-new-init-2
                          (java::byte-value -10)
                          (java::byte-value 69)))
    ("ShortArrayNewInit2" (test-short-array-new-init-2
                           (java::short-value 900)
                           (java::short-value -8000)))
    ("IntArrayNewInit2" (test-int-array-new-init-2
                         (java::int-value 0)
                         (java::int-value 282828)))
    ("LongArrayNewInit2" (test-long-array-new-init-2
                          (java::long-value -348792734089274032)
                          (java::long-value 837483)))
    ;; creation with initializer of 3 components:
    ("BooleanArrayNewInit3" (test-boolean-array-new-init-3
                             (java::boolean-value t)
                             (java::boolean-value t)
                             (java::boolean-value nil)))
    ("CharArrayNewInit3" (test-char-array-new-init-3
                          (java::char-value 7361)
                          (java::char-value 0)
                          (java::char-value 1800)))
    ("ByteArrayNewInit3" (test-byte-array-new-init-3
                          (java::byte-value -10)
                          (java::byte-value 1)
                          (java::byte-value 69)))
    ("ShortArrayNewInit3" (test-short-array-new-init-3
                           (java::short-value 32767)
                           (java::short-value 900)
                           (java::short-value -8000)))
    ("IntArrayNewInit3" (test-int-array-new-init-3
                         (java::int-value 10)
                         (java::int-value 2828288)
                         (java::int-value -9)))
    ("LongArrayNewInit3" (test-long-array-new-init-3
                          (java::long-value -1134834089274032)
                          (java::long-value 202)
                          (java::long-value -10000000)))
    ;; conversion to list:
    ("BooleanArrayToList" (test-boolean-array-to-boolean-list
                           (java::boolean-array-new-init
                            (list (java::boolean-value t)
                                  (java::boolean-value nil)
                                  (java::boolean-value nil)))))
    ("CharArrayToList" (test-char-array-to-ubyte16-list
                        (java::char-array-new-init
                         (list (java::char-value 65)
                               (java::char-value 8000)))))
    ("ByteArrayToList" (test-byte-array-to-sbyte8-list
                        (java::byte-array-new-init
                         (list (java::byte-value -15)
                               (java::byte-value -35)
                               (java::byte-value 90)))))
    ("ShortArrayToList" (test-short-array-to-sbyte16-list
                         (java::short-array-new-init
                          (list (java::short-value -32768)
                                (java::short-value 32767)))))
    ("IntArrayToList" (test-int-array-to-sbyte32-list
                       (java::int-array-new-init
                        (list (java::int-value 0)))))
    ("LongArrayToList" (test-long-array-to-sbyte64-list
                        (java::long-array-new-init
                         (list (java::long-value 1)
                               (java::long-value 888888888888888888)
                               (java::long-value -888888888888888888)
                               (java::long-value -100)
                               (java::long-value 23)))))
    ("BooleanArrayToListEmpty" (test-boolean-array-to-boolean-list
                                (java::boolean-array-new-init nil)))
    ("CharArrayToListEmpty" (test-char-array-to-ubyte16-list
                             (java::char-array-new-init nil)))
    ("ByteArrayToListEmpty" (test-byte-array-to-sbyte8-list
                             (java::byte-array-new-init nil)))
    ("ShortArrayToListEmpty" (test-short-array-to-sbyte16-list
                              (java::short-array-new-init nil)))
    ("IntArrayToListEmpty" (test-int-array-to-sbyte32-list
                            (java::int-array-new-init nil)))
    ("LongArrayToListEmpty" (test-long-array-to-sbyte64-list
                             (java::long-array-new-init nil)))
    ;; conversion from list:
    ("BooleanArrayFromList" (test-boolean-array-from-boolean-list
                             '(t nil nil nil t t t t nil)))
    ("CharArrayFromList" (test-char-array-from-ubyte16-list
                          '(0 65 66 800 8000 45000 1 2 22)))
    ("ByteArrayFromList" (test-byte-array-from-sbyte8-list
                          '(-67 0 1 -127 127 -128 80)))
    ("ShortArrayFromList" (test-short-array-from-sbyte16-list
                           '(10 -1 20 8339 32766 -282 -111)))
    ("IntArrayFromList" (test-int-array-from-sbyte32-list
                         '(1 1 2 3 5 8 13 21 34 45 1000000000 -1000000000)))
    ("LongArrayFromList" (test-long-array-from-sbyte64-list
                          '(485827452
                            -2937193929939492394
                            1
                            -11
                            0
                            0
                            0
                            100)))
    ("BooleanArrayFromListEmpty" (test-boolean-array-from-boolean-list nil))
    ("CharArrayFromListEmpty" (test-char-array-from-ubyte16-list nil))
    ("ByteArrayFromListEmpty" (test-byte-array-from-sbyte8-list nil))
    ("ShortArrayFromListEmpty" (test-short-array-from-sbyte16-list nil))
    ("IntArrayFromListEmpty" (test-int-array-from-sbyte32-list nil))
    ("LongArrayFromListEmpty" (test-long-array-from-sbyte64-list nil))))

(defconst *shallow-guarded-more-tests*
  '(;; F:
    ("F0" (f (java::int-array-new-init
              (list (java::int-value 0)
                    (java::int-value 1)
                    (java::int-value 2)
                    (java::int-value 3)
                    (java::int-value 4)
                    (java::int-value 5)
                    (java::int-value 6)
                    (java::int-value 7)))
             (java::int-value 6)
             (java::int-value 2)))
    ("F1" (f (java::int-array-new-init
              (list (java::int-value -100)
                    (java::int-value -200)
                    (java::int-value -300)
                    (java::int-value -400)
                    (java::int-value -500)))
             (java::int-value 0)
             (java::int-value 3)))
    ;; G:
    ("G0" (g (java::byte-array-new-init
              (list (java::byte-value 63)
                    (java::byte-value 0)))
             (java::short-array-new-init
              (list (java::short-value 11)
                    (java::short-value 22)
                    (java::short-value 33)))))
    ("G1" (g (java::byte-array-new-init
              (list (java::byte-value -100)))
             (java::short-array-new-init
              (list))))
    ;; H:
    ("H0" (h (java::byte-value 0)))
    ("H1" (h (java::byte-value 10)))
    ("H2" (h (java::byte-value 100)))
    ;; J:
    ("J0" (j (java::byte-array-new-init
              (list (java::byte-value 0)
                    (java::byte-value 1)
                    (java::byte-value 2)
                    (java::byte-value 3)))
             (java::byte-array-new-init
              (list (java::byte-value 0)
                    (java::byte-value -1)
                    (java::byte-value -2)
                    (java::byte-value -3)))
             (java::int-value 1)
             (java::int-value 3)))
    ("J1" (j (java::byte-array-new-init
              (list (java::byte-value 10)
                    (java::byte-value 10)
                    (java::byte-value 10)))
             (java::byte-array-new-init
              (list (java::byte-value 100)
                    (java::byte-value 100)))
             (java::int-value 0)
             (java::int-value 1)))))

(defconst *shallow-guarded-tests*
  (append *shallow-guarded-basic-tests*
          *shallow-guarded-more-tests*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize the input and output types of the tested functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; read:

(java::atj-main-function-type test-boolean-array-read
                              (:jboolean[] :jint) :jboolean)

(java::atj-main-function-type test-char-array-read
                              (:jchar[] :jint) :jchar)

(java::atj-main-function-type test-byte-array-read
                              (:jbyte[] :jint) :jbyte)

(java::atj-main-function-type test-short-array-read
                              (:jshort[] :jint) :jshort)

(java::atj-main-function-type test-int-array-read
                              (:jint[] :jint) :jint)

(java::atj-main-function-type test-long-array-read
                              (:jlong[] :jint) :jlong)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; length:

(java::atj-main-function-type test-boolean-array-length (:jboolean[]) :jint)

(java::atj-main-function-type test-char-array-length (:jchar[]) :jint)

(java::atj-main-function-type test-byte-array-length (:jbyte[]) :jint)

(java::atj-main-function-type test-short-array-length (:jshort[]) :jint)

(java::atj-main-function-type test-int-array-length (:jint[]) :jint)

(java::atj-main-function-type test-long-array-length (:jlong[]) :jint)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; write:

(java::atj-main-function-type test-boolean-array-write
                              (:jboolean[] :jint :jboolean)
                              (a :jboolean[]))

(java::atj-main-function-type test-char-array-write
                              (:jchar[] :jint :jchar)
                              (a :jchar[]))

(java::atj-main-function-type test-byte-array-write
                              (:jbyte[] :jint :jbyte)
                              (a :jbyte[]))

(java::atj-main-function-type test-short-array-write
                              (:jshort[] :jint :jshort)
                              (a :jshort[]))

(java::atj-main-function-type test-int-array-write
                              (:jint[] :jint :jint)
                              (a :jint[]))

(java::atj-main-function-type test-long-array-write
                              (:jlong[] :jint :jlong)
                              (a :jlong[]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; creation with length:

(java::atj-main-function-type test-boolean-array-new-len (:jint) :jboolean[])

(java::atj-main-function-type test-char-array-new-len (:jint) :jchar[])

(java::atj-main-function-type test-byte-array-new-len (:jint) :jbyte[])

(java::atj-main-function-type test-short-array-new-len (:jint) :jshort[])

(java::atj-main-function-type test-int-array-new-len (:jint) :jint[])

(java::atj-main-function-type test-long-array-new-len (:jint) :jlong[])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; creation with initializer:

(java::atj-main-function-type test-boolean-array-new-init-0
                              () :jboolean[])

(java::atj-main-function-type test-char-array-new-init-0
                              () :jchar[])

(java::atj-main-function-type test-byte-array-new-init-0
                              () :jbyte[])

(java::atj-main-function-type test-short-array-new-init-0
                              () :jshort[])

(java::atj-main-function-type test-int-array-new-init-0
                              () :jint[])

(java::atj-main-function-type test-long-array-new-init-0
                              () :jlong[])

(java::atj-main-function-type test-boolean-array-new-init-1
                              (:jboolean) :jboolean[])

(java::atj-main-function-type test-char-array-new-init-1
                              (:jchar) :jchar[])

(java::atj-main-function-type test-byte-array-new-init-1
                              (:jbyte) :jbyte[])

(java::atj-main-function-type test-short-array-new-init-1
                              (:jshort) :jshort[])

(java::atj-main-function-type test-int-array-new-init-1
                              (:jint) :jint[])

(java::atj-main-function-type test-long-array-new-init-1
                              (:jlong) :jlong[])

(java::atj-main-function-type test-boolean-array-new-init-2
                              (:jboolean :jboolean) :jboolean[])

(java::atj-main-function-type test-char-array-new-init-2
                              (:jchar :jchar) :jchar[])

(java::atj-main-function-type test-byte-array-new-init-2
                              (:jbyte :jbyte) :jbyte[])

(java::atj-main-function-type test-short-array-new-init-2
                              (:jshort :jshort) :jshort[])

(java::atj-main-function-type test-int-array-new-init-2
                              (:jint :jint) :jint[])

(java::atj-main-function-type test-long-array-new-init-2
                              (:jlong :jlong) :jlong[])

(java::atj-main-function-type test-boolean-array-new-init-3
                              (:jboolean :jboolean :jboolean) :jboolean[])

(java::atj-main-function-type test-char-array-new-init-3
                              (:jchar :jchar :jchar) :jchar[])

(java::atj-main-function-type test-byte-array-new-init-3
                              (:jbyte :jbyte :jbyte) :jbyte[])

(java::atj-main-function-type test-short-array-new-init-3
                              (:jshort :jshort :jshort) :jshort[])

(java::atj-main-function-type test-int-array-new-init-3
                              (:jint :jint :jint) :jint[])

(java::atj-main-function-type test-long-array-new-init-3
                              (:jlong :jlong :jlong) :jlong[])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; conversion to list:

(java::atj-main-function-type test-boolean-array-to-boolean-list
                              (:jboolean[]) :avalue)

(java::atj-main-function-type test-char-array-to-ubyte16-list
                              (:jchar[]) :avalue)

(java::atj-main-function-type test-byte-array-to-sbyte8-list
                              (:jbyte[]) :avalue)

(java::atj-main-function-type test-short-array-to-sbyte16-list
                              (:jshort[]) :avalue)

(java::atj-main-function-type test-int-array-to-sbyte32-list
                              (:jint[]) :avalue)

(java::atj-main-function-type test-long-array-to-sbyte64-list
                              (:jlong[]) :avalue)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; conversion from list:

(java::atj-main-function-type test-boolean-array-from-boolean-list
                              (:avalue) :jboolean[])

(java::atj-main-function-type test-char-array-from-ubyte16-list
                              (:avalue) :jchar[])

(java::atj-main-function-type test-byte-array-from-sbyte8-list
                              (:avalue) :jbyte[])

(java::atj-main-function-type test-short-array-from-sbyte16-list
                              (:avalue) :jshort[])

(java::atj-main-function-type test-int-array-from-sbyte32-list
                              (:avalue) :jint[])

(java::atj-main-function-type test-long-array-from-sbyte64-list
                              (:avalue) :jlong[])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; other functions:

(java::atj-main-function-type f (:jint[] :jint :jint) :jint)

(java::atj-main-function-type g (:jbyte[] :jshort[]) :jint)

(java::atj-main-function-type h (:jbyte) :jchar[])

(java::atj-main-function-type i (:jfloat[] :jdouble[] :jint :jint) :jdouble)

(java::atj-main-function-type j
                              (:jbyte[] :jbyte[] :jint :jint)
                              ((bytes1 :jbyte[]) (bytes2 :jbyte[])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the tested functions, with tests.

(java::atj test-boolean-array-read
           test-char-array-read
           test-byte-array-read
           test-short-array-read
           test-int-array-read
           test-long-array-read
           test-boolean-array-length
           test-char-array-length
           test-byte-array-length
           test-short-array-length
           test-int-array-length
           test-long-array-length
           test-boolean-array-write
           test-char-array-write
           test-byte-array-write
           test-short-array-write
           test-int-array-write
           test-long-array-write
           test-boolean-array-new-len
           test-char-array-new-len
           test-byte-array-new-len
           test-short-array-new-len
           test-int-array-new-len
           test-long-array-new-len
           test-boolean-array-new-init-0
           test-char-array-new-init-0
           test-byte-array-new-init-0
           test-short-array-new-init-0
           test-int-array-new-init-0
           test-long-array-new-init-0
           test-boolean-array-new-init-1
           test-char-array-new-init-1
           test-byte-array-new-init-1
           test-short-array-new-init-1
           test-int-array-new-init-1
           test-long-array-new-init-1
           test-boolean-array-new-init-2
           test-char-array-new-init-2
           test-byte-array-new-init-2
           test-short-array-new-init-2
           test-int-array-new-init-2
           test-long-array-new-init-2
           test-boolean-array-new-init-3
           test-char-array-new-init-3
           test-byte-array-new-init-3
           test-short-array-new-init-3
           test-int-array-new-init-3
           test-long-array-new-init-3
           test-boolean-array-to-boolean-list
           test-char-array-to-ubyte16-list
           test-byte-array-to-sbyte8-list
           test-short-array-to-sbyte16-list
           test-int-array-to-sbyte32-list
           test-long-array-to-sbyte64-list
           test-boolean-array-from-boolean-list
           test-char-array-from-ubyte16-list
           test-byte-array-from-sbyte8-list
           test-short-array-from-sbyte16-list
           test-int-array-from-sbyte32-list
           test-long-array-from-sbyte64-list
           f
           g
           h
           i
           j
           :deep nil
           :guards t
           :java-class "PrimarraysShallowGuarded"
           :tests *shallow-guarded-tests*)
