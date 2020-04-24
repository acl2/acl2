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

; constructors from components, applied to LIST calls:

;;;;;;;;;;;;;;;;;;;;

; lists of length 0:

(defun test-boolean-array-of-list-0 ()
  (java::boolean-array nil))

(defun test-char-array-of-list-0 ()
  (java::char-array nil))

(defun test-byte-array-of-list-0 ()
  (java::byte-array nil))

(defun test-short-array-of-list-0 ()
  (java::short-array nil))

(defun test-int-array-of-list-0 ()
  (java::int-array nil))

(defun test-long-array-of-list-0 ()
  (java::long-array nil))

;;;;;;;;;;;;;;;;;;;;

; lists of length 1:

(defun test-boolean-array-of-list-1 (x)
  (declare (xargs :guard (java::boolean-value-p x)))
  (java::boolean-array (list x)))

(defun test-char-array-of-list-1 (x)
  (declare (xargs :guard (java::char-value-p x)))
  (java::char-array (list x)))

(defun test-byte-array-of-list-1 (x)
  (declare (xargs :guard (java::byte-value-p x)))
  (java::byte-array (list x)))

(defun test-short-array-of-list-1 (x)
  (declare (xargs :guard (java::short-value-p x)))
  (java::short-array (list x)))

(defun test-int-array-of-list-1 (x)
  (declare (xargs :guard (java::int-value-p x)))
  (java::int-array (list x)))

(defun test-long-array-of-list-1 (x)
  (declare (xargs :guard (java::long-value-p x)))
  (java::long-array (list x)))

;;;;;;;;;;;;;;;;;;;;

; lists of length 2:

(defun test-boolean-array-of-list-2 (x y)
  (declare (xargs :guard (and (java::boolean-value-p x)
                              (java::boolean-value-p y))))
  (java::boolean-array (list x y)))

(defun test-char-array-of-list-2 (x y)
  (declare (xargs :guard (and (java::char-value-p x)
                              (java::char-value-p y))))
  (java::char-array (list x y)))

(defun test-byte-array-of-list-2 (x y)
  (declare (xargs :guard (and (java::byte-value-p x)
                              (java::byte-value-p y))))
  (java::byte-array (list x y)))

(defun test-short-array-of-list-2 (x y)
  (declare (xargs :guard (and (java::short-value-p x)
                              (java::short-value-p y))))
  (java::short-array (list x y)))

(defun test-int-array-of-list-2 (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::int-array (list x y)))

(defun test-long-array-of-list-2 (x y)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y))))
  (java::long-array (list x y)))

;;;;;;;;;;;;;;;;;;;;

; lists of length 3:

(defun test-boolean-array-of-list-3 (x y z)
  (declare (xargs :guard (and (java::boolean-value-p x)
                              (java::boolean-value-p y)
                              (java::boolean-value-p z))))
  (java::boolean-array (list x y z)))

(defun test-char-array-of-list-3 (x y z)
  (declare (xargs :guard (and (java::char-value-p x)
                              (java::char-value-p y)
                              (java::char-value-p z))))
  (java::char-array (list x y z)))

(defun test-byte-array-of-list-3 (x y z)
  (declare (xargs :guard (and (java::byte-value-p x)
                              (java::byte-value-p y)
                              (java::byte-value-p z))))
  (java::byte-array (list x y z)))

(defun test-short-array-of-list-3 (x y z)
  (declare (xargs :guard (and (java::short-value-p x)
                              (java::short-value-p y)
                              (java::short-value-p z))))
  (java::short-array (list x y z)))

(defun test-int-array-of-list-3 (x y z)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y)
                              (java::int-value-p z))))
  (java::int-array (list x y z)))

(defun test-long-array-of-list-3 (x y z)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y)
                              (java::long-value-p z))))
  (java::long-array (list x y z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; read operations:

(defun test-boolean-array-read (a i)
  (declare
   (xargs :guard (and (java::boolean-array-p a)
                      (java::int-value-p i)
                      (java::boolean-array-index-in-range-p a i))))
  (java::boolean-array-read a i))

(defun test-char-array-read (a i)
  (declare
   (xargs :guard (and (java::char-array-p a)
                      (java::int-value-p i)
                      (java::char-array-index-in-range-p a i))))
  (java::char-array-read a i))

(defun test-byte-array-read (a i)
  (declare
   (xargs :guard (and (java::byte-array-p a)
                      (java::int-value-p i)
                      (java::byte-array-index-in-range-p a i))))
  (java::byte-array-read a i))

(defun test-short-array-read (a i)
  (declare
   (xargs :guard (and (java::short-array-p a)
                      (java::int-value-p i)
                      (java::short-array-index-in-range-p a i))))
  (java::short-array-read a i))

(defun test-int-array-read (a i)
  (declare
   (xargs :guard (and (java::int-array-p a)
                      (java::int-value-p i)
                      (java::int-array-index-in-range-p a i))))
  (java::int-array-read a i))

(defun test-long-array-read (a i)
  (declare
   (xargs :guard (and (java::long-array-p a)
                      (java::int-value-p i)
                      (java::long-array-index-in-range-p a i))))
  (java::long-array-read a i))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; length operations:

(defun test-boolean-array-length (a)
  (declare (xargs :guard (java::boolean-array-p a)))
  (java::boolean-array-length a))

(defun test-char-array-length (a)
  (declare (xargs :guard (java::char-array-p a)))
  (java::char-array-length a))

(defun test-byte-array-length (a)
  (declare (xargs :guard (java::byte-array-p a)))
  (java::byte-array-length a))

(defun test-short-array-length (a)
  (declare (xargs :guard (java::short-array-p a)))
  (java::short-array-length a))

(defun test-int-array-length (a)
  (declare (xargs :guard (java::int-array-p a)))
  (java::int-array-length a))

(defun test-long-array-length (a)
  (declare (xargs :guard (java::long-array-p a)))
  (java::long-array-length a))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; write operations:

(defun test-boolean-array-write (a i e)
  (declare
   (xargs :guard (and (java::boolean-array-p a)
                      (java::int-value-p i)
                      (java::boolean-array-index-in-range-p a i)
                      (java::boolean-value-p e))))
  (java::boolean-array-write a i e))

(defun test-char-array-write (a i e)
  (declare
   (xargs :guard (and (java::char-array-p a)
                      (java::int-value-p i)
                      (java::char-array-index-in-range-p a i)
                      (java::char-value-p e))))
  (java::char-array-write a i e))

(defun test-byte-array-write (a i e)
  (declare
   (xargs :guard (and (java::byte-array-p a)
                      (java::int-value-p i)
                      (java::byte-array-index-in-range-p a i)
                      (java::byte-value-p e))))
  (java::byte-array-write a i e))

(defun test-short-array-write (a i e)
  (declare
   (xargs :guard (and (java::short-array-p a)
                      (java::int-value-p i)
                      (java::short-array-index-in-range-p a i)
                      (java::short-value-p e))))
  (java::short-array-write a i e))

(defun test-int-array-write (a i e)
  (declare
   (xargs :guard (and (java::int-array-p a)
                      (java::int-value-p i)
                      (java::int-array-index-in-range-p a i)
                      (java::int-value-p e))))
  (java::int-array-write a i e))

(defun test-long-array-write (a i e)
  (declare
   (xargs :guard (and (java::long-array-p a)
                      (java::int-value-p i)
                      (java::long-array-index-in-range-p a i)
                      (java::long-value-p e))))
  (java::long-array-write a i e))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; constructors from length:

(defun test-boolean-array-of-length (l)
  (declare (xargs :guard (and (java::int-value-p l)
                              (<= 0 (java::int-value->int l)))))
  (java::boolean-array-of-length l))

(defun test-char-array-of-length (l)
  (declare (xargs :guard (and (java::int-value-p l)
                              (<= 0 (java::int-value->int l)))))
  (java::char-array-of-length l))

(defun test-byte-array-of-length (l)
  (declare (xargs :guard (and (java::int-value-p l)
                              (<= 0 (java::int-value->int l)))))
  (java::byte-array-of-length l))

(defun test-short-array-of-length (l)
  (declare (xargs :guard (and (java::int-value-p l)
                              (<= 0 (java::int-value->int l)))))
  (java::short-array-of-length l))

(defun test-int-array-of-length (l)
  (declare (xargs :guard (and (java::int-value-p l)
                              (<= 0 (java::int-value->int l)))))
  (java::int-array-of-length l))

(defun test-long-array-of-length (l)
  (declare (xargs :guard (and (java::int-value-p l)
                              (<= 0 (java::int-value->int l)))))
  (java::long-array-of-length l))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; More functions over (ACL2 representations of) Java primitive arrays.

(defun f (array i j)
  (declare
   (xargs :guard (and
                  (java::int-array-p array)
                  (java::int-value-p i)
                  (java::int-value-p j)
                  (java::int-array-index-in-range-p array i)
                  (java::int-array-index-in-range-p array j))))
  (java::int-add (java::int-array-read array i)
                 (java::int-array-read array j)))

(defun g (bytearray shortarray)
  (declare (xargs :guard (and (java::byte-array-p bytearray)
                              (java::short-array-p shortarray))))
  (java::int-add (java::byte-array-length bytearray)
                 (java::short-array-length shortarray)))

(defun h (length)
  (declare (xargs :guard (and (java::byte-value-p length)
                              (>= (java::byte-value->int length) 0))
                  :guard-hints (("Goal" :in-theory (enable java::byte-to-short
                                                           java::short-to-int
                                                           sbyte16-fix
                                                           sbyte32-fix)))))
  (b* ((length (java::byte-to-short length))
       (length (java::short-to-int length)))
    (java::char-array-of-length length)))

(defun i (floatarray doublearray i j)
  (declare
   (xargs :guard (and (java::float-array-p floatarray)
                      (java::double-array-p doublearray)
                      (java::int-value-p i)
                      (java::int-value-p j)
                      (java::float-array-index-in-range-p floatarray i)
                      (java::double-array-index-in-range-p doublearray j))))
  (java::double-rem (java::float-to-double
                     (java::float-array-read floatarray i))
                    (java::double-array-read doublearray j)))

(defun j (bytes1 bytes2 i1 i2)
  (declare (xargs :guard (and (java::byte-array-p bytes1)
                              (java::byte-array-p bytes2)
                              (java::int-value-p i1)
                              (java::int-value-p i2)
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
  '(;; constructors from components applied to LIST calls of length 0:
    ("BooleanArrayOfList0" (test-boolean-array-of-list-0))
    ("CharArrayOfList0" (test-char-array-of-list-0))
    ("ByteArrayOfList0" (test-byte-array-of-list-0))
    ("ShortArrayOfList0" (test-short-array-of-list-0))
    ("IntArrayOfList0" (test-int-array-of-list-0))
    ("LongArrayOfList0" (test-long-array-of-list-0))
    ;; constructors from components applied to LIST calls of length 1:
    ("BooleanArrayOfList1" (test-boolean-array-of-list-1
                            (java::boolean-value t)))
    ("CharArrayOfList1" (test-char-array-of-list-1
                         (java::char-value 8888)))
    ("ByteArrayOfList1" (test-byte-array-of-list-1
                         (java::byte-value -1)))
    ("ShortArrayOfList1" (test-short-array-of-list-1
                          (java::short-value 8000)))
    ("IntArrayOfList1" (test-int-array-of-list-1
                        (java::int-value 2000000000)))
    ("LongArrayOfList1" (test-long-array-of-list-1
                         (java::long-value -8000000000000000000)))
    ;; constructors from components applied to LIST calls of length 2:
    ("BooleanArrayOfList2" (test-boolean-array-of-list-2
                            (java::boolean-value t)
                            (java::boolean-value nil)))
    ("CharArrayOfList2" (test-char-array-of-list-2
                         (java::char-value 736)
                         (java::char-value 18000)))
    ("ByteArrayOfList2" (test-byte-array-of-list-2
                         (java::byte-value -10)
                         (java::byte-value 69)))
    ("ShortArrayOfList2" (test-short-array-of-list-2
                          (java::short-value 900)
                          (java::short-value -8000)))
    ("IntArrayOfList2" (test-int-array-of-list-2
                        (java::int-value 0)
                        (java::int-value 282828)))
    ("LongArrayOfList2" (test-long-array-of-list-2
                         (java::long-value -348792734089274032)
                         (java::long-value 837483)))
    ;; constructors from components applied to LIST calls of length 3:
    ("BooleanArrayOfList3" (test-boolean-array-of-list-3
                            (java::boolean-value t)
                            (java::boolean-value t)
                            (java::boolean-value nil)))
    ("CharArrayOfList3" (test-char-array-of-list-3
                         (java::char-value 7361)
                         (java::char-value 0)
                         (java::char-value 1800)))
    ("ByteArrayOfList3" (test-byte-array-of-list-3
                         (java::byte-value -10)
                         (java::byte-value 1)
                         (java::byte-value 69)))
    ("ShortArrayOfList3" (test-short-array-of-list-3
                          (java::short-value 32767)
                          (java::short-value 900)
                          (java::short-value -8000)))
    ("IntArrayOfList3" (test-int-array-of-list-3
                        (java::int-value 10)
                        (java::int-value 2828288)
                        (java::int-value -9)))
    ("LongArrayOfList3" (test-long-array-of-list-3
                         (java::long-value -1134834089274032)
                         (java::long-value 202)
                         (java::long-value -10000000)))
    ;; read operations:
    ("BooleanArrayRead" (test-boolean-array-read
                         (java::boolean-array
                          (list (java::boolean-value t)
                                (java::boolean-value nil)
                                (java::boolean-value nil)))
                         (java::int-value 2)))
    ("CharArrayRead" (test-char-array-read
                      (java::char-array
                       (list (java::char-value 722)
                             (java::char-value 9990)
                             (java::char-value 1)))
                      (java::int-value 1)))
    ("ByteArrayRead" (test-byte-array-read
                      (java::byte-array
                       (list (java::byte-value -100)
                             (java::byte-value 100)))
                      (java::int-value 0)))
    ("ShortArrayRead" (test-short-array-read
                       (java::short-array
                        (list (java::short-value -100)
                              (java::short-value 100)
                              (java::short-value 32001)
                              (java::short-value -5000)))
                       (java::int-value 2)))
    ("IntArrayRead" (test-int-array-read
                     (java::int-array
                      (list (java::int-value 1000000000)))
                     (java::int-value 0)))
    ("LongArrayRead" (test-long-array-read
                      (java::long-array
                       (list (java::long-value 1000000000)
                             (java::long-value 1000000000000000000)))
                      (java::int-value 1)))
    ;; length operations:
    ("BooleanArrayLength" (test-boolean-array-length
                           (java::boolean-array
                            (list (java::boolean-value t)
                                  (java::boolean-value nil)
                                  (java::boolean-value nil)))))
    ("CharArrayLength" (test-char-array-length
                        (java::char-array
                         (list (java::char-value 722)
                               (java::char-value 9990)
                               (java::char-value 1)))))
    ("ByteArrayLength" (test-byte-array-length
                        (java::byte-array
                         (list (java::byte-value -100)
                               (java::byte-value 100)))))
    ("ShortArrayLength" (test-short-array-length
                         (java::short-array
                          (list (java::short-value -100)
                                (java::short-value 100)
                                (java::short-value 32001)
                                (java::short-value -5000)))))
    ("IntArrayLength" (test-int-array-length
                       (java::int-array
                        (list (java::int-value 1000000000)))))
    ("LongArrayLength" (test-long-array-length
                        (java::long-array
                         (list (java::long-value 1000000000)
                               (java::long-value 1000000000000000000)))))
    ;; write operations:
    ("BooleanArrayWrite" (test-boolean-array-write
                          (java::boolean-array
                           (list (java::boolean-value t)
                                 (java::boolean-value nil)
                                 (java::boolean-value nil)))
                          (java::int-value 2)
                          (java::boolean-value t)))
    ("CharArrayWrite" (test-char-array-write
                       (java::char-array
                        (list (java::char-value 722)
                              (java::char-value 9990)
                              (java::char-value 1)))
                       (java::int-value 1)
                       (java::char-value 88)))
    ("ByteArrayWrite" (test-byte-array-write
                       (java::byte-array
                        (list (java::byte-value -100)
                              (java::byte-value 100)))
                       (java::int-value 0)
                       (java::byte-value -10)))
    ("ShortArrayWrite" (test-short-array-write
                        (java::short-array
                         (list (java::short-value -100)
                               (java::short-value 100)
                               (java::short-value 32001)
                               (java::short-value -5000)))
                        (java::int-value 2)
                        (java::short-value 1)))
    ("IntArrayWrite" (test-int-array-write
                      (java::int-array
                       (list (java::int-value 1000000000)))
                      (java::int-value 0)
                      (java::int-value -100000)))
    ("LongArrayWrite" (test-long-array-write
                       (java::long-array
                        (list (java::long-value 1000000000)
                              (java::long-value 1000000000000000000)))
                       (java::int-value 1)
                       (java::long-value -55555555555555555)))
    ;; constructors from length:
    ("BooleanArrayFromLength0" (test-boolean-array-of-length
                                (java::int-value 0)))
    ("BooleanArrayFromLength1" (test-boolean-array-of-length
                                (java::int-value 80)))
    ("CharArrayFromLength0" (test-char-array-of-length
                             (java::int-value 8)))
    ("CharArrayFromLength1" (test-char-array-of-length
                             (java::int-value 19)))
    ("ByteArrayFromLength0" (test-byte-array-of-length
                             (java::int-value 73)))
    ("ByteArrayFromLength1" (test-byte-array-of-length
                             (java::int-value 1)))
    ("ShortArrayFromLength0" (test-short-array-of-length
                              (java::int-value 7)))
    ("ShortArrayFromLength1" (test-short-array-of-length
                              (java::int-value 111)))
    ("IntArrayFromLength0" (test-int-array-of-length
                            (java::int-value 0)))
    ("IntArrayFromLength1" (test-int-array-of-length
                            (java::int-value 9)))
    ("LongArrayFromLength0" (test-long-array-of-length
                             (java::int-value 20)))
    ("LongArrayFromLength1" (test-long-array-of-length
                             (java::int-value 23)))))

(defconst *shallow-guarded-more-tests*
  '(;; F:
    ("F0" (f (java::int-array (list (java::int-value 0)
                                    (java::int-value 1)
                                    (java::int-value 2)
                                    (java::int-value 3)
                                    (java::int-value 4)
                                    (java::int-value 5)
                                    (java::int-value 6)
                                    (java::int-value 7)))
             (java::int-value 6)
             (java::int-value 2)))
    ("F1" (f (java::int-array (list (java::int-value -100)
                                    (java::int-value -200)
                                    (java::int-value -300)
                                    (java::int-value -400)
                                    (java::int-value -500)))
             (java::int-value 0)
             (java::int-value 3)))
    ;; G:
    ("G0" (g (java::byte-array (list (java::byte-value 63)
                                     (java::byte-value 0)))
             (java::short-array (list (java::short-value 11)
                                      (java::short-value 22)
                                      (java::short-value 33)))))
    ("G1" (g (java::byte-array (list (java::byte-value -100)))
             (java::short-array (list))))
    ;; H:
    ("H0" (h (java::byte-value 0)))
    ("H1" (h (java::byte-value 10)))
    ("H2" (h (java::byte-value 100)))
    ;; J:
    ("J0" (j (java::byte-array (list (java::byte-value 0)
                                     (java::byte-value 1)
                                     (java::byte-value 2)
                                     (java::byte-value 3)))
             (java::byte-array (list (java::byte-value 0)
                                     (java::byte-value -1)
                                     (java::byte-value -2)
                                     (java::byte-value -3)))
             (java::int-value 1)
             (java::int-value 3)))
    ("J1" (j (java::byte-array (list (java::byte-value 10)
                                     (java::byte-value 10)
                                     (java::byte-value 10)))
             (java::byte-array (list (java::byte-value 100)
                                     (java::byte-value 100)))
             (java::int-value 0)
             (java::int-value 1)))))

(defconst *shallow-guarded-tests*
  (append *shallow-guarded-basic-tests*
          *shallow-guarded-more-tests*))
