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
; that manipulates Java primitive arrays.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A function that reads from an int[] array.

(defun read-from-array (array i j)
  (declare
   (xargs :guard (and
                  (java::int-array-p array)
                  (java::int-value-p i)
                  (java::int-value-p j)
                  (integer-range-p 0 (len array) (java::int-value->int i))
                  (integer-range-p 0 (len array) (java::int-value->int j)))))
  (java::int-add (java::int-array-read array i)
                 (java::int-array-read array j)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A function that obtains and adds the lengths of a byte[] and short[] array.

(defun add-lengths-of-arrays (bytearray shortarray)
  (declare (xargs :guard (and (java::byte-array-p bytearray)
                              (java::short-array-p shortarray))))
  (java::int-add (java::byte-array-length bytearray)
                 (java::short-array-length shortarray)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A function that creates a new char[] array of a certain length.

(defun create-array-of-length (length)
  (declare (xargs :guard (and (java::byte-value-p length)
                              (>= (java::byte-value->int length) 0))
                  :guard-hints (("Goal" :in-theory (enable java::byte-to-short
                                                           java::short-to-int
                                                           sbyte16-fix
                                                           sbyte32-fix)))))
  (b* ((length (java::byte-to-short length))
       (length (java::short-to-int length)))
    (java::char-array-of-length length)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A function that creates a new long[] array from a list of components.

(defun create-array-with-components (x y z)
  (declare (xargs :guard (and (java::long-value-p x)
                              (java::long-value-p y)
                              (java::long-value-p z))))
  (java::long-array-with-comps (list x y z)))
