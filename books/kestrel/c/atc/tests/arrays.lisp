; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib) (:open-output-channel!)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some examples to test code generation for arrays.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read elements from arrays.

(defun |read| (|a| |i|)
  (declare (xargs :guard (and (c::uchar-arrayp |a|)
                              (c::sintp |i|)
                              (c::uchar-array-sint-index-okp |a| |i|))))
  (c::uchar-array-read-sint |a| |i|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Return arrays unchanged.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return1| (|a|)
  (declare (xargs :guard (c::uchar-arrayp |a|)))
  |a|)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return2| (|a| |b|)
  (declare (xargs :guard (and (c::ushort-arrayp |a|)
                              (c::sllong-arrayp |b|))))
  (declare (ignore |b|))
  |a|)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |return3| (|a| |b|)
  (declare (xargs :guard (and (c::uchar-arrayp |a|)
                              (c::sllong-arrayp |b|))))
  (mv |b| |a|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Write elements to arrays.

(defun |write| (|a| |i|)
  (declare
   (xargs
    :guard (and (c::uchar-arrayp |a|)
                (c::sintp |i|)
                (c::uchar-array-sint-index-okp |a| |i|))))
  (let ((|a| (c::uchar-array-write-sint |a| |i| (c::uchar-from-sint
                                                 (c::sint-dec-const 88)))))
    |a|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |read|
        |return1|
        |return2|
        |return3|
        |write|
        :output-file "arrays.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

On macOS or Linux, you can compile and run this code as follows:

  gcc -o arrays arrays.c arrays-test.c
  ./arrays

|#
