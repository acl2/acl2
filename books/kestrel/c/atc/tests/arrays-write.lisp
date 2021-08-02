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

; Some examples to test code generation for array writing.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |f| (|a| |i|)
  (declare
   (xargs
    :guard (and (c::uchar-arrayp |a|)
                (c::sintp |i|)
                (c::uchar-array-sint-index-okp |a| |i|))
    :guard-hints (("Goal" :in-theory (enable c::uchar-array-sint-index-okp
                                             c::uchar-array-index-okp
                                             c::uchar-array-write-sint
                                             c::uchar-array-write)))))
  (let ((|a| (c::uchar-array-write-sint |a| |i| (c::uchar-from-sint
                                                 (c::sint-dec-const 88)))))
    |a|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |copy$loop| (|a| |b| |len| |i|)
  (declare (xargs :guard (and (c::uchar-arrayp |a|)
                              (c::uchar-arrayp |b|)
                              (c::sintp |len|)
                              (c::sintp |i|)
                              (equal (len (c::uchar-array->elements |a|))
                                     (c::sint->get |len|))
                              (equal (len (c::uchar-array->elements |b|))
                                     (c::sint->get |len|))
                              (<= 0
                                  (c::sint->get |i|))
                              (<= (c::sint->get |i|)
                                  (c::sint->get |len|)))
                  :guard-hints (("Goal"
                                 :do-not-induct t
                                 :in-theory
                                 (enable c::uchar-array-sint-index-okp
                                         c::uchar-array-index-okp
                                         c::boolean-from-sint
                                         c::lt-sint-sint
                                         c::add-sint-sint
                                         c::add-sint-sint-okp
                                         c::sint-integerp-alt-def
                                         c::uchar-array-write-sint
                                         c::uchar-array-write
                                         c::sint-integer-value
                                         c::assign)))
                  :measure (nfix (- (c::sint->get |len|)
                                    (c::sint->get |i|)))
                  :hints (("Goal"
                           :in-theory (enable c::boolean-from-sint
                                              c::lt-sint-sint
                                              c::add-sint-sint
                                              c::sint-integerp-alt-def
                                              c::assign)))))
  (if (mbt (and (c::sintp |i|)
                (c::sintp |len|)
                (>= (c::sint->get |i|) 0)
                (>= (c::sint->get |len|) 0)))
      (if (c::boolean-from-sint (c::lt-sint-sint |i| |len|))
          (let* ((|b| (c::uchar-array-write-sint
                       |b| |i| (c::uchar-array-read-sint |a| |i|)))
                 (|i| (c::assign (c::add-sint-sint |i| (c::sint-dec-const 1)))))
            (|copy$loop| |a| |b| |len| |i|))
        (mv |b| |i|))
    (mv :irrelevant :irrelevant)))

;;;;;;;;;;;;;;;;;;;;

(defun |copy| (|a| |b| |len|)
  (declare (xargs :guard (and (c::uchar-arrayp |a|)
                              (c::uchar-arrayp |b|)
                              (c::sintp |len|)
                              (equal (len (c::uchar-array->elements |a|))
                                     (c::sint->get |len|))
                              (equal (len (c::uchar-array->elements |b|))
                                     (c::sint->get |len|)))))
  (let ((|i| (c::declar (c::sint-dec-const 0))))
    (mv-let (|b| |i|)
      (|copy$loop| |a| |b| |len| |i|)
      (declare (ignore |i|))
      |b|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |f| |copy$loop| |copy| :output-file "arrays-write.c"
        :experimental (:array-writes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

On macOS or Linux, you can compile and run this code as follows:

  gcc -o arrays-write arrays-write.c arrays-write-test.c
  ./arrays-write

|#
