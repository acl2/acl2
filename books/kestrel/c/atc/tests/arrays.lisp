; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |read| (|a| |i|)
  (declare (xargs :guard (and (c::uchar-arrayp |a|)
                              (c::sintp |i|)
                              (c::uchar-array-index-okp |a| |i|))))
  (c::uchar-array-read |a| |i|))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |write| (|a| |i|)
  (declare
   (xargs
    :guard (and (c::uchar-arrayp |a|)
                (c::sintp |i|)
                (c::uchar-array-index-okp |a| |i|))))
  (let ((|a| (c::uchar-array-write |a| |i| (c::uchar-from-sint
                                            (c::sint-dec-const 88)))))
    |a|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |copy$loop| (|a| |b| |len| |i|)
  (declare (xargs :guard (and (c::uchar-arrayp |a|)
                              (c::uchar-arrayp |b|)
                              (c::sintp |len|)
                              (c::sintp |i|)
                              (equal (c::uchar-array-length |a|)
                                     (c::integer-from-sint |len|))
                              (equal (c::uchar-array-length |b|)
                                     (c::integer-from-sint |len|))
                              (<= 0
                                  (c::integer-from-sint |i|))
                              (<= (c::integer-from-sint |i|)
                                  (c::integer-from-sint |len|)))
                  :guard-hints (("Goal"
                                 :do-not-induct t
                                 :in-theory
                                 (enable c::uchar-array-index-okp
                                         c::uchar-array-integer-index-okp
                                         c::boolean-from-sint
                                         c::lt-sint-sint
                                         c::add-sint-sint
                                         c::add-sint-sint-okp
                                         c::sint-integerp-alt-def
                                         c::assign
                                         c::integer-from-cinteger-alt-def)))
                  :measure (nfix (- (c::integer-from-sint |len|)
                                    (c::integer-from-sint |i|)))
                  :hints (("Goal"
                           :in-theory (enable c::boolean-from-sint
                                              c::lt-sint-sint
                                              c::add-sint-sint
                                              c::sint-integerp-alt-def
                                              c::assign)))))
  (if (mbt (and (c::sintp |i|)
                (c::sintp |len|)
                (>= (c::integer-from-sint |i|) 0)
                (>= (c::integer-from-sint |len|) 0)))
      (if (c::boolean-from-sint (c::lt-sint-sint |i| |len|))
          (let* ((|b| (c::uchar-array-write
                       |b| |i| (c::uchar-array-read |a| |i|)))
                 (|i| (c::assign (c::add-sint-sint |i| (c::sint-dec-const 1)))))
            (|copy$loop| |a| |b| |len| |i|))
        (mv |b| |i|))
    (mv :irrelevant :irrelevant)))

;;;;;;;;;;;;;;;;;;;;

(defun |copy| (|a| |b| |len|)
  (declare (xargs :guard (and (c::uchar-arrayp |a|)
                              (c::uchar-arrayp |b|)
                              (c::sintp |len|)
                              (equal (c::uchar-array-length |a|)
                                     (c::integer-from-sint |len|))
                              (equal (c::uchar-array-length |b|)
                                     (c::integer-from-sint |len|)))))
  (let ((|i| (c::declar (c::sint-dec-const 0))))
    (mv-let (|b| |i|)
      (|copy$loop| |a| |b| |len| |i|)
      (declare (ignore |i|))
      |b|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |read|
        |return1|
        |return2|
        |return3|
        |write|
        |copy$loop|
        |copy|
        :file-name "arrays"
        :header t)
