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

(include-book "defobject") ; reuse these DEFOBJECTs

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some examples to test code generation for external objects.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |f| (|x| |arr|)
  (declare (xargs :guard (and (c::sintp |x|)
                              (object-|arr|-p |arr|)
                              (c::sint-array-index-okp |arr| |x|))
                  :guard-hints (("Goal" :in-theory (enable object-|arr|-p)))))
  (c::sint-array-read |arr| |x|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |g$loop| (|i| |sum| |arr2|)
  (declare (xargs :guard (and (c::sintp |i|)
                              (c::uintp |sum|)
                              (object-|arr2|-p |arr2|)
                              (<= 0 (c::integer-from-sint |i|))
                              (<= (c::integer-from-sint |i|) 8))
                  :guard-hints (("Goal"
                                 :in-theory (enable
                                             c::add-sint-sint-okp
                                             c::add-sint-sint
                                             c::sint-integerp-alt-def
                                             c::ne-sint-sint
                                             c::uint-array-index-okp
                                             object-|arr2|-p
                                             c::assign
                                             c::integer-from-cinteger-alt-def)))
                  :measure (nfix (- 8 (c::integer-from-sint |i|)))
                  :hints (("Goal" :in-theory (enable c::ne-sint-sint
                                                     c::add-sint-sint
                                                     c::sint-from-boolean
                                                     c::sint-integerp-alt-def
                                                     c::assign)))))
  (if (mbt (and (<= 0 (c::integer-from-sint |i|))
                (<= (c::integer-from-sint |i|) 8)))
      (if (c::boolean-from-sint (c::ne-sint-sint |i| (c::sint-dec-const 8)))
          (let* ((|sum| (c::assign
                         (c::add-uint-uint
                          |sum|
                          (c::uint-array-read |arr2| |i|))))
                 (|i| (c::assign (c::add-sint-sint |i| (c::sint-dec-const 1)))))
            (|g$loop| |i| |sum| |arr2|))
        (mv |i| |sum|))
    (mv nil nil)))

(defun |g| (|arr2|)
  (declare (xargs :guard (object-|arr2|-p |arr2|)))
  (let* ((|i| (c::declar (c::sint-dec-const 0)))
         (|sum| (c::declar (c::uint-dec-const 0))))
    (mv-let (|i| |sum|)
        (|g$loop| |i| |sum| |arr2|)
      (declare (ignore |i|))
      |sum|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |h| (|x| |arr|)
  (declare (xargs :guard (and (c::sintp |x|)
                              (object-|arr|-p |arr|)
                              (c::sint-array-index-okp |arr| |x|))
                  :guard-hints (("Goal" :in-theory (enable object-|arr|-p)))))
  (let ((|arr| (c::sint-array-write |arr| |x| (c::sint-dec-const 1))))
    |arr|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |i$loop| (|arr2| |idx|)
  (declare (xargs :guard (and (object-|arr2|-p |arr2|)
                              (c::sintp |idx|)
                              (<= 0 (c::integer-from-sint |idx|))
                              (<= (c::integer-from-sint |idx|) 8))
                  :guard-hints (("Goal"
                                 :in-theory (enable
                                             c::add-sint-sint-okp
                                             c::add-sint-sint
                                             c::sint-integerp-alt-def
                                             c::ne-sint-sint
                                             c::uint-array-index-okp
                                             object-|arr2|-p
                                             c::assign
                                             c::integer-from-cinteger-alt-def)))
                  :measure (nfix (- 8 (c::integer-from-sint |idx|)))
                  :hints (("Goal" :in-theory (enable c::ne-sint-sint
                                                     c::add-sint-sint
                                                     c::sint-from-boolean
                                                     c::sint-integerp-alt-def
                                                     c::assign)))))
  (if (mbt (and (<= 0 (c::integer-from-sint |idx|))
                (<= (c::integer-from-sint |idx|) 8)))
      (if (c::boolean-from-sint (c::ne-sint-sint |idx| (c::sint-dec-const 8)))
          (let* ((|arr2| (c::uint-array-write
                          |arr2|
                          |idx|
                          (c::add-uint-uint
                           (c::uint-array-read |arr2| |idx|)
                           (c::uint-dec-const 1))))
                 (|idx| (c::assign
                         (c::add-sint-sint |idx| (c::sint-dec-const 1)))))
            (|i$loop| |arr2| |idx|))
        (mv |idx| |arr2|))
    (mv nil nil)))

(defun |i| (|arr2|)
  (declare (xargs :guard (object-|arr2|-p |arr2|)))
  (let* ((|idx| (c::declar (c::sint-dec-const 0))))
    (mv-let (|idx| |arr2|)
        (|i$loop| |arr2| |idx|)
      (declare (ignore |idx|))
      |arr2|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |j| (|x| |global|)
  (declare
   (xargs :guard (and (c::sintp |x|)
                      (object-|global|-p |global|))
          :guard-hints (("Goal" :in-theory (enable object-|global|-p)))))
  (c::eq-sint-sint |x| (c::sint-from-sshort |global|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |k| (|global_0|)
  (declare
   (xargs :guard (object-|global_0|-p |global_0|)
          :guard-hints (("Goal" :in-theory (enable object-|global_0|-p)))))
  (if (c::boolean-from-sint (c::lt-uint-uint |global_0| (c::uint-dec-const 10)))
      (let ((|global_0|
             (c::assign (c::add-uint-uint |global_0| (c::uint-dec-const 1)))))
        |global_0|)
    (let ((|global_0|
           (c::assign (c::sub-uint-uint |global_0| (c::uint-dec-const 1)))))
      |global_0|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |k_caller| (|global_0|)
  (declare (xargs :guard (object-|global_0|-p |global_0|)))
  (let ((|global_0| (|k| |global_0|)))
    |global_0|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |arr|
        |f|
        |arr2|
        |g$loop|
        |g|
        |h|
        |i$loop|
        |i|
        |perm|
        |arr_no_init|
        |global|
        |global_0|
        |j|
        |k|
        |k_caller|
        :file-name "ext-objs"
        :header t)
