; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib) (:open-output-channel!)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some tests for external objects.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::defobject |arr|
              :type (c::sint 5)
              :init ((c::sint-dec-const 1)
                     (c::sint-dec-const 2)
                     (c::sint-dec-const 3)
                     (c::sint-dec-const 4)
                     (c::sint-dec-const 5)))

(c::defobject |arr2|
              :type (c::uint 8)
              :init ((c::uint-dec-const 10)
                     (c::uint-dec-const 20)
                     (c::uint-dec-const 30)
                     (c::uint-dec-const 40)
                     (c::uint-dec-const 50)
                     (c::uint-dec-const 60)
                     (c::uint-dec-const 70)
                     (c::uint-dec-const 80)))

(c::defobject |perm|
              :type (c::uchar 3)
              :init ((c::uchar-from-sint (c::sint-hex-const 17))
                     (c::uchar-from-sint (c::sint-hex-const 2))
                     (c::uchar-from-sint (c::sint-oct-const 22))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |f| (|x| |arr|)
  (declare (xargs :guard (and (c::sintp |x|)
                              (object-|arr|-p |arr|)
                              (c::sint-array-sint-index-okp |arr| |x|))
                  :guard-hints (("Goal" :in-theory (enable object-|arr|-p)))))
  (c::sint-array-read-sint |arr| |x|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |g$loop| (|i| |sum| |arr2|)
  (declare (xargs :guard (and (c::sintp |i|)
                              (c::uintp |sum|)
                              (object-|arr2|-p |arr2|)
                              (<= 0 (c::sint->get |i|))
                              (<= (c::sint->get |i|) 8))
                  :guard-hints (("Goal"
                                 :in-theory (enable c::add-sint-sint-okp
                                                    c::add-sint-sint
                                                    c::sint-integerp-alt-def
                                                    c::ne-sint-sint
                                                    c::uint-array-sint-index-okp
                                                    c::uint-array-index-okp
                                                    object-|arr2|-p
                                                    c::assign)))
                  :measure (nfix (- 8 (c::sint->get |i|)))
                  :hints (("Goal" :in-theory (enable c::ne-sint-sint
                                                     c::add-sint-sint
                                                     c::sint-from-boolean
                                                     c::sint-integer-fix
                                                     c::sint-integerp-alt-def
                                                     c::assign)))))
  (if (mbt (and (<= 0 (c::sint->get |i|))
                (<= (c::sint->get |i|) 8)))
      (if (c::boolean-from-sint (c::ne-sint-sint |i| (c::sint-dec-const 8)))
          (let* ((|sum| (c::assign
                         (c::add-uint-uint
                          |sum|
                          (c::uint-array-read-sint |arr2| |i|))))
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
                              (c::sint-array-sint-index-okp |arr| |x|))
                  :guard-hints (("Goal" :in-theory (enable object-|arr|-p)))))
  (let ((|arr| (c::sint-array-write-sint |arr| |x| (c::sint-dec-const 1))))
    |arr|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |i$loop| (|arr2| |idx|)
  (declare (xargs :guard (and (object-|arr2|-p |arr2|)
                              (c::sintp |idx|)
                              (<= 0 (c::sint->get |idx|))
                              (<= (c::sint->get |idx|) 8))
                  :guard-hints (("Goal"
                                 :in-theory (enable c::add-sint-sint-okp
                                                    c::add-sint-sint
                                                    c::sint-integerp-alt-def
                                                    c::ne-sint-sint
                                                    c::uint-array-sint-index-okp
                                                    c::uint-array-index-okp
                                                    object-|arr2|-p
                                                    c::assign)))
                  :measure (nfix (- 8 (c::sint->get |idx|)))
                  :hints (("Goal" :in-theory (enable c::ne-sint-sint
                                                     c::add-sint-sint
                                                     c::sint-from-boolean
                                                     c::sint-integer-fix
                                                     c::sint-integerp-alt-def
                                                     c::assign)))))
  (if (mbt (and (<= 0 (c::sint->get |idx|))
                (<= (c::sint->get |idx|) 8)))
      (if (c::boolean-from-sint (c::ne-sint-sint |idx| (c::sint-dec-const 8)))
          (let* ((|arr2| (c::uint-array-write-sint
                          |arr2|
                          |idx|
                          (c::add-uint-uint
                           (c::uint-array-read-sint |arr2| |idx|)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |arr| |f| |arr2| |g$loop| |g| :output-file "ext-objs.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This will be merged with the one above when proof generation is extended.
(c::atc |arr| |arr2| |f| |h| |i$loop| |i| |perm|
        :output-file "ext-objs-2.c"
        :proofs nil)
