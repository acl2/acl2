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

(defun |g| (|x| |arr|)
  (declare (xargs :guard (and (c::sintp |x|)
                              (object-|arr|-p |arr|)
                              (c::sint-array-sint-index-okp |arr| |x|))
                  :guard-hints (("Goal" :in-theory (enable object-|arr|-p)))))
  (let ((|arr| (c::sint-array-write-sint |arr| |x| (c::sint-dec-const 1))))
    |arr|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |arr| |f| |g| |perm| :output-file "ext-objs.c" :proofs nil)
