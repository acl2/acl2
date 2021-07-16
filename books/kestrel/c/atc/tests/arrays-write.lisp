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
    (mv (c::uchar-array-read-sint |a| |i|) |a|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |f| :output-file "arrays-write.c" :experimental (:array-writes))
