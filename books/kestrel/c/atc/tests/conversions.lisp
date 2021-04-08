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

; This file tests integer conversions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |f| (|x| |y|)
  (declare (xargs :guard (and (c::ucharp |x|)
                              (c::ucharp |y|))
                  :guard-hints (("Goal"
                                 :in-theory (enable c::sint-from-uchar-okp
                                                    c::sint-integerp-alt-def
                                                    c::uchar-integerp-alt-def
                                                    c::ucharp
                                                    c::uchar->get
                                                    c::sint-max
                                                    c::uchar-max
                                                    c::char-bits
                                                    c::int-bits)))))
  (c::sint-bitxor (c::sint-from-uchar |x|)
                  (c::sint-from-uchar |y|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |g| (|i|)
  (declare (xargs :guard (c::sintp |i|)))
  (c::uchar-from-sint (c::sint-bitnot |i|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |f| |g| :output-file "conversions.c")
