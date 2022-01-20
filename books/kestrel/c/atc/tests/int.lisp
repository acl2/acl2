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

; An example with integer operations.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (set-default-hints '((nonlinearp-default-hint
                         stable-under-simplificationp
                         hist
                         pspv))))

  (defun |f| (|x| |y| |z|)
    (declare (xargs :guard (and (c::sintp |x|)
                                (c::sintp |y|)
                                (c::sintp |z|)
                                ;; -10 <= x <= 10:
                                (<= -10 (c::sint->get |x|))
                                (<= (c::sint->get |x|) 10)
                                ;; -10 <= y <= 10:
                                (<= -10 (c::sint->get |y|))
                                (<= (c::sint->get |y|) 10)
                                ;; -10 <= z <= 10:
                                (<= -10 (c::sint->get |z|))
                                (<= (c::sint->get |z|) 10))
                    :guard-hints (("Goal"
                                   :in-theory
                                   (e/d (c::sint-integerp-alt-def
                                         c::add-sint-sint-okp
                                         c::sub-sint-sint-okp
                                         c::mul-sint-sint-okp
                                         c::add-sint-sint
                                         c::sub-sint-sint)
                                        (c::sint->get-upper-bound))))))
    (c::mul-sint-sint (c::add-sint-sint |x| |y|)
                      (c::sub-sint-sint |z| (c::sint-dec-const 3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |f| :output-file "int.c")
