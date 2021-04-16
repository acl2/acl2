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

; Some examples to test code generation for local variables.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |f| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))))
  (let ((|z| (c::lt-sint-sint |x| |y|)))
    (c::lognot-sint |z|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |g| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))))
  (let* ((|x_lt_y| (c::lt-sint-sint |x| |y|))
         (|x_eq_y| (c::eq-sint-sint |x| |y|))
         (|x_le_y| (c::logor-sint-sint |x_lt_y| |x_eq_y|)))
    (c::lognot-sint |x_le_y|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defun |h| (|x| |y|)
    (declare (xargs :guard (and (c::sintp |x|)
                                (c::sintp |y|)
                                ;; -10 <= x <= 10:
                                (<= -10 (c::sint->get |x|))
                                (<= (c::sint->get |x|) 10)
                                ;; -10 <= y <= 10:
                                (<= -10 (c::sint->get |y|))
                                (<= (c::sint->get |y|) 10))
                    :guard-hints (("Goal"
                                   :do-not-induct t
                                   :in-theory (enable c::sint-integerp-alt-def
                                                      c::add-sint-sint-okp
                                                      c::sub-sint-sint-okp
                                                      c::mul-sint-sint-okp
                                                      c::add-sint-sint
                                                      c::sub-sint-sint
                                                      c::mul-sint-sint
                                                      c::ge-sint-sint)))))
    (if (c::sint-nonzerop (c::ge-sint-sint |x| (c::sint-const 0)))
        (let ((|z| (c::add-sint-sint |x| |y|)))
          (c::mul-sint-sint (c::sint-const 2) |z|))
      (c::sub-sint-sint |y| |x|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |f| |g| |h| :output-file "locvars.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

On macOS or Linux, you can compile and run this code as follows:

  gcc -o locvars locvars.c locvars-test.c
  ./locvars

|#
