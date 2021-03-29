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
  (let ((|z| (c::sint-lt |x| |y|)))
    (c::sint-lognot |z|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |g| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))))
  (let* ((|x_lt_y| (c::sint-lt |x| |y|))
         (|x_eq_y| (c::sint-eq |x| |y|))
         (|x_le_y| (c::sint-logor |x_lt_y| |x_eq_y|)))
    (c::sint-lognot |x_le_y|)))

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
                                                      c::sint
                                                      c::sint->get
                                                      c::sintp
                                                      c::sint-add-okp
                                                      c::sint-sub-okp
                                                      c::sint-mul-okp
                                                      c::sint-add
                                                      c::sint-sub
                                                      c::sint-mul
                                                      c::sint-ge)))))
    (if (c::sint-nonzerop (c::sint-ge |x| (c::sint-const 0)))
        (let ((|z| (c::sint-add |x| |y|)))
          (c::sint-mul (c::sint-const 2) |z|))
      (c::sint-sub |y| |x|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |f| |g| |h| :output-file "locvars.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

On macOS or Linux, you can compile and run this code as follows:

  gcc -o locvars locvars.c locvars-test.c
  ./locvars

|#
