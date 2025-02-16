; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib) (:open-output-channel!)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some examples to test code generation for local variable declarations.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |f| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))
                  :guard-hints (("Goal" :in-theory (enable c::declar)))))
  (let ((|z| (c::declar (c::lt-sint-sint |x| |y|))))
    (c::lognot-sint |z|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |g| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))
                  :guard-hints (("Goal" :in-theory (enable c::declar)))))
  (let* ((|x_lt_y| (c::declar (c::lt-sint-sint |x| |y|)))
         (|x_eq_y| (c::declar (c::eq-sint-sint |x| |y|)))
         (|x_le_y| (c::declar (c::bitior-sint-sint |x_lt_y| |x_eq_y|))))
    (c::lognot-sint |x_le_y|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defun |h| (|x| |y|)
    (declare (xargs :guard (and (c::sintp |x|)
                                (c::sintp |y|)
                                ;; -10 <= x <= 10:
                                (<= -10 (c::integer-from-sint |x|))
                                (<= (c::integer-from-sint |x|) 10)
                                ;; -10 <= y <= 10:
                                (<= -10 (c::integer-from-sint |y|))
                                (<= (c::integer-from-sint |y|) 10))
                    :guard-hints (("Goal"
                                   :do-not-induct t
                                   :in-theory (enable c::declar
                                                      c::sint-integerp-alt-def
                                                      c::add-sint-sint-okp
                                                      c::sub-sint-sint-okp
                                                      c::mul-sint-sint-okp
                                                      c::add-sint-sint
                                                      c::sub-sint-sint
                                                      c::mul-sint-sint
                                                      c::ge-sint-sint)))))
    (if (c::boolean-from-sint (c::ge-sint-sint |x| (c::sint-dec-const 0)))
        (let ((|z| (c::declar (c::add-sint-sint |x| |y|))))
          (c::mul-sint-sint (c::sint-dec-const 2) |z|))
      (c::sub-sint-sint |y| |x|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |f| |g| |h| :file-name "locvars" :header t)
