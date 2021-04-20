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

; Some examples to test code generation for assignments to local variables.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |f| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|)
                              (c::sintp |y|))))
  (let* ((|a| (c::bitand-sint-sint |x| |y|))
         (|a| (c::bitnot-sint |a|)))
    (c::gt-sint-sint |a| (c::sint-const 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |g| (|a| |b|)
  (declare (xargs :guard (and (c::sintp |a|)
                              (c::sintp |b|)
                              ;; 0 <= a <= 100:
                              (<= 0 (c::sint->get |a|))
                              (<= (c::sint->get |a|) 100))
                  :guard-hints (("Goal"
                                 :in-theory
                                 (enable c::add-sint-sint-okp
                                         c::sint-integerp-alt-def)))))
  (let ((|a| (c::add-sint-sint |a| (c::sint-const 200))))
    (c::lt-sint-sint |b| |a|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |h| (|x| |y| |z|)
  (declare (xargs :guard (and (c::sintp |x|)
                              (c::sintp |y|)
                              (c::sintp |z|))))
  (let* ((|a| (c::bitand-sint-sint |x| |y|))
         (|a| (c::bitior-sint-sint |a| |z|))
         (|b| (c::bitxor-sint-sint |x| |z|))
         (|a| (c::bitand-sint-sint |a| |b|)))
    (c::lt-sint-sint |a| |b|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |f| |g| |h| :output-file "assign.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

On macOS or Linux, you can compile and run this code as follows:

  gcc -o assign assign.c assign-test.c
  ./assign

|#
