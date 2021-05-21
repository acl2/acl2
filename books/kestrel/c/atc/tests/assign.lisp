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

(include-book "std/testing/must-succeed-star" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |i| (|p| |q|)
  (declare (xargs :guard (and (c::sintp |p|)
                              (c::sintp |q|))))
  (let ((|x| (c::bitand-sint-sint |p| |q|)))
    (if (c::boolean-from-sint (c::lt-sint-sint |x| (c::sint-const 33)))
        (let ((|x| (c::bitnot-sint |x|)))
          (c::bitior-sint-sint |q| |x|))
      (let* ((|x| (c::lognot-sint |x|))
             (|x| (c::bitand-sint-sint |p| |x|)))
        (c::bitxor-sint-sint |x| |q|)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |j| (|x|)
  (declare (xargs :guard (c::sintp |x|)))
  (let ((|y| (c::sint-const 0)))
    (let ((|y| (if (c::boolean-from-sint
                    (c::lt-sint-sint |x| (c::sint-const 100)))
                   (let ((|y| (c::bitior-sint-sint |y| (c::sint-const 6666))))
                     |y|)
                 (let ((|y| (c::bitxor-sint-sint |y| (c::sint-const 7777))))
                   |y|))))
      (c::bitand-sint-sint |x| |y|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |k| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|)
                              (c::sintp |y|))))
  (let* ((|a| (c::lognot-sint |x|))
         (|b| (c::bitnot-sint |x|)))
    (mv-let (|a| |b|)
      (if (c::boolean-from-sint |y|)
          (let ((|a| (c::bitnot-sint |a|)))
            (mv |a| |b|))
        (let* ((|b| (c::sint-const 2))
               (|a| (c::sint-const 14)))
          (mv |a| |b|)))
      (c::bitxor-sint-sint |a| |b|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |f| |g| |h| |i| |j| |k| :output-file "assign.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

On macOS or Linux, you can compile and run this code as follows:

  gcc -o assign assign.c assign-test.c
  ./assign

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Examples of invalid ACL2 representations of C code that must be rejected.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The transforming term for |x| does not end with |x|.

(must-succeed*
 (defun |foo| (|x| |y|)
   (declare (xargs :guard (and (c::uintp |x|) (c::uintp |y|))))
   (let ((|x| (let ((|w| (c::add-uint-uint |x| |y|)))
                |w|)))
     (c::add-uint-uint |x| (c::uint-const 7))))
 (must-fail
  (c::atc |foo| :output-file "foo.c")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The transforming term bound to |x| is not an IF.

(must-succeed*
 (defun |foo| (|x| |y|)
   (declare (xargs :guard (and (c::uintp |x|) (c::uintp |y|))))
   (let ((|x| (let* ((|y| (c::uint-const 0))
                     (|x| (c::add-uint-uint |x| |y|)))
                |x|)))
     (c::add-uint-uint |x| |y|)))
 (must-fail
  (c::atc |foo| :output-file "foo.c" :proofs nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The inner binding of |y| is invalid because |y| is in scope,
; but not in the same scope as where the inner binding occurs,
; and |y| is not being transformed (only |x| is).

(must-succeed*
 (defun |foo| (|x|)
   (declare (xargs :guard (c::sintp |x|)))
   (let ((|y| (c::bitnot-sint |x|)))
     (let ((|x| (if (c::boolean-from-sint |y|)
                    (let* ((|y| (c::sint-const 0))
                           (|x| |y|))
                      |x|)
                  |x|)))
       (c::bitand-sint-sint |x| |y|))))
 (must-fail
  (c::atc |foo| :output-file "foo.c" :proofs nil)))
