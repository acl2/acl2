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

; Some examples to test code generation for conditionals.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |f| (|x| |y| |z|)
  (declare (xargs :guard (and (c::sintp |x|)
                              (c::sintp |y|)
                              (c::sintp |z|))))
  (if (c::sint-nonzerop |x|)
      |y|
    |z|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |g| (|e|)
  (declare (xargs :guard (c::sintp |e|)))
  (if (c::sint-nonzerop (c::sint-ge |e| (c::sint-const 0)))
      (if (c::sint-nonzerop (c::sint-lt |e| (c::sint-const 1000)))
          (c::sint-const 1)
        (c::sint-const 2))
    (c::sint-const 3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |h| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|)
                              (c::sintp |y|)
                              ;; x > 0:
                              (> (c::sint->get |x|) 0))
                  :guard-hints (("Goal"
                                 :in-theory (enable c::sint-sub-okp
                                                    sbyte32p
                                                    sbyte32-fix
                                                    c::sint->get)))))
  (c::sint-sub |x|
               (if (c::sint-nonzerop (c::sint-ge |y| (c::sint-const 18)))
                   (c::sint-const 0)
                 (c::sint-const 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |i| (|a| |b|)
  (declare (xargs :guard (and (c::sintp |a|)
                              (c::sintp |b|))
                  :guard-hints (("Goal" :in-theory (enable
                                                    c::sint-nonzerop
                                                    c::sint-gt
                                                    c::sint-sub-okp
                                                    c::sint->get
                                                    sbyte32p
                                                    sbyte32-fix)))))
  (if (c::sint-nonzerop (c::sint-gt |a| |b|))
      (c::sint-sub |a|
                   (if (c::sint-nonzerop (c::sint-eq |b| (c::sint-const 3)))
                       (c::sint-const 0)
                     (c::sint-const 1)))
    |b|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |j| (|x|)
  (declare (xargs :guard (and (c::sintp |x|)
                              (>= (c::sint->get |x|) 0))
                  :guard-hints (("Goal" :in-theory (enable
                                                    c::sint-nonzerop
                                                    c::sint-lt
                                                    c::sint-sub-okp
                                                    c::sint-mul-okp
                                                    c::sint->get
                                                    sbyte32p
                                                    sbyte32-fix)))))
  (if (c::sint-nonzerop (c::sint-lt |x| (c::sint-const 1000)))
      (c::sint-mul |x| (c::sint-const 10))
    (c::sint-sub |x| (c::sint-const 1000000))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |f|
        |g|
        |h|
        |i|
        |j|
        :output-file "conditionals.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

On macOS or Linux, you can compile and run this code as follows:

  gcc -o conditionals conditionals.c conditionals-test.c
  ./conditionals

|#
