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
  (if (c::boolean-from-sint |x|)
      |y|
    |z|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |g| (|e|)
  (declare (xargs :guard (c::sintp |e|)))
  (if (c::boolean-from-sint (c::ge-sint-sint |e| (c::sint-const 0)))
      (if (c::boolean-from-sint (c::lt-sint-sint |e| (c::sint-const 1000)))
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
                                 :in-theory (enable c::sub-sint-sint-okp
                                                    c::sint-integerp-alt-def)))))
  (c::sub-sint-sint |x|
                    (if (c::boolean-from-sint
                         (c::ge-sint-sint |y| (c::sint-const 18)))
                        (c::sint-const 0)
                      (c::sint-const 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |i| (|a| |b|)
  (declare (xargs :guard (and (c::sintp |a|)
                              (c::sintp |b|))
                  :guard-hints (("Goal"
                                 :in-theory (enable c::boolean-from-sint
                                                    c::sint-integerp-alt-def
                                                    c::gt-sint-sint
                                                    c::sub-sint-sint-okp)))))
  (if (c::boolean-from-sint (c::gt-sint-sint |a| |b|))
      (c::sub-sint-sint |a|
                        (if (c::boolean-from-sint
                             (c::eq-sint-sint |b| (c::sint-const 3)))
                            (c::sint-const 0)
                          (c::sint-const 1)))
    |b|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |j| (|x|)
  (declare (xargs :guard (and (c::sintp |x|)
                              (>= (c::sint->get |x|) 0))
                  :guard-hints (("Goal"
                                 :in-theory (enable c::sint-integerp-alt-def
                                                    c::lt-sint-sint
                                                    c::sub-sint-sint-okp
                                                    c::mul-sint-sint-okp)))))
  (if (c::boolean-from-sint (c::lt-sint-sint |x| (c::sint-const 1000)))
      (c::mul-sint-sint |x| (c::sint-const 10))
    (c::sub-sint-sint |x| (c::sint-const 10000))))

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
