; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
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

(defun |cond1| (|x| |y| |z|)
  (declare (xargs :guard (and (c::sintp |x|)
                              (c::sintp |y|)
                              (c::sintp |z|))))
  (if (c::sint-nonzerop |x|)
      |y|
    |z|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |cond2| (|x|)
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

(c::atc |cond1|
        |cond2|
        :output-file "conditionals.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

On macOS or Linux, you can compile and run this code as follows:

  gcc -o conditionals conditionals.c conditionals-test.c
  ./conditionals

|#
