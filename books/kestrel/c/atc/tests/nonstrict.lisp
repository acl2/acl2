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

; Some examples to test code generation for non-strict logical operators.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |and| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))))
  (c::sint01 (and (c::sint-nonzerop |x|)
                  (c::sint-nonzerop |y|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |or| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))))
  (c::sint01 (or (c::sint-nonzerop |x|)
                 (c::sint-nonzerop |y|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |ifand| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))))
  (if (and (c::sint-nonzerop (c::lt-sint-sint |x| |y|))
           (c::sint-nonzerop (c::lt-sint-sint |y| (c::sint-const 100))))
      |x|
    |y|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |ifor| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))))
  (if (or (c::sint-nonzerop (c::lt-sint-sint |x| |y|))
          (c::sint-nonzerop (c::ge-sint-sint |y| (c::sint-const 100))))
      |x|
    |y|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |condand| (|x|)
  (declare (xargs :guard (c::sintp |x|)))
  (c::eq-sint-sint |x|
              (if (and (c::sint-nonzerop
                        (c::le-sint-sint (c::sint-const 0) |x|))
                       (c::sint-nonzerop
                        (c::le-sint-sint |x| (c::sint-const 10))))
                  (c::sint-const 10)
                (c::sint-const 20))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |condor| (|x|)
  (declare (xargs :guard (c::sintp |x|)))
  (c::eq-sint-sint |x|
              (if (or (c::sint-nonzerop
                       (c::lt-sint-sint |x| (c::sint-const 0)))
                      (c::sint-nonzerop
                       (c::gt-sint-sint |x| (c::sint-const 10))))
                  (c::sint-const 10)
                (c::sint-const 20))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |notandor| (|x|)
  (declare (xargs :guard (c::sintp |x|)))
  (c::sint01
   (and (or (and (c::sint-nonzerop (c::le-sint-sint (c::sint-const 10)
                                               |x|))
                 (c::sint-nonzerop (c::le-sint-sint |x|
                                               (c::sint-const 20))))
            (and (c::sint-nonzerop (c::le-sint-sint (c::sint-const 100)
                                               |x|))
                 (c::sint-nonzerop (c::le-sint-sint |x|
                                               (c::sint-const 200)))))
        (not (and (c::sint-nonzerop (c::le-sint-sint (c::sint-const 4)
                                                |x|))
                  (c::sint-nonzerop (c::le-sint-sint |x|
                                                (c::sint-const 6))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |and|
        |or|
        |ifand|
        |ifor|
        |condand|
        |condor|
        |notandor|
        :output-file "nonstrict.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

On macOS or Linux, you can compile and run this code as follows:

  gcc -o nonstrict nonstrict.c nonstrict-test.c
  ./nonstrict

|#
