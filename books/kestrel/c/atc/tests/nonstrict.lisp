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
  (c::sint-from-boolean (and (c::boolean-from-sint |x|)
                             (c::boolean-from-sint |y|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |or| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))))
  (c::sint-from-boolean (or (c::boolean-from-sint |x|)
                            (c::boolean-from-sint |y|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |ifand| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))))
  (if (and (c::boolean-from-sint (c::lt-sint-sint |x| |y|))
           (c::boolean-from-sint (c::lt-sint-sint |y| (c::sint-dec-const 100))))
      |x|
    |y|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |ifor| (|x| |y|)
  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))))
  (if (or (c::boolean-from-sint (c::lt-sint-sint |x| |y|))
          (c::boolean-from-sint (c::ge-sint-sint |y| (c::sint-dec-const 100))))
      |x|
    |y|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |condand| (|x|)
  (declare (xargs :guard (c::sintp |x|)))
  (c::eq-sint-sint |x|
                   (c::condexpr
                    (if (and (c::boolean-from-sint
                              (c::le-sint-sint (c::sint-dec-const 0) |x|))
                             (c::boolean-from-sint
                              (c::le-sint-sint |x| (c::sint-dec-const 10))))
                        (c::sint-dec-const 10)
                      (c::sint-dec-const 20)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |condor| (|x|)
  (declare (xargs :guard (c::sintp |x|)))
  (c::eq-sint-sint |x|
                   (c::condexpr
                    (if (or (c::boolean-from-sint
                             (c::lt-sint-sint |x| (c::sint-dec-const 0)))
                            (c::boolean-from-sint
                             (c::gt-sint-sint |x| (c::sint-dec-const 10))))
                        (c::sint-dec-const 10)
                      (c::sint-dec-const 20)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |notandor| (|x|)
  (declare (xargs :guard (c::sintp |x|)))
  (c::sint-from-boolean
   (and (or (and (c::boolean-from-sint
                  (c::le-sint-sint (c::sint-dec-const 10)
                                   |x|))
                 (c::boolean-from-sint
                  (c::le-sint-sint |x|
                                   (c::sint-dec-const 20))))
            (and (c::boolean-from-sint
                  (c::le-sint-sint (c::sint-dec-const 100)
                                   |x|))
                 (c::boolean-from-sint
                  (c::le-sint-sint |x|
                                   (c::sint-dec-const 200)))))
        (not (and (c::boolean-from-sint
                   (c::le-sint-sint (c::sint-dec-const 4)
                                    |x|))
                  (c::boolean-from-sint
                   (c::le-sint-sint |x|
                                    (c::sint-dec-const 6))))))))

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
