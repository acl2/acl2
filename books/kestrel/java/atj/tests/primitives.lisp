; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../implementation" :ttags (:open-input-channel (:oslib) (:quicklisp) :quicklisp.osicat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the generation of Java code
; that manipulates Java primitive values.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A function over (ACL2 representations of) Java int values.

(defun f-int (x y)
  (declare (xargs :guard (and (java::int-value-p x)
                              (java::int-value-p y))))
  (java::jint-add (java::jint-mul (java::int-value 2) x)
                  (java::jint-mul y y)))

(java::def-atj-function-type f-int (:jint :jint) :jint)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(java::atj f-int
           :deep nil
           :guards t
           :java-class "PrimitiveInt")
