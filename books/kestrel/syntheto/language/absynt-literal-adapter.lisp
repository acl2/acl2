; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "abstract-syntax")

(define make-expression-literal-boolean (key (val booleanp))
  :returns (retval expressionp)
  (declare (ignore key))
  (make-expression-literal :get (make-literal-boolean :value val)))

(define make-expression-literal-character (key (char characterp))
  :returns (retval expressionp)
  (declare (ignore key))
  (make-expression-literal :get (make-literal-character :value char)))

(define make-expression-literal-string (key (str stringp))
  :returns (retval expressionp)
  (declare (ignore key))
  (make-expression-literal :get (make-literal-string :value str)))

(define make-expression-literal-integer (key (n natp))
  :returns (retval expressionp)
  (declare (ignore key))
  (make-expression-literal :get (make-literal-integer :value n)))
