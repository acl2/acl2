; Syntheto Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "../translation")

(defconst *specification-sort-spec*
  (let ((input (identifier "input"))
        (output (identifier "output")))
    (toplevel-specification
     (make-function-specification
      :name (identifier "myspec")
      :functions
      (list (make-function-header
             :name (identifier "fun")
             :inputs (list (make-typed-variable :name input
                                                :type (type-integer)))
             :outputs (list (make-typed-variable :name output
                                                 :type (type-integer)))))
      :specifier
      (make-function-specifier-input-output
       :relation
       (make-expression-binary
        :operator (binary-op-gt)
        :left-operand (make-expression-variable :name output)
        :right-operand (make-expression-variable :name input)))))))

(translate-to-acl2 *specification-sort-spec*)
