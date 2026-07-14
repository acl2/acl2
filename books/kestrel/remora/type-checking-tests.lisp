; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "parser-interface")
(include-book "type-checking")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test that a standalone Remora expression
; parses and type-checks without error.
; The argument is a string of Remora source for a standalone expression.
; The macro expands to an assert-event that runs
; parse-top-exp-from-string followed by check-top-expr,
; and passes when the result is not an error.
; The type of the expression is printed to the comment window
; for manual inspection; the expected type is not checked.

(defmacro test-check-top-expr (code)
  `(assert-event
    (b* ((code ,code)
         (ast (parse-top-exp-from-string code))
         (tast (check-top-expr ast))
         ((when (reserrp tast))
          (prog2$ (cw "~x0~%" tast) nil)))
      (not (cw "~x0~%" (type+expr->type tast))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test that a standalone Remora expression
; parses but does not type-check.
; The argument is a string of Remora source for a standalone expression.
; The macro expands to an assert-event that runs
; parse-top-exp-from-string followed by check-top-expr,
; and passes when parsing succeeds and type checking returns an error.
; The error is printed to the comment window for manual inspection.

(defmacro test-check-top-expr-fail (code)
  `(assert-event
    (b* ((code ,code)
         (ast (parse-top-exp-from-string code))
         ((when (reserrp ast))
          (prog2$ (cw "~x0~%" ast) nil))
         (tast (check-top-expr ast)))
      (and (not (cw "~x0~%" tast))
           (reserrp tast)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Full instantiation of a polymorphic primitive operation,
; as an n-ary ispace application.
(test-check-top-expr
 "(i-app (t-app length Int) 3 (dims 4 5))")

; Partial instantiation, providing just the dimension:
; the type is a product type over the remaining shape variable.
(test-check-top-expr
 "(i-app (t-app length Int) 3)")

; Completion of a partial instantiation, as a chain.
(test-check-top-expr
 "(i-app (i-app (t-app length Int) 3) (dims 4 5))")

; A shape argument where a dimension is expected.
(test-check-top-expr-fail
 "(i-app (t-app length Int) (dims 4 5))")

; More ispace arguments than bound variables.
(test-check-top-expr-fail
 "(i-app (t-app length Int) 3 (dims 4 5) 7)")
