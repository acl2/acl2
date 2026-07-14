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
(include-book "evaluation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test that a standalone Remora expression
; parses, type-checks, and evaluates without error.
; The argument is a string of Remora source for a standalone expression.
; The macro expands to an assert-event that runs the full pipeline
; (parse-top-exp-from-string,
; check-top-expr,
; and eval-top-expr with an evaluation limit of one million)
; and passes when the resulting value is not an error.
; The value is printed to the comment window for manual inspection;
; the expected value is not checked.

(defmacro test-eval-top-expr (code)
  `(assert-event
    (b* ((code ,code)
         (ast (parse-top-exp-from-string code))
         (tast (check-top-expr ast))
         (expr (type+expr->expr tast))
         (val (eval-top-expr expr 1000000)))
      (and (not (cw "~x0~%" val))
           (not (reserrp val))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-eval-top-expr "3")

(test-eval-top-expr
 "(let ((val x 4)) x)")

(test-eval-top-expr
 "(let ((val x 10) (val y 20)) (+ x y))")

(test-eval-top-expr
 "
(i-app (t-app (frame [0] (Forall (&t) (Pi ($d) (-> ((A &t $d)) Int)))) Int) 3)
")

(test-eval-top-expr
 "
(t-app (i-app (frame [0] (Pi ($d) (Forall (&t) (-> ((A &t $d)) Int)))) 3) Int)
")

(test-eval-top-expr
 "
((i-app (t-app (t-fn (&t) (i-fn ($d) (fn ((x (A &t $d))) x))) Int) 3) [1 2 3])
")

; Partial instantiation of a polymorphic primitive operation:
; the value is an intermediate instantiation stage.
(test-eval-top-expr
 "(i-app (t-app length Int) 3)")

; Completion of a partial instantiation, as a chain of unary applications.
(test-eval-top-expr
 "(i-app (i-app (t-app length Int) 3) (dims 4 5))")

; Partial application of an ispace lambda abstraction:
; the value is a closure over the remaining parameter.
(test-eval-top-expr
 "(i-app (i-fn ($d $e) (fn ((x (A Int (dims $d $e)))) x)) 3)")
