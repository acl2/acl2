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

; Partial instantiation of an empty frame of a two-parameter product type:
; the value is an empty vector over the peeled product type value.
(test-eval-top-expr
 "(i-app (frame [0] (Pi ($d $e) (-> ((A Int (dims $d $e))) Int))) 3)")

; Completion of that instantiation, as a chain.
(test-eval-top-expr
 "(i-app (i-app (frame [0] (Pi ($d $e) (-> ((A Int (dims $d $e))) Int))) 3) 4)")

; Full instantiation of a two-parameter type lambda abstraction,
; as a chain of unary applications through unary closures.
(test-eval-top-expr
 "
((i-app (t-app (t-fn (&t &u) (i-fn ($d) (fn ((x (A &t $d))) x))) Int Int) 3)
 [1 2 3])
")

; Full instantiation of an empty frame of a two-parameter universal type:
; the first unary application peels the universal type value,
; the second one completes the instantiation.
(test-eval-top-expr
 "(t-app (frame [0] (Forall (&t &u) (Pi ($d) (-> ((A &t $d)) Int)))) Int Int)")

; Partial application of a type lambda abstraction:
; the value is a closure over the remaining parameter.
(test-eval-top-expr
 "(t-app (t-fn (&t &u) (i-fn ($d) (fn ((x (A &t $d))) x))) Int)")

; Partial instantiation of an empty frame of a two-parameter universal type:
; the value is an empty vector over
; the universal type value binding the remaining parameter.
(test-eval-top-expr
 "(t-app (frame [0] (Forall (&t &u) (Pi ($d) (-> ((A &t $d)) Int)))) Int)")

; Completion of that instantiation, as a chain.
(test-eval-top-expr
 "
(t-app (t-app (frame [0] (Forall (&t &u) (Pi ($d) (-> ((A &t $d)) Int)))) Int)
       Int)
")

; Application of a two-parameter term lambda abstraction,
; as a chain of unary applications through a unary closure:
; the first argument creates a closure binding the first parameter,
; whose body is the inner one-parameter lambda abstraction,
; and the second argument completes the application.
(test-eval-top-expr
 "((fn ((x Int) (y Int)) (+ x y)) 3 4)")

; The same, with rank-polymorphic lifting over a non-scalar frame:
; the first (lifted) application step produces
; an array of unary closures (one per frame position),
; to which the second argument array is applied element-wise.
(test-eval-top-expr
 "((fn ((x Int) (y Int)) (+ x y)) [1 2 3] [4 5 6])")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A let-bound type function with one parameter and a result type annotation:
; the annotation is wrapped into a unary universal type for evaluation.
(test-eval-top-expr
 "(let ((t-fun (f (&t) : Int) 7)) (t-app f Int))")

; A type function binding with no parameters
; is treated as a plain value binding, as in [impl].
(test-eval-top-expr
 "(let ((t-fun (f () : Int) 7)) (+ f 1))")

; Similarly for an ispace function binding with no parameters.
(test-eval-top-expr
 "(let ((i-fun (f () : Int) 7)) (+ f 1))")

; Similarly for a function binding with no value parameters.
(test-eval-top-expr
 "(let ((fun (f : Int) 7)) (+ f 1))")

; Similarly for a combined function binding with no parameters at all,
; whether the type and ispace parameter lists are empty or absent.
(test-eval-top-expr
 "(let ((fun (@f () () : Int) 7)) (+ f 1))")
(test-eval-top-expr
 "(let ((fun (@f _ _ : Int) 7)) (+ f 1))")

; In a combined function binding, only the layers with parameters
; are present: here the type and function layers but no ispace layer.
(test-eval-top-expr
 "(let ((fun (@f (&t) () (x Int) : Int) x))
  (@f (Int) () 7))")

; A let-bound ispace function with one parameter and a result type annotation:
; the annotation is wrapped into a unary product type for evaluation.
(test-eval-top-expr
 "(let ((i-fun (f ($d) : Int) 7)) (i-app f 3))")

; A let-bound combined function
; with one type parameter, one ispace parameter, and one value parameter:
; it desugars to a nest of unary abstractions, with a nested unary type.
(test-eval-top-expr
 "(let ((fun (@f (&t) ($d) (x (A &t $d)) : (A &t $d)) x))
  (@f (Int) (3) [1 2 3]))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests for the reduce primitive,
; whose final stage executes Remora code
; and is thus part of the evaluation mutual recursion.

(defmacro iv (n) `(expr-value-base (base-value-int (int-value ,n))))

(defconst *tv-int* (type-value-base (base-type-int)))

(defconst *vec3*
  (expr-value-vector (list (iv 1) (iv 2) (iv 3))))

(defconst *add-fun*
  (expr-value-primop (primop-value-int-binary (int-binary-primop-add))))

(defconst *sub-fun*
  (expr-value-primop (primop-value-int-binary (int-binary-primop-sub))))

; Sum fold over a vector of scalar cells: (+ (+ 1 2) 3) = 6.
(assert-event
 (equal (prim-reduce *tv-int* 2 nil *add-fun* *vec3* 1000)
        (iv 6)))

; The fold is a left fold, seeded with the first cell:
; (- (- 1 2) 3) = -4, whereas a right fold would give (- 1 (- 2 3)) = 2.
(assert-event
 (equal (prim-reduce *tv-int* 2 nil *sub-fun* *vec3* 1000)
        (iv -4)))

; A single cell (d = 0) is returned directly,
; without ever applying the function value.
(assert-event
 (equal (prim-reduce *tv-int* 0 nil *sub-fun*
                     (expr-value-vector (list (iv 7)))
                     1000)
        (iv 7)))

; Argument cell dimensions not matching the instantiation.
(assert-event
 (reserrp (prim-reduce *tv-int* 1 nil *add-fun* *vec3* 1000)))

; Via the higher-order eval-primop-fun.
(assert-event
 (equal (eval-primop-fun (make-primop-value-reduce-t-d-s-f :tval *tv-int*
                                                           :dval 2
                                                           :sval nil
                                                           :fval *add-fun*)
                         *vec3*
                         1000)
        (iv 6)))

; End-to-end: parse, type-check, and evaluate a reduce expression.
(test-eval-top-expr
 "(@reduce (Int) (2 []) + [1 2 3])")
