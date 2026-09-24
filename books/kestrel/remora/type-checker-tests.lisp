; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Contributions by; Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "parser-interface")
(include-book "type-checker")

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
         (tast (check-top-expr ast)))
      (and (not (reserrp tast))
           (not (cw "~x0~%" (type+expr->type tast)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test that a standalone Remora expression
; parses but does not type-check.
; The argument is a string of Remora source for a standalone expression.
; The macro expands to an assert-event that runs
; parse-top-exp-from-string followed by check-top-expr,
; and passes when type checking returns an error.
; The error is printed to the comment window for manual inspection.

(defmacro test-check-top-expr-fail (code)
  `(assert-event
    (b* ((code ,code)
         (ast (parse-top-exp-from-string code))
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

; The variable $d escapes.
(test-check-top-expr-fail
 "(unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) v)")

; Application of a unary ispace lambda abstraction:
; its computed type is a unary product type, matched by the application.
(test-check-top-expr
 "(i-app (i-fn ($d) (fn ((x (A Int $d))) x)) 3)")

; The inner variable $d escapes, and the outer variable $d does not interfere.
(test-check-top-expr-fail
 "(let ((i-fun (f ($d))
        (unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) v)))
  (@length (Int) (5 []) (i-app f 5)))")

; As above but without the consumer:
; the escaped witness $d would be captured by the i-fun's $d,
; making the expression appear to have type [Int 5]
; while evaluating to a vector of length 3.
(test-check-top-expr-fail
 "(let ((i-fun (f ($d))
        (unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) v)))
  (i-app f 5))")

; As above with the length instantiation matching the run-time value:
; also rejected, since the escape is the problem,
; not which length is demanded.
(test-check-top-expr-fail
 "(let ((i-fun (f ($d))
        (unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) v)))
  (@length (Int) (3 []) (i-app f 5)))")

; The witness $w escapes; the unrelated outer variable $z does not mask it.
(test-check-top-expr-fail
 "(let ((i-fun (f ($z))
        (unbox ($w v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) v)))
  (i-app f 5))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Nothing escapes when the body's type does not mention the witness,
; even when the witness shadows an outer ispace variable.
(test-check-top-expr
 "(let ((i-fun (f ($d))
        (unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) 0)))
  (i-app f 5))")

; The idiomatic use of a witness:
; consume the payload inside the unbox,
; instantiating with the witness itself; the body's type is closed.
(test-check-top-expr
 "(unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e))))
   (@length (Int) ($d []) v))")

; The witness name appears in the body's type only under a binder
; (the Pi introduced by the i-fn), so it does not escape:
; the escape check must be aware of binders within types.
(test-check-top-expr
 "(unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e))))
   (i-fn ($d) 7))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The tests below are commented out because they currently fail:
; the type checker accepts these expressions,
; but each one gets stuck (a dynamic shape error) when evaluated,
; so each should be rejected.
; They exploit shadowing of ispace variables rather than escaping witnesses:
; a type recorded in the environment mentions an ispace variable
; that a later homonymous binder silently reinterprets (captures).
; The escape check in the unbox case of check-expr cannot see them,
; because the escaping type is closed in each case;
; rejecting them requires binder freshness,
; e.g. uniquification of bound variables before type checking
; (see unique-names.lisp)
; or freshness checks at every ispace binder.
; If freshness is enforced, these should become passing tests.

; The type of u refers to the outer $d
; but is reinterpreted at the witness $d inside the unbox:
; length is instantiated at the witness (3 at run time)
; and applied to u (of length 5 at run time).
; (test-check-top-expr-fail
;  "(let ((i-fun (f ($d))
;         (fn ((u [Int $d]))
;           (unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e))))
;             (@length (Int) ($d []) u)))))
;   ((i-app f 5) [1 2 3 4 5]))")

; The Sigma body type (A Int $d) mentions the outer $d free;
; renaming the Sigma variable $e to the witness $d
; rebinds (captures) that occurrence,
; so the type of v is misread at the witness.
; (test-check-top-expr-fail
;  "(let ((i-fun (f ($d))
;         (fn ((u [Int $d]))
;           (unbox ($d v (box (3) u (Sigma ($e) (A Int $d))))
;             (@length (Int) ($d []) v)))))
;   ((i-app f 5) [1 2 3 4 5]))")

; The same reinterpretation with no unbox involved:
; the inner i-fn's $d shadows the outer $d in the type of u.
; (test-check-top-expr-fail
;  "(let ((i-fun (f ($d))
;         (fn ((u [Int $d]))
;           (i-fn ($d) (@length (Int) ($d []) u)))))
;   (i-app ((i-app f 5) [1 2 3 4 5]) 3))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Full instantiation of a two-parameter type lambda abstraction,
; as an n-ary type application.
(test-check-top-expr
 "(t-app (t-fn (&t &u) (i-fn ($d) (fn ((x (A &t $d))) x))) Int Int)")

; Partial instantiation, providing just the first type:
; the type is the (lifted) universal type over the remaining variable.
(test-check-top-expr
 "(t-app (t-fn (&t &u) (i-fn ($d) (fn ((x (A &t $d))) x))) Int)")

; Completion of a partial instantiation, as a chain.
(test-check-top-expr
 "(t-app (t-app (t-fn (&t &u) (i-fn ($d) (fn ((x (A &t $d))) x))) Int) Int)")

; More type arguments than bound variables.
(test-check-top-expr-fail
 "(t-app (t-fn (&t) (i-fn ($d) (fn ((x (A &t $d))) x))) Int Int)")

; Application of a unary type lambda abstraction:
; its computed type is a unary universal type, matched by the application.
(test-check-top-expr
 "(t-app (t-fn (&t) (i-fn ($d) (fn ((x (A &t $d))) x))) Int)")

; Application of a let-bound type function with one parameter:
; its recorded type is a unary universal type, matched by the application.
(test-check-top-expr
 "(let ((t-fun (f (&t)) (i-fn ($d) (fn ((x (A &t $d))) x))))
  (t-app f Int))")

; A type function binding with no parameters
; is treated as a plain value binding,
; as in [impl], whose parser turns it directly into a value binding.
(test-check-top-expr
 "(let ((t-fun (f () : Int) 7)) (+ f 1))")

; Similarly for an ispace function binding with no parameters.
(test-check-top-expr
 "(let ((i-fun (f () : Int) 7)) (+ f 1))")

; Similarly for a function binding with no value parameters.
(test-check-top-expr
 "(let ((fun (f : Int) 7)) (+ f 1))")

; Similarly for a combined function binding with no parameters at all,
; whether the type and ispace parameter lists are empty or absent.
(test-check-top-expr
 "(let ((fun (@f () () : Int) 7)) (+ f 1))")
(test-check-top-expr
 "(let ((fun (@f _ _ : Int) 7)) (+ f 1))")

; In a combined function binding, only the layers with parameters
; are present: here the type and function layers but no ispace layer.
(test-check-top-expr
 "(let ((fun (@f (&t) () (x Int) : Int) x))
  (@f (Int) () 7))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Full application of a two-parameter term lambda abstraction,
; as a chain of unary applications.
(test-check-top-expr
 "((fn ((x Int) (y Int)) (+ x y)) 3 4)")

; Partial application of a two-parameter term lambda abstraction:
; its type is a (lifted) one-input function type over the remaining parameter.
(test-check-top-expr
 "((fn ((x Int) (y Int)) (+ x y)) 3)")

; Completion of a partial application, as a chain of unary applications.
(test-check-top-expr
 "(((fn ((x Int) (y Int)) (+ x y)) 3) 4)")

; Rank-polymorphic application over a non-scalar frame:
; each argument's frame joins into the principal shape.
(test-check-top-expr
 "((fn ((x Int) (y Int)) (+ x y)) [1 2 3] [4 5 6])")

; More arguments than parameters (over-application):
; after the last parameter, the result is not a function type.
(test-check-top-expr-fail
 "((fn ((x Int)) x) 3 4)")

; Partial application through a let-bound function:
; g is the function partially applied to its first argument,
; then applied to its second.
; (This test was previously expected to fail before term application
; was made curried.)
(test-check-top-expr
 "
(let ((fun (f (x Int) (y Int) : Int) (+ x y))
      (val g (f 2)))
  (g 3))
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Application of a let-bound combined function
; with one type parameter and one ispace parameter:
; its recorded type is a unary universal type over a unary product type,
; matched by the type and ispace applications.
(test-check-top-expr
 "(let ((fun (@f (&t) ($d) (x (A &t $d)) : (A &t $d)) x))
  (@f (Int) (3) [1 2 3]))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Inference of type and ispace applications (see check/infer-app):
; a function with a universal or product type
; is applied directly to an argument,
; and the type and ispace arguments are inferred from the argument type.
; Since the argument type must match the parameter type syntactically,
; the arguments are explicit arrays, whose types have plain dimensions,
; rather than bracket expressions, whose types have concatenated shapes.

; Universal type over product type,
; as in the explicit instantiation just above.
(test-check-top-expr
 "(let ((fun (@f (&t) ($d) (x (A &t (dims $d))) : (A &t (dims $d))) x))
  (f (array [3] 1 2 3)))")

; The same, with a different element type.
(test-check-top-expr
 "(let ((fun (@f (&t) ($d) (x (A &t (dims $d))) : (A &t (dims $d))) x))
  (f (array [2] #t #f)))")

; Product type over universal type, via explicit abstractions.
(test-check-top-expr
 "((i-fn ($d) (t-fn (&t) (fn ((x (A &t (dims $d)))) x))) (array [3] 1 2 3))")

; Universal type only.
(test-check-top-expr
 "(let ((fun (@f (&t) () (x (A &t (dims))) : (A &t (dims))) x))
  (f 7))")

; Product type only.
(test-check-top-expr
 "(let ((fun (@f () ($d) (x (A Int (dims $d))) : (A Int (dims $d))) x))
  (f (array [3] 1 2 3)))")

; A shape variable is inferred as the whole shape of the argument.
(test-check-top-expr
 "(let ((fun (@f (&t) (@s) (x (A &t @s)) : (A &t @s)) x))
  (f (array [2 3] 1 2 3 4 5 6)))")

; Two ispace parameters, in an n-ary product type.
(test-check-top-expr
 "(let ((fun (@f (&t) ($m $n) (x (A &t (dims $m $n))) : (A &t (dims $m $n)))
        x))
  (f (array [2 3] 1 2 3 4 5 6)))")

; An array-kind type variable is inferred as the whole argument type.
(test-check-top-expr
 "(let ((fun (@f (*x) () (v *x) : *x) v))
  (f (array [3] 1 2 3)))")

; The inferred applications precede the term application,
; so a two-parameter function is applied to its arguments in a chain:
; the first (unary) application infers the instantiation,
; and the second one is an ordinary application.
(test-check-top-expr
 "(let ((fun (@f (&t) ($d) (x (A &t (dims $d))) (y (A &t (dims $d)))
             : (A &t (dims $d)))
        x))
  ((f (array [3] 1 2 3)) (array [3] 4 5 6)))")

; An n-ary term application performs no inference, for now.
(test-check-top-expr-fail
 "(let ((fun (@f (&t) ($d) (x (A &t (dims $d))) (y (A &t (dims $d)))
             : (A &t (dims $d)))
        x))
  (f (array [3] 1 2 3) (array [3] 4 5 6)))")

; Parameters that do not occur in the parameter type
; cannot be inferred from the argument;
; explicit instantiation is still possible.
(test-check-top-expr-fail
 "(let ((fun (@f (&t) ($d) (x (A Int (dims))) : Int) 5))
  (f 7))")
(test-check-top-expr
 "(let ((fun (@f (&t) ($d) (x (A Int (dims))) : Int) 5))
  (@f (Int) (3) 7))")

; A mismatched argument.
(test-check-top-expr-fail
 "(let ((fun (@f (&t) ($d) (x (A &t (dims $d))) : (A &t (dims $d))) x))
  (f 7))")

; An argument with a non-empty frame is not accepted, for now:
; the argument type must match the whole parameter type.
(test-check-top-expr-fail
 "(let ((fun (@f (&t) ($d) (x (A &t (dims $d))) : (A &t (dims $d))) x))
  (f (array [2 3] 1 2 3 4 5 6)))")

; A bracket expression has a concatenated shape,
; which does not match the plain dimensions of the parameter type, for now.
(test-check-top-expr-fail
 "(let ((fun (@f (&t) ($d) (x (A &t (dims $d))) : (A &t (dims $d))) x))
  (f [1 2 3]))")

; The types of the primitive operations use bracket types and splices,
; which the syntactic matching does not handle, for now.
(test-check-top-expr-fail
 "(length (array [3] 1 2 3))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Shapes with multiplications, like the one of the result of flatten,
; are handled by the suffix check and by the join of shapes
; (see check-shape-suffix and join-shapes),
; with the multiplications treated as uninterpreted
; (see ispace-equivalence-checker).

; The result of flatten, of shape [(* 2 3)],
; is passed to length instantiated at the same shape.
(test-check-top-expr
 "(@length (Int) ((* 2 3) [])
   (@flatten (Int) (2 3 []) (array [2 3] 1 2 3 4 5 6)))")

; The result of flatten is the frame of an application of +.
(test-check-top-expr
 "(+ (@flatten (Int) (2 3 []) (array [2 3] 1 2 3 4 5 6)) 1)")
