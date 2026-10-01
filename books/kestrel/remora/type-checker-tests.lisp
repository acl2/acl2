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

; Alpha renaming of an ispace binder in a type application:
; the type argument mentions the shape variable @s bound outside,
; and the body of the universal type binds its own @s in a product type,
; which must be renamed apart when the argument is substituted.
; The instantiated function is then applied to a vector of functions
; whose type mentions the outer @s, which type-checks only without capture.
(test-check-top-expr
 "(i-fn (@s)
  (fn ((f (A (-> (A Int @s) (A Int (dims))) (dims 2))))
    ((i-app (t-app (t-fn (&t) (i-fn (@s) (fn ((x (A &t @s))) x)))
                   (-> (A Int @s) (A Int (dims))))
            (dims 2))
     f)))")

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
; The types are matched modulo equivalence (see type-matcher),
; so the arguments may be explicit arrays, whose types have plain dimensions,
; or bracket expressions, whose types have concatenated shapes.

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
; which matches the plain dimensions of the parameter type
; modulo shape equivalence.
(test-check-top-expr
 "(let ((fun (@f (&t) ($d) (x (A &t (dims $d))) : (A &t (dims $d))) x))
  (f [1 2 3]))")

; The types of the primitive operations use bracket types,
; which are matched to the array types of the arguments (see type-match):
; the length of a vector, given as an explicit array or as a bracket expression,
; and the length (i.e. the first dimension) of a matrix.
(test-check-top-expr
 "(length (array [3] 1 2 3))")
(test-check-top-expr
 "(length [1 2 3])")
(test-check-top-expr
 "(length (array [2 3] 1 2 3 4 5 6))")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Applications of the primitive operations (see primop-types)
; with inferred type and ispace arguments (see check/infer-app),
; one section per primitive operation.
; The failing tests marked as objectives are well-typed expressions
; that the inference does not handle yet;
; they should be flipped to passing tests as the inference is extended.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; length : (Forall (&t) (Pi ($d @s) (-> [&t $d @s] Int)))
; The applications to vectors and to a matrix are tested above.

; The element type may be any atom type:
; a base type, a function type, a sum type.
(test-check-top-expr
 "(length [#t #f])")
(test-check-top-expr
 "(length [(fn ((x Int)) x) (fn ((x Int)) x)])")
(test-check-top-expr
 "(length [(box (3) [1 2 3] (Sigma ($e) (A Int $e)))])")

; The shape variable is inferred as the shape of the elements,
; here the shape [2] of the vectors.
(test-check-top-expr
 "(length [[1 2] [3 4]])")

; The argument may be any expression with a non-scalar array type:
; a let-bound variable, a rank-polymorphic application, a string.
(test-check-top-expr
 "(let ((val x [1 2 3])) (length x))")
(test-check-top-expr
 "(length (+ [1 2 3] [4 5 6]))")
(test-check-top-expr
 "(length \"abc\")")

; A scalar has no length:
; the type of the argument must have at least one dimension.
(test-check-top-expr-fail
 "(length 5)")
(test-check-top-expr-fail
 "(length (length [1 2 3]))")

; Partial explicit instantiation, with the remaining arguments inferred:
; the type argument is explicit and the ispace arguments are inferred;
; the type argument and the dimension are explicit and the shape is inferred.
(test-check-top-expr
 "((t-app length Int) [1 2 3])")
(test-check-top-expr
 "((i-app (t-app length Int) 3) [1 2 3])")

; The explicit dimension does not match the argument.
(test-check-top-expr-fail
 "((i-app (t-app length Int) 3) [1 2])")

; OBJECTIVE: the explicit dimension matches the rows of the matrix,
; with the shape inferred as empty,
; so length should be applied to each row, over the frame [2];
; but the inference does not handle frames yet.
; The fully explicit instantiation, which involves no inference,
; is accepted, with the frame.
(test-check-top-expr-fail
 "((i-app (t-app length Int) 3) [[1 2 3] [4 5 6]])")
(test-check-top-expr
 "(@length (Int) (3 []) [[1 2 3] [4 5 6]])")

; Inference under an ispace binder:
; the dimension is inferred as the bound dimension variable,
; and the shape as empty.
(test-check-top-expr
 "(i-fn ($n) (fn ((x [Int $n])) (length x)))")

; A shape variable may stand for the empty shape,
; so an array of unknown shape may be a scalar,
; and length is not applicable to it.
(test-check-top-expr-fail
 "(i-fn (@s) (fn ((x (A Int @s))) (length x)))")

; The shape variable of the type of length
; is inferred as the homonymous bound shape variable.
(test-check-top-expr
 "(i-fn ($n @s) (fn ((x [Int $n @s])) (length x)))")

; The dimension is inferred as the witness of an unboxing,
; which does not escape, since the result is a scalar;
; compare with the explicit instantiation above.
(test-check-top-expr
 "(unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) (length v))")

; A primitive operation is a value with its polymorphic type:
; bound by a let, or passed as an argument to a function,
; it is applied with inference.
(test-check-top-expr
 "(let ((val f length)) (f [1 2 3]))")
(test-check-top-expr
 "((fn ((g (Forall (&t) (Pi ($d @s) (-> [&t $d @s] Int))))) (g [1 2 3]))
   length)")

; OBJECTIVE: a combined application without type and ispace arguments
; performs no inference, for now (like an n-ary term application),
; but it should be treated like the plain application (length [1 2 3]).
(test-check-top-expr-fail
 "(@length _ _ [1 2 3])")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; head : (Forall (&t) (Pi ($d @s) (-> [&t (+ 1 $d) @s] [&t @s])))

; The dimension is inferred modulo additive equivalence (see ispace-matcher):
; from the length 3 of a vector, it is inferred as 2;
; from the first dimension 2 of a matrix, it is inferred as 1,
; and the shape variable is inferred as the shape [3] of the rows.
(test-check-top-expr
 "(head [1 2 3])")
(test-check-top-expr
 "(head (array [2 3] 1 2 3 4 5 6))")

; From the length 1 of a singleton vector, the dimension is inferred as 0.
(test-check-top-expr
 "(head [7])")

; A scalar has no head:
; the type of the argument must have at least one dimension.
(test-check-top-expr-fail
 "(head 5)")
(test-check-top-expr-fail
 "(head (head [1 2]))")

; The result of head is used with inference again:
; the head of a matrix is a vector, whose head or length is inferred;
; the head of a vector of functions is a function, which is applied.
(test-check-top-expr
 "(head (head [[1 2] [3 4]]))")
(test-check-top-expr
 "(length (head [[1 2 3] [4 5 6]]))")
(test-check-top-expr
 "((head [(fn ((x Int)) x)]) 7)")

; Partial explicit instantiation, with the shape inferred:
; the length in the input type is (+ 1 2),
; which is normalized to 3 before matching.
(test-check-top-expr
 "((i-app (t-app head Int) 2) [1 2 3])")

; The explicit dimension does not match the argument.
(test-check-top-expr-fail
 "((i-app (t-app head Int) 3) [1 2 3])")

; OBJECTIVE: as for length, the explicit dimension matches the rows,
; so head should be applied to each row, over the frame [2],
; yielding the first column;
; but the inference does not handle frames yet.
; The fully explicit instantiation is accepted, with the frame.
(test-check-top-expr-fail
 "((i-app (t-app head Int) 2) [[1 2 3] [4 5 6]])")
(test-check-top-expr
 "(@head (Int) (2 []) [[1 2 3] [4 5 6]])")

; Inference under an ispace binder, modulo additive equivalence:
; the dimension is inferred as the bound variable $n
; from the lengths (+ 1 $n) and (+ $n 1),
; as (+ 1 $n) from the length (+ 2 $n),
; as (+ $m $n) from the length (+ 1 $m $n),
; and as the uninterpreted (* 2 $n) from the length (+ 1 (* 2 $n)).
(test-check-top-expr
 "(i-fn ($n) (fn ((x [Int (+ 1 $n)])) (head x)))")
(test-check-top-expr
 "(i-fn ($n) (fn ((x [Int (+ $n 1)])) (head x)))")
(test-check-top-expr
 "(i-fn ($n) (fn ((x [Int (+ 2 $n)])) (head x)))")
(test-check-top-expr
 "(i-fn ($m $n) (fn ((x [Int (+ 1 $m $n)])) (head x)))")
(test-check-top-expr
 "(i-fn ($n) (fn ((x [Int (+ 1 (* 2 $n))])) (head x)))")

; A vector of unknown length $n may be empty,
; so head is not applicable to it:
; there is no dimension $d with (+ 1 $d) equivalent to $n.
(test-check-top-expr-fail
 "(i-fn ($n) (fn ((x [Int $n])) (head x)))")

; The shape variable is inferred as the bound shape variable.
(test-check-top-expr
 "(i-fn (@s) (fn ((x [Int 3 @s])) (head x)))")

; An unboxed vector of unknown length may be empty (compare with length),
; unless its sum type says that the length is a successor.
(test-check-top-expr-fail
 "(unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) (head v))")
(test-check-top-expr
 "(unbox ($d v (box (2) [1 2 3] (Sigma ($e) (A Int (+ 1 $e))))) (head v))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; tail : (Forall (&t) (Pi ($d @s) (-> [&t (+ 1 $d) @s] [&t $d @s])))

; The input type is the same as for head, so the inference is the same;
; but the output type keeps the inferred dimension,
; which the following tests use.

; The tail of a vector of length 3 has length 2,
; the tail of a matrix with 2 rows has 1 row,
; and the tail of a singleton vector is empty.
(test-check-top-expr
 "(tail [1 2 3])")
(test-check-top-expr
 "(tail (array [2 3] 1 2 3 4 5 6))")
(test-check-top-expr
 "(tail [7])")

; A scalar has no tail.
(test-check-top-expr-fail
 "(tail 5)")

; The inferred length of the result is used by further inference:
; the tail of a vector of length 3 has a head,
; and can be tailed twice more, but not three times more,
; because the length of the third tail is 0;
; the tail of a singleton vector has a length (namely 0) but no head.
(test-check-top-expr
 "(head (tail [1 2 3]))")
(test-check-top-expr
 "(tail (tail (tail [1 2 3])))")
(test-check-top-expr-fail
 "(tail (tail (tail (tail [1 2 3]))))")
(test-check-top-expr
 "(length (tail [7]))")
(test-check-top-expr-fail
 "(head (tail [7]))")

; Partial explicit instantiation, with the shape inferred.
(test-check-top-expr
 "((i-app (t-app tail Int) 2) [1 2 3])")

; OBJECTIVE: as for head, the explicit dimension matches the rows,
; so tail should be applied to each row, over the frame [2],
; yielding the matrix without its first column;
; but the inference does not handle frames yet.
; The fully explicit instantiation is accepted, with the frame.
(test-check-top-expr-fail
 "((i-app (t-app tail Int) 2) [[1 2 3] [4 5 6]])")
(test-check-top-expr
 "(@tail (Int) (2 []) [[1 2 3] [4 5 6]])")

; Inference under an ispace binder,
; with the result used by further inference:
; the tail of a vector of length (+ 1 $n) has length $n,
; so it may be empty and has no head;
; the tail of a vector of length (+ 2 $n) has length (+ 1 $n),
; so it has a head.
(test-check-top-expr
 "(i-fn ($n) (fn ((x [Int (+ 1 $n)])) (tail x)))")
(test-check-top-expr-fail
 "(i-fn ($n) (fn ((x [Int (+ 1 $n)])) (head (tail x))))")
(test-check-top-expr
 "(i-fn ($n) (fn ((x [Int (+ 2 $n)])) (head (tail x))))")

; The shape variable is inferred as the bound shape variable
; through a chain of applications:
; the tails of an array of shape [3 @s] have shapes [2 @s] and [1 @s],
; and the head of the latter has shape @s.
(test-check-top-expr
 "(i-fn (@s) (fn ((x [Int 3 @s])) (head (tail (tail x)))))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; append : (Forall (&t)
;           (Pi ($m $n @s)
;            (-> ([&t $m @s] [&t $n @s]) [&t (+ $m $n) @s])))

; OBJECTIVE: append takes two arguments,
; but the inference is limited to unary applications:
; the n-ary application performs no inference,
; and the unary application to the first argument fails,
; because the dimension $n of the second input
; does not occur in the first input,
; so it cannot be inferred from the first argument;
; the inference should consider all the arguments of an n-ary application,
; or defer the instantiation of $n to the application to the second argument.
(test-check-top-expr-fail
 "(append [1 2] [3 4 5])")
(test-check-top-expr-fail
 "((append [1 2]) [3 4 5])")

; The fully explicit instantiation is accepted;
; the length (+ 2 3) of the result is used by further inference
; modulo additive equivalence:
; the length is inferred as 5,
; and the head is inferred with the explicit dimension 4,
; since (+ 1 4) and (+ 2 3) are both normalized to 5.
(test-check-top-expr
 "(@append (Int) (2 3 []) [1 2] [3 4 5])")
(test-check-top-expr
 "(length (@append (Int) (2 3 []) [1 2] [3 4 5]))")
(test-check-top-expr
 "((i-app (t-app head Int) 4) (@append (Int) (2 3 []) [1 2] [3 4 5]))")

; Partial explicit instantiation, with the dimensions explicit
; and the shape inferred from the first argument,
; which fixes the shape of the elements of the second argument:
; the elements of the vectors are scalars,
; and the elements of the matrices are vectors of length 2;
; the explicit dimension of the second argument is checked.
(test-check-top-expr
 "(((i-app (t-app append Int) 2 3) [1 2]) [3 4 5])")
(test-check-top-expr
 "(((i-app (t-app append Int) 1 2) [[1 2]]) [[3 4] [5 6]])")
(test-check-top-expr-fail
 "(((i-app (t-app append Int) 2 3) [1 2]) [3 4])")

; Under ispace binders, with the bound dimension variables explicit,
; the shape is inferred from the first argument:
; the first input type [Int $m @s] contains the bound variable $m,
; which is rigid, i.e. not a pattern variable.
(test-check-top-expr
 "(i-fn ($m $n) (fn ((x [Int $m]) (y [Int $n]))
    (((i-app (t-app append Int) $m $n) x) y)))")

; The result of a fully explicit instantiation under ispace binders
; has length (+ $m $n), which is used by further inference:
; its length is inferred as (+ $m $n);
; it has no head, since (+ $m $n) may be 0;
; it has a head when the first vector has length (+ 1 $m).
(test-check-top-expr
 "(i-fn ($m $n) (fn ((x [Int $m]) (y [Int $n]))
    (length (@append (Int) ($m $n []) x y))))")
(test-check-top-expr-fail
 "(i-fn ($m $n) (fn ((x [Int $m]) (y [Int $n]))
    (head (@append (Int) ($m $n []) x y))))")
(test-check-top-expr
 "(i-fn ($m $n) (fn ((x [Int (+ 1 $m)]) (y [Int $n]))
    (head (@append (Int) ((+ 1 $m) $n []) x y))))")
