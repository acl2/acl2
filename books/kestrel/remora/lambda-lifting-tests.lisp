; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "lambda-lifting")
(include-book "parser-interface")
(include-book "validator")
(include-book "evaluation")

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of lambda lifting (see LAMBDA-LIFTING in lambda-lifting.lisp).
;
; Each test gives a program and the expected result of the lifting, both
; in concrete syntax, and checks four things: that lifting the parsed
; program yields the parsed expected result; that no lifted definition is
; placed before a definition or declaration it refers to (see below); that
; the result type-checks; and that the type-checked program and its lifting
; evaluate to the same value, which is not an error --- or, for a test that
; says :ERROR T, that both evaluations are errors.
;
; For an expression, the lifted definitions are wrapped around it, so the
; placement check is that the result has no free variables beyond those of
; the program.  For a file, it is that each declaration of the result refers
; only to primitive operations and to the names declared before it, as each
; declaration of the program does.
;
; The guard of LAMBDA-LIFT-TOP-EXPR requires the binders of the program to
; bind distinct names, and a test checks that its program does.  The
; transformation does not rely on that, though, and several programs reuse
; names to test that it handles shadowing: those tests say :UNIQUE NIL, and
; check that the program does reuse a name and run with guard checking off
; (so the logical definition is run on the out-of-guard input).

(defmacro test-lambda-lift (code expected &key (unique 't) error)
  (let ((test
         `(assert!
           (b* ((ast (parse-top-exp-from-string ,code))
                (expected (parse-top-exp-from-string ,expected))
                ((when (or (reserrp ast) (reserrp expected))) nil)
                ((unless (equal (not (expr-duplicate-names ast)) ,unique)) nil)
                (new (lambda-lift-top-expr ast))
                ((unless (set::subset (expr-free-expr-vars new)
                                      (expr-free-expr-vars ast)))
                 nil)
                (tast (check-top-expr ast))
                ((when (reserrp tast)) nil)
                ((when (reserrp (check-top-expr new))) nil)
                (expr (type+expr->expr tast))
                (val (eval-top-expr expr 100000))
                (new-val (eval-top-expr (lambda-lift-top-expr expr) 100000)))
             (and (equal new expected)
                  ,(if error
                       '(and (reserrp val) (reserrp new-val))
                     '(and (not (reserrp val))
                           (equal new-val val))))))))
    (if unique
        test
      `(with-guard-checking-event nil ,test))))

; The bindings, in order, that refer to a variable not in scope where they
; are: CTX is the set of variables in scope before the first, and each
; binding adds the variables it binds for the ones after it.

(define bind-list-out-of-scope ((binds bind-listp) (ctx string-setp))
  :returns (names string-listp)
  :short "The names of the bindings that refer to a variable not in scope."
  (b* (((when (endp binds)) nil)
       (b (car binds))
       (rest (bind-list-out-of-scope
              (cdr binds)
              (set::union (bind-bound-expr-vars b) (string-sfix ctx)))))
    (if (set::subset (bind-free-expr-vars b) (string-sfix ctx))
        rest
      (cons (bind-name b) rest))))

; The same for files, which are run via FILE-TO-EXPR.  With :UNIQUIFY T,
; the file is first made to satisfy the guard of LAMBDA-LIFT-FILE by
; FILE-UNIQUIFY-NAMES, as the drivers in lambda-lifting-from-file.lisp and
; monomorphize-from-file.lisp do.

(defmacro test-lambda-lift-file (code expected &key uniquify)
  `(assert!
    (b* ((ast (parse-from-string ,code))
         (expected (parse-from-string ,expected))
         ((when (or (reserrp ast) (reserrp expected))) nil)
         (in ,(if uniquify '(file-uniquify-names ast) 'ast))
         ((when (file-duplicate-names in)) nil)
         (new (lambda-lift-file in))
         ((when (or (bind-list-out-of-scope (decl-list-to-binds (file->decls in))
                                            (primop-names))
                    (bind-list-out-of-scope (decl-list-to-binds (file->decls new))
                                            (primop-names))))
          nil)
         (expr (file-to-expr ast))
         (new-expr (file-to-expr new))
         ((when (or (reserrp expr) (reserrp new-expr))) nil)
         (tast (check-top-expr expr))
         (new-tast (check-top-expr new-expr))
         ((when (or (reserrp tast) (reserrp new-tast))) nil)
         (val (eval-top-expr (type+expr->expr tast) 100000))
         (new-val (eval-top-expr (type+expr->expr new-tast) 100000)))
      (and (equal new expected)
           (not (reserrp val))
           (equal new-val val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A lambda that uses a local variable captures it: the variable becomes a
; leading parameter of the definition, and is passed where the lambda was.

(test-lambda-lift
 "(let ((val x 1)) ((fn ((y Int)) (+ x y)) 2))"
 "(let ((fun (lam_0 (x (A Int (dims))) (y Int)) (+ x y)))
    (let ((val x 1))
      ((lam_0 x) 2)))")

; A lambda whose body is a lambda yields one definition.

(test-lambda-lift
 "((fn ((x Int)) (fn ((y Int)) (+ x y))) 3 4)"
 "(let ((fun (lam_0 (x Int) (y Int)) (+ x y)))
    (lam_0 3 4))")

; A parameter may shadow a variable of the same name (outside the guard).

(test-lambda-lift
 "((fn ((x Int)) ((fn ((x Int)) (* x 10)) (+ x 1))) 4)"
 "(let ((fun (lam_0 (x Int)) (* x 10)))
    (let ((fun (lam_1 (x Int)) (lam_0 (+ x 1))))
      (lam_1 4)))"
 :unique nil)

; A local function is hoisted; the variables it captures become leading
; parameters, and its uses become the definition applied to them.

(test-lambda-lift
 "(let ((val a 10) (fun (f (x Int) : Int) (+ x a))) (f 5))"
 "(let ((fun (f0 (a (A Int (dims))) (x Int) : Int) (+ x a)))
    (let ((val a 10))
      ((f0 a) 5)))")

(test-lambda-lift
 "(let ((val a 1) (fun (f (x Int) : Int) (+ x a)))
    (let ((val b 2)) (f b)))"
 "(let ((fun (f0 (a (A Int (dims))) (x Int) : Int) (+ x a)))
    (let ((val a 1))
      (let ((val b 2))
        ((f0 a) b))))")

; A :FUN with no parameters is a value binding, whose body is evaluated
; where it is bound, so it stays local.  Hoisted without parameters, its
; body would be evaluated at the top level: here, the division by zero in a
; lambda that is never applied would become an error.

(test-lambda-lift
 "(let ((val g (fn ((x Int)) (let ((fun (k : Int) (/ 1 0))) 7)))) 5)"
 "(let ((fun (lam_0 (x Int)) (let ((fun (k : Int) (/ 1 0))) 7)))
    (let ((val g lam_0)) 5))")

; Hoisted with the variable it captures as a parameter, its body would be
; evaluated only at its uses: here, the error at the binding would be lost.

(test-lambda-lift
 "(let ((val n 0) (fun (k : Int) (/ 1 n))) 5)"
 "(let ((val n 0) (fun (k : Int) (/ 1 n))) 5)"
 :error t)

(test-lambda-lift
 "(let ((val n 2) (fun (k : Int) (* n 10))) (+ k 1))"
 "(let ((val n 2) (fun (k : Int) (* n 10))) (+ k 1))")

; A lambda or local function that captures a variable whose type mentions a
; type or ispace variable stays in place: the captured variable would become
; a parameter of the definition, outside the binder of that variable.  This
; holds also of a lambda that captures such a function.

(test-lambda-lift
 "((t-app (t-fn (&t) (fn ((x &t)) ((fn ((y Int)) x) 1))) Int) 5)"
 "((t-app (t-fn (&t) (fn ((x &t)) ((fn ((y Int)) x) 1))) Int) 5)")

(test-lambda-lift
 "((i-app (i-fn ($d) (fn ((x (A Int $d))) ((fn ((y Int)) x) 1))) 3) [1 2 3])"
 "((i-app (i-fn ($d) (fn ((x (A Int $d))) ((fn ((y Int)) x) 1))) 3) [1 2 3])")

(test-lambda-lift
 "((t-app (t-fn (&t) (fn ((x &t)) (let ((fun (f (y Int)) x)) (f 1)))) Int) 5)"
 "((t-app (t-fn (&t) (fn ((x &t)) (let ((fun (f (y Int)) x)) (f 1)))) Int) 5)")

(test-lambda-lift
 "((t-app (t-fn (&t)
     (fn ((x &t)) (let ((fun (f (y Int)) x)) ((fn ((z Int)) (f z)) 1))))
   Int)
   5)"
 "((t-app (t-fn (&t)
     (fn ((x &t)) (let ((fun (f (y Int)) x)) ((fn ((z Int)) (f z)) 1))))
   Int)
   5)")

; Under such a binder, a lambda or local function that captures nothing
; open is lifted as usual.

(test-lambda-lift
 "((t-app (t-fn (&t) (fn ((x &t)) ((fn ((y Int)) (+ y 1)) 1))) Int) 5)"
 "(let ((fun (lam_0 (y Int)) (+ y 1)))
    ((t-app (t-fn (&t) (fn ((x &t)) (lam_0 1))) Int) 5))")

(test-lambda-lift
 "(t-app (t-fn (&t)
    (let ((val a 1) (fun (f (y Int) : Int) (+ y a)))
      ((fn ((z Int)) (f z)) 5)))
   Int)"
 "(let ((fun (f0 (a (A Int (dims))) (y Int) : Int) (+ y a)))
    (let ((fun (lam_0 (a (A Int (dims))) (z Int)) ((f0 a) z)))
      (t-app (t-fn (&t) (let ((val a 1)) ((lam_0 a) 5))) Int)))")

; A lambda or local function that captures a variable the type environment
; does not type stays in place: the captured variable would become an
; untyped parameter, on which evaluation fails.  The variable of an unboxing
; is such a variable, even when its type is closed, as here.  (Lifted, both
; programs evaluated to an error rather than 6.)

(test-lambda-lift
 "(unbox ($d f (box (3) 5 (Sigma ($n) Int))) ((fn ((y Int)) (+ y f)) 1))"
 "(unbox ($d f (box (3) 5 (Sigma ($n) Int))) ((fn ((y Int)) (+ y f)) 1))")

(test-lambda-lift
 "(unbox ($d f (box (3) 5 (Sigma ($n) Int)))
    (let ((fun (g (y Int) : Int) (+ y f))) (g 1)))"
 "(unbox ($d f (box (3) 5 (Sigma ($n) Int)))
    (let ((fun (g (y Int) : Int) (+ y f))) (g 1)))")

; A lambda under an unboxing that captures nothing unboxed is lifted as
; usual.

(test-lambda-lift
 "(unbox ($d f (box (3) 5 (Sigma ($n) Int))) ((fn ((y Int)) (+ y 1)) f))"
 "(let ((fun (lam_0 (y Int)) (+ y 1)))
    (unbox ($d f (box (3) 5 (Sigma ($n) Int))) (lam_0 f)))")

; The type of a variable bound by a :LET is inferred only from the types of
; other such variables (see EXTEND-TENV-WITH-LET-BIND): here X is computed
; from the parameter P, so it is untyped, and the inner lambda, which
; captures it, stays in place; the outer lambda captures nothing and is
; lifted.

(test-lambda-lift
 "((fn ((p Int)) (let ((val x (+ p 1))) ((fn ((y Int)) (+ x y)) 2))) 5)"
 "(let ((fun (lam_0 (p Int))
            (let ((val x (+ p 1))) ((fn ((y Int)) (+ x y)) 2))))
    (lam_0 5))")

; A lifted definition is bound at the top, which evaluates the type of its
; first parameter: a lambda whose first parameter's type fails to evaluate
; (a closed type may, as here, with a negative dimension) stays in place.
; Lifted, this lambda, which is never evaluated, would make the program fail
; where it is bound.

(test-lambda-lift
 "(let ((fun (g (x Int)) (fn ((y (A Int [(- 2 5)]))) 7))) 5)"
 "(let ((fun (g0 (x Int)) (fn ((y (A Int [(- 2 5)]))) 7))) 5)")

; Applying a function over an empty frame takes its result type from the
; function value, so a lifted definition keeps the result type of its
; lambda, and a lambda annotated with one is not flattened into.  (The type
; checker annotates every lambda, so the evaluated programs are annotated,
; whereas the expected results are lifted from the unannotated ones.  These
; evaluated to an error after lifting, rather than to an empty array.)

(test-lambda-lift
 "((fn ((y Int)) (+ y 1)) (array [0] Int))"
 "(let ((fun (lam_0 (y Int)) (+ y 1))) (lam_0 (array [0] Int)))")

(test-lambda-lift
 "(let ((val x 1)) ((fn ((y Int)) (+ x y)) (array [0] Int)))"
 "(let ((fun (lam_0 (x (A Int (dims))) (y Int)) (+ x y)))
    (let ((val x 1)) ((lam_0 x) (array [0] Int))))")

(test-lambda-lift
 "((fn ((x Int)) (fn ((y Int)) (+ x y))) (array [0] Int))"
 "(let ((fun (lam_0 (x Int) (y Int)) (+ x y))) (lam_0 (array [0] Int)))")

(test-lambda-lift
 "(let ((val a 10) (fun (f (x Int) : Int) (+ x a))) (f (array [0] Int)))"
 "(let ((fun (f0 (a (A Int (dims))) (x Int) : Int) (+ x a)))
    (let ((val a 10)) ((f0 a) (array [0] Int))))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Outside the guard: a binder of the name of a hoisted function hides it,
; so the uses of the name under the binder are not replaced.  The binder may
; be a lambda parameter, a later binding of the same :LET, a function
; parameter, the variable of an unboxing, or a parameter of a combined
; function.

(test-lambda-lift
 "(let ((val a 1) (fun (f (x Int) : Int) (+ x a)))
    ((fn ((f Int)) (+ f 1)) (f 2)))"
 "(let ((fun (f0 (a (A Int (dims))) (x Int) : Int) (+ x a)))
    (let ((fun (lam_0 (f Int)) (+ f 1)))
      (let ((val a 1))
        (lam_0 ((f0 a) 2)))))"
 :unique nil)

(test-lambda-lift
 "(let ((fun (f (x Int) : Int) (+ x 1)))
    ((fn ((y Int)) (fn ((f Int)) (+ f y))) 10 (f 1)))"
 "(let ((fun (f0 (x Int) : Int) (+ x 1)))
    (let ((fun (lam_0 (y Int) (f Int)) (+ f y)))
      (lam_0 10 (f0 1))))"
 :unique nil)

(test-lambda-lift
 "(let ((fun (f (x Int) : Int) (+ x 1)) (val f 5)) (+ f 1))"
 "(let ((fun (f0 (x Int) : Int) (+ x 1)))
    (let ((val f 5))
      (+ f 1)))"
 :unique nil)

(test-lambda-lift
 "(let ((fun (f (x Int) : Int) (+ x 1)))
    (let ((fun (g (f Int) : Int) (* f 2))) (g (f 3))))"
 "(let ((fun (f0 (x Int) : Int) (+ x 1)))
    (let ((fun (g0 (f Int) : Int) (* f 2)))
      (g0 (f0 3))))"
 :unique nil)

(test-lambda-lift
 "(let ((fun (f (x Int) : Int) (+ x 1)))
    (unbox ($d f (box (3) [1 2 3] (Sigma ($n) [Int $n]))) (length f)))"
 "(let ((fun (f0 (x Int) : Int) (+ x 1)))
    (unbox ($d f (box (3) [1 2 3] (Sigma ($n) [Int $n])))
      (length f)))"
 :unique nil)

(test-lambda-lift
 "(let ((val a 3) (fun (f (x Int) : Int) (* x a)))
    (let ((fun (@g () () (f Int) : Int) (+ f 1))) (+ (g 2) (f 2))))"
 "(let ((fun (f0 (a (A Int (dims))) (x Int) : Int) (* x a)))
    (let ((val a 3))
      (let ((fun (@g () () (f Int) : Int) (+ f 1)))
        (+ (g 2) ((f0 a) 2)))))"
 :unique nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Outside the guard: the uses of a hoisted function would pass the
; variables it captures, so a function one of whose captured variables is
; bound again in its scope stays local, since at a use under that binder the
; variable means something else.  The binder may be in a later :LET, a
; later binding of the same :LET, or a parameter of a later binding.

(test-lambda-lift
 "(let ((val a 1) (fun (f (x Int) : Int) (+ x a)))
    (let ((val a 2)) (f 5)))"
 "(let ((val a 1) (fun (f (x Int) : Int) (+ x a)))
    (let ((val a 2)) (f 5)))"
 :unique nil)

(test-lambda-lift
 "(let ((val a 1) (fun (f (x Int) : Int) (+ x a)) (val a 2)) (f 5))"
 "(let ((val a 1) (fun (f (x Int) : Int) (+ x a)) (val a 2)) (f 5))"
 :unique nil)

(test-lambda-lift
 "(let ((val a 1)
        (fun (f (x Int) : Int) (+ x a))
        (fun (g (a Int) : Int) (f a)))
    (g 5))"
 "(let ((val a 1)
        (fun (f (x Int) : Int) (+ x a))
        (fun (g (a Int) : Int) (f a)))
    (g 5))"
 :unique nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; In a file, the definitions lifted out of a declaration go right before
; it, after the declarations they may refer to.

(test-lambda-lift-file
 "(def (val base 100))
  (def (fun (f (x Int) : Int) ((fn ((y Int)) (+ y base)) x)))
  (entry (main) (f 1))"
 "(def (val base 100))
  (def (fun (lam_0 (y Int)) (+ y base)))
  (def (fun (f (x Int) : Int) (lam_0 x)))
  (entry (main) (f 1))")

(test-lambda-lift-file
 "(def (fun (inc (x Int) : Int) (+ x 1)))
  (def (val k 5))
  (def (fun (g (w Int) : Int)
         (let ((fun (h (y Int) : Int) (inc (+ y k)))) (h w))))
  (entry (main) (g ((fn ((z Int)) (* z k)) 2)))"
 "(def (fun (inc (x Int) : Int) (+ x 1)))
  (def (val k 5))
  (def (fun (h0 (y Int) : Int) (inc (+ y k))))
  (def (fun (g (w Int) : Int) (h0 w)))
  (def (fun (lam_0 (z Int)) (* z k)))
  (entry (main) (g (lam_0 2)))")

; A file whose functions reuse a parameter name is uniquified first.

(test-lambda-lift-file
 "(def (fun (inc (x Int) : Int) (+ x 1)))
  (def (val k 5))
  (def (fun (g (x Int) : Int)
         (let ((fun (h (y Int) : Int) (inc (+ y k)))) (h x))))
  (entry (main) (g ((fn ((z Int)) (* z k)) 2)))"
 "(def (fun (inc (x Int) : Int) (+ x 1)))
  (def (val k 5))
  (def (fun (h0 (y Int) : Int) (inc (+ y k))))
  (def (fun (g (x0 Int) : Int) (h0 x0)))
  (def (fun (lam_0 (z Int)) (* z k)))
  (entry (main) (g (lam_0 2)))"
 :uniquify t)

; Definitions lifted out of a declaration that depend on each other, and on
; earlier declarations, come after what they depend on: H0 uses G0, which
; uses INC and BASE; the lambda in F uses H (so H0, passing the K that H
; captures) and BASE; the lambdas in Q and MAIN use C and INC.

(test-lambda-lift-file
 "(def (val base 100))
  (def (fun (inc (x Int) : Int) (+ x 1)))
  (def (fun (f (n Int) : Int)
         (let ((val k 3)
               (fun (g (y Int) : Int) (+ (inc y) base))
               (fun (h (z Int) : Int) (g (+ z k))))
           ((fn ((w Int)) (h (+ w base))) n))))
  (def (val c (f 1)))
  (def (fun (q (m Int) : Int) ((fn ((v Int)) (+ v c)) (f m))))
  (entry (main) (+ (q 2) ((fn ((u Int)) (inc u)) c)))"
 "(def (val base 100))
  (def (fun (inc (x Int) : Int) (+ x 1)))
  (def (fun (g0 (y Int) : Int) (+ (inc y) base)))
  (def (fun (h0 (k (A Int (dims))) (z Int) : Int) (g0 (+ z k))))
  (def (fun (lam_0 (k (A Int (dims))) (w Int)) ((h0 k) (+ w base))))
  (def (fun (f (n Int) : Int) (let ((val k 3)) ((lam_0 k) n))))
  (def (val c (f 1)))
  (def (fun (lam_1 (v Int)) (+ v c)))
  (def (fun (q (m Int) : Int) (lam_1 (f m))))
  (def (fun (lam_2 (u Int)) (inc u)))
  (entry (main) (+ (q 2) (lam_2 c)))")
