; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "lambda-lifting-validation")
(include-book "parser-interface")

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of the typing of values in LAMBDA-LIFTING-VALIDATION, on which its
; hypothesis CHECK-SOUND-P rests.  They are evidence that the typing is
; neither too strict (a value a checked program evaluates to has the type the
; checker gives the program, as CHECK-SOUND-P claims) nor too lax (a value
; does not have an inequivalent type).

; The value of a checked program has the checked type.

(defmacro test-typed (code)
  `(assert!
    (b* ((ast (parse-top-exp-from-string ,code))
         ((when (reserrp ast)) nil)
         (tast (check-top-expr ast))
         ((when (reserrp tast)) nil)
         (val (eval-top-expr (type+expr->expr tast) 100000))
         ((when (reserrp val)) nil)
         (tval (eval-type (type+expr->type tast)
                          (expr-denv->tenv (init-expr-denv))))
         ((when (reserrp tval)) nil))
      (expr-value-typed-p val tval))))

; The value of the first program does not have the type of the second.

(defmacro test-not-typed (code other)
  `(assert!
    (b* ((ast (parse-top-exp-from-string ,code))
         ((when (reserrp ast)) nil)
         (tast (check-top-expr ast))
         ((when (reserrp tast)) nil)
         (val (eval-top-expr (type+expr->expr tast) 100000))
         ((when (reserrp val)) nil)
         (other (parse-top-exp-from-string ,other))
         ((when (reserrp other)) nil)
         (otast (check-top-expr other))
         ((when (reserrp otast)) nil)
         (otval (eval-type (type+expr->type otast)
                           (expr-denv->tenv (init-expr-denv))))
         ((when (reserrp otval)) nil))
      (not (expr-value-typed-p val otval)))))

; The bindings of a checked top-level :LET evaluate to an environment typed
; by the static environments the checker extends the initial ones to.

(defmacro test-binds-typed (code)
  `(assert!
    (b* ((ast (parse-top-exp-from-string ,code))
         ((when (reserrp ast)) nil)
         ((unless (expr-case ast :let)) nil)
         (binds (expr-let->binds ast))
         (senvs (check-bind-list binds
                                 (init-ispace-senv)
                                 (init-type-senv)
                                 (init-expr-senv)))
         ((when (reserrp senvs)) nil)
         (denv (eval-bind-list binds (init-expr-denv) 100000))
         ((when (reserrp denv)) nil))
      (and (expr-denv-typed-p denv
                              (senvs+binds->ienv senvs)
                              (senvs+binds->tenv senvs)
                              (senvs+binds->eenv senvs))
           (expr-denv-typed-for-p denv
                                  (senvs+binds->ienv senvs)
                                  (senvs+binds->tenv senvs)
                                  (senvs+binds->eenv senvs)
                                  (bind-list-bound-expr-vars binds))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Data.

(test-typed "5")
(test-typed "1.5")
(test-typed "#t")
(test-typed "[1 2 3]")
(test-typed "[[1 2] [3 4]]")
(test-typed "(array [0] Int)")
(test-typed "(box (3) [1 2 3] (Sigma ($n) [Int $n]))")

; Closures: lambdas, with and without captured variables, curried ones,
; local functions, and type and ispace lambdas.

(test-typed "(fn ((y Int)) (+ y 1))")
(test-typed "(let ((val x 1)) (fn ((y Int)) (+ x y)))")
(test-typed "(fn ((x Int) (y Int)) (+ x y))")
(test-typed "(let ((val a 10) (fun (f (x Int) : Int) (+ x a))) f)")
(test-typed "(t-fn (&t) (fn ((x &t)) x))")
(test-typed "(i-fn ($d) (fn ((x (A Int $d))) x))")
(test-typed "[(fn ((y Int)) y) (fn ((y Int)) (+ y 1))]")

; Primitive operations, also partially applied.

(test-typed "+")
(test-typed "length")
(test-typed "(+ 1)")

; Values do not have inequivalent types.

(test-not-typed "5" "[1 2 3]")
(test-not-typed "[1 2 3]" "[1 2]")
(test-not-typed "1.5" "1")
(test-not-typed "(fn ((y Int)) (+ y 1))" "(fn ((y Int)) #t)")
(test-not-typed "(fn ((y Int)) (+ y 1))" "(fn ((y Bool)) 1)")
(test-not-typed "(fn ((y Int)) [y y])" "(fn ((y Int)) y)")

; Bindings, including type definitions.

(test-binds-typed
 "(let ((val x [1 2 3]) (fun (f (y Int) : Int) (+ y 1)) (val z (f x))) z)")
(test-binds-typed
 "(let ((type &t Int) (fun (g (y &t)) y) (val w (g 4))) w)")
