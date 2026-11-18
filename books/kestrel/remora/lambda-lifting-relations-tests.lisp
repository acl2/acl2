; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "lambda-lifting-relations")
(include-book "parser-interface")

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of the relations of LAMBDA-LIFTING-RELATIONS: a program that
; evaluates to a closure, and its lambda-lifted form, evaluate to values
; that the relation relates, via a witness built here from the context of
; the traversal at the closure's body, with the definitions bound as at the
; top of the lifted program.  The witnesses cover a lifted lambda, a lifted
; lambda partially applied, a hoisted local function, a kept lambda, and a
; lifted lambda that refers to a hoisted local function (whose environment
; binds the function in the original program, and its replacement's
; variables in the lifted one).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The checked, annotated form of a program.

(defun prog-expr (code)
  (declare (xargs :mode :program))
  (type+expr->expr (check-top-expr (parse-top-exp-from-string code))))

; The environment at the top of the lifted program, binding the definitions.

(defun lifted-genv (expr)
  (declare (xargs :mode :program))
  (b* (((mv & lifted &)
        (ll-expr expr nil nil nil nil (expr-all-expr-vars expr))))
    (eval-bind-list lifted (init-expr-denv) 100000)))

; Whether a program and its lifted form evaluate to related values.

(defun rel-check (code w)
  (declare (xargs :mode :program))
  (b* ((expr (prog-expr code))
       (val (eval-top-expr expr 100000))
       (new-val (eval-top-expr (lambda-lift-top-expr expr) 100000)))
    (and (not (reserrp val))
         (not (reserrp new-val))
         (expr-value-ll-related-p new-val val w (lifted-genv expr)))))

(defun ctx (code tenv tlets locals)
  (declare (xargs :mode :program))
  (make-ll-context :tenv tenv :tlets tlets :locals locals :lmap nil
                   :used (expr-all-expr-vars (prog-expr code))))

(defun lw (ctx prest flat)
  (declare (xargs :mode :program))
  (make-ll-value-witness-lambda
   :ctx ctx :prest prest :flat flat
   :denv (make-ll-denv-witness :vals nil :limit 0)))

(defconst *int* (type-base (base-type-int)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A lifted lambda that captures a variable bound by a :LET, whose type is
; inferred.

(defconst *t1* "(let ((val x 1)) (fn ((y Int)) (+ x y)))")

(defun t1-ctx ()
  (declare (xargs :mode :program))
  (b* ((expr (prog-expr *t1*))
       (b (car (expr-let->binds expr)))
       ((mv tenv tlets) (extend-tenv-with-let-bind b nil nil nil))
       (a (expr-atom->atom (expr-let->body expr)))
       (params (list (atom-lambda->param a))))
    (make-ll-context :tenv (extend-tenv-with-params params tenv)
                     :tlets (tlets-without (list "y") tlets)
                     :locals (set::insert "y" (set::insert "x" nil))
                     :lmap nil
                     :used (expr-all-expr-vars expr))))

(defconst *w1* (lw (t1-ctx) nil t))

(assert! (rel-check *t1* *w1*))

; The same witness does not relate the lifted value to that of a program
; that captures a different value.

(defconst *t1b* "(let ((val x 2)) (fn ((y Int)) (+ x y)))")

(assert! (not (expr-value-ll-related-p
               (eval-top-expr (lambda-lift-top-expr (prog-expr *t1*)) 100000)
               (eval-top-expr (prog-expr *t1b*) 100000)
               *w1*
               (lifted-genv (prog-expr *t1*)))))

; A lambda inside a lambda, applied to its first argument: each lambda is
; lifted (the type checker annotates them, so the chain is not flattened),
; and the inner one's body refers to the definition of the innermost one.

(defconst *t2*
  "((fn ((x Int)) (fn ((y Int)) (fn ((z Int)) (+ x (+ y z))))) 3)")

(assert! (rel-check *t2*
                    (lw (ctx *t2*
                             (omap::update "x" *int* (omap::update "y" *int* nil))
                             nil
                             (set::insert "x" (set::insert "y" nil)))
                        nil t)))

; A hoisted local function.

(defconst *t3* "(let ((val a 10) (fun (f (x Int) : Int) (+ x a))) f)")

(defun t3-ctx ()
  (declare (xargs :mode :program))
  (b* ((expr (prog-expr *t3*))
       (b (car (expr-let->binds expr)))
       ((mv tenv tlets) (extend-tenv-with-let-bind b nil nil nil)))
    (ctx *t3* (omap::update "x" *int* tenv) tlets
         (set::insert "a" (set::insert "x" nil)))))

(assert! (rel-check *t3* (lw (t3-ctx) nil nil)))

; A kept lambda, open in a type variable.

(defconst *t4* "(t-app (t-fn (&t) (fn ((x &t)) x)) Int)")

(assert! (rel-check *t4*
                    (lw (ctx *t4*
                             (omap::update "x" (type-var (type-var-atom "t")) nil)
                             nil
                             (set::insert "x" nil))
                        nil nil)))

; A lifted lambda that refers to a hoisted local function: the original
; closure's environment binds the function, and the lifted one's binds the
; variables of the function's replacement, which evaluates to a related
; value.

(defconst *t5*
  "(let ((val a 10) (fun (f (x Int) : Int) (+ x a))) (fn ((y Int)) (f y)))")

(defun t5-w ()
  (declare (xargs :mode :program))
  (b* ((expr (prog-expr *t5*))
       (used (expr-all-expr-vars expr))
       (binds (expr-let->binds expr))
       ((mv tenv1 tlets1)
        (extend-tenv-with-let-bind (car binds) nil nil nil))
       (fctx (make-ll-context :tenv (omap::update "x" *int* tenv1)
                              :tlets tlets1
                              :locals (set::insert "a" (set::insert "x" nil))
                              :lmap nil
                              :used used))
       ((mv & & tenv locals lmap & tlets)
        (ll-let-binds binds (expr-expr-var-binders (expr-let->body expr))
                      nil nil nil nil used))
       (ctx (make-ll-context :tenv (omap::update "y" *int* tenv)
                             :tlets (tlets-without (list "y") tlets)
                             :locals (set::insert "y" locals)
                             :lmap lmap
                             :used used)))
    (make-ll-value-witness-lambda
     :ctx ctx :prest nil :flat t
     :denv (make-ll-denv-witness
            :vals (omap::update "f" (lw fctx nil nil) nil)
            :limit 100))))

(assert! (rel-check *t5* (t5-w)))
