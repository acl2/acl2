; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "lambda-lifting-free-variables")
(include-book "evaluation")

(include-book "portcullis")

(local (include-book "std/basic/inductions" :dir :system))

(local (in-theory (disable (:e tau-system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lambda-lifting-evaluation
  :parents (lambda-lifting)
  :short "Evaluation of the syntax that lambda lifting builds."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lambda lifting replaces a lambda by a reference to its lifted
     definition: the definition's fresh name applied to the variables the
     lambda captured (see @(tsee emit-lifted-lambda)), built by @(tsee
     apply-to-names) from the variable expressions @(tsee names-to-exprs)
     makes.  This book says how the evaluator (see @(see evaluation)) treats
     that syntax: a list of variable expressions evaluates to the values of
     the variables, in order, looked up by @(tsee expr-denv-lookup-exprs)
     (@(tsee eval-expr-list-of-names-to-exprs)); an expression applied to
     variables evaluates to the function value applied to those values
     (@(tsee eval-expr-of-apply-to-names)), whether the application is the
     unary @(':app') or the n-ary @(':appn'); and so the reference that
     replaces a lifted lambda evaluates to the definition's value applied
     to the values of the captured variables, or to the definition's value
     itself when nothing is captured (@(tsee
     eval-expr-of-e-of-emit-lifted-lambda)).  The fuel conditions are the
     ones the evaluator's structure imposes: one unit for each level of
     nesting.")
   (xdoc::p
    "These are the evaluation facts about the pieces the transformation
     introduces, together with the free-variable facts of @(see
     lambda-lifting-free-variables).  What they do not yet give is the
     preservation of evaluation by the traversal @(tsee ll-expr) itself,
     the analogue of @(tsee eval-type-of-type-rename-ispace-vars) for
     renaming (see @(see renaming-evaluation)).  Unlike renaming, lifting
     changes the shape of the values: a lambda evaluates to a closure over
     the environment at its position, while its replacement evaluates to a
     partial application of the lifted definition's closure, whose
     environment is the one at the top and which takes the captured
     variables as arguments.  Relating the two calls for a simulation
     relation between expression values that identifies such closures up
     to the captured environment, in the manner of @(tsee
     expr-value-alpha-related-via-p) for renaming, and an induction over
     the evaluator with it.  The relation is in @(see
     lambda-lifting-relations); the induction is future work."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Evaluation of the syntax the transformation builds.


(define expr-denv-lookup-exprs ((names string-listp) (denv expr-denvp))
  :returns (vals expr-value-list-resultp
                 :hints (("Goal"
                          :induct t
                          :in-theory (enable expr-valuep-when-result-not-error
                                             expr-value-listp-when-result-not-error))))
  :short "Look up a list of expression variables in an expression dynamic
          environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the list of their values, in order,
     or an error if any is not in the environment."))
  (b* (((when (endp names)) nil)
       ((ok val) (expr-denv-lookup-expr (car names) denv))
       ((ok vals) (expr-denv-lookup-exprs (cdr names) denv)))
    (cons val vals))
  ///
  (defret len-of-expr-denv-lookup-exprs
    (implies (not (reserrp vals))
             (equal (len vals) (len names)))
    :hints (("Goal" :induct t :in-theory (enable len)))))

(defrule eval-expr-of-expr-var
  (equal (eval-expr (expr-var name) denv limit)
         (if (zp limit)
             (reserr :limit)
           (expr-denv-lookup-expr name denv)))
  :expand ((eval-expr (expr-var name) denv limit)))

(defrule eval-expr-list-of-names-to-exprs
  (implies (< (len names) (nfix limit))
           (equal (eval-expr-list (names-to-exprs names) denv limit)
                  (expr-denv-lookup-exprs names denv)))
  :induct (acl2::cdr-dec-induct names limit)
  :enable (names-to-exprs expr-denv-lookup-exprs len)
  :expand ((:free (a l) (eval-expr-list (cons a l) denv limit))
           (eval-expr-list nil denv limit)))

(defrule apply-to-names-when-not-consp
  (implies (not (consp names))
           (equal (apply-to-names fun names)
                  (expr-fix fun)))
  :enable apply-to-names)

(defruled eval-expr-of-apply-to-names-when-one-name
  (implies (and (consp names)
                (not (consp (cdr names)))
                (< 1 (nfix limit)))
           (equal (eval-expr (apply-to-names fun names) denv limit)
                  (b* (((ok funval) (eval-expr fun denv (1- limit)))
                       ((ok argvals) (expr-denv-lookup-exprs names denv)))
                    (eval-app funval argvals (1- limit)))))
  :do-not-induct t
  :enable (apply-to-names nfix
           not-reserrp-when-expr-valuep
           not-reserrp-when-expr-value-listp
           expr-valuep-when-result-not-error
           expr-value-listp-when-result-not-error)
  :expand ((:free (f a) (eval-expr (expr-app f a) denv limit))
           (expr-denv-lookup-exprs names denv)
           (expr-denv-lookup-exprs (cdr names) denv)))

(defruled eval-expr-of-apply-to-names-when-more-names
  (implies (and (consp (cdr names))
                (< (1+ (len names)) (nfix limit)))
           (equal (eval-expr (apply-to-names fun names) denv limit)
                  (b* (((ok funval) (eval-expr fun denv (1- limit)))
                       ((ok argvals) (expr-denv-lookup-exprs names denv)))
                    (eval-app funval argvals (1- limit)))))
  :do-not-induct t
  :use ((:instance eval-expr-list-of-names-to-exprs (limit (1- limit))))
  :enable (apply-to-names nfix
           not-reserrp-when-expr-valuep
           not-reserrp-when-expr-value-listp
           expr-valuep-when-result-not-error
           expr-value-listp-when-result-not-error)
  :disable (eval-expr-list-of-names-to-exprs len)
  :expand ((len names)
           (len (cdr names))
           (:free (f as) (eval-expr (expr-appn f as) denv limit))))

(defrule eval-expr-of-apply-to-names
  (implies (and (consp names)
                (< (1+ (len names)) (nfix limit)))
           (equal (eval-expr (apply-to-names fun names) denv limit)
                  (b* (((ok funval) (eval-expr fun denv (1- limit)))
                       ((ok argvals) (expr-denv-lookup-exprs names denv)))
                    (eval-app funval argvals (1- limit)))))
  :do-not-induct t
  :use (eval-expr-of-apply-to-names-when-one-name
        eval-expr-of-apply-to-names-when-more-names)
  :enable (nfix consp-when-positive-len positive-len-when-consp)
  :disable len)

; The reference that replaces a lifted lambda evaluates by looking up the
; definition's name and the captured variables and applying the one to the
; others.

(defrule eval-expr-of-e-of-emit-lifted-lambda
  (b* (((mv e & &) (emit-lifted-lambda params body type? tenv locals used))
       (name (fresh-expr-var "lam_" (string-sfix used)))
       (fv (set::intersect
            (set::difference (expr-free-expr-vars body)
                             (set::mergesort (var+type?-list->var params)))
            locals)))
    (implies (and (consp (mv-nth 1 (emit-lifted-lambda params body type?
                                                       tenv locals used)))
                  (< (1+ (len fv)) (nfix limit)))
             (equal (eval-expr e denv limit)
                    (if (consp fv)
                        (b* (((ok funval) (expr-denv-lookup-expr name denv))
                             ((ok argvals) (expr-denv-lookup-exprs fv denv)))
                          (eval-app funval argvals (1- limit)))
                      (expr-denv-lookup-expr name denv)))))
  :do-not-induct t
  :use ((:instance eval-expr-of-apply-to-names
                   (fun (expr-var (fresh-expr-var "lam_" (string-sfix used))))
                   (names (set::intersect
                           (set::difference
                            (expr-free-expr-vars body)
                            (set::mergesort (var+type?-list->var params)))
                           locals))))
  :enable (emit-lifted-lambda nfix)
  :disable (len
            set::intersect-under-set-equiv
            set::difference-under-set-equiv
            set::mergesort-under-set-equiv))
