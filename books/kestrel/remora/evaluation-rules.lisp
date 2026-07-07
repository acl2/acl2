; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "evaluation")

(include-book "std/basic/ifix" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ evaluation-rules
  :parents (dynamic-semantics)
  :short "ACL2 rules to reason about Remora evaluation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a small start towards a comprehensive set of ACL2 rules
     to reason about Remora evaluation, e.g. for symbolic execution."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dims-of-expr-value-rules
  :short "Rules about the dimensions of expression values."

  (defruled dims-of-expr-value-when-base
    (implies (and (expr-value-wfp eval)
                  (expr-value-case eval :base))
             (equal (dims-of-expr-value eval)
                    nil))
    :enable (dims-of-expr-value
             check-dims-of-expr-value))

  (defruled dims-of-expr-value-when-primop
    (implies (expr-value-case eval :primop)
             (equal (dims-of-expr-value eval)
                    nil))
    :enable (dims-of-expr-value
             check-dims-of-expr-value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection fun-value-param-dims-rules
  :short "Rules about the dimensions of functions."

  (defruled fun-value-param-dims-of-int-add
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :int-add))
             (equal (fun-value-param-dims funval)
                    (list nil nil)))
    :enable (fun-value-param-dims
             expr-value-first-fun
             not-reserrp-when-expr-valuep
             type-of-primop-value-fun
             primop-value-funp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection lift-expr-value-to-frame-rules
  :short "Rules about lifting expression values."

  (defruled lift-expr-value-to-frame-nil-nil
    (equal (lift-expr-value-to-frame eval nil nil)
           (list (expr-value-fix eval)))
    :enable (lift-expr-value-to-frame
             cells-at-depth-in-expr-value
             repeat-each))

  (defruled lift-expr-value-list-to-frame-when-atom
    (implies (acl2::atom vals)
             (equal (lift-expr-value-list-to-frame vals frames pframe)
                    nil))
    :enable lift-expr-value-list-to-frame)

  (defruled lift-expr-value-list-to-frame-when-consp
    (implies (and (consp vals)
                  (consp frames)
                  (equal cells (lift-expr-value-to-frame (car vals)
                                                         (car frames)
                                                         pframe))
                  (expr-value-listp cells)
                  (equal cellss (lift-expr-value-list-to-frame (cdr vals)
                                                               (cdr frames)
                                                               pframe))
                  (expr-value-list-listp cellss))
             (equal (lift-expr-value-list-to-frame vals frames pframe)
                    (cons cells cellss)))
    :enable (lift-expr-value-list-to-frame
             not-reserrp-when-expr-value-listp
             not-reserrp-when-expr-value-list-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection eval-app-cell-rules
  :short "Rules about @(tsee eval-app-cell)."

  (defruled eval-app-cell-of-int-add
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :int-add)
                  (consp argvals)
                  (consp (cdr argvals))
                  (endp (cddr argvals))
                  (equal argval1 (first argvals))
                  (equal argval2 (second argvals))
                  (expr-value-case argval1 :base)
                  (expr-value-case argval2 :base)
                  (equal baseval1 (expr-value-base->val argval1))
                  (equal baseval2 (expr-value-base->val argval2))
                  (base-value-case baseval1 :int)
                  (base-value-case baseval2 :int)
                  (equal intval1 (base-value-int->val baseval1))
                  (equal intval2 (base-value-int->val baseval2))
                  (not (zp limit)))
             (equal (eval-app-cell funval argvals denv limit)
                    (expr-value-base
                     (base-value-int
                      (int-value (+ (int-value->int intval1)
                                    (int-value->int intval2)))))))
    :enable (eval-app-cell
             eval-primop-fun
             primop-value-funp
             prim-int-add
             arity-of-primop-value-fun
             type-of-primop-value-fun
             len
             check-expr-value-int
             not-reserrp-when-int-valuep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection eval-app-rules
  :short "Rules about @(tsee eval-app)."

  (defruled eval-app-list-when-atom
    (implies (and (acl2::atom funvals)
                  (not (zp limit)))
             (equal (eval-app-list funvals argvalss denv limit)
                    nil))
    :enable eval-app-list)

  (defruled eval-app-list-when-consp
    (implies (and (consp funvals)
                  (not (zp limit))
                  (expr-value-list-listp argvalss)
                  (expr-value-list-list-wfp argvalss)
                  (cons-listp argvalss)
                  (equal argvals (car-list argvalss))
                  (expr-value-list-wfp argvals)
                  (equal val (eval-app-cell (car funvals)
                                            argvals
                                            denv
                                            (1- limit)))
                  (expr-valuep val)
                  (equal vals (eval-app-list (cdr funvals)
                                             (cdr-list argvalss)
                                             denv
                                             (1- limit)))
                  (expr-value-listp vals))
             (equal (eval-app-list funvals argvalss denv limit)
                    (cons val vals)))
    :enable (eval-app-list
             not-reserrp-when-expr-valuep
             not-reserrp-when-expr-value-listp))

  (defruled eval-app-of-int-add-no-lifting
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :int-add)
                  (expr-value-list-wfp argvals)
                  (consp argvals)
                  (consp (cdr argvals))
                  (endp (cddr argvals))
                  (equal argval1 (first argvals))
                  (equal argval2 (second argvals))
                  (expr-value-case argval1 :base)
                  (expr-value-case argval2 :base)
                  (equal baseval1 (expr-value-base->val argval1))
                  (equal baseval2 (expr-value-base->val argval2))
                  (base-value-case baseval1 :int)
                  (base-value-case baseval2 :int)
                  (equal intval1 (base-value-int->val baseval1))
                  (equal intval2 (base-value-int->val baseval2))
                  (integerp limit)
                  (>= limit 3))
             (equal (eval-app funval argvals denv limit)
                    (expr-value-base
                     (base-value-int
                      (int-value (+ (int-value->int intval1)
                                    (int-value->int intval2)))))))
    :enable (eval-app
             fun-value-param-dims-of-int-add
             len
             dims-of-expr-value-list
             dims-of-expr-value-when-base
             dims-of-expr-value-when-primop
             lift-expr-value-to-frame-nil-nil
             lift-expr-value-list-to-frame-when-atom
             lift-expr-value-list-to-frame-when-consp
             not-reserrp-when-expr-value-listp
             not-reserrp-when-expr-value-list-listp
             eval-app-list-when-atom
             eval-app-list-when-consp
             car-list
             eval-app-cell-of-int-add
             expr-value-with-nonempty-dims)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection eval-expr-rules
  :short "Rules about @(tsee eval-expr)."

  (defruled eval-expr-when-var
    (implies (and (expr-case expr :var)
                  (not (zp limit)))
             (equal (eval-expr expr denv limit)
                    (denv-lookup-expr-var (expr-var->name expr) denv)))
    :enable eval-expr)

  (defruled eval-expr-when-app
    (implies (and (expr-case expr :app)
                  (not (zp limit))
                  (equal funval
                         (eval-expr (expr-app->fun expr) denv (1- limit)))
                  (expr-valuep funval)
                  (equal argvals
                         (eval-expr-list (expr-app->args expr) denv (1- limit)))
                  (expr-value-listp argvals))
             (equal (eval-expr expr denv limit)
                    (eval-app funval argvals denv (1- limit))))
    :enable (eval-expr
             not-reserrp-when-expr-valuep
             not-reserrp-when-expr-value-listp))

  (defruled eval-expr-list-when-atom
    (implies (and (acl2::atom exprs)
                  (not (zp limit)))
             (equal (eval-expr-list exprs denv limit)
                    nil))
    :enable (eval-expr-list))

  (defruled eval-expr-list-when-consp
    (implies (and (consp exprs)
                  (not (zp limit))
                  (equal val (eval-expr (car exprs) denv (1- limit)))
                  (expr-valuep val)
                  (equal vals (eval-expr-list (cdr exprs) denv (1- limit)))
                  (expr-value-listp vals))
             (equal (eval-expr-list exprs denv limit)
                    (cons val vals)))
    :enable (eval-expr-list
             not-reserrp-when-expr-valuep
             not-reserrp-when-expr-value-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection eval-rules
  :short "Ruleset for evaluation."

  (def-ruleset eval-rules
    '(eval-expr-when-var
      eval-expr-when-app
      eval-expr-list-when-atom
      eval-expr-list-when-consp
      eval-app-of-int-add-no-lifting
      not-reserrp-when-expr-valuep
      acl2::ifix-when-integerp)))
