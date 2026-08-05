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

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

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
             expr-value-wfp)
    :expand ((check-dims-of-expr-value eval)))

  (defruled expr-value-wfp-when-base
    (implies (expr-value-case val :base)
             (expr-value-wfp val))
    :enable (expr-value-wfp
             check-dims-of-expr-value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection fun-value-param-dims-rules
  :short "Rules about the dimensions of functions."

  (defruled fun-value-param-dims-of-int-binary
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :int-binary))
             (equal (fun-value-param-dims funval)
                    (list nil nil)))
    :enable (fun-value-param-dims
             expr-value-first-fun
             not-reserrp-when-expr-valuep
             type-of-primop-value-fun
             primop-value-funp))

  (defruled fun-value-param-dims-of-int-binary-x
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :int-binary-x))
             (equal (fun-value-param-dims funval)
                    (list nil)))
    :enable (fun-value-param-dims
             expr-value-first-fun
             not-reserrp-when-expr-valuep
             type-of-primop-value-fun
             primop-value-funp))

  (defruled fun-value-param-dims-of-float-binary
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary))
             (equal (fun-value-param-dims funval)
                    (list nil nil)))
    :enable (fun-value-param-dims
             expr-value-first-fun
             not-reserrp-when-expr-valuep
             type-of-primop-value-fun
             primop-value-funp))

  (defruled fun-value-param-dims-of-float-binary-x
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary-x))
             (equal (fun-value-param-dims funval)
                    (list nil)))
    :enable (fun-value-param-dims
             expr-value-first-fun
             not-reserrp-when-expr-valuep
             type-of-primop-value-fun
             primop-value-funp))

  (defruled fun-value-param-dims-of-reshape
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :reshape-t-s1-s2))
             (equal (fun-value-param-dims funval)
                    (list (primop-value-reshape-t-s1-s2->s1val opval))))
    :enable (fun-value-param-dims
             expr-value-first-fun
             not-reserrp-when-expr-valuep
             type-of-primop-value-fun
             primop-value-funp
             nest-function-type-values
             arrow-type-value-inputs
             dims-of-type-value-list
             dims-of-type-value)))

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

  (defruled eval-app-cell-of-int-binary
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :int-binary)
                  (integerp limit)
                  (>= limit 2))
             (equal (eval-app-cell funval argval limit)
                    (expr-value-primop
                     (make-primop-value-int-binary-x
                      :op (primop-value-int-binary->op opval)
                      :xval argval))))
    :expand (eval-app-cell funval argval limit)
    :enable (eval-primop-fun
             eval-primop-fun-fo
             primop-value-funp
             primop-value-fun-fo-p))

  (defruled eval-app-cell-of-int-binary-x-add
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :int-binary-x)
                  (equal op (primop-value-int-binary-x->op opval))
                  (int-binary-primop-case op :add)
                  (equal xval (primop-value-int-binary-x->xval opval))
                  (expr-value-case xval :base)
                  (expr-value-case argval :base)
                  (equal baseval1 (expr-value-base->val xval))
                  (equal baseval2 (expr-value-base->val argval))
                  (base-value-case baseval1 :int)
                  (base-value-case baseval2 :int)
                  (equal intval1 (base-value-int->val baseval1))
                  (equal intval2 (base-value-int->val baseval2))
                  (integerp limit)
                  (>= limit 2))
             (equal (eval-app-cell funval argval limit)
                    (expr-value-base
                     (base-value-int
                      (int-value (+ (int-value->int intval1)
                                    (int-value->int intval2)))))))
    :expand (eval-app-cell funval argval limit)
    :enable (eval-primop-fun
             eval-primop-fun-fo
             primop-value-funp
             primop-value-fun-fo-p
             prim-int-add
             check-expr-value-int
             not-reserrp-when-int-valuep))

  (defruled eval-app-cell-of-float-binary
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary)
                  (integerp limit)
                  (>= limit 2))
             (equal (eval-app-cell funval argval limit)
                    (expr-value-primop
                     (make-primop-value-float-binary-x
                      :op (primop-value-float-binary->op opval)
                      :xval argval))))
    :expand (eval-app-cell funval argval limit)
    :enable (eval-primop-fun
             eval-primop-fun-fo
             primop-value-funp
             primop-value-fun-fo-p))

  (defruled eval-app-cell-of-float-binary-x-add
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary-x)
                  (equal op (primop-value-float-binary-x->op opval))
                  (float-binary-primop-case op :add)
                  (equal xval (primop-value-float-binary-x->xval opval))
                  (expr-value-case xval :base)
                  (expr-value-case argval :base)
                  (equal baseval1 (expr-value-base->val xval))
                  (equal baseval2 (expr-value-base->val argval))
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (integerp limit)
                  (>= limit 2))
             (equal (eval-app-cell funval argval limit)
                    (expr-value-base
                     (base-value-float
                      (float-value-ratio (+ (float-value-ratio->ratio floatval1)
                                            (float-value-ratio->ratio floatval2)))))))
    :expand (eval-app-cell funval argval limit)
    :enable (eval-primop-fun
             eval-primop-fun-fo
             primop-value-funp
             primop-value-fun-fo-p
             prim-float-add
             check-expr-value-float
             not-reserrp-when-float-valuep))

  (defruled eval-app-cell-of-float-binary-x-sub
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary-x)
                  (equal op (primop-value-float-binary-x->op opval))
                  (float-binary-primop-case op :sub)
                  (equal xval (primop-value-float-binary-x->xval opval))
                  (expr-value-case xval :base)
                  (expr-value-case argval :base)
                  (equal baseval1 (expr-value-base->val xval))
                  (equal baseval2 (expr-value-base->val argval))
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (integerp limit)
                  (>= limit 2))
             (equal (eval-app-cell funval argval limit)
                    (expr-value-base
                     (base-value-float
                      (float-value-ratio (- (float-value-ratio->ratio floatval1)
                                            (float-value-ratio->ratio floatval2)))))))
    :expand (eval-app-cell funval argval limit)
    :enable (eval-primop-fun
             eval-primop-fun-fo
             primop-value-funp
             primop-value-fun-fo-p
             prim-float-sub
             check-expr-value-float
             not-reserrp-when-float-valuep))

  (defruled eval-app-cell-of-float-binary-x-mul
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary-x)
                  (equal op (primop-value-float-binary-x->op opval))
                  (float-binary-primop-case op :mul)
                  (equal xval (primop-value-float-binary-x->xval opval))
                  (expr-value-case xval :base)
                  (expr-value-case argval :base)
                  (equal baseval1 (expr-value-base->val xval))
                  (equal baseval2 (expr-value-base->val argval))
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (equal rat1 (float-value-ratio->ratio floatval1))
                  (equal rat2 (float-value-ratio->ratio floatval2))
                  (integerp limit)
                  (>= limit 2))
             (equal (eval-app-cell funval argval limit)
                    (expr-value-base
                     (base-value-float
                      (if (or (and (equal rat1 0) (< rat2 0))
                              (and (< rat1 0) (equal rat2 0)))
                          (float-value-neg0)
                        (float-value-ratio (* rat1 rat2)))))))
    :expand (eval-app-cell funval argval limit)
    :enable (eval-primop-fun
             eval-primop-fun-fo
             primop-value-funp
             primop-value-fun-fo-p
             prim-float-mul
             check-expr-value-float
             not-reserrp-when-float-valuep
             rfix
             xor
             fix))

  (defruled eval-app-cell-of-float-binary-x-div
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary-x)
                  (equal op (primop-value-float-binary-x->op opval))
                  (float-binary-primop-case op :div)
                  (equal xval (primop-value-float-binary-x->xval opval))
                  (expr-value-case xval :base)
                  (expr-value-case argval :base)
                  (equal baseval1 (expr-value-base->val xval))
                  (equal baseval2 (expr-value-base->val argval))
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (equal rat1 (float-value-ratio->ratio floatval1))
                  (equal rat2 (float-value-ratio->ratio floatval2))
                  (not (equal rat2 0))
                  (integerp limit)
                  (>= limit 2))
             (equal (eval-app-cell funval argval limit)
                    (expr-value-base
                     (base-value-float
                      (if (and (equal rat1 0) (< rat2 0))
                          (float-value-neg0)
                        (float-value-ratio (/ rat1 rat2)))))))
    :expand (eval-app-cell funval argval limit)
    :enable (eval-primop-fun
             eval-primop-fun-fo
             primop-value-funp
             primop-value-fun-fo-p
             prim-float-div
             check-expr-value-float
             not-reserrp-when-float-valuep
             xor
             rfix))

  (defruled eval-app-cell-of-float-binary-x-expt
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary-x)
                  (equal op (primop-value-float-binary-x->op opval))
                  (float-binary-primop-case op :expt)
                  (equal xval (primop-value-float-binary-x->xval opval))
                  (expr-value-case xval :base)
                  (expr-value-case argval :base)
                  (equal baseval1 (expr-value-base->val xval))
                  (equal baseval2 (expr-value-base->val argval))
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (equal rat1 (float-value-ratio->ratio floatval1))
                  (equal rat2 (float-value-ratio->ratio floatval2))
                  (integerp rat2)
                  (integerp limit)
                  (>= limit 2))
             (equal (eval-app-cell funval argval limit)
                    (expr-value-base
                     (base-value-float
                      (if (and (equal rat1 0) (< rat2 0))
                          (float-value-posinf)
                        (float-value-ratio (expt rat1 rat2)))))))
    :expand (eval-app-cell funval argval limit)
    :enable (eval-primop-fun
             eval-primop-fun-fo
             primop-value-funp
             primop-value-fun-fo-p
             prim-float-expt
             check-expr-value-float
             not-reserrp-when-float-valuep
             rfix))

  (defruled eval-app-cell-of-float-binary-x-max
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary-x)
                  (equal op (primop-value-float-binary-x->op opval))
                  (float-binary-primop-case op :max)
                  (equal xval (primop-value-float-binary-x->xval opval))
                  (expr-value-case xval :base)
                  (expr-value-case argval :base)
                  (equal baseval1 (expr-value-base->val xval))
                  (equal baseval2 (expr-value-base->val argval))
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (integerp limit)
                  (>= limit 2))
             (equal (eval-app-cell funval argval limit)
                    (expr-value-base
                     (base-value-float
                      (float-value-ratio (max (float-value-ratio->ratio floatval1)
                                              (float-value-ratio->ratio floatval2)))))))
    :expand (eval-app-cell funval argval limit)
    :enable (eval-primop-fun
             eval-primop-fun-fo
             primop-value-funp
             primop-value-fun-fo-p
             prim-float-max
             check-expr-value-float
             not-reserrp-when-float-valuep
             max
             rfix))

  (defruled eval-app-cell-of-float-binary-x-min
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary-x)
                  (equal op (primop-value-float-binary-x->op opval))
                  (float-binary-primop-case op :min)
                  (equal xval (primop-value-float-binary-x->xval opval))
                  (expr-value-case xval :base)
                  (expr-value-case argval :base)
                  (equal baseval1 (expr-value-base->val xval))
                  (equal baseval2 (expr-value-base->val argval))
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (integerp limit)
                  (>= limit 2))
             (equal (eval-app-cell funval argval limit)
                    (expr-value-base
                     (base-value-float
                      (float-value-ratio (min (float-value-ratio->ratio floatval1)
                                              (float-value-ratio->ratio floatval2)))))))
    :expand (eval-app-cell funval argval limit)
    :enable (eval-primop-fun
             eval-primop-fun-fo
             primop-value-funp
             primop-value-fun-fo-p
             prim-float-min
             check-expr-value-float
             not-reserrp-when-float-valuep
             min
             rfix))

  (defruled eval-app-cell-of-reshape
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :reshape-t-s1-s2)
                  (integerp limit)
                  (>= limit 2))
             (equal (eval-app-cell funval argval limit)
                    (prim-reshape
                     (primop-value-reshape-t-s1-s2->tval opval)
                     (primop-value-reshape-t-s1-s2->s1val opval)
                     (primop-value-reshape-t-s1-s2->s2val opval)
                     argval)))
    :expand (eval-app-cell funval argval limit)
    :enable (eval-primop-fun
             eval-primop-fun-fo
             primop-value-funp
             primop-value-fun-fo-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection eval-app-rules
  :short "Rules about @(tsee eval-app)."

  (defruled eval-app-list-when-atom
    (implies (and (acl2::atom funvals)
                  (not (zp limit)))
             (equal (eval-app-list funvals argvals limit)
                    nil))
    :enable eval-app-list)

  (defruled eval-app-list-when-consp
    (implies (and (consp funvals)
                  (not (zp limit))
                  (consp argvals)
                  (expr-value-wfp (car argvals))
                  (equal val (eval-app-cell (car funvals)
                                            (car argvals)
                                            (1- limit)))
                  (expr-valuep val)
                  (equal vals (eval-app-list (cdr funvals)
                                             (cdr argvals)
                                             (1- limit)))
                  (expr-value-listp vals))
             (equal (eval-app-list funvals argvals limit)
                    (cons val vals)))
    :enable (eval-app-list
             not-reserrp-when-expr-valuep
             not-reserrp-when-expr-value-listp))

  (defruled eval-app-of-int-add-no-lifting
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :int-binary)
                  (equal op (primop-value-int-binary->op opval))
                  (int-binary-primop-case op :add)
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
                  (>= limit 5))
             (equal (eval-app funval argvals limit)
                    (expr-value-base
                     (base-value-int
                      (int-value (+ (int-value->int intval1)
                                    (int-value->int intval2)))))))
    :enable (fun-value-param-dims-of-int-binary
             fun-value-param-dims-of-int-binary-x
             len
             dims-of-expr-value-list
             dims-of-expr-value-when-base
             dims-of-expr-value-when-primop
             lift-expr-value-to-frame-nil-nil
             not-reserrp-when-expr-value-listp
             not-reserrp-when-expr-valuep
             eval-app-list-when-atom
             eval-app-list-when-consp
             eval-app-cell-of-int-binary
             eval-app-cell-of-int-binary-x-add
             expr-value-with-nonempty-dims)
    :expand ((eval-app funval argvals limit)
             (:free (fv lim) (eval-app fv (cdr argvals) lim))
             (:free (fv lim) (eval-app fv (cddr argvals) lim))))

  (defruled eval-app-of-float-add-no-lifting
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary)
                  (equal op (primop-value-float-binary->op opval))
                  (float-binary-primop-case op :add)
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
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (integerp limit)
                  (>= limit 5))
             (equal (eval-app funval argvals limit)
                    (expr-value-base
                     (base-value-float
                      (float-value-ratio (+ (float-value-ratio->ratio floatval1)
                                            (float-value-ratio->ratio floatval2)))))))
    :enable (fun-value-param-dims-of-float-binary
             fun-value-param-dims-of-float-binary-x
             len
             dims-of-expr-value-list
             dims-of-expr-value-when-base
             dims-of-expr-value-when-primop
             lift-expr-value-to-frame-nil-nil
             not-reserrp-when-expr-value-listp
             not-reserrp-when-expr-valuep
             eval-app-list-when-atom
             eval-app-list-when-consp
             eval-app-cell-of-float-binary
             eval-app-cell-of-float-binary-x-add
             list-repeatp
             expr-value-with-nonempty-dims)
    :expand ((eval-app funval argvals limit)
             (:free (fv lim) (eval-app fv (cdr argvals) lim))
             (:free (fv lim) (eval-app fv (cddr argvals) lim))))

  (defruled eval-app-of-float-sub-no-lifting
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary)
                  (equal op (primop-value-float-binary->op opval))
                  (float-binary-primop-case op :sub)
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
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (integerp limit)
                  (>= limit 5))
             (equal (eval-app funval argvals limit)
                    (expr-value-base
                     (base-value-float
                      (float-value-ratio (- (float-value-ratio->ratio floatval1)
                                            (float-value-ratio->ratio floatval2)))))))
    :enable (fun-value-param-dims-of-float-binary
             fun-value-param-dims-of-float-binary-x
             len
             dims-of-expr-value-list
             dims-of-expr-value-when-base
             dims-of-expr-value-when-primop
             lift-expr-value-to-frame-nil-nil
             not-reserrp-when-expr-value-listp
             not-reserrp-when-expr-valuep
             eval-app-list-when-atom
             eval-app-list-when-consp
             eval-app-cell-of-float-binary
             eval-app-cell-of-float-binary-x-sub
             list-repeatp
             expr-value-with-nonempty-dims)
    :expand ((eval-app funval argvals limit)
             (:free (fv lim) (eval-app fv (cdr argvals) lim))
             (:free (fv lim) (eval-app fv (cddr argvals) lim))))

  (defruled eval-app-of-float-mul-no-lifting
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary)
                  (equal op (primop-value-float-binary->op opval))
                  (float-binary-primop-case op :mul)
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
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (equal rat1 (float-value-ratio->ratio floatval1))
                  (equal rat2 (float-value-ratio->ratio floatval2))
                  (integerp limit)
                  (>= limit 5))
             (equal (eval-app funval argvals limit)
                    (expr-value-base
                     (base-value-float
                      (if (or (and (equal rat1 0) (< rat2 0))
                              (and (< rat1 0) (equal rat2 0)))
                          (float-value-neg0)
                        (float-value-ratio (* rat1 rat2)))))))
    :enable (fun-value-param-dims-of-float-binary
             fun-value-param-dims-of-float-binary-x
             len
             dims-of-expr-value-list
             dims-of-expr-value-when-base
             dims-of-expr-value-when-primop
             lift-expr-value-to-frame-nil-nil
             not-reserrp-when-expr-value-listp
             not-reserrp-when-expr-valuep
             eval-app-list-when-atom
             eval-app-list-when-consp
             eval-app-cell-of-float-binary
             eval-app-cell-of-float-binary-x-mul
             list-repeatp
             expr-value-with-nonempty-dims)
    :expand ((eval-app funval argvals limit)
             (:free (fv lim) (eval-app fv (cdr argvals) lim))
             (:free (fv lim) (eval-app fv (cddr argvals) lim))))

  (defruled eval-app-of-float-div-no-lifting
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary)
                  (equal op (primop-value-float-binary->op opval))
                  (float-binary-primop-case op :div)
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
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (equal rat1 (float-value-ratio->ratio floatval1))
                  (equal rat2 (float-value-ratio->ratio floatval2))
                  (not (equal rat2 0))
                  (integerp limit)
                  (>= limit 5))
             (equal (eval-app funval argvals limit)
                    (expr-value-base
                     (base-value-float
                      (if (and (equal rat1 0) (< rat2 0))
                          (float-value-neg0)
                        (float-value-ratio (/ rat1 rat2)))))))
    :enable (fun-value-param-dims-of-float-binary
             fun-value-param-dims-of-float-binary-x
             len
             dims-of-expr-value-list
             dims-of-expr-value-when-base
             dims-of-expr-value-when-primop
             lift-expr-value-to-frame-nil-nil
             not-reserrp-when-expr-value-listp
             not-reserrp-when-expr-valuep
             eval-app-list-when-atom
             eval-app-list-when-consp
             eval-app-cell-of-float-binary
             eval-app-cell-of-float-binary-x-div
             list-repeatp
             expr-value-with-nonempty-dims)
    :expand ((eval-app funval argvals limit)
             (:free (fv lim) (eval-app fv (cdr argvals) lim))
             (:free (fv lim) (eval-app fv (cddr argvals) lim))))

  (defruled eval-app-of-float-expt-no-lifting
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary)
                  (equal op (primop-value-float-binary->op opval))
                  (float-binary-primop-case op :expt)
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
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (equal rat1 (float-value-ratio->ratio floatval1))
                  (equal rat2 (float-value-ratio->ratio floatval2))
                  (integerp rat2)
                  (integerp limit)
                  (>= limit 5))
             (equal (eval-app funval argvals limit)
                    (expr-value-base
                     (base-value-float
                      (if (and (equal rat1 0) (< rat2 0))
                          (float-value-posinf)
                        (float-value-ratio (expt rat1 rat2)))))))
    :enable (fun-value-param-dims-of-float-binary
             fun-value-param-dims-of-float-binary-x
             len
             dims-of-expr-value-list
             dims-of-expr-value-when-base
             dims-of-expr-value-when-primop
             lift-expr-value-to-frame-nil-nil
             not-reserrp-when-expr-value-listp
             not-reserrp-when-expr-valuep
             eval-app-list-when-atom
             eval-app-list-when-consp
             eval-app-cell-of-float-binary
             eval-app-cell-of-float-binary-x-expt
             list-repeatp
             expr-value-with-nonempty-dims)
    :expand ((eval-app funval argvals limit)
             (:free (fv lim) (eval-app fv (cdr argvals) lim))
             (:free (fv lim) (eval-app fv (cddr argvals) lim))))

  (defruled eval-app-of-float-max-no-lifting
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary)
                  (equal op (primop-value-float-binary->op opval))
                  (float-binary-primop-case op :max)
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
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (integerp limit)
                  (>= limit 5))
             (equal (eval-app funval argvals limit)
                    (expr-value-base
                     (base-value-float
                      (float-value-ratio (max (float-value-ratio->ratio floatval1)
                                              (float-value-ratio->ratio floatval2)))))))
    :enable (fun-value-param-dims-of-float-binary
             fun-value-param-dims-of-float-binary-x
             len
             dims-of-expr-value-list
             dims-of-expr-value-when-base
             dims-of-expr-value-when-primop
             lift-expr-value-to-frame-nil-nil
             not-reserrp-when-expr-value-listp
             not-reserrp-when-expr-valuep
             eval-app-list-when-atom
             eval-app-list-when-consp
             eval-app-cell-of-float-binary
             eval-app-cell-of-float-binary-x-max
             list-repeatp
             expr-value-with-nonempty-dims)
    :expand ((eval-app funval argvals limit)
             (:free (fv lim) (eval-app fv (cdr argvals) lim))
             (:free (fv lim) (eval-app fv (cddr argvals) lim))))

  (defruled eval-app-of-float-min-no-lifting
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :float-binary)
                  (equal op (primop-value-float-binary->op opval))
                  (float-binary-primop-case op :min)
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
                  (base-value-case baseval1 :float)
                  (base-value-case baseval2 :float)
                  (equal floatval1 (base-value-float->val baseval1))
                  (equal floatval2 (base-value-float->val baseval2))
                  (float-value-case floatval1 :ratio)
                  (float-value-case floatval2 :ratio)
                  (integerp limit)
                  (>= limit 5))
             (equal (eval-app funval argvals limit)
                    (expr-value-base
                     (base-value-float
                      (float-value-ratio (min (float-value-ratio->ratio floatval1)
                                              (float-value-ratio->ratio floatval2)))))))
    :enable (fun-value-param-dims-of-float-binary
             fun-value-param-dims-of-float-binary-x
             len
             dims-of-expr-value-list
             dims-of-expr-value-when-base
             dims-of-expr-value-when-primop
             lift-expr-value-to-frame-nil-nil
             not-reserrp-when-expr-value-listp
             not-reserrp-when-expr-valuep
             eval-app-list-when-atom
             eval-app-list-when-consp
             eval-app-cell-of-float-binary
             eval-app-cell-of-float-binary-x-min
             list-repeatp
             expr-value-with-nonempty-dims)
    :expand ((eval-app funval argvals limit)
             (:free (fv lim) (eval-app fv (cdr argvals) lim))
             (:free (fv lim) (eval-app fv (cddr argvals) lim))))

  (defruled check-list-suffix-same
    (equal (check-list-suffix x x)
           (mv t nil))
    :enable check-list-suffix)

  (defruled eval-app-of-reshape-no-lifting
    (implies (and (expr-value-case funval :primop)
                  (equal opval (expr-value-primop->val funval))
                  (primop-value-case opval :reshape-t-s1-s2)
                  (equal tval (primop-value-reshape-t-s1-s2->tval opval))
                  (equal s1 (primop-value-reshape-t-s1-s2->s1val opval))
                  (equal s2 (primop-value-reshape-t-s1-s2->s2val opval))
                  (expr-value-list-wfp argvals)
                  (consp argvals)
                  (endp (cdr argvals))
                  (equal argval1 (first argvals))
                  (equal (dims-of-expr-value argval1) s1)
                  (equal val (prim-reshape tval s1 s2 argval1))
                  (expr-valuep val)
                  (expr-value-wfp val)
                  (integerp limit)
                  (>= limit 4))
             (equal (eval-app funval argvals limit)
                    val))
    :enable (fun-value-param-dims-of-reshape
             check-list-suffix-same
             len
             dims-of-expr-value-list
             dims-of-expr-value-when-primop
             lift-expr-value-to-frame-nil-nil
             not-reserrp-when-expr-value-listp
             not-reserrp-when-expr-valuep
             acl2::not-reserrp-when-nat-list-listp
             eval-app-list-when-atom
             eval-app-list-when-consp
             eval-app-cell-of-reshape
             list-repeatp
             expr-value-with-nonempty-dims)
    :expand ((eval-app funval argvals limit)
             (:free (fv lim) (eval-app fv (cdr argvals) lim)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection eval-expr-rules
  :short "Rules about @(tsee eval-expr)."

  (defruled eval-expr-when-var
    (implies (and (expr-case expr :var)
                  (not (zp limit)))
             (equal (eval-expr expr denv limit)
                    (expr-denv-lookup-expr (expr-var->name expr) denv)))
    :enable eval-expr)

  (defruled eval-expr-when-appn
    (implies (and (expr-case expr :appn)
                  (not (zp limit))
                  (equal funval
                         (eval-expr (expr-appn->fun expr) denv (1- limit)))
                  (expr-valuep funval)
                  (equal argvals
                         (eval-expr-list (expr-appn->args expr) denv (1- limit)))
                  (expr-value-listp argvals))
             (equal (eval-expr expr denv limit)
                    (eval-app funval argvals (1- limit))))
    :enable (eval-expr
             not-reserrp-when-expr-valuep
             not-reserrp-when-expr-value-listp))

  (defruled eval-expr-when-bracket
    (implies (and (expr-case expr :bracket)
                  (not (zp limit))
                  (equal vals
                         (eval-expr-list (expr-bracket->exprs expr)
                                         denv
                                         (1- limit)))
                  (expr-value-listp vals)
                  (consp vals)
                  (list-repeatp (dims-of-expr-value-list vals)))
             (equal (eval-expr expr denv limit)
                    (expr-value-vector vals)))
    :enable (eval-expr
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
      eval-expr-when-appn
      eval-expr-when-bracket
      eval-expr-list-when-atom
      eval-expr-list-when-consp
      eval-app-of-int-add-no-lifting
      eval-app-of-float-add-no-lifting
      eval-app-of-float-sub-no-lifting
      eval-app-of-float-mul-no-lifting
      eval-app-of-float-div-no-lifting
      eval-app-of-float-expt-no-lifting
      eval-app-of-float-max-no-lifting
      eval-app-of-float-min-no-lifting
      eval-app-of-reshape-no-lifting
      not-reserrp-when-expr-valuep
      acl2::ifix-when-integerp)))
