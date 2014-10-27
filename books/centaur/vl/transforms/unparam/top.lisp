; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>
;                  Sol Swords <sswords@centtech.com>

(in-package "VL")

(include-book "lineup")
(include-book "override")
(include-book "scopesubst")

(define vl-paramdecl-set-default ((x vl-paramdecl-p)
                                  (val vl-maybe-paramvalue-p))
  :returns (mv ok
               (new-x vl-paramdecl-p))
  (b* (((vl-paramdecl x))
       (val (vl-maybe-paramvalue-fix val))
       ((mv ok type)
        (vl-paramtype-case x.type
          :vl-typeparam
          (if (or (not val) (vl-paramvalue-datatype-p val))
              (mv t (change-vl-typeparam x.type :default val))
            (mv nil (change-vl-typeparam x.type :default nil)))
          :vl-implicitvalueparam
          (if (or (not val) (vl-paramvalue-expr-p val))
              (mv t (change-vl-implicitvalueparam x.type :default val))
            (mv nil (change-vl-implicitvalueparam x.type :default nil)))
          :vl-explicitvalueparam
          (if (or (not val) (vl-paramvalue-expr-p val))
              (mv t (change-vl-explicitvalueparam x.type :default val))
            (mv nil (change-vl-explicitvalueparam x.type :default nil))))))
    (mv ok 
        (change-vl-paramdecl x :type type))))

(define vl-paramdecl-remove-default ((x vl-paramdecl-p))
  :returns (new-x vl-paramdecl-p)
  (b* (((mv ?ok ans) (vl-paramdecl-set-default x nil)))
    ans))

(define vl-paramdecllist-remove-defaults ((x vl-paramdecllist-p))
  :returns (new-x vl-paramdecllist-p)
  (if (atom x)
      nil
    (cons (vl-paramdecl-remove-default (car x))
          (vl-paramdecllist-remove-defaults (cdr x)))))


(define vl-scopeinfo-resolve-params ((x vl-paramdecloverridelist-p)
                                     (scopeinfo vl-scopeinfo-p)
                                     (ss vl-scopestack-p)
                                     (final-params-acc vl-paramdecllist-p)
                                     (warnings vl-warninglist-p)
                                     (ctx vl-context-p))
  :returns (mv (successp)
               (warnings vl-warninglist-p)
               (new-scopeinfo vl-scopeinfo-p
                       "input scopeinfo modified with final parameter values")
               (final-params vl-paramdecllist-p))
  (b* (((when (atom x))
        (mv t (ok) (vl-scopeinfo-fix scopeinfo)
            (revappend-without-guard
             (vl-paramdecllist-fix final-params-acc) nil)))
       ((vl-paramdecloverride x1) (car x))
       (current-ss (vl-scopestack-push scopeinfo ss))
       (subst-decl (vl-paramdecl-scopesubst x1.decl current-ss))
       (ov-value (or x1.override
                     (vl-paramtype->default
                      (vl-paramdecl->type subst-decl))))
       ((unless ov-value)
        (mv nil (fatal :type :vl-bad-inst
                       :msg "~a0: no value for parameter ~s1."
                       :args (list (vl-context-fix ctx) (vl-paramdecl->name x1.decl)))
            (vl-scopeinfo-fix scopeinfo)
            nil))
       ((mv ok warnings final-value)
        (vl-override-parameter-value subst-decl ov-value current-ss warnings ctx))
       ((unless ok)
        (mv nil warnings (vl-scopeinfo-fix scopeinfo) nil))

       ((mv ok final-paramdecl)
        (vl-paramdecl-set-default subst-decl final-value))
       ((unless ok)
        (mv nil
            (warn :type :vl-programming-error
                  :msg "~a0: Tried to set the value of an type/value ~
                        parameter ~a1 as value/type ~a2"
                  :args (list (vl-context-fix ctx) x1.decl final-value))
            (vl-scopeinfo-fix scopeinfo)
            nil))

       ((vl-scopeinfo scopeinfo))
       (new-scopeinfo (change-vl-scopeinfo
                       scopeinfo
                       :locals (hons-acons (vl-paramdecl->name final-paramdecl)
                                           final-paramdecl
                                           scopeinfo.locals))))
    (vl-scopeinfo-resolve-params (cdr x) new-scopeinfo ss 
                                 (cons final-paramdecl
                                       final-params-acc)
                                 warnings ctx)))
                                     
      

(define vl-scope-finalize-params ((x vl-scope-p)
                                  (formals vl-paramdecllist-p)
                                  (actuals vl-paramargs-p)
                                  (warnings vl-warninglist-p)
                                  (ss vl-scopestack-p)
                                  (ctx vl-context-p))
  :returns (mv (successp)
               (warnings vl-warninglist-p)
               (new-ss vl-scopestack-p
                       "modified scopestack with x pushed onto it, but modified
                        with the overridden parameter values")
               (final-paramdecls vl-paramdecllist-p))
  (b* (((mv ok warnings overrides)
        (vl-make-paramdecloverrides formals actuals warnings ctx))
       ((unless ok)
        (mv nil warnings (vl-scopestack-fix ss) nil))
       (scopeinfo (vl-scope->scopeinfo x (vl-scopestack->design ss)))
       (scopeinfo-with-empty-params
        (change-vl-scopeinfo
         scopeinfo
         :locals (vl-paramdecllist-alist
                  (vl-paramdecllist-remove-defaults formals)
                  (vl-scopeinfo->locals scopeinfo))))
       ((mv ok warnings scopeinfo-with-real-params final-paramdecls)
        (vl-scopeinfo-resolve-params overrides scopeinfo-with-empty-params ss nil warnings ctx)))
    (mv ok warnings (vl-scopestack-push scopeinfo-with-real-params ss)
        final-paramdecls)))

(defprod vl-unparam-signature
  ((modname stringp)
   (final-params vl-paramdecllist-p))
  :layout :tree)

(fty::deflist vl-unparam-signaturelist :elt-type vl-unparam-signature
  :elementp-of-nil nil)

(define vl-unparam-newname ((modname stringp)
                            (paramdecls vl-paramdecllist-p))
  




(define vl-unparam-inst
  :parents (unparameterization)
  :short "Try to unparameterize a single module instance."

  ((inst     vl-modinst-p
             "Instance of some module.  The module being instantiated may or
              may not have parameters.")
   (ss       vl-scopestack-p)
   (warnings vl-warninglist-p
             "Warnings accumulator for the submodule.")
   (modname  stringp "Containing module name, for context"))

  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (inst     vl-modinst-p
                "Updated module instance, perhaps instantiating a new module
                 like @('my_adder$width=5') instead of @('my_adder').")
      (needed-sigs (iff (vl-unparam-signature-p needed-sigs) needed-sigs)
                   "An unparam-signature for the instantiated module, if needed."))

  (b* (((vl-modinst inst) (vl-modinst-fix inst))

       (mod (vl-scopestack-find-definition inst.modname ss))
       ((unless (and mod (eq (tag mod) :vl-module)))
        (vl-unparam-debug "~a0: can't find module ~a1.~%" inst.modname)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: trying to instantiate undefined module ~s1."
                   :args (list inst inst.modname))
            inst nil))

       ((vl-module mod) mod)

       ((when (atom mod.paramdecls))
        ;; Optimization.  In the common case there are no parameter
        ;; declarations for the submodule.  In this case, all we need to do is
        ;; make sure the instance is also parameter-free.
        (if (vl-paramargs-empty-p inst.paramargs)
            (mv t (ok) inst 
                (make-vl-unparam-signature :name inst.modname))
          (mv nil
              (fatal :type :vl-bad-instance
                     :msg "~a0: parameter arguments given to ~s1, but ~s1 ~
                           does not take any parameters."
                     :args (list inst inst.modname))
              inst nil)))

       (ctx (make-vl-context :mod modname :elem inst))

       ((mv ok warnings mod-ss final-paramdecls)
        (vl-scope-finalize-params mod
                                  mod.paramdecls
                                  inst.paramargs
                                  warnings
                                  ss
                                  ctx))
       ((unless ok)
        ;; already warned
        (vl-unparam-debug "~a0: failed to finalize params~%" inst)
        (mv nil warnings inst nil))


       (new-modname      (vl-unparam-newname inst.modname final-paramdecls))

       (new-inst (change-vl-modinst inst
                                    :modname new-modname
                                    :paramargs (make-vl-paramargs-plain :args nil)))

       (unparam-signature (make-vl-unparam-signature
                           :name inst.modname
                           :valsigma valsigma
                           :typesigma typesigma)))

    (vl-unparam-debug "~a0: success, new instance is ~a1.~%" inst new-inst)
    (mv t warnings new-inst unparam-signature)))

