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
;; (include-book "scopesubst")
(include-book "../../mlib/blocks")
(include-book "../../mlib/writer") ;; for generating the new module names...
(local (include-book "../../util/default-hints"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))

(defxdoc unparameterization
  :parents (transforms)
  :short "Expand away modules with parameters; similar to the idea of
<i>elaboration</i> of the design."

  :long "<p>Unparameterization is a Verilog transformation which, given a set
of Verilog modules, is supposed to produce an equivalent, parameter-free set of
modules.</p>


<h3>Background on Parameters</h3>

<p>See @(see vl-paramtype) and @(see vl-paramdecl) for background on our
representation of parameter declarations.  Parameters can be declared as either
ordinary @('parameter')s or as @('localparam')s.  Parameters may have default
values, and their defaults can refer to other parameters in the module.  Some
simple examples of parameters are:</p>

@({
    module m (a, b, c) ;
      ...
      parameter size = 4 ;
      localparam twosize = 2 * size ;
      ...
    endmodule
})

<p>Such a module can be instantiated in various ways, e.g.,:</p>

@({
    module uses_m (x y z) ;
      ...
      m #(6)        m_instance_1 (.a(x), .b(y), .c(z)) ; // size 6
      m #(.size(6)) m_instance_2 (.a(x), .b(y), .c(z)) ; // size 6
      m             m_instance_3 (.a(x), .b(y), .c(z)) ; // size 4
      ...
    endmodule
})

<p>Local parameters are just like parameters except that they cannot be
assigned to from outside the module.  They seem like about the cleanest way to
introduce named constants, as unlike @('`define') they don't pollute the global
namespace.</p>

<p>Parameters can also be given values via the @('defparam') statement, but
this construct is being deprecated (see SystemVerilog-2012 section C.4.1) and
may be removed from future versions of the language.  We generally think that
using @('defparam') is bad form.  VL does not support @('defparam'), so we do
not consider it here.</p>


<h3>Unparameterization</h3>

<p>The basic idea behind unparameterization is pretty simple.</p>

<p>Suppose we are dealing with a parameterized module called @('plus'), which
takes a single parameter called @('size').  There may be several modules, say
@('m1'), @('m2'), and @('m3'), which contain instances of @('plus') with
different sizes, say @('8'), @('16'), and @('32').</p>

<p>Our general goal is to eliminate @('plus') from our module list by replacing
it with three new modules, @('plus$size=8'), @('plus$size=16'), and
@('plus$size=32'), which are copies of @('plus') except that @('size') has been
replaced everywhere with @('8'), @('16'), or @('32') as suggested by their
names.</p>

<p>At the same time, we need to change the instances of @('plus') throughout
@('m1'), @('m2'), and @('m3') with appropriate instances of the new modules.
Finally, once all of the instances of the generic @('plus') have been done away
with, we can safely remove @('plus') from our module list.</p>")

(local (xdoc::set-default-parents unparameterization))

(define vl-paramdecl-set-default ((x vl-paramdecl-p)
                                  (val vl-maybe-paramvalue-p))
  :returns (mv ok
               (new-x vl-paramdecl-p))
  :guard-debug t
  (b* (((vl-paramdecl x))
       (val (vl-maybe-paramvalue-fix val))
       ((mv ok type)
        (vl-paramtype-case x.type
          :vl-typeparam
          (if (or (not val) (vl-paramvalue-case val :type))
              (mv t (change-vl-typeparam x.type :default
                                         (and val (vl-paramvalue-type->type val))))
            (mv nil (change-vl-typeparam x.type :default nil)))
          :vl-implicitvalueparam
          (if (or (not val) (vl-paramvalue-case val :expr))
              (mv t (change-vl-implicitvalueparam x.type :default
                                                  (and val (vl-paramvalue-expr->expr val))))
            (mv nil (change-vl-implicitvalueparam x.type :default nil)))
          :vl-explicitvalueparam
          (if (or (not val) (vl-paramvalue-case val :expr))
              (mv t (change-vl-explicitvalueparam x.type :default
                                                  (and val (vl-paramvalue-expr->expr val))))
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


(define vl-paramdecl-resolve-indices-top ((x vl-paramdecl-p)
                                          (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x vl-paramdecl-p))
  (b* ((prefs (vl-paramdecl-parameter-refs x ss))
       (fns   (vl-paramdecl-functions-called x))
       ((mv warnings fntable) (vl-funnames-svex-compile fns ss 1000))
       ((wmv warnings paramtable) (vl-paramrefs-svex-compile prefs 1000))
       ((wmv warnings ?changedp new-x)
        (vl-paramdecl-resolve-indices
         x (make-vl-svexconf :ss ss :fns fntable :params paramtable))))
    (mv warnings new-x)))
       

      


(define vl-scopeinfo-resolve-params ((x vl-paramdecloverridelist-p)
                                     (scopeinfo vl-scopeinfo-p)
                                     (ss vl-scopestack-p
                                         "Scopestack in the module whose params
                                          we're overriding")
                                     (outer-ss vl-scopestack-p
                                               "Scopestack for the overrides")
                                     (final-params-acc vl-paramdecllist-p)
                                     (warnings vl-warninglist-p)
                                     (ctx vl-context-p))
  :prepwork ((local (in-theory (e/d (vl-paramdecloverridelist-fix)
                                    (append
                                     vl-context-p-when-vl-ctxelement-p
                                     acl2::append-when-not-consp)))))
  :returns (mv (successp)
               (warnings vl-warninglist-p)
               (new-scopeinfo vl-scopeinfo-p
                       "input scopeinfo modified with final parameter values")
               (final-params vl-paramdecllist-p))
  ;; :hooks ((:fix :hints (("Goal" :induct (vl-scopeinfo-resolve-params
  ;;                                        x scopeinfo ss final-params-acc warnings ctx)
  ;;                        :expand ((:free (scopeinfo ss final-params-acc warnings ctx)
  ;;                                  (vl-scopeinfo-resolve-params
  ;;                                   x scopeinfo ss final-params-acc warnings ctx))
  ;;                                 (:free (a b scopeinfo ss final-params-acc warnings ctx)
  ;;                                  (vl-scopeinfo-resolve-params
  ;;                                   (cons a b)
  ;;                                   scopeinfo ss final-params-acc warnings ctx)))
  ;;                        :in-theory (e/d (vl-paramdecloverridelist-fix)
  ;;                                        ((:d vl-scopeinfo-resolve-params)))))))

  (b* (((when (atom x))
        (mv t (ok) (vl-scopeinfo-fix scopeinfo)
            (revappend-without-guard
             (vl-paramdecllist-fix final-params-acc) nil)))
       ((vl-paramdecloverride x1) (car x))
       (current-ss (vl-scopestack-push (vl-scopeinfo-fix scopeinfo) ss))
       (warnings (ok))
       (ctx (vl-context-fix ctx))
       ;; In case the type or size has unresolved indices, resolve indices in the parameter.
       ;; BOZO This unnecessarily resolves indices in the default expression as
       ;; well; this is just a performance bug.
       ((wmv warnings decl :ctx ctx) (vl-paramdecl-resolve-indices-top x1.decl current-ss))

       (ov-value (or x1.override
                     (vl-paramtype->default
                      (vl-paramdecl->type decl))))
       ((unless ov-value)
        (mv nil (fatal :type :vl-bad-inst
                       :msg "~a0: no value for parameter ~s1."
                       :args (list (vl-context-fix ctx) (vl-paramdecl->name x1.decl)))
            (vl-scopeinfo-fix scopeinfo)
            nil))
       (ov-ss (if x1.override
                  outer-ss
                current-ss))

       ((mv ok warnings final-paramdecl)
        (vl-override-parameter-value decl current-ss ov-value ov-ss warnings ctx))
       ((unless ok)
        (mv nil warnings (vl-scopeinfo-fix scopeinfo) nil))

       ((vl-scopeinfo scopeinfo))
       (new-scopeinfo (change-vl-scopeinfo
                       scopeinfo
                       :locals (hons-acons (vl-paramdecl->name final-paramdecl)
                                           final-paramdecl
                                           scopeinfo.locals))))
    (vl-scopeinfo-resolve-params (cdr x) new-scopeinfo ss outer-ss
                                 (cons final-paramdecl
                                       final-params-acc)
                                 warnings ctx)))



(define vl-scope-finalize-params ((x vl-scope-p)
                                  (formals vl-paramdecllist-p)
                                  (actuals vl-paramargs-p)
                                  (warnings vl-warninglist-p)
                                  (ss vl-scopestack-p
                                      "ss where the instantiated module was found,
                                       without the module itself")
                                  (outer-ss vl-scopestack-p
                                            "ss for the instantiating context")
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
         :locals (make-fast-alist
                  (vl-paramdecllist-alist
                   (vl-paramdecllist-remove-defaults formals)
                   (vl-scopeinfo->locals scopeinfo)))))
       ((mv ok warnings scopeinfo-with-real-params final-paramdecls)
        (vl-scopeinfo-resolve-params
         overrides scopeinfo-with-empty-params ss outer-ss nil warnings ctx)))
    (mv ok warnings (vl-scopestack-push scopeinfo-with-real-params ss)
        final-paramdecls)))








(defprod vl-unparam-signature
  ((modname stringp)
   (final-params vl-paramdecllist-p))
  :layout :tree)

(fty::deflist vl-unparam-signaturelist :elt-type vl-unparam-signature
  :elementp-of-nil nil)

(fty::defalist vl-unparam-sigalist :key-type vl-unparam-signature
  :val-type vl-scopestack-p)

(define vl-unparam-newname-exprstring ((x vl-maybe-expr-p))
  :returns (str stringp :rule-classes :type-prescription)
  :hooks ((:fix :hints(("Goal" :in-theory (enable (tau-system))))))
  (if x
      (if (and (vl-expr-resolved-p x)
               (b* (((mv & size) (vl-expr-selfsize x nil))
                    ((mv & type) (vl-expr-typedecide x nil)))
                 (and (eql size 32) (eq type :vl-signed))))
          ;; Special case to avoid things like size=32'sd5.
          (str::natstr (vl-resolved->val x))
        (acl2::substitute #\_ #\Space (vl-pps-expr x)))
    "NULL"))

(define vl-unparam-newname-aux ((x vl-paramdecllist-p)
                                &key (ps 'ps))
  :parents (vl-unparam-newname)
  (b* (((when (atom x)) ps)
       ((vl-paramdecl x1) (car x))
       ((when x1.localp)
        ;; we think localparams are always determined by the nonlocal params,
        ;; so we don't need to include them in the name.
        (vl-unparam-newname-aux (cdr x)))
       ((the string name-part)
        (acl2::substitute #\_ #\Space x1.name))
       ((the string type-expr-part)
        (vl-paramtype-case x1.type
          :vl-implicitvalueparam (vl-unparam-newname-exprstring x1.type.default)
          :vl-explicitvalueparam (vl-unparam-newname-exprstring x1.type.default)
          :vl-typeparam (if x1.type.default
                            (with-local-ps (vl-pp-datatype x1.type.default))
                          "NULL"))))
    (vl-ps-seq (vl-print "$")
               (vl-print-str name-part)
               (vl-print "=")
               (vl-print-str type-expr-part)
               (vl-unparam-newname-aux (cdr x)))))



(define vl-unparam-newname
  :short "Generate a new name for an unparameterized module."
  ((origname stringp              "Original name of the module, e.g., @('my_adder').")
   (paramdecls vl-paramdecllist-p "Final, overridden paramdecls for the module."))
  :returns (new-name stringp :rule-classes :type-prescription
                     "New, mangled name, e.g., @('my_adder$size=5').")
  :long "<p>This is a dumb but probably sufficient way to generate new names.
Note that we explicitly check (later on) that no name conflicts are
introduced.</p>"
  (hons-copy (with-local-ps (vl-ps-seq (vl-print-str origname)
                                       (vl-unparam-newname-aux paramdecls)))))


(define vl-unparam-inst
  :parents (unparameterization)
  :short "Compute the final parameter values for a single module instance."
  ((inst     vl-modinst-p
             "Instance of some module.  The module being instantiated may or
              may not have parameters.")
   (ss       vl-scopestack-p "Scopestack where the module is instantiated")
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
                   "An unparam-signature for the instantiated module, if needed.")
      (mod-ss   vl-scopestack-p
                "Scopestack which (on success) contains the module with its final parameters."))

  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (vl-module-p x)
                               (vl-scope-p x))))
             (local (defthm vl-scope-p-when-vl-interface-p-strong
                      (implies (vl-interface-p x)
                               (vl-scope-p x)))))

  (b* (((vl-modinst inst) (vl-modinst-fix inst))
       ((mv mod mod-ss) (vl-scopestack-find-definition/ss inst.modname ss))
       (ss (vl-scopestack-fix ss))
       ((unless (and mod
                     (or (eq (tag mod) :vl-module)
                         (eq (tag mod) :vl-interface))))
        (vl-unparam-debug "~a0: can't find module ~a1.~%" inst inst.modname)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: trying to instantiate undefined module ~s1."
                   :args (list inst inst.modname))
            inst nil ss))

       (mod.paramdecls (if (eq (tag mod) :vl-module)
                           (vl-module->paramdecls mod)
                         (vl-interface->paramdecls mod)))

       ((when (atom mod.paramdecls))
        ;; Optimization.  In the common case there are no parameter
        ;; declarations for the submodule.  In this case, all we need to do is
        ;; make sure the instance is also parameter-free.
        (if (vl-paramargs-empty-p inst.paramargs)
            (mv t (ok) inst
                (make-vl-unparam-signature :modname inst.modname)
                (vl-scopestack-push mod mod-ss))
          (mv nil
              (fatal :type :vl-bad-instance
                     :msg "~a0: parameter arguments given to ~s1, but ~s1 ~
                           does not take any parameters."
                     :args (list inst inst.modname))
              inst nil mod-ss)))

       (ctx (make-vl-context :mod modname :elem inst))

       ((mv ok warnings mod-ss final-paramdecls)
        (vl-scope-finalize-params mod
                                  mod.paramdecls
                                  inst.paramargs
                                  warnings
                                  mod-ss
                                  ss
                                  ctx))
       ((unless ok)
        ;; already warned
        (vl-unparam-debug "~a0: failed to finalize params~%" inst)
        (mv nil warnings inst nil mod-ss))


       (new-modname      (vl-unparam-newname inst.modname final-paramdecls))

       (new-inst (change-vl-modinst inst
                                    :modname new-modname
                                    :paramargs (make-vl-paramargs-plain :args nil)))

       (unparam-signature (make-vl-unparam-signature
                           :modname inst.modname
                           :final-params final-paramdecls)))

    (vl-unparam-debug "~a0: success, new instance is ~a1.~%" inst new-inst)
    (mv t warnings new-inst unparam-signature mod-ss)))

(define vl-unparam-instlist ((x vl-modinstlist-p)
                             (ss       vl-scopestack-p
                                       "Scopestack where the instances occur.")
                             (warnings vl-warninglist-p
                                       "Warnings accumulator for the submodule.")
                             (modname  stringp "Containing module name, for context")
                             (sigalist vl-unparam-sigalist-p "Accumulator"))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (insts    vl-modinstlist-p
                         "Updated module instances")
               (sigalist vl-unparam-sigalist-p "Needed signatures and their scopestacks"))
  :hooks ((:fix :hints(("Goal" :in-theory (disable (:d vl-unparam-instlist))
                        :induct (vl-unparam-instlist x ss warnings modname sigalist)
                        :expand ((:free (ss warnings modname sigalist)
                                  (vl-unparam-instlist x ss warnings modname sigalist))
                                 (:free (ss warnings modname sigalist)
                                  (vl-unparam-instlist
                                   (vl-modinstlist-fix x)
                                   ss warnings modname sigalist)))))))
  (b* (((when (atom x)) (mv t (ok) nil (vl-unparam-sigalist-fix sigalist)))
       ((mv ok1 warnings inst1 sig new-ss) (vl-unparam-inst (car x) ss warnings modname))
       (sigalist
        (if sig
            (cons (cons sig new-ss) sigalist)
          sigalist))
       ((mv ok2 warnings insts2 sigalist)
        (vl-unparam-instlist (cdr x) ss warnings modname sigalist)))
    (mv (and ok1 ok2) warnings (cons inst1 insts2) sigalist)))


(define vl-gencase-match ((x vl-expr-p)
                          (y vl-expr-p)
                          (ss vl-scopestack-p)
                          (warnings vl-warninglist-p))
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (equalp))
  (b* ((eq-expr (make-vl-binary :op :vl-binary-ceq
                                :left x :right y))
       (warnings (ok))
       ((wmv warnings res) (vl-consteval eq-expr ss))
       ((mv ok result)
        (vl-expr-case res
          :vl-value (vl-value-case res.val
                      :vl-constint (mv t (not (eql 0 res.val.value)))
                      :otherwise (mv nil nil))
          :otherwise (mv nil nil))))
    (if ok
        (mv t warnings result)
      (mv nil
          (fatal :type :vl-generate-resolve-fail
                 :msg "Couldn't determine whether test expression ~a0 matched ~
                     case expression ~a1."
                 :args (list (vl-expr-fix x) (vl-expr-fix y)))
          nil))))

(define vl-gencase-some-match ((x vl-expr-p)
                               (y vl-exprlist-p)
                               (ss vl-scopestack-p)
                               (warnings vl-warninglist-p))
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (equalp))
  (b* (((when (atom y)) (mv t (ok) nil))
       ((mv ok warnings first) (vl-gencase-match x (car y) ss warnings))
       ((unless ok) (mv nil warnings nil))
       ((when first) (mv ok warnings first)))
    (vl-gencase-some-match x (cdr y) ss warnings)))


(define vl-genblob-resolve-indices-top ((x vl-genblob-p)
                                        (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x vl-genblob-p))
  (b* ((prefs (vl-genblob-parameter-refs x ss))
       (fns   (vl-genblob-functions-called x))
       ((mv warnings fntable) (vl-funnames-svex-compile fns ss 1000))
       ((wmv warnings paramtable) (vl-paramrefs-svex-compile prefs 1000))
       ((wmv warnings ?changedp new-x)
        (vl-genblob-resolve-indices
         x (make-vl-svexconf :ss ss :fns fntable :params paramtable))))
    (mv warnings new-x)))


(with-output :off (event)
  :evisc (:gag-mode (evisc-tuple 3 4 nil nil ))
  (defines vl-generate-resolve
    :prepwork ((local (include-book "centaur/misc/arith-equivs" :dir :system))
               (local (in-theory (disable
                                  cons-equal
                                  vl-genelement-p-by-tag-when-vl-scopeitem-p
                                  vl-genelement-p-when-member-equal-of-vl-genelementlist-p
                                  member-equal
                                  default-car default-cdr
                                  vl-warninglist-p-when-not-consp
                                  vl-gencaselist-p-when-not-consp
                                  vl-genelementlist-p-when-not-consp
                                  vl-genblob-p-by-tag-when-vl-scope-p
                                  vl-warninglist-p-when-subsetp-equal
                                  acl2::loghead
                                  ifix nfix)))
               (local (defthm vl-genelement-fix-under-iff
                        (vl-genelement-fix x)
                        :hints(("Goal" :in-theory (enable (tau-system))))))
               (local (defthm elemlist-count-of-body-lt-loop-count
                        (implies (equal (vl-genelement-kind x) :vl-genloop)
                                 (< (vl-genelementlist-count (list (vl-genloop->body x)))
                                    (vl-genelement-count x)))
                        :hints(("Goal" :in-theory (enable vl-genelement-count
                                                          vl-genelementlist-count))))))
    (define vl-genblob-resolve ((x vl-genblob-p)
                                (ss vl-scopestack-p)
                                (warnings vl-warninglist-p))
      :returns (mv (ok)
                   (warnings1 vl-warninglist-p)
                   (new-x vl-genblob-p))
      :measure (two-nats-measure (vl-genblob-count x) 0)
      (b* (((vl-genblob x) (vl-genblob-fix x))
           ((mv ok warnings x-ss ?final-paramdecls)
            ;; BOZO figure out a real context
            (vl-scope-finalize-params x x.paramdecls
                                      (make-vl-paramargs-named)
                                      warnings ss ss 'fake-context-for-unparam))
           ((unless ok) (mv nil warnings (vl-genblob-fix x)))
           (x (change-vl-genblob x :paramdecls final-paramdecls))
           ((wmv warnings new-x)
            (vl-genblob-resolve-indices-top x x-ss))
           ((vl-genblob new-x))
           ((mv ok warnings new-generates)
            (vl-generatelist-resolve x.generates x-ss warnings)))
        (mv ok warnings (change-vl-genblob new-x :generates new-generates))))
        
           

    (define vl-generate-resolve
      ((x vl-genelement-p "The generate block to resolve")
       (ss vl-scopestack-p "Current scopestack with resolved params")
       (warnings vl-warninglist-p))
      :returns (mv (ok)
                   (warnings1 vl-warninglist-p)
                   (new-x vl-genelement-p))
      :measure (two-nats-measure (vl-genblob-generate-count x) 0)
      :verify-guards nil
      (b* ((x (vl-genelement-fix x)))
        (vl-genelement-case x
          :vl-genbase (b* ((xlist (list x))
                           (blob (vl-sort-genelements xlist))
                           ((mv ok warnings new-blob)
                            (vl-genblob-resolve blob ss warnings))
                           ((unless ok) (mv nil warnings (vl-genelement-fix x))))
                        (mv t warnings
                            (make-vl-genblock
                             :elems (vl-genblob->elems new-blob xlist)
                             :loc (vl-modelement->loc x.item))))

          :vl-genblock
          (b* ((blob (vl-sort-genelements x.elems
                                          :scopetype :vl-genblock
                                          :name x.name))
               ((mv ok warnings new-blob)
                (vl-genblob-resolve blob ss warnings))
               ((unless ok)
                (mv nil warnings (vl-genelement-fix x))))
            (mv t warnings
                (change-vl-genblock x :elems (vl-genblob->elems new-blob x.elems))))
            

          ;; Didn't expect to see these resolved forms yet; leave them.
          
          :vl-genarray
          (mv t (warn :type :vl-already-resolved-generate
                      :msg "~a0: Didn't expect to see an already-resolved genarray."
                      :args (list x))
              x)

          :vl-genif
          (b* (((wmv warnings testval) (vl-consteval x.test ss))
               ((unless (vl-expr-resolved-p testval))
                (mv nil (fatal :type :vl-generate-resolve-fail
                               :msg "~a0: Failed to evaluate the test expression ~a1."
                               :args (list x x.test))
                    x))
               (testval (vl-resolved->val testval))
               (subelem (if (eql 0 testval) x.else x.then)))
            (vl-generate-resolve subelem ss warnings))

          :vl-gencase
          ;; BOZO the sizing on this is probably wrong
          (b* (((mv ok warnings elem)
                (vl-gencaselist-resolve x.cases x.test x ss warnings))
               ((when elem) (mv ok warnings elem)))
            (vl-generate-resolve x.default ss warnings))

          :vl-genloop
          (b* (((wmv warnings initval) (vl-consteval x.initval ss))
               ((unless (vl-expr-resolved-p initval))
                (mv nil (fatal :type :vl-generate-resolve-fail
                               :msg "~a0: Failed to evaluate the initial value expression ~a1."
                               :args (list x x.initval))
                    x))
               (body.name (and (eql (vl-genelement-kind x.body) :vl-genblock)
                               (vl-genblock->name x.body)))
               ;; ((mv body.name body.elems)
               ;;  (if (eql (vl-genelement-kind x.body) :vl-genblock)
               ;;      (mv (vl-genblock->name x.body) (vl-genblock->elems x.body))
               ;;    (mv nil (list x.body))))
               ;; (blob (vl-sort-genelements body.elems
               ;;                            :scopetype :vl-genarrayblock
               ;;                            :name nil))
               ((mv ok warnings arrayblocks)
                (vl-genloop-resolve 100000 ;; recursion limit
                                    x.body
                                    x.var (vl-resolved->val initval)
                                    x.nextval x.continue
                                    x ss warnings)))
            (mv ok warnings
                (make-vl-genarray :name body.name :var x.var :blocks arrayblocks
                                  :loc x.loc))))))


    (define vl-generatelist-resolve ((x vl-genelementlist-p)
                                     (ss vl-scopestack-p)
                                     (warnings vl-warninglist-p))
      :returns (mv (ok)
                   (warnings1 vl-warninglist-p)
                   (new-elems vl-genelementlist-p))
      :measure (two-nats-measure (vl-genblob-generates-count x) 0)
      (b* (((when (atom x)) (mv t (ok) nil))
           ((mv ok1 warnings first)
            (vl-generate-resolve (car x) ss warnings))
           ((mv ok2 warnings rest)
            (vl-generatelist-resolve (cdr x) ss warnings)))
        (mv (and ok1 ok2) warnings (cons first rest))))



    (define vl-gencaselist-resolve ((x vl-gencaselist-p)
                                    (test vl-expr-p)
                                    (orig-x vl-genelement-p)
                                    (ss vl-scopestack-p)
                                    (warnings vl-warninglist-p))
      :guard (eq (vl-genelement-kind orig-x) :vl-gencase)
      :returns (mv (ok)
                   (warnings1 vl-warninglist-p)
                   (new-elem (iff (vl-genelement-p new-elem) new-elem)))
      :measure (two-nats-measure (vl-genblob-gencaselist-count x) 0)
      (b* ((x (vl-gencaselist-fix x))
           ((when (atom x)) (mv t (ok) nil))

           ((cons exprs1 block1) (car x))

           ((mv ok warnings matchp) (vl-gencase-some-match test exprs1 ss warnings))
           ((unless ok)
            (mv nil warnings (vl-genelement-fix orig-x)))
           ((unless matchp)
            (vl-gencaselist-resolve (cdr x) test orig-x ss warnings)))
        (vl-generate-resolve block1 ss warnings)))

    (define vl-genloop-resolve ((clk natp "recursion limit")
                                (body vl-genelement-p)
                                (var   stringp)
                                (current-val integerp)
                                (nextval vl-expr-p)
                                (continue vl-expr-p)
                                (orig-x vl-genelement-p)
                                (ss vl-scopestack-p)
                                (warnings vl-warninglist-p))
      :returns (mv (ok)
                   (warnings1 vl-warninglist-p)
                   (new-blocks vl-genarrayblocklist-p))
      :measure (two-nats-measure (vl-genblob-generate-count body) clk)
      (b* (((when (zp clk))
            (mv nil
                (fatal :type :vl-generate-resolve-fail
                       :msg "~a0: Iteration limit ran out in for loop."
                       :args (list (vl-genelement-fix orig-x)))
                nil))
           (var-param (make-vl-paramdecl
                       :name var
                       :type (make-vl-explicitvalueparam
                              :type *vl-plain-old-integer-type*
                              :default (vl-make-index (acl2::loghead 32 current-val)))
                       :loc *vl-fakeloc*))

           ;; Make a fake scope containing just the index param, and finalize it.
           ((mv ok warnings idx-ss ?final-paramdecls)
            (vl-scope-finalize-params (make-vl-genblob)
                                      (list var-param)
                                      (make-vl-paramargs-named)
                                      warnings ss ss 'fake-context-for-unparam)) ;; bozo make real context
           ((unless ok)
            (mv nil warnings nil))

           ;; Check whether we continue.
           ((wmv warnings continue-val) (vl-consteval continue idx-ss))
           ((unless (vl-expr-resolved-p continue-val))
            (mv nil
                (fatal :type :vl-generate-resolve-fail
                       :msg "~a0: Failed to evaluate the loop termination expression ~a1"
                       :args (list (vl-genelement-fix orig-x) (vl-expr-fix continue)))
                nil))

           ((when (eql (vl-resolved->val continue-val) 0))
            (mv t warnings nil))

           

           ((mv ok warnings new-body)
            (vl-generate-resolve body idx-ss warnings))

           ((unless ok)
            (mv nil warnings nil))

           (block1 (make-vl-genarrayblock :index current-val
                                          :elems (vl-genelement-case new-body
                                                   :vl-genblock new-body.elems
                                                   :otherwise (list new-body))))

           ((wmv warnings next-value) (vl-consteval nextval idx-ss))

           ((unless (vl-expr-resolved-p next-value))
            (mv nil
                (fatal :type :vl-generate-resolve-fail
                       :msg "~a0: Failed to evaluate the loop increment expression ~a1"
                       :args (list (vl-genelement-fix orig-x) (vl-expr-fix nextval)))
                nil))

           ((mv ok warnings rest-blocks)
            (vl-genloop-resolve (1- clk) body var
                                (vl-resolved->val next-value)
                                nextval continue
                                orig-x ss warnings)))
        (mv ok warnings (cons block1 rest-blocks))))
    ///
    (local (in-theory (disable vl-genblob-resolve (:t vl-genblob-resolve)
                               vl-generate-resolve (:t vl-generate-resolve)
                               vl-generatelist-resolve (:t vl-generatelist-resolve)
                               ;; vl-generateblock-resolve (:t vl-generateblock-resolve)
                               vl-gencaselist-resolve (:t vl-gencaselist-resolve)
                               vl-genloop-resolve (:t vl-genloop-resolve)
                               acl2::mv-nth-cons-meta)))

    (verify-guards vl-generate-resolve
      :hints (("goal" :expand ((vl-gencaselist-p x))))
      :guard-debug t)

    (deffixequiv-mutual vl-generate-resolve)))







(def-genblob-transform vl-genblob-collect-modinst-paramsigs
  ((ss vl-scopestack-p)
   (warnings vl-warninglist-p)
   (modname stringp)
   (sigalist vl-unparam-sigalist-p))
  :parents (xf-unparameterize)
  :short "Collect parameterization signatures needed for module instances of a given module."
  :long "<p>Expects that the module is fully unparameterized, with parameter values
         substituted in everywhere.  Accumulates an unparameterization signature
         alist of instances that require unparameterization.</p>"

  :returns ((successp)
            (warnings vl-warninglist-p)
            (sigalist vl-unparam-sigalist-p))

  (b* (((vl-genblob x) (vl-genblob-fix x))
       (ss (vl-scopestack-push x ss))
       ((mv ok1 warnings insts sigalist)
        (vl-unparam-instlist x.modinsts ss warnings modname sigalist))

       ((mv ok2 warnings sigalist generates)
        (vl-generates-collect-modinst-paramsigs
         x.generates ss warnings modname sigalist)))
    (mv (and ok1 ok2) warnings sigalist
        (change-vl-genblob x :modinsts insts :generates generates)))

  :apply-to-generates vl-generates-collect-modinst-paramsigs
  :combine-bindings ((successp (and successp1 successp2)))
  :empty-list-bindings ((successp t))
  :prepwork ((local (in-theory (disable cons-equal
                                        vl-genelement-p-by-tag-when-vl-scopeitem-p
                                        acl2::subsetp-when-atom-right
                                        default-car default-cdr)))))


(define vl-module-resolve-indices-top ((x vl-module-p)
                                       (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x vl-module-p))
  (b* ((prefs (vl-module-parameter-refs x ss))
       (fns   (vl-module-functions-called x))
       ((mv warnings fntable) (vl-funnames-svex-compile fns ss 1000))
       ((wmv warnings paramtable) (vl-paramrefs-svex-compile prefs 1000))
       ((wmv warnings ?changedp new-x)
        (vl-module-resolve-indices
         x (make-vl-svexconf :ss ss :fns fntable :params paramtable))))
    (mv warnings new-x)))


(define vl-create-unparameterized-module
  ((x vl-module-p)
   (final-paramdecls vl-paramdecllist-p)
   (ss vl-scopestack-p "scopestack with the module's scopeinfo and final parameters"))

  :returns (mv (okp)
               (new-mod vl-module-p)
               (sigalist vl-unparam-sigalist-p))
  (b* (((vl-module x))
       (name (vl-unparam-newname x.name final-paramdecls))
       (warnings x.warnings)
       ((mv ok warnings generates) (vl-generatelist-resolve x.generates ss warnings))
       ((unless ok)
        (mv nil (change-vl-module x :warnings warnings) nil))

       ((mv warnings new-x) (vl-module-resolve-indices-top x ss))

       (mod (change-vl-module new-x
                              :generates generates
                              :name name))

       ;; now change it to a genblob to rewrite the instances & collect the signatures
       (genblob (vl-module->genblob mod))
       ((mv ok warnings sigalist new-genblob)
        (vl-genblob-collect-modinst-paramsigs genblob ss warnings x.name nil))

       (final-mod1 (vl-genblob->module new-genblob mod))
       (final-mod (change-vl-module final-mod1 :warnings warnings)))
    (mv ok final-mod sigalist)))


(defines vl-unparameterize-main
  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (vl-module-p x)
                               (vl-scope-p x))))
             (local (defthm len-equal-0
                      (equal (equal (len x) 0)
                             (not (consp x))))))
  (define vl-unparameterize-main
    ((sig vl-unparam-signature-p "a single signature to expand")
     (sig-ss vl-scopestack-p "the scopestack for this signature")
     (donelist "fast alist of previously-seen signatures")
     (depthlimit natp "termination counter")
     (ss vl-scopestack-p))
    :measure (two-nats-measure depthlimit 0)
    :verify-guards nil
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-mods vl-modulelist-p
                           "All of the modules (not seen before) that you need
                            to meet this signature, including instantiated
                            ones"
                  :hints ('(:in-theory (disable vl-unparameterize-main-list
                                                vl-unparameterize-main)
                            :expand ((vl-unparameterize-main sig sig-ss donelist depthlimit ss)))))
                 (donelist))
    (b* ((sig (vl-unparam-signature-fix sig))
         ((when (hons-get sig donelist)) (mv t nil nil donelist))
         (warnings nil)
         ((when (zp depthlimit))
          (mv nil
              (fatal :type :vl-unparameterize-loop
                     :msg "Recursion depth ran out in unparameterize -- loop ~
                           in the hierarchy?")
              nil donelist))

         (donelist (hons-acons sig t donelist))

         ((vl-unparam-signature sig))
         (mod (vl-scopestack-find-definition sig.modname ss))
         ((unless (and mod (eq (tag mod) :vl-module)))
          (mv nil
              (fatal :type :vl-unparameterize-programming-error
                     :msg "Couldn't find module ~s0"
                     :args (list sig.modname))
              nil donelist))

         ((mv mod-ok new-mod sigalist)
          (vl-create-unparameterized-module mod sig.final-params sig-ss))

         ((mv unparams-ok warnings new-mods donelist)
          (vl-unparameterize-main-list sigalist donelist (1- depthlimit) ss)))
      (mv (and mod-ok unparams-ok)
          warnings (cons new-mod new-mods) donelist)))

  (define vl-unparameterize-main-list ((sigs vl-unparam-sigalist-p)
                                       (donelist)
                                       (depthlimit natp)
                                       (ss vl-scopestack-p))
    :measure (two-nats-measure depthlimit (len (vl-unparam-sigalist-fix sigs)))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-mods vl-modulelist-p
                  :hints ('(:in-theory (disable vl-unparameterize-main-list
                                                vl-unparameterize-main)
                            :expand ((vl-unparameterize-main-list sigs donelist depthlimit ss)))))
                 (donelist))
    (b* ((sigs (vl-unparam-sigalist-fix sigs))
         ((when (atom sigs)) (mv t nil nil donelist))
         ((mv ok1 warnings1 new-mods1 donelist)
          (vl-unparameterize-main (caar sigs) (cdar sigs) donelist depthlimit ss))
         ((mv ok2 warnings2 new-mods2 donelist)
          (vl-unparameterize-main-list (cdr sigs) donelist depthlimit ss)))
      (mv (and ok1 ok2)
          (append warnings1 warnings2)
          (append new-mods1 new-mods2)
          donelist)))
  ///
  (local (in-theory (disable vl-unparameterize-main
                             vl-unparameterize-main-list)))
  (defthm-vl-unparameterize-main-flag
    (defthm true-listp-of-vl-unparameterize-main-warnings
      (true-listp (mv-nth 1 (vl-unparameterize-main sig sig-ss donelist depthlimit ss)))
      :hints ('(:expand ((vl-unparameterize-main sig sig-ss donelist depthlimit ss))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main)
    (defthm true-listp-of-vl-unparameterize-main-list-warnings
      (true-listp (mv-nth 1 (vl-unparameterize-main-list sigs donelist depthlimit ss)))
      :hints ('(:expand ((vl-unparameterize-main-list sigs donelist depthlimit ss))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main-list))

  (defthm-vl-unparameterize-main-flag
    (defthm true-listp-of-vl-unparameterize-main-mods
      (true-listp (mv-nth 2 (vl-unparameterize-main sig sig-ss donelist depthlimit ss)))
      :hints ('(:expand ((vl-unparameterize-main sig sig-ss donelist depthlimit ss))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main)
    (defthm true-listp-of-vl-unparameterize-main-list-mods
      (true-listp (mv-nth 2 (vl-unparameterize-main-list sigs donelist depthlimit ss)))
      :hints ('(:expand ((vl-unparameterize-main-list sigs donelist depthlimit ss))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main-list))

  (verify-guards vl-unparameterize-main)

  (deffixequiv-mutual vl-unparameterize-main
    :hints ((and stable-under-simplificationp
                 (flag::expand-calls-computed-hint
                  clause '(vl-unparameterize-main
                           vl-unparameterize-main-list))))))




(define vl-module-default-signature ((modname stringp)
                                     (ss       vl-scopestack-p)
                                     (warnings vl-warninglist-p))
  :returns (mv (sig (iff (vl-unparam-signature-p sig) sig)
                    "Indicates success")
               (sig-ss vl-scopestack-p)
               (warnings vl-warninglist-p))
  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (vl-module-p x)
                               (vl-scope-p x)))))
  (b* ((modname (string-fix modname))
       (x (vl-scopestack-find-definition modname ss))
       ((unless (and x (eq (tag x) :vl-module)))
        (mv nil
            (vl-scopestack-fix ss)
            (fatal :type :vl-unparam-fail
                   :msg "Programming error: top-level module ~s0 not found"
                   :args (list modname))))

       ((mv ok warnings new-ss final-paramdecls)
        (vl-scope-finalize-params x
                                  (vl-module->paramdecls x)
                                  (make-vl-paramargs-named)
                                  warnings
                                  ss ss
                                  (vl-context modname)))
       ((unless ok) (mv nil (vl-scopestack-fix ss) warnings)))
    (mv (make-vl-unparam-signature :modname modname :final-params final-paramdecls)
        new-ss warnings)))


(define vl-modulelist-default-signatures ((names string-listp)
                                          (ss    vl-scopestack-p)
                                          (warnings vl-warninglist-p))
  :returns (mv (sigs vl-unparam-sigalist-p)
               (warnings vl-warninglist-p))
  (if (atom names)
      (mv nil (vl-warninglist-fix warnings))
    (b* (((mv sig sig-ss warnings) (vl-module-default-signature (car names) ss warnings))
         ((mv sigs warnings) (vl-modulelist-default-signatures (cdr names) ss warnings)))
      (mv (if sig
              (cons (cons sig sig-ss) sigs)
            sigs)
          warnings))))


(define vl-design-unparameterize
  :short "Top-level @(see unparameterization) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (;; Throw out modules that have problems with shadowed parameters.
       ;; We won't need this.
       ;; ((vl-design x) (vl-design-unparam-check x))
       ((vl-design x))
       (ss      (vl-scopestack-init x))
       (topmods (vl-modulelist-toplevel x.mods))

       ;; This is something Sol wanted for Samev.  The idea is to instance
       ;; every top-level module with its default parameters, so that we don't
       ;; just throw away the whole design if someone is trying to check a
       ;; parameterized module.
       ((mv top-sigs warnings) (vl-modulelist-default-signatures topmods ss x.warnings))

       ((mv ?ok warnings1 new-mods donelist)
        (vl-unparameterize-main-list top-sigs nil 1000 ss))

       (warnings (append warnings1 warnings)))
    (fast-alist-free donelist)
    (vl-scopestacks-free)
    (change-vl-design x :warnings warnings :mods new-mods)))
