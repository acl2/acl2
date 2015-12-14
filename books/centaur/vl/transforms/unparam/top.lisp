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
(include-book "centaur/sv/vl/elaborate" :dir :system)
(include-book "../../util/namedb")
;; (include-book "scopesubst")
(include-book "../../mlib/blocks")
(include-book "../../mlib/strip")
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


;; (define vl-paramdecl-resolve-indices-top ((x vl-paramdecl-p)
;;                                           (ss vl-scopestack-p))
;;   :returns (mv (warnings vl-warninglist-p)
;;                (new-x vl-paramdecl-p))
;;   (b* ((prefs (vl-paramdecl-parameter-refs x ss))
;;        (fns   (vl-paramdecl-functions-called x))
;;        ((mv warnings fntable) (vl-funnames-svex-compile fns ss 1000))
;;        ((wmv warnings paramtable) (vl-paramrefs-svex-compile prefs 1000))
;;        ((wmv warnings ?changedp new-x)
;;         (vl-paramdecl-resolve-indices
;;          x (make-vl-svexconf :ss ss :fns fntable :params paramtable))))
;;     (mv warnings new-x)))





(define vl-scopeinfo-resolve-params
  ((x vl-paramdecloverridelist-p)
   (scopeinfo vl-scopeinfo-p
              "Represents the module scope")
   (elabindex "Scoped in the module whose parameters we're overriding.  However,
               the SS in this elabindex is at the global level, and we always push
               the scopeinfo onto the top of it before using it.  This is a bad
               breakage of the elabindex abstraction, but before changing this
               we'd need to think hard about how parameter values and types are
               resolved.")
   (outer-ss vl-scopestack-p
             "Scope of the overrides -- read-only")
   (outer-scope-path vl-elabtraversal-p "How to get to the scopes for the override context")
   (final-params-acc vl-paramdecllist-p)
   (warnings vl-warninglist-p))
  :prepwork ((local (in-theory (e/d (vl-paramdecloverridelist-fix)
                                    (append
                                     acl2::append-when-not-consp)))))
  :returns (mv (successp)
               (warnings vl-warninglist-p)
               (final-params vl-paramdecllist-p)
               (elabindex "with parameters resolved"))
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

  (b* ((outside-module-ss (vl-elabindex->ss))
       (elabindex (vl-elabindex-update-ss
                   (vl-scopestack-push (vl-scopeinfo-fix scopeinfo)
                                       outside-module-ss)
                   elabindex))
       ((when (atom x))
        (mv t (ok)
            (revappend-without-guard
             (vl-paramdecllist-fix final-params-acc) nil)
            elabindex))
       ((vl-paramdecloverride x1) (car x))
       (warnings (ok))


       ((mv ok warnings final-paramdecl elabindex)
        (vl-override-parameter
         x1.decl elabindex x1.override outer-ss outer-scope-path warnings))
       ((unless ok)
        (mv nil warnings nil elabindex))

       ((vl-scopeinfo scopeinfo))
       (new-scopeinfo (change-vl-scopeinfo
                       scopeinfo
                       :locals (hons-acons (vl-paramdecl->name final-paramdecl)
                                           final-paramdecl
                                           scopeinfo.locals)))
       (elabindex (vl-elabindex-update-ss outside-module-ss elabindex)))
    (vl-scopeinfo-resolve-params (cdr x) new-scopeinfo elabindex outer-ss outer-scope-path
                                 (cons final-paramdecl
                                       final-params-acc)
                                 warnings)))


#|
(trace$ #!vl (vl-scope-finalize-params
              :entry (list 'vl-scope-finalize-params
                           (if (eq (tag x) :vl-module)
                               (with-local-ps (vl-pp-module x nil))
                             (tag x))
                           (with-local-ps (vl-pp-paramdecllist formals)))
              :exit (list 'vl-scope-finalize-params
                          (with-local-ps (vl-pp-paramdecllist (nth 3 values))))))
|#



(define vl-scope-finalize-params
  ((formals vl-paramdecllist-p)
   (actuals vl-paramargs-p)
   (warnings vl-warninglist-p)
   (elabindex "in the scope of the instantiated module.  Warning: this function
               returns an elabindex with a somewhat mangled scopestack.")
   (outer-ss vl-scopestack-p)
   (outer-scope-path vl-elabtraversal-p "How to get to the scopes for the override context"))
  :returns (mv (successp)
               (warnings vl-warninglist-p)
               (elabindex "with the overridden parameter values")
               (final-paramdecls vl-paramdecllist-p))
  (b* (((mv ok warnings overrides)
        (vl-make-paramdecloverrides formals actuals warnings))
       ((unless ok)
        (mv nil warnings elabindex nil))
       (mod-ss (vl-elabindex->ss))
       ((mv err mod-scope no-mod-ss)
        (vl-scopestack-case mod-ss
          :local (mv nil mod-ss.top mod-ss.super)
          :global (mv nil mod-ss.design (vl-scopestack-null))
          :null (mv t nil nil)))
       ((when err)
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "Empty scopestack -- expected at least the design scope")
            elabindex nil))
       ;; BOZO Horrible hack: We'll replace the top of the elabindex SS with a
       ;; scope crafted without the paramdecl defaults, and gradually replace
       ;; them with the overridden ones as we compute them.
       (elabindex (vl-elabindex-update-ss no-mod-ss elabindex))
       (scopeinfo (vl-scope->scopeinfo mod-scope (vl-scopestack->design mod-ss)))
       (scopeinfo-with-empty-params
        (change-vl-scopeinfo
         scopeinfo
         ;; Trick: remove the defaults from the parameters as bound in the
         ;; locals, since they don't yet have finalized values.
         :locals (make-fast-alist
                  (vl-paramdecllist-alist
                   (vl-paramdecllist-remove-defaults formals)
                   (vl-scopeinfo->locals scopeinfo)))))
       ((mv ok warnings final-paramdecls elabindex)
        (vl-scopeinfo-resolve-params
         overrides scopeinfo-with-empty-params elabindex outer-ss outer-scope-path nil warnings)))
    (mv ok warnings elabindex
        final-paramdecls)))





(defxdoc vl-unparameterize-flow
  :short "How the heck does unparameterization/elaboration work?"

  :long "<h3>Basic Idea</h3>

<p>Our algorithm processes a list of <i>signatures</i> that specify what
modules we want to create with what parameters.</p>

<p>We start from the top-level modules.  Any module that is never instantiated
is assumed to be a top-level module, and we'll use its default parameters (if
it has parameters).  The initial signature list has the top level modules,
associated with their default parameters.</p>

<p>Recursively, to create a module with a set of parameters, we apply @(see
vl-genblob-resolve), which substitutes the parameter values everywhere they're
needed, and then examines the module instances.  For each module instance that
has parameters, we add to our list of signatures the needed module, and replace
that instance with a parameter-free instance of that module.  (The function
that does this on each instance is @(see vl-unparam-inst).)</p>

<p>When we're done with the current module, we recur on the list of signatures
we accumulated; when we're done with those, we've completely unparameterized
the module and all of its dependencies.  This is what @(see
vl-unparameterize-main) does.</p>

<h3>Tricky Parts</h3>

<h2>Scoping</h2>
<p>When we unparameterize a module instance like</p>

@({
     module supermod ; 
       ...
       foo #(.size(64), .kind(foo_t)) myinst (...) ;
     endmodule
})

<p>The actual parameter arguments (64, foo_t) need to be resolved in the scope
of supermod.  But then, we are going to create a signature for specializing
@('foo') that binds size to 64, kind to foo_t.  What scope are these bindings
relative to?  Our answer is: they need to be independent of scope.</p>

<p>To accomplish this, for value parameters (e.g. size) we insist that the each
value gets resolved to a literal (e.g., 64, \"foo\", etc.), and such literals
are of course independent of scope.  If we can't resolve a parameter, e.g., you
write @('.size(a+b)') and we don't know what a/b are, then we are just going to
fail to unparameterize this.</p>

<p>For type parameters the situation is harder.  We can't simply replace a
named type like foo_t with its definition (recursively), because various rules
in SystemVerilog prohibit that, especially pertaining to signedness.</p>

<blockquote>
<p>(Digression: e.g., consider the type foo_t:</p>
@({
 typedef logic signed [3:0] [5:0] signedarr_t;
 typedef signedarr_t [7:0] foo_t;
 })
<p>You can't define foo_t without a subsidiary typedef, because there's no way
to directly express a multidimensional array of which some inner dimension is
signed.)</p>
</blockquote>

<p>So what to do?  Our approach is to annotate the named type (see @(see
vl-usertype)) with its definition as the @('res') field of the @(see
vl-usertype); any usertypes referenced in the @('res') field also are similarly
annotated with their definitions, recursively.  This is similar to expressing
it as one monolithically defined type, but we can tell which parts are named,
which lets us be faithful to the awkward semantics.  However, the names are
basically vestigial -- we don't generally know what scope they're from, so it
doesn't make sense to look them up anywhere!</p>

<p>In summary: the actual values for type parameters in our signatures are
scope agnostic in the sense that we know we can't trust their names, and in
the sense that we don't need their names to know anything about them, because
we have these @('res') fields to use instead.</p>

<h2>Sharing Isomorphically Parameterized Modules</h2>

<p>If a module is instantiated twice with the same parameters, we don't want to
create two different unparameterized versions of that module.  However, we need
to be careful not to share a definition for two modules whose parameters look
the same, but are actually different.  E.g., a module with a type parameter may
be instantiated twice with two types that have the same name, but refer to
different definitions because they occur in different scopes.</p>

<p>To keep track of this, we create a key for each module instantiation.  Two
module instantiations should produce the same key only if they are
instantiations of the same module, all value parameters resolve to the same
values, and all type parameters are the same up to and including the scope in
which any usertypes are defined.  To track which scope is which, we use @(see
vl-scopestack->hashkey), which reduces a scopestack to a hierarchy of
names.</p>

<p>These instance keys are used to track the generated names of modules, the
parameters used to instantiate them, and 

")




(define vl-unparam-basename-exprstring ((x vl-maybe-expr-p))
  :returns (str stringp :rule-classes :type-prescription)
  :hooks ((:fix :hints(("Goal" :in-theory (enable (tau-system))))))
  (if x
      ;; Why do we care about whether it's resolved?  We don't really.  But we
      ;; thought it was really ugly to see unparameterized module names such as
      ;; foo$size=32'sd5.  We'd rather see foo$size=5.  And very frequently,
      ;; parameter names are indeed resolved plain signed integers.  So this is
      ;; purely an aesthetic hack and there's no reason to ever think about
      ;; whether these are unique or anything.
      (if (and (vl-expr-resolved-p x)
               (b* (((mv & size) (vl-expr-selfsize x nil nil))
                    ((mv & type) (vl-expr-typedecide x nil nil)))
                 (and (eql size 32) (eq type :vl-signed))))
          (str::natstr (vl-resolved->val x))
        ;; Generic, safe but stupid way to get a name that should be reasonably
        ;; intuitive and reasonably unique.
        (acl2::substitute #\_ #\Space (vl-pps-expr x)))
    "NULL"))

(define vl-unparam-basename-aux ((x vl-paramdecllist-p)
                                &key (ps 'ps))
  :parents (vl-unparam-basename)
  (b* (((when (atom x)) ps)
       ((vl-paramdecl x1) (car x))
       ((when x1.localp)
        ;; we think localparams are always determined by the nonlocal params,
        ;; so we don't need to include them in the name.
        (vl-unparam-basename-aux (cdr x)))
       ((the string name-part)
        (acl2::substitute #\_ #\Space x1.name))
       ((the string type-expr-part)
        (vl-paramtype-case x1.type
          :vl-implicitvalueparam (vl-unparam-basename-exprstring x1.type.default)
          :vl-explicitvalueparam (vl-unparam-basename-exprstring x1.type.default)
          :vl-typeparam (if x1.type.default
                            (acl2::substitute #\_ #\Space
                                              (with-local-ps (vl-pp-datatype x1.type.default)))
                          "NULL"))))
    (vl-ps-seq (vl-print "$")
               (vl-print-str name-part)
               (vl-print "=")
               (vl-print-str type-expr-part)
               (vl-unparam-basename-aux (cdr x)))))


;; actualkey:
;;    for a value parameter:
;;      if the actual is (can be?) resolved, then its resolution
;;      else, we have a problem anyway and maybe we just want to fail
;;    for a type parameter:
;;      if a type containing no names, then just itself
;;        -- actually use something like the strip of itself
;;      if a user-defined type name like foo_t or bar::foo_t or baz.bar.foo_t, then
;;         look up the scope for foo_t and get its hash key
;;         pair this key with modified type replacing the scoped name with just
;;         the local name & otherwise stripping expressions
;;              e.g.,  (root.mymod . foo_t) if locally defined
;;                     (root.bar . foo_t) if imported from package bar
;;                     or similar
;;      if something more complex, e.g., a struct/union containing names
;;         use the current scope's hash key
;;         pair it with the type itself

;; For a particular module instance, we'll construct an instkey consisting of
;; the original module name and the list of actualkeys of the parameters.  This
;; (we hope) identifies the combination of module and parameters just uniquely
;; enough, i.e. it's sensitive enough to scoping to know which type you are
;; talking about, but mostly insensitive to the exact phrasing of expressions,
;; different ways to refer to the same type, the particular scope you happen to
;; be in when referencing types, etc.

(define vl-unparam-actualkey ((x vl-paramdecl-p)
                              (inst-ss vl-scopestack-p "instantiating context")
                              (mod-ss  vl-scopestack-p "instantiated module context"))
  :returns (actualkey)
  (b* (((vl-paramdecl x)))
    (vl-paramtype-case x.type
      :vl-implicitvalueparam (and x.type.default
                                  (vl-expr-strip x.type.default))
      :vl-explicitvalueparam 
      ;; I think we only need to care about the default value (which at this
      ;; point is the final value).  I think we can ignore the type.  Why?
      ;; I think the only way that the parameter's type can vary from one
      ;; instantiation to the next is if it is, itself, a parameterized
      ;; type, or includes a parameterized type, e.g., in bar or baz below:
      ;;
      ;;    parameter type T = foo_t;
      ;;    localparameter T bar = 0;
      ;;    localparameter struct { T a; } baz = 0;
      ;; 
      ;; But in that case, we'll have some previous type parameter that
      ;; will be part of the instkey, and that should end up being different.
      ;; So just look at the value.
      (and x.type.default
           (vl-expr-strip x.type.default))
      :vl-typeparam
      (b* (((unless x.type.default)
            (raise "no default on type parameter ~x0~%" x))
           (has-usertypes (vl-datatype-has-usertypes x.type.default))
           ((unless has-usertypes) (vl-datatype-strip x.type.default)))
        ;; Has usertypes.  If it is itself a usertype, look it up, modify the
        ;; type to change the name to its final name component, pair this with
        ;; the scopekey where it is found.  Otherwise, pair the type with the
        ;; scopekey for the local scopestack -- not great but good enough.
        ;; BOZO this probably doesn't work if the typedef depends on parameters
        ;; that vary in different module instantiations!
        (vl-datatype-case x.type.default
          :vl-usertype
          (b* (((mv err trace ?context tail)
                (vl-follow-scopeexpr x.type.default.name
                                     (if x.overriddenp inst-ss mod-ss)))
               ((when err) (raise "Error resolving type name: ~x0~%"
                                  err))
               ((vl-hidstep step) (car trace))
               (scopekey (vl-scopestack->hashkey step.ss))
               (newtypename (make-vl-scopeexpr-end :hid tail)))
            (hons (vl-datatype-strip
                   (change-vl-usertype x.type.default
                                       :name newtypename))
                  scopekey))
          :otherwise
          (b* ((scopekey (vl-scopestack->hashkey (if x.overriddenp inst-ss mod-ss))))
            (hons (vl-datatype-strip x.type.default) scopekey)))))))

(defprojection vl-unparam-actualkeys ((x vl-paramdecllist-p)
                                      (inst-ss vl-scopestack-p)
                                      (mod-ss  vl-scopestack-p))
  :returns (actualkeys)
  ;; bozo add option to defprojection to make this a honsed list
  (vl-unparam-actualkey x inst-ss mod-ss))


(define vl-unparam-instkey-p ((x))
  :short "Mainly, the type of an element produced by vl-unparam-inst->instkey."
  (and (consp x)
       (stringp (car x)))
  ///
  (define vl-unparam-instkey-fix ((x vl-unparam-instkey-p))
    :returns (new-x vl-unparam-instkey-p)
    (mbe :logic (if (vl-unparam-instkey-p x) x '(""))
         :exec x)
    ///
    (defret vl-unparam-instkey-fix-idempotent
      (implies (vl-unparam-instkey-p x)
               (equal new-x x)))
    (fty::deffixtype vl-unparam-instkey
      :pred vl-unparam-instkey-p
      :fix vl-unparam-instkey-fix
      :equiv vl-unparam-instkey-equiv
      :define t)))

(fty::deflist vl-unparam-instkeylist :elt-type vl-unparam-instkey)

(define vl-unparam-inst->instkey ((origname stringp)
                                  (paramdecls vl-paramdecllist-p)
                                  (inst-ss vl-scopestack-p
                                           "scopestack from the instantiating context")
                                  (mod-ss  vl-scopestack-p
                                           "scopestack from the instantiated module
                                            context (just paramdecls)"))
  :returns (instkey vl-unparam-instkey-p
                    :hints(("Goal" :in-theory (enable vl-unparam-instkey-p))))
  (hons (string-fix origname) (vl-unparam-actualkeys paramdecls inst-ss mod-ss)))

(defprod vl-unparam-signature
  ((modname stringp)
   (newname stringp)
   (final-params vl-paramdecllist-p)
   ;; BOZO We used to pass the svexconf from the parameter override step with
   ;; the signature and use it to elaborate the new module.  This seems
   ;; overcomplicated and error prone to me now, but I don't understand why we
   ;; used to do it.  Just for efficiency?  Doesn't seem like we'd gain that much.
   ;; (svexconf vl-svexconf-p)
   )
  :short "An unparam signature describes a module/parameter combo that needs to be created."
  :long "<p>Note on the final-params: These are relative to the scope of some
instantiating module.  That doesn't matter for value parameters, because they
must all be resolved to literal expressions anyway.  Type parameters should be
resolved such that the usertype names are vestigial and the relevant definition
for each usertype is stored in the res field.</p>"
  :layout :tree)

;; (fty::deflist vl-unparam-signaturelist :elt-type vl-unparam-signature
;;   :elementp-of-nil nil)

;; (fty::defalist vl-unparam-sigalist :key-type vl-unparam-signature
;;   :val-type vl-svexconf-p)
  

(fty::defalist vl-unparam-instkeymap
  :key-type vl-unparam-instkey
  :val-type vl-unparam-signature)


(defprod vl-unparam-ledger
  ((ndb   vl-namedb
         "For generating fresh names in case of conflicts that can arise due to
          local names.  For instance, two different modules could define their
          own (different) state_t types and use it as a type parameter to some
          submodule foo.  If that happens, we need to generate new names like foo$state_t
          that are distinct.  Initially this needs to contain all of top-level
          names of the design.  We'll extend it with all new module names that
          we generate.")
   (instkeymap vl-unparam-instkeymap
            "Mapping from instkey to new module name that we've assigned so
             far.  Fast alist.")))


(define vl-unparam-basename 
  :short "Generate a new name for an unparameterized module."
  ((origname stringp              "Original name of the module, e.g., @('my_adder').")
   (paramdecls vl-paramdecllist-p "Final, overridden paramdecls for the module."))
  :returns (new-name stringp :rule-classes :type-prescription
                     "New, mangled name, e.g., @('my_adder$size=5').")
  (with-local-ps (vl-ps-seq (vl-print-str origname)
                            (vl-unparam-basename-aux paramdecls))))

(define vl-paramdecllist-all-localp ((x vl-paramdecllist-p))
  (if (atom x)
      t
    (and (vl-paramdecl->localp (car x))
         (vl-paramdecllist-all-localp (cdr x)))))

#|
(trace$ #!vl (vl-unparam-add-to-ledger
              :entry (list 'vl-unparam-add-to-ledger
                           origname
                           (with-local-ps (vl-pp-paramdecllist paramdecls))
                           ledger)
              :exit (b* (((list instkey ledger) values))
                      (list 'vl-unparam-add-to-ledger
                            instkey ledger))))

|#

(define vl-unparam-add-to-ledger
  :short "Generate an instkey for an unparameterized module and add it to the ledger
          if it isn't there already."
  ((origname stringp              "Original name of the module, e.g., @('my_adder').")
   (paramdecls vl-paramdecllist-p "Final, overridden paramdecls for the module.")
   (ledger     vl-unparam-ledger-p  "Ledger for disambiguating generated module names")
   (inst-ss         vl-scopestack-p "Scopestack for the instantiating context")
   (mod-ss          vl-scopestack-p "Scopestack for the instantiated module"))
  :returns (mv (instkey vl-unparam-instkey-p "Instance key uniquely identifying
                                              the module/parameter combo.")
               (ledger vl-unparam-ledger-p "Updated ledger whose instkeymap
                                                binds the instkey."))
  (b* (((vl-unparam-ledger ledger) (vl-unparam-ledger-fix ledger))
       (origname (string-fix origname))
       (instkey (vl-unparam-inst->instkey origname paramdecls inst-ss mod-ss))
       (existing (cdr (hons-get instkey ledger.instkeymap)))
       ((when existing)
        ;; This module has already been named -- just return the existing name.
        (mv instkey ledger))
       ((when (vl-paramdecllist-all-localp paramdecls))
        ;; If there are no parameters, or there are only localparams, preserve
        ;; the original name of the module.
        (b* ((signature (make-vl-unparam-signature :modname origname
                                                   :newname origname
                                                   :final-params paramdecls))
             (instkeymap (hons-acons instkey signature ledger.instkeymap)))
          (mv instkey (change-vl-unparam-ledger ledger
                                                :instkeymap instkeymap))))
       ;; Haven't named this particular combination yet: generate the name,
       ;; uniquify it, and add it to the ledger.
       (basename (vl-unparam-basename origname paramdecls))
       ((mv newname ndb) (vl-namedb-plain-name basename ledger.ndb))
       (signature (make-vl-unparam-signature :modname origname
                                             :newname newname
                                             :final-params paramdecls))
       (instkeymap (hons-acons instkey signature ledger.instkeymap)))
    (mv instkey (change-vl-unparam-ledger ledger
                                          :ndb ndb
                                          :instkeymap instkeymap)))
  ///
  (defret vl-unparam-add-to-ledger-binds-instkey
    (hons-assoc-equal instkey (vl-unparam-ledger->instkeymap ledger))))


(define vl-unparam-add-to-ledger-without-renaming
  :short "Generate an instkey for an unparameterized module and add it to the ledger
          without munging the name to reflect unparameterization."
  ((origname stringp              "Original name of the module, e.g., @('my_adder').")
   (paramdecls vl-paramdecllist-p "Final, overridden paramdecls for the module.")
   (ledger     vl-unparam-ledger-p  "Ledger for disambiguating generated module names")
   (inst-ss         vl-scopestack-p "Scopestack for the instantiating context")
   (mod-ss          vl-scopestack-p "Scopestack for the instantiated module"))
  :returns (mv (instkey vl-unparam-instkey-p "Instance key uniquely identifying
                                              the module/parameter combo.")
               (ledger vl-unparam-ledger-p "Updated ledger whose instkeymap
                                                binds the instkey."))
  (b* (((vl-unparam-ledger ledger) (vl-unparam-ledger-fix ledger))
       (origname (string-fix origname))
       (instkey (vl-unparam-inst->instkey origname paramdecls inst-ss mod-ss))
       (existing (cdr (hons-get instkey ledger.instkeymap)))
       ((when existing)
        ;; This module has already been named -- just return the existing name.
        (mv instkey ledger))
       (signature (make-vl-unparam-signature :modname origname
                                             :newname origname
                                             :final-params paramdecls))
       (instkeymap (hons-acons instkey signature ledger.instkeymap)))

    (mv instkey (change-vl-unparam-ledger ledger
                                          :instkeymap instkeymap)))
  ///
  (defret vl-unparam-add-to-ledger-without-renaming-binds-instkey
    (hons-assoc-equal instkey (vl-unparam-ledger->instkeymap ledger))))


(define vl-unparam-inst
  :parents (unparameterization)
  :short "Compute the final parameter values for a single module instance."
  ((inst     vl-modinst-p
             "Instance of some module.  The module being instantiated may or
              may not have parameters.")
   (elabindex "at the instanting context")
   (ledger  vl-unparam-ledger-p)
   (warnings vl-warninglist-p
             "Warnings accumulator for the submodule."))
  :guard-debug t
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (inst     vl-modinst-p
                "Updated module instance, perhaps instantiating a new module
                 like @('my_adder$width=5') instead of @('my_adder').")
      (instkey (implies successp (vl-unparam-instkey-p instkey))
                "An instkey for the instantiated module, if needed. Note: Currently
                 we produce an instkey even if there are no parameters.  Not sure
                 why we need to do this.")
      (new-elabindex)
      (ledger         vl-unparam-ledger-p))

  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (vl-module-p x)
                               (vl-scope-p x))))
             (local (defthm vl-scope-p-when-vl-interface-p-strong
                      (implies (vl-interface-p x)
                               (vl-scope-p x)))))

  (b* (((vl-modinst inst) (vl-modinst-fix inst))
       (ledger (vl-unparam-ledger-fix ledger))
       (ss (vl-elabindex->ss))
       (scopes (vl-elabindex->scopes))
       ((mv mod mod-ss) (vl-scopestack-find-definition/ss inst.modname ss))
       ((unless (and mod
                     (or (eq (tag mod) :vl-module)
                         (eq (tag mod) :vl-interface))))
        (vl-unparam-debug "~a0: can't find module ~a1.~%" inst inst.modname)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: trying to instantiate undefined module ~s1."
                   :args (list inst inst.modname))
            inst nil elabindex ledger))

       (mod.paramdecls (if (eq (tag mod) :vl-module)
                           (vl-module->paramdecls mod)
                         (vl-interface->paramdecls mod)))

       ;; ((when (atom mod.paramdecls))
       ;;  ;; Optimization.  In the common case there are no parameter
       ;;  ;; declarations for the submodule.  In this case, all we need to do is
       ;;  ;; make sure the instance is also parameter-free.
       ;;  (if (vl-paramargs-empty-p inst.paramargs)
       ;;      (b* (((mv instkey ledger) (vl-unparam-add-to-ledger
       ;;                                 inst.modname nil ledger conf.ss)))
       ;;        (mv t (ok) inst instkey ledger))
       ;;    (mv nil
       ;;        (fatal :type :vl-bad-instance
       ;;               :msg "~a0: parameter arguments given to ~s1, but ~s1 ~
       ;;                     does not take any parameters."
       ;;               :args (list inst inst.modname))
       ;;        inst nil
       ;;        ledger)))
       
       (elabindex (vl-elabindex-traverse mod-ss (list (vl-elabinstruction-root))))
       (elabindex (vl-elabindex-push mod))

       ((mv ok warnings elabindex final-paramdecls)
        (vl-scope-finalize-params mod.paramdecls
                                  inst.paramargs
                                  warnings
                                  elabindex
                                  ss
                                  (rev (vl-elabscopes->elabtraversal scopes))))

       (inside-mod-ss (vl-elabindex->ss))
       (elabindex (vl-elabindex-undo)) ;; back at global scope
       
       ((unless ok)
        ;; already warned
        (vl-unparam-debug "~a0: failed to finalize params~%" inst)
        (b* ((elabindex (vl-elabindex-undo))) ;; back to original scope
          (mv nil warnings inst nil elabindex ledger)))

       ;; Weird case: A type parameter B can have a default value that
       ;; references a previous type parameter A.  If this is the case and B is
       ;; not overridden, then we won't find the definition for B just by
       ;; looking in the instantiating scope; we need to look in the module
       ;; scope (but only the paramdecls are relevant).  So we need to pass
       ;; both the scopestack from the instantiating context and the scopestack
       ;; from the module (returned from scope-finalize-params).  The name of
       ;; the scope is kind of wrong -- it's the original module name.  But the
       ;; key that we generate still differentiates between differently
       ;; parameterized versions of the module, because for any parameter that
       ;; differs, either (1) it is overridden differently between the two
       ;; versions, in which case it's instname component will be different, or
       ;; (2) it depends on another parameter that differs.

       ((mv instkey ledger)
        (vl-unparam-add-to-ledger inst.modname final-paramdecls ledger ss
                                  inside-mod-ss))

       ((vl-unparam-signature sig)
        (cdr (hons-get instkey (vl-unparam-ledger->instkeymap ledger))))

       (new-inst (change-vl-modinst inst
                                    :modname sig.newname
                                    :paramargs (make-vl-paramargs-named)))

       ;; Now, our elabindex is kind of messed up in that we now have the
       ;; un-mangled module name associated with some info that depends on the
       ;; particular parameters.  Fix this by associating that info with the
       ;; new module name, and clobbering the info associated with the
       ;; unmangled name.
       (scopes (vl-elabindex->scopes))
       (mod-scope (vl-elabscopes-subscope (vl-elabkey-def inst.modname)
                                          (vl-elabindex->scopes)))
       ;; Do it in this order in case inst.modname and sig.newname are the same!
       (scopes (b* (((unless mod-scope) scopes)
                    (scopes (vl-elabscopes-update-subscope (vl-elabkey-def inst.modname)
                                              (make-vl-elabscope) scopes)))
                 (vl-elabscopes-update-subscope (vl-elabkey-def sig.newname)
                                                mod-scope scopes)))
       (elabindex (vl-elabindex-update-scopes scopes elabindex))
       ;; Go back to original instantiating scope.
       (elabindex (vl-elabindex-undo)))

    (vl-unparam-debug "~a0: success, new instance is ~a1.~%" inst new-inst)
    (mv t warnings new-inst instkey elabindex ledger)))

(define vl-unparam-instlist ((x vl-modinstlist-p)
                             (elabindex
                              "where the instances occur")
                             (ledger         vl-unparam-ledger-p)
                             (warnings vl-warninglist-p
                                       "Warnings accumulator for the submodule.")
                             (keylist  vl-unparam-instkeylist-p "Accumulator"))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (insts    vl-modinstlist-p
                         "Updated module instances")
               (keylist  vl-unparam-instkeylist-p "Needed instkeys")
               (new-elabindex)
               (ledger         vl-unparam-ledger-p))
  ;; :hooks ((:fix :hints(("Goal" :in-theory (disable (:d vl-unparam-instlist))
  ;;                       :induct (vl-unparam-instlist x ss warnings modname sigalist)
  ;;                       :expand ((:free (ss warnings modname sigalist)
  ;;                                 (vl-unparam-instlist x ss warnings modname sigalist))
  ;;                                (:free (ss warnings modname sigalist)
  ;;                                 (vl-unparam-instlist
  ;;                                  (vl-modinstlist-fix x)
  ;;                                  ss warnings modname sigalist)))))))
  (b* (((when (atom x)) (mv t (ok) nil (vl-unparam-instkeylist-fix keylist)
                            elabindex (vl-unparam-ledger-fix ledger)))
       ((mv ok1 warnings inst1 instkey1 elabindex ledger)
        (vl-unparam-inst (car x) elabindex ledger warnings))
       (keylist (if ok1 (cons instkey1 keylist) keylist))
       ((mv ok2 warnings insts2 keylist elabindex ledger)
        (vl-unparam-instlist (cdr x) elabindex ledger warnings keylist)))
    (mv (and ok1 ok2) warnings (cons inst1 insts2) keylist elabindex ledger)))


(define vl-gencase-match ((x vl-expr-p)
                          (y vl-expr-p)
                          (ss vl-scopestack-p)
                          (scopes vl-elabscopes-p)
                          (warnings vl-warninglist-p))
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (equalp))
  (b* ((eq-expr (make-vl-binary :op :vl-binary-ceq
                                :left x :right y))
       (warnings (ok))
       ((wmv warnings res) (vl-consteval eq-expr ss scopes))
       ((mv ok result)
        (vl-expr-case res
          :vl-literal (vl-value-case res.val
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
                               (scopes vl-elabscopes-p)
                               (warnings vl-warninglist-p))
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (equalp))
  (b* (((when (atom y)) (mv t (ok) nil))
       ((mv ok warnings first) (vl-gencase-match x (car y) ss scopes warnings))
       ((unless ok) (mv nil warnings nil))
       ((when first) (mv ok warnings first)))
    (vl-gencase-some-match x (cdr y) ss scopes warnings)))


#|
(trace$ #!vl (vl-genblob-resolve-aux
              :entry (list 'vl-genblob-resolve-aux
                           (with-local-ps (vl-pp-genblob x nil)))
              :exit (list 'vl-genblob-resolve-aux
                          (with-local-ps (vl-pp-genblob (nth 3 values) nil)))))
|#




(with-output :off (event)
  :evisc (:gag-mode (evisc-tuple 3 4 nil nil ))
  ;; Elaborates, resolves generates.  Collects signatures required for modinsts.
  (defines vl-generate-resolve
    :prepwork ((local (include-book "centaur/misc/arith-equivs" :dir :system))
               (local (in-theory (disable
                                  cons-equal
                                  vl-genelement-p-by-tag-when-vl-scopeitem-p
                                  vl-genelement-p-by-tag-when-vl-ctxelement-p
                                  vl-genelement-p-when-member-equal-of-vl-genelementlist-p
                                  append
                                  acl2::append-when-not-consp
                                  acl2::true-listp-append
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
                                                          vl-genelementlist-count)))))
               (local (defthm vl-genblob-count-of-change-all-but-generates
                        (equal (vl-genblob-count
                                (make-vl-genblob :generates (vl-genblob->generates x)
                                                 :portdecls portdecls
                                                 :assigns assigns
                                                 :aliases aliases
                                                 :vardecls vardecls
                                                 :paramdecls paramdecls
                                                 :fundecls fundecls
                                                 :taskdecls taskdecls
                                                 :modinsts modinsts
                                                 :gateinsts gateinsts
                                                 :alwayses alwayses
                                                 :initials initials
                                                 :finals finals
                                                 :typedefs typedefs
                                                 :imports imports
                                                 :fwdtypedefs fwdtypedefs
                                                 :modports modports
                                                 :genvars genvars
                                                 :properties properties
                                                 :sequences sequences
                                                 :assertions assertions
                                                 :cassertions cassertions
                                                 :dpiimports dpiimports
                                                 :dpiexports dpiexports
                                                 :ports ports
                                                 :scopetype scopetype
                                                 :name name))
                               (vl-genblob-count x))
                        :hints (("goal" :expand ((:free (x) (vl-genblob-count x))))))))
    (define vl-genblob-resolve-aux ((x vl-genblob-p)
                                    (elabindex "in the genblob's own scope")
                                    (ledger vl-unparam-ledger-p)
                                    (warnings vl-warninglist-p))
      :returns (mv (ok)
                   (warnings1 vl-warninglist-p)
                   (keylist vl-unparam-instkeylist-p)
                   (new-x vl-genblob-p)
                   (new-elabindex)
                   (ledger vl-unparam-ledger-p))
      :measure (two-nats-measure (vl-genblob-count x) 0)
      (b* (((vl-genblob x) (vl-genblob-fix x))
           (ledger (vl-unparam-ledger-fix ledger))
           ;; ((mv ok warnings x-ss ?final-paramdecls)
           ;;  ;; BOZO figure out a real context
           ;;  (vl-scope-finalize-params x x.paramdecls
           ;;                            (make-vl-paramargs-named)
           ;;                            warnings ss ss 'fake-context-for-unparam))
           ;; ((unless ok) (mv nil warnings (vl-genblob-fix x)))
           ;; (x (change-vl-genblob x :paramdecls final-paramdecls))
           ((wmv ?ok warnings new-x elabindex)
            (vl-genblob-elaborate x elabindex))

           ((mv ok warnings keylist1 new-generates elabindex ledger)
            ;; Not new-x.generates (complicates termination)
            (vl-generatelist-resolve x.generates elabindex ledger warnings))

           ((vl-genblob new-x))
           ((mv ok2 warnings new-insts keylist elabindex ledger)
            (vl-unparam-instlist new-x.modinsts elabindex ledger warnings nil)))
        (mv (and ok ok2)
            warnings (append-without-guard keylist1 keylist)
            (change-vl-genblob new-x :generates new-generates
                               :modinsts new-insts)
            elabindex
            ledger)))


    (define vl-genblob-resolve ((x vl-genblob-p)
                                (elabindex
                                    "without the genblob's scope")
                                (ledger vl-unparam-ledger-p)
                                (warnings vl-warninglist-p))
      :returns (mv (ok)
                   (warnings1 vl-warninglist-p)
                   (keylist vl-unparam-instkeylist-p)
                   (new-x vl-genblob-p)
                   (new-elabindex)
                   (ledger vl-unparam-ledger-p))
      :measure (two-nats-measure (vl-genblob-count x) 5)
      ;; wrapper around vl-genblob-elaborate that finalizes the params.
      (b* ((ledger (vl-unparam-ledger-fix ledger))
           ((vl-genblob x) (vl-genblob-fix x))
           ((vl-elabindex elabindex))
           (elabindex (vl-elabindex-push x))
           ((mv ok warnings elabindex paramdecls)
            (vl-scope-finalize-params x.paramdecls
                                      (make-vl-paramargs-named)
                                      warnings elabindex elabindex.ss
                                      (caar (vl-elabindex->undostack elabindex))))
           (elabindex (vl-elabindex-undo))
           ((unless ok)
            (mv nil warnings nil x elabindex ledger))
           (x1 (change-vl-genblob x :paramdecls paramdecls))
           (elabindex (vl-elabindex-push x1))
           ((mv ok warnings keylist new-x elabindex ledger)
            (vl-genblob-resolve-aux x1 elabindex ledger warnings))
           (elabindex (vl-elabindex-undo)))
        (mv ok warnings keylist new-x elabindex ledger)))


#||
 (trace$
 #!vl (vl-generate-resolve
       :entry (list 'vl-generate-resolve
                    (with-local-ps (vl-pp-genelement x))
                    :conf conf)
       :exit (b* (((list ok warnings1 ?sigalist new-x) values)
                  (warnings (take (- (len warnings1) (len warnings)) warnings1)))
               (list 'vl-generate-resolve
                     ok
                     (with-local-ps (vl-print-warnings warnings))
                     (with-local-ps (vl-pp-genelement new-x))))))


||#

    ;; For consistency with svex, we need to be very careful about exactly when
    ;; we push frames onto the scopestack.  The svex scheme is that any
    ;; generate construct produces a nested module, and loops/arrays produce a
    ;; module for the whole loop/array plus modules inside it for each
    ;; repetition.  So we need to take care to follow the same discipline.

    (define vl-generate-resolve
      ((x vl-genelement-p "The generate block to resolve")
       (elabindex)
       (ledger vl-unparam-ledger-p)
       (warnings vl-warninglist-p))
      :returns (mv (ok)
                   (warnings1 vl-warninglist-p)
                   (keylist vl-unparam-instkeylist-p)
                   (new-x vl-genelement-p)
                   (new-elabindex)
                   (ledger vl-unparam-ledger-p))
      :measure (two-nats-measure (vl-genblob-generate-count x) 0)
      :verify-guards nil
      (b* ((x (vl-genelement-fix x))
           (ledger (vl-unparam-ledger-fix ledger)))
        (vl-genelement-case x
          :vl-genbase (b* ((xlist (list x))
                           (blob (vl-sort-genelements xlist))
                           ((mv ok warnings keylist new-blob elabindex ledger)
                            (vl-genblob-resolve blob elabindex ledger warnings))
                           ((unless ok) (mv nil warnings keylist (vl-genelement-fix x) elabindex ledger)))
                        (mv t warnings keylist
                            (make-vl-genblock
                             :elems (vl-genblob->elems new-blob xlist)
                             :loc (vl-modelement->loc x.item))
                            elabindex
                            ledger))

          :vl-genblock
          (b* ((blob (vl-sort-genelements x.elems
                                          :scopetype :vl-genblock
                                          :name x.name))
               ((mv ok warnings keylist new-blob elabindex ledger)
                (vl-genblob-resolve blob elabindex ledger warnings))
               ((unless ok)
                (mv nil warnings keylist x elabindex ledger)))
            (mv t warnings keylist
                (change-vl-genblock x :elems (vl-genblob->elems new-blob x.elems))
                elabindex
                ledger))


          ;; Didn't expect to see these resolved forms yet; leave them.

          :vl-genarray
          (mv t (warn :type :vl-already-resolved-generate
                      :msg "~a0: Didn't expect to see an already-resolved genarray."
                      :args (list x))
              nil x elabindex ledger)

          :vl-genif
          (b* (((vl-elabindex elabindex))
               ((wmv warnings testval) (vl-consteval x.test elabindex.ss elabindex.scopes))
               ((unless (vl-expr-resolved-p testval))
                (mv nil (fatal :type :vl-generate-resolve-fail
                               :msg "~a0: Failed to evaluate the test expression ~a1."
                               :args (list x x.test))
                    nil x elabindex ledger))
               (testval (vl-resolved->val testval))
               (subelem (if (eql 0 testval) x.else x.then)))
            (vl-generate-resolve subelem elabindex ledger warnings))

          :vl-gencase
          ;; BOZO the sizing on this may be wrong
          (b* (((mv ok warnings keylist elem elabindex ledger)
                (vl-gencaselist-resolve x.cases x.test x elabindex ledger warnings))
               ((when elem) (mv ok warnings keylist elem elabindex ledger)))
            (vl-generate-resolve x.default elabindex ledger warnings))

          :vl-genloop
          (b* (((vl-elabindex elabindex))
               ((wmv warnings initval) (vl-consteval x.initval elabindex.ss elabindex.scopes))
               ((unless (vl-expr-resolved-p initval))
                (mv nil (fatal :type :vl-generate-resolve-fail
                               :msg "~a0: Failed to evaluate the initial value expression ~a1."
                               :args (list x x.initval))
                    nil x elabindex ledger))
               ((unless (vl-genelement-case x.body :vl-genblock))
                (mv nil (Fatal :type :vl-generate-resolve-fail
                               :msg "~a0: Body of generate loop should have been coerced to a block."
                               :args (list x))
                    nil x elabindex ledger))
               (body.name (vl-genblock->name x.body))
               ;; ((mv body.name body.elems)
               ;;  (if (eql (vl-genelement-kind x.body) :vl-genblock)
               ;;      (mv (vl-genblock->name x.body) (vl-genblock->elems x.body))
               ;;    (mv nil (list x.body))))
               ;; (blob (vl-sort-genelements body.elems
               ;;                            :scopetype :vl-genarrayblock
               ;;                            :name nil))
               ((mv ok warnings keylist arrayblocks elabindex ledger)
                (vl-genloop-resolve 100000 ;; recursion limit
                                    x.body
                                    x.var (vl-resolved->val initval)
                                    x.nextval x.continue
                                    x elabindex ledger warnings)))
            (mv ok warnings keylist
                (make-vl-genarray :name body.name :var x.var :blocks arrayblocks
                                  :loc x.loc)
                elabindex
                ledger)))))


    (define vl-generatelist-resolve ((x vl-genelementlist-p)
                                     (elabindex)
                                     (ledger vl-unparam-ledger-p)
                                     (warnings vl-warninglist-p))
      :returns (mv (ok)
                   (warnings1 vl-warninglist-p)
                   (keylist vl-unparam-instkeylist-p)
                   (new-elems vl-genelementlist-p)
                   (new-elabindex)
                   (ledger vl-unparam-ledger-p))
      :measure (two-nats-measure (vl-genblob-generates-count x) 0)
      (b* ((ledger (vl-unparam-ledger-fix ledger))
           ((when (atom x)) (mv t (ok) nil nil elabindex ledger))
           ((mv ok1 warnings keylist1 first elabindex ledger)
            (vl-generate-resolve (car x) elabindex ledger warnings))
           ((mv ok2 warnings keylist2 rest elabindex ledger)
            (vl-generatelist-resolve (cdr x) elabindex ledger warnings)))
        (mv (and ok1 ok2) warnings
            (append-without-guard keylist1 keylist2)
            (cons first rest)
            elabindex ledger)))



    (define vl-gencaselist-resolve ((x vl-gencaselist-p)
                                    (test vl-expr-p)
                                    (orig-x vl-genelement-p)
                                    (elabindex)
                                    (ledger vl-unparam-ledger-p)
                                    (warnings vl-warninglist-p))
      :guard (eq (vl-genelement-kind orig-x) :vl-gencase)
      :returns (mv (ok)
                   (warnings1 vl-warninglist-p)
                   (keylist vl-unparam-instkeylist-p)
                   (new-elem (iff (vl-genelement-p new-elem) new-elem))
                   (new-elabindex)
                   (ledger vl-unparam-ledger-p))
      :measure (two-nats-measure (vl-genblob-gencaselist-count x) 0)
      (b* ((ledger (vl-unparam-ledger-fix ledger))
           (x (vl-gencaselist-fix x))
           ((when (atom x)) (mv t (ok) nil nil elabindex ledger))

           ((cons exprs1 block1) (car x))

           ((vl-elabindex elabindex))
           ((mv ok warnings matchp) (vl-gencase-some-match test exprs1 elabindex.ss elabindex.scopes warnings))
           ((unless ok)
            (mv nil warnings nil (vl-genelement-fix orig-x) elabindex ledger))
           ((unless matchp)
            (vl-gencaselist-resolve (cdr x) test orig-x elabindex ledger warnings)))
        (vl-generate-resolve block1 elabindex ledger warnings)))

    (define vl-genloop-resolve ((clk natp "recursion limit")
                                (body vl-genelement-p)
                                (var   stringp)
                                (current-val integerp)
                                (nextval vl-expr-p)
                                (continue vl-expr-p)
                                (orig-x vl-genelement-p)
                                (elabindex)
                                (ledger vl-unparam-ledger-p)
                                (warnings vl-warninglist-p))
      :returns (mv (ok)
                   (warnings1 vl-warninglist-p)
                   (keylist vl-unparam-instkeylist-p)
                   (new-blocks vl-genarrayblocklist-p)
                   (new-elabindex)
                   (ledger vl-unparam-ledger-p))
      :measure (two-nats-measure (vl-genblob-generate-count body) clk)
      (b* ((ledger (vl-unparam-ledger-fix ledger))
           ((when (zp clk))
            (mv nil
                (fatal :type :vl-generate-resolve-fail
                       :msg "~a0: Iteration limit ran out in for loop."
                       :args (list (vl-genelement-fix orig-x)))
                nil nil elabindex ledger))
           (var-param (make-vl-paramdecl
                       :name var
                       :type (make-vl-explicitvalueparam
                              :type *vl-plain-old-integer-type*
                              :default (vl-make-index (acl2::loghead 32 current-val)))
                       :loc *vl-fakeloc*))

           ;; Make a fake scope containing just the index param.
           ;; This seems dicey wrt svex consitency, but the key thing is
           ;; that we push 2 frames onto the ss total.  This first one only
           ;; contains the loop iterator, which won't be referenced in svex
           ;; since it'll resolve to a constant.

           (idx-scope (make-vl-scopeinfo :locals (hons-acons var var-param nil)))
           (elabindex (vl-elabindex-push idx-scope))

           ;; ((mv ok warnings idx-ss ?final-paramdecls)
           ;;  (vl-scope-finalize-params (make-vl-genblob)
           ;;                            (list var-param)
           ;;                            (make-vl-paramargs-named)
           ;;                            warnings ss ss 'fake-context-for-unparam)) ;; bozo make real context

           ;; ((unless ok)
           ;;  (mv nil warnings nil))

           ;; Check whether we continue.
           ((wmv ok warnings continue-val ?svex elabindex)
            (vl-expr-resolve-to-constant continue elabindex))
           ((unless (and ok (vl-expr-resolved-p continue-val)))
            (b* ((elabindex (vl-elabindex-undo)))
              (mv nil
                  (fatal :type :vl-generate-resolve-fail
                         :msg "~a0: Failed to evaluate the loop termination expression ~a1"
                         :args (list (vl-genelement-fix orig-x) (vl-expr-fix continue)))
                  nil nil elabindex ledger)))

           ((when (eql (vl-resolved->val continue-val) 0))
            (b* ((elabindex (vl-elabindex-undo)))
              (mv t (ok) nil nil elabindex ledger)))


           ((mv ok warnings keylist1 new-body elabindex ledger)
            (vl-generate-resolve body elabindex ledger warnings))

           ((unless ok)
            (b* ((elabindex (vl-elabindex-undo)))
              (mv nil warnings nil nil elabindex ledger)))

           (param-genelt (make-vl-genbase :item var-param))
           (block1 (make-vl-genarrayblock :index current-val
                                          :elems (vl-genelement-case new-body
                                                   :vl-genblock (cons param-genelt new-body.elems)
                                                   :otherwise
                                                   (cons param-genelt (list new-body)))))

           ((wmv ok warnings next-value ?svex elabindex)
            (vl-expr-resolve-to-constant nextval elabindex))
           
           (elabindex (vl-elabindex-undo))

           ((unless (and ok (vl-expr-resolved-p next-value)))
            (mv nil
                (fatal :type :vl-generate-resolve-fail
                       :msg "~a0: Failed to evaluate the loop increment expression ~a1"
                       :args (list (vl-genelement-fix orig-x) (vl-expr-fix nextval)))
                nil nil elabindex ledger))
           
           ((mv ok warnings keylist2 rest-blocks elabindex ledger)
            (vl-genloop-resolve (1- clk) body var
                                (vl-resolved->val next-value)
                                nextval continue
                                orig-x elabindex ledger warnings)))
        (mv ok warnings
            (append-without-guard keylist1 keylist2)
            (cons block1 rest-blocks)
            elabindex ledger)))
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







;; (def-genblob-transform vl-genblob-collect-modinst-paramsigs
;;   ((ss vl-scopestack-p)
;;    (warnings vl-warninglist-p)
;;    (modname stringp)
;;    (sigalist vl-unparam-sigalist-p))
;;   :parents (xf-unparameterize)
;;   :short "Collect parameterization signatures needed for module instances of a given module."
;;   :long "<p>Expects that the module is fully unparameterized, with parameter values
;;          substituted in everywhere.  Accumulates an unparameterization signature
;;          alist of instances that require unparameterization.</p>"

;;   :returns ((successp)
;;             (warnings vl-warninglist-p)
;;             (sigalist vl-unparam-sigalist-p))

;;   (b* (((vl-genblob x) (vl-genblob-fix x))
;;        (ss (vl-scopestack-push x ss))
;;        ((mv ok1 warnings insts sigalist)
;;         (vl-unparam-instlist x.modinsts ss warnings modname sigalist))

;;        ((mv ok2 warnings sigalist generates)
;;         (vl-generates-collect-modinst-paramsigs
;;          x.generates ss warnings modname sigalist)))
;;     (mv (and ok1 ok2) warnings sigalist
;;         (change-vl-genblob x :modinsts insts :generates generates)))

;;   :apply-to-generates vl-generates-collect-modinst-paramsigs
;;   :combine-bindings ((successp (and successp1 successp2)))
;;   :empty-list-bindings ((successp t))
;;   :prepwork ((local (in-theory (disable cons-equal
;;                                         vl-genelement-p-by-tag-when-vl-scopeitem-p
;;                                         acl2::subsetp-when-atom-right
;;                                         default-car default-cdr)))))



#||
(trace$ #!vl (vl-create-unparameterized-module
              :entry (list 'vl-create-unparameterized-module
                           (vl-module->name x)
                           (with-local-ps (vl-pp-paramdecllist final-paramdecls)))
              :exit (B* (((list ?ok ?mod ?keylist ?ledger) values))
                      (list 'vl-create-unparameterized-module
                            (with-local-ps (vl-pp-module mod global-ss))
                            keylist))))
||#

(define vl-create-unparameterized-module
  ((x vl-module-p)
   (name stringp "New name including parameter disambiguation")
   (final-paramdecls vl-paramdecllist-p)
   (elabindex "at global level")
   (ledger   vl-unparam-ledger-p))
  :returns (mv (okp)
               (new-mod vl-module-p)
               (keylist vl-unparam-instkeylist-p "signatures for this module")
               (new-elabindex)
               (ledger vl-unparam-ledger-p))
  (b* ((name (string-fix name))
       (x (change-vl-module x :name name
                            :paramdecls final-paramdecls))
       ((vl-module x))
       (elabindex (vl-elabindex-push x))
       ;; Note: instead of making a new svexconf here, we used to save the
       ;; svexconf produced by vl-scope-finalize-params when processing the
       ;; module instance.  We don't do that now because it pushes the module
       ;; with the wrong name, which would screw scopestack hashing when
       ;; processing instances inside this module.  I think it's fine to just
       ;; make a fresh svexconf from the new module with replaced
       ;; name/paramdecls.
       (warnings x.warnings)

       (blob (vl-module->genblob x))
       ((wmv ok warnings keylist new-blob elabindex ledger
             :ctx name)
        (vl-genblob-resolve-aux blob elabindex ledger nil))
       (elabindex (vl-elabindex-undo))
       (mod (vl-genblob->module new-blob x))
       (mod (change-vl-module mod :warnings warnings))
       ((unless ok)
        ;; (cw "not ok~%")
        (mv nil mod nil elabindex ledger)))
    (mv ok mod keylist elabindex ledger)))


(define vl-create-unparameterized-interface
  ((x vl-interface-p)
   (name stringp "New name including parameter disambiguation")
   (final-paramdecls vl-paramdecllist-p)
   (elabindex "at global scope")
   (ledger   vl-unparam-ledger-p))

  :returns (mv (okp)
               (new-mod vl-interface-p)
               (keylist vl-unparam-instkeylist-p "signatures for this interface")
               (new-elabindex)
               (ledger vl-unparam-ledger-p))
  (b* ((name (string-fix name))
       (x (change-vl-interface x :name name
                            :paramdecls final-paramdecls))
       ((vl-interface x))
       (elabindex (vl-elabindex-push x))
       (warnings x.warnings)

       (blob (vl-interface->genblob x))
       ((wmv ok warnings keylist new-blob elabindex ledger :ctx name)
        (vl-genblob-resolve-aux blob elabindex ledger nil))
       (elabindex (vl-elabindex-undo))
       (mod (vl-genblob->interface new-blob x))
       (mod (change-vl-interface mod :warnings warnings))
       ((unless ok)
        ;; (cw "not ok~%")
        (mv nil mod nil elabindex ledger)))
    (mv ok mod nil elabindex ledger)))


(fty::defalist vl-unparam-donelist :key-type vl-unparam-instkey)


(defines vl-unparameterize-main
  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (vl-module-p x)
                               (vl-scope-p x))))
             (local (defthm vl-scope-p-when-vl-interface-p-strong
                      (implies (vl-interface-p x)
                               (vl-scope-p x))))
             (local (defthm len-equal-0
                      (equal (equal (len x) 0)
                             (not (consp x))))))
  (define vl-unparameterize-main
    ((instkey vl-unparam-instkey-p "a single signature to expand")
     (donelist vl-unparam-donelist-p "fast alist of previously-seen signatures")
     (depthlimit natp "termination counter")
     (elabindex "global scope")
     (ledger   vl-unparam-ledger-p))
    :measure (two-nats-measure depthlimit 0)
    :verify-guards nil
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-mods vl-modulelist-p
                           "All of the modules (not seen before) that you need
                            to meet this signature, including instantiated
                            ones")
                 (new-interfaces vl-interfacelist-p
                           "All of the interfaces (not seen before) that you need
                            to meet this signature, including instantiated
                            ones")
                 (donelist vl-unparam-donelist-p)
                 (new-elabindex)
                 (ledger   vl-unparam-ledger-p))
    (b* ((instkey (vl-unparam-instkey-fix instkey))
         (ledger (vl-unparam-ledger-fix ledger))
         (donelist (vl-unparam-donelist-fix donelist))
         ((when (hons-get instkey donelist)) (mv t nil nil nil donelist elabindex ledger))
         (warnings nil)
         ((when (zp depthlimit))
          (mv nil
              (fatal :type :vl-unparameterize-loop
                     :msg "Recursion depth ran out in unparameterize -- loop ~
                           in the hierarchy?")
              nil nil donelist elabindex ledger))

         (sig (cdr (hons-get instkey (vl-unparam-ledger->instkeymap ledger))))
         ((unless sig)
          (raise "Programming error: missing instkey in ledger: ~x0~%" instkey)
          (mv nil
              (fatal :type :vl-unparameterize-programming-error
                     :msg "Couldn't find instkey ~a0~%"
                     :args (list instkey))
              nil nil donelist elabindex ledger))
         ((vl-unparam-signature sig))
         (donelist (hons-acons instkey t donelist))

         (mod (vl-scopestack-find-definition sig.modname (vl-elabindex->ss)))

         ((unless (and mod (or (eq (tag mod) :vl-module)
                               (eq (tag mod) :vl-interface))))
          (mv nil
              (fatal :type :vl-unparameterize-programming-error
                     :msg "Couldn't find module ~s0"
                     :args (list sig.modname))
              nil nil donelist elabindex ledger))

         ((mv mod-ok new-mod sigalist elabindex ledger)
          (if (eq (tag mod) :vl-interface)
              (vl-create-unparameterized-interface mod sig.newname sig.final-params elabindex ledger)
            (vl-create-unparameterized-module mod sig.newname sig.final-params elabindex ledger)))

         ((mv unparams-ok warnings new-mods new-ifaces donelist elabindex ledger)
          (vl-unparameterize-main-list sigalist donelist (1- depthlimit) elabindex ledger)))
      (mv (and mod-ok unparams-ok)
          warnings
          (if (eq (tag mod) :vl-module) (cons new-mod new-mods) new-mods)
          (if (eq (tag mod) :vl-interface) (cons new-mod new-ifaces) new-ifaces)
          donelist elabindex ledger)))

  (define vl-unparameterize-main-list ((keys vl-unparam-instkeylist-p)
                                       (donelist vl-unparam-donelist-p)
                                       (depthlimit natp)
                                       (elabindex "global scope")
                                       (ledger  vl-unparam-ledger-p))
    :measure (two-nats-measure depthlimit (len keys))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-mods vl-modulelist-p)
                 (new-ifaces vl-interfacelist-p)
                 (donelist vl-unparam-donelist-p)
                 (new-elabindex)
                 (ledger vl-unparam-ledger-p))
    (b* ((keys (vl-unparam-instkeylist-fix keys))
         (donelist (vl-unparam-donelist-fix donelist))
         (ledger (vl-unparam-ledger-fix ledger))
         ((when (atom keys)) (mv t nil nil nil donelist elabindex ledger))
         ((mv ok1 warnings1 new-mods1 new-ifaces1 donelist elabindex ledger)
          (vl-unparameterize-main (car keys) donelist depthlimit elabindex ledger))
         ((mv ok2 warnings2 new-mods2 new-ifaces2 donelist elabindex ledger)
          (vl-unparameterize-main-list (cdr keys) donelist depthlimit elabindex ledger)))
      (mv (and ok1 ok2)
          (append warnings1 warnings2)
          (append new-mods1 new-mods2)
          (append new-ifaces1 new-ifaces2)
          donelist elabindex ledger)))
  ///
  (local (in-theory (disable vl-unparameterize-main
                             vl-unparameterize-main-list)))
  (defthm-vl-unparameterize-main-flag
    (defthm true-listp-of-vl-unparameterize-main-warnings
      (true-listp (mv-nth 1 (vl-unparameterize-main instkey donelist depthlimit elabindex ledger)))
      :hints ('(:expand ((vl-unparameterize-main instkey donelist depthlimit elabindex ledger))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main)
    (defthm true-listp-of-vl-unparameterize-main-list-warnings
      (true-listp (mv-nth 1 (vl-unparameterize-main-list keys donelist depthlimit elabindex ledger)))
      :hints ('(:expand ((vl-unparameterize-main-list keys donelist depthlimit elabindex ledger))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main-list))

  (defthm-vl-unparameterize-main-flag
    (defthm true-listp-of-vl-unparameterize-main-mods
      (true-listp (mv-nth 2 (vl-unparameterize-main instkey donelist depthlimit elabindex ledger)))
      :hints ('(:expand ((vl-unparameterize-main instkey donelist depthlimit elabindex ledger))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main)
    (defthm true-listp-of-vl-unparameterize-main-list-mods
      (true-listp (mv-nth 2 (vl-unparameterize-main-list keys donelist depthlimit elabindex ledger)))
      :hints ('(:expand ((vl-unparameterize-main-list keys donelist depthlimit elabindex ledger))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main-list))

  (defthm-vl-unparameterize-main-flag
    (defthm true-listp-of-vl-unparameterize-main-ifaces
      (true-listp (mv-nth 3 (vl-unparameterize-main instkey donelist depthlimit elabindex ledger)))
      :hints ('(:expand ((vl-unparameterize-main instkey donelist depthlimit elabindex ledger))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main)
    (defthm true-listp-of-vl-unparameterize-main-list-ifaces
      (true-listp (mv-nth 3 (vl-unparameterize-main-list keys donelist depthlimit elabindex ledger)))
      :hints ('(:expand ((vl-unparameterize-main-list keys donelist depthlimit elabindex ledger))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main-list))

  (verify-guards vl-unparameterize-main)

  (deffixequiv-mutual vl-unparameterize-main
    :hints ((and stable-under-simplificationp
                 (flag::expand-calls-computed-hint
                  clause '(vl-unparameterize-main
                           vl-unparameterize-main-list))))))



(define vl-toplevel-default-signature ((modname stringp)
                                       (warnings vl-warninglist-p)
                                       (elabindex "global scope")
                                       (ledger vl-unparam-ledger-p))
  :returns (mv (ok)
               (instkey (implies ok (vl-unparam-instkey-p instkey)))
               (warnings vl-warninglist-p)
               (new-elabindex)
               (ledger vl-unparam-ledger-p))
  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (vl-module-p x)
                               (vl-scope-p x))))
             (local (defthm vl-scope-p-when-vl-interface-p-strong
                      (implies (vl-interface-p x)
                               (vl-scope-p x)))))
  (b* ((modname (string-fix modname))
       (ledger (vl-unparam-ledger-fix ledger))
       (x (vl-scopestack-find-definition modname (vl-elabindex->ss)))
       ((unless (and x
                     (or (eq (tag x) :vl-module)
                         (eq (tag x) :vl-interface))))
        (mv nil nil
            (fatal :type :vl-unparam-fail
                   :msg "Programming error: top-level module/interface ~s0 not found"
                   :args (list modname))
            elabindex ledger))
       ((vl-elabindex elabindex))
       (elabindex (vl-elabindex-push x))
       (paramdecls (if (eq (tag x) :vl-module)
                       (vl-module->paramdecls x)
                     (vl-interface->paramdecls x)))
       ((mv ok warnings elabindex final-paramdecls)
        (vl-scope-finalize-params paramdecls
                                  (make-vl-paramargs-named)
                                  warnings
                                  elabindex elabindex.ss
                                  (caar (vl-elabindex->undostack))))
       (inside-mod-ss (vl-elabindex->ss))
       (elabindex (vl-elabindex-undo))
       ((unless ok) (mv nil nil warnings elabindex ledger))
       ((mv instkey ledger) (vl-unparam-add-to-ledger-without-renaming
                             modname final-paramdecls ledger elabindex.ss
                             inside-mod-ss)))

    (mv t instkey warnings elabindex ledger)))

(define vl-toplevel-default-signatures ((names string-listp)
                                        (warnings vl-warninglist-p)
                                        (elabindex "design level")
                                        (ledger vl-unparam-ledger-p))
  :returns (mv (instkeys vl-unparam-instkeylist-p)
               (warnings vl-warninglist-p)
               (new-elabindex)
               (ledger vl-unparam-ledger-p))
  (if (atom names)
      (mv nil (vl-warninglist-fix warnings)
          elabindex (vl-unparam-ledger-fix ledger))
    (b* (((mv ok instkey warnings elabindex ledger)
          (vl-toplevel-default-signature (car names) warnings elabindex ledger))
         ((mv instkeys warnings elabindex ledger)
          (vl-toplevel-default-signatures (cdr names) warnings elabindex ledger)))
      (mv (if ok
              (cons instkey instkeys)
            instkeys)
          warnings elabindex ledger))))


#|
(trace$ #!Vl (vl-package-elaborate
              :entry (list 'vl-package-elaborate
                           (with-local-ps (vl-pp-package x)))
              :exit (list 'vl-package-elaborate
                           (with-local-ps (vl-pp-package (nth 2 values))))))

||#
(define vl-package-elaborate ((x        vl-package-p)
                              (elabindex "design level")
                              (warnings vl-warninglist-p))
  :prepwork ((local (in-theory (enable (vl-context-p) vl-context-p))))
  :short "Resolve parameters in packages."
  :long "<p>Assumption: packages reference each other only in reverse parse
order, i.e., later-defined packages can reference parameters inside
earlier-defined packages.  This gets around some horrible complications in
implementation.  We still have to do some convoluted stuff with
scopestacks.</p>"

  :returns (mv (ok)
               (warnings1 vl-warninglist-p)
               (new-elabindex)
               (new-x     vl-package-p))

  (b* (((vl-package x) (vl-package-fix x))
       ((vl-elabindex elabindex))
       (elabindex (vl-elabindex-push x))
       ((mv ok warnings elabindex new-params)
        (vl-scope-finalize-params x.paramdecls
                                  (make-vl-paramargs-named)
                                  warnings
                                  elabindex elabindex.ss
                                  (caar (vl-elabindex->undostack))))
       (new-x (change-vl-package x :paramdecls new-params))
       ((unless ok)
        (b* ((elabindex (vl-elabindex-undo)))
          (mv nil warnings elabindex x)))
       ;; Note: When processing modules/interfaces, rather than using the
       ;; svexconf returned by scope-finalize-params we create a new empty conf
       ;; containing a SS with the new module (see the comment in
       ;; vl-create-unparameterized-module).  Here it seems OK to use that
       ;; svexconf because the package name remains the same.  Also not sure if
       ;; anything inside a package is sensitive to the named scopes (we
       ;; currently only use scopestack hashing for disambiguating
       ;; unparameterized modules, which don't currently exist inside
       ;; packages).
       ((wmv ok warnings new-x elabindex)
        (vl-package-elaborate-aux new-x elabindex))
       (elabindex (vl-elabindex-undo)))
    (mv ok warnings elabindex new-x)))

(define vl-packagelist-elaborate ((x vl-packagelist-p)
                                  (elabindex "design level")
                                  (warnings vl-warninglist-p))
  :returns (mv (ok)
               (warnings1 vl-warninglist-p)
               (new-elabindex)
               (new-x     vl-packagelist-p))
  (b* (((when (atom x)) (mv t (ok) elabindex nil))
       ((mv ok1 warnings elabindex pkg1) (vl-package-elaborate (car x) elabindex warnings))
       ((mv ok2 warnings elabindex pkgs) (vl-packagelist-elaborate (cdr x) elabindex  warnings)))
    (mv (and ok1 ok2) warnings elabindex (cons pkg1 pkgs))))



;; (define vl-packages-finalize-params ((packages vl-packagelist-p)
;;                                      (design vl-design-p)
;;                                      (warnings vl-warninglist-p))
;;   :prepwork ((local (in-theory (enable (vl-context-p) vl-context-p))))
;;   :short "Resolve parameters in packages."
;;   :long "<p>Assumption: packages reference each other only in reverse parse
;; order, i.e., later-defined packages can reference parameters inside
;; earlier-defined packages.  This gets around some horrible complications in
;; implementation.  We still have to do some convoluted stuff with
;; scopestacks.</p>"

;;   :returns (mv (ok)
;;                (warnings1 vl-warninglist-p)
;;                (packages1 vl-packagelist-p))

;;   (b* (((when (atom packages))
;;         (mv t (ok) nil))
;;        ((vl-package pkg1) (vl-package-fix (car packages)))
;;        ((vl-design design))
;;        (ss (vl-scopestack-init design))
;;        ((mv ok warnings & pkg1-params)
;;         (vl-scope-finalize-params pkg1
;;                                   pkg1.paramdecls
;;                                   (make-vl-paramargs-named)
;;                                   warnings
;;                                   ss ss
;;                                   pkg1))
;;        (- (vl-scopestacks-free))
;;        (new-pkg1 (change-vl-package pkg1 :paramdecls pkg1-params))
;;        ((unless ok)
;;         (mv nil warnings nil))
;;        (design1 (change-vl-design design :packages (cons new-pkg1 design.packages)))

;;        ((mv ok warnings rest-packages)
;;         (vl-packages-finalize-params (cdr packages) design1 warnings))
;;        ((unless ok) (mv nil warnings nil)))
;;     (mv t warnings (cons pkg1 rest-packages))))




(define vl-design-elaborate
  :short "Top-level @(see unparameterization) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  :prepwork ((local (defthm string-listp-of-scopedef-alist-key
                      (implies (vl-scopedef-alist-p x)
                               (string-listp (acl2::alist-keys x)))
                      :hints(("Goal" :in-theory (enable vl-scopedef-alist-p))))))
  
  (b* (;; Throw out modules that have problems with shadowed parameters.
       ;; We won't need this.
       ;; ((vl-design x) (vl-design-unparam-check x))
       ((vl-design x) (vl-design-fix x))
       ((local-stobjs elabindex) (mv new-x elabindex))
       (elabindex (vl-elabindex-init x))
       ((mv ?ok warnings elabindex params)
        (vl-scope-finalize-params x.paramdecls
                                  (make-vl-paramargs-named)
                                  x.warnings
                                  elabindex
                                  ;; outer ss and scopes shouldn't be used
                                  nil nil))
       (new-x (change-vl-design x :paramdecls params))

       ;; ;; We used to use the conf returned by scope-finalize-params here, which
       ;; ;; might be ok but it adds an extra level of hierarchy in the ss which
       ;; ;; is a little weird here.
       ;; (ss (vl-scopestack-init new-x))
       ;; (conf (make-vl-svexconf :ss ss))

       (elabindex (vl-elabindex-init new-x))

       ;; Why do we call design-elaborate-aux before unparameterizing modules,
       ;; interfaces, & packages?  This skips those fields, so we're really
       ;; only elaborating design-level functions, tasks, variables, types,
       ;; paramdecls (though these should already be done), udps, and
       ;; dpiimports.  We could perhaps get into trouble here since these could
       ;; depend on packages and package parameters.
       ((wmv ?ok1 warnings new-x elabindex)
        (vl-design-elaborate-aux new-x elabindex))

       ((mv ?ok warnings elabindex new-packages)
        (vl-packagelist-elaborate x.packages elabindex warnings))

       ;; Note: We used to make a new elabindex with the elaborated design and
       ;; packages in it.  Not sure if we need to do this anymore since the
       ;; elabindex should keep track of all that (and there are no parameter
       ;; overrides to confuse things).
       ;; (new-x (change-vl-design new-x :packages new-packages))

       ;; ;; Note: For some reason we previously didn't make a new conf with the
       ;; ;; new packages in it.  Not sure if that was intentional or not.
       ;; ;; Probably want some good cosim testing of package parameters.
       ;; (ss (vl-scopestack-init new-x))
       ;; (conf (make-vl-svexconf :ss ss))

       (topmods
        ;; [Jared] for linting it's nice to also keep top-level interfaces
        ;; around; even if they aren't instantiated we'd rather get their
        ;; warnings.
        (vl-design-toplevel x))

       ;; Make a ledger with initially empty instkeymap and namefactory
       ;; containing the top-level definitions' names -- modules, UDPs,
       ;; interfaces, programs.
       (top-names (acl2::alist-keys (vl-design-scope-definition-alist new-x nil)))
       (ledger (make-vl-unparam-ledger
                :ndb (vl-starting-namedb top-names)))

       ;; This is something Sol wanted for Samev.  The idea is to instance
       ;; every top-level module with its default parameters, so that we don't
       ;; just throw away the whole design if someone is trying to check a
       ;; parameterized module.
       ((mv top-sigs warnings elabindex ledger)
        (vl-toplevel-default-signatures topmods warnings elabindex ledger))

       ((wmv ?ok warnings new-mods new-ifaces donelist elabindex ledger)
        (vl-unparameterize-main-list top-sigs nil 1000 elabindex ledger)))
    (fast-alist-free donelist)
    (vl-free-namedb (vl-unparam-ledger->ndb ledger))
    (fast-alist-free (vl-unparam-ledger->instkeymap ledger))
    (vl-scopestacks-free)
    (mv (change-vl-design new-x :warnings warnings :mods new-mods :interfaces new-ifaces :packages new-packages)
        elabindex)))
