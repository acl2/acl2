; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "VL")

(include-book "vl-svstmt")
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system)
                           nfix natp)))


(local (in-theory (disable member append
                           sv::svarlist-addr-p-when-subsetp-equal
                           vl-warninglist-p-when-not-consp
                           acl2::true-listp-append
                           acl2::subsetp-when-atom-right
                           acl2::subsetp-when-atom-left)))

(fty::defvisitor-template elaborate ((x :object)
                                     (conf vl-svexconf-p)
                                     &key
                                     ((reclimit natp) '1000))
  :returns (mv (ok (:join (and ok1 ok)
                    :initial t
                    :tmp-var ok1))
               (warnings (:join (append-without-guard warnings1 warnings)
                          :initial nil
                          :tmp-var warnings1)
                         vl-warninglist-p)
               (new-x :update)
               (new-conf (:acc conf :fix (vl-svexconf-fix conf))
                         vl-svexconf-p))

    :type-fns ((vl-datatype vl-datatype-elaborate-fn)
               (vl-expr     vl-expr-elaborate-fn))
    :prod-fns ((vl-hidindex  (indices vl-indexlist-resolve-constants-fn))
               (vl-range     (msb vl-index-resolve-if-constant-fn)
                             (lsb vl-index-resolve-if-constant-fn))
               (vl-plusminus (base vl-index-resolve-if-constant-fn)
                             (width vl-index-resolve-constant-fn))
               (vl-arrayrange-index (expr vl-index-resolve-if-constant-fn))
               (vl-valuerange-single (expr vl-index-resolve-if-constant-fn))
               (vl-patternkey-expr   (key vl-index-resolve-if-constant-fn)) ;; BOZO this will break struct field names
               (vl-casttype-size (size vl-index-resolve-if-constant-fn))
               (vl-slicesize-expr (expr vl-index-resolve-if-constant-fn))
               (vl-arrayrange-index (expr vl-index-resolve-if-constant-fn))
               ;; skip these fields because they won't be done right automatically
               )
    :field-fns ((atts :skip)
                (mods :skip)
                (interfaces :skip)
                (packages :skip))

  :fnname-template <type>-elaborate)


  
(local (in-theory (disable cons-equal)))

(fty::defvisitor-multi vl-elaborate
  :defines-args (:ruler-extenders :all ;; :measure-debug t
                 )
  (fty::defvisitor :template elaborate
    :type expressions-and-datatypes
    :measure (acl2::nat-list-measure
              (list reclimit :order :count 0))
    :renames ((vl-expr vl-expr-elaborate-aux)
              (vl-datatype vl-datatype-elaborate-aux))
    
    :short "Resolve constant expressions, parameter values, and datatypes."
    :long "
<p>In the previous version of VL, we used to do a series of transforms that:</p>

<ul>
<li>expanded function definitions into assignments (see @(see
vl2014::expand-functions))</li>

<li>resolved parameter values and created all the necessary versions of
parametrized modules (see @(see vl2014::unparameterization))</li>

<li>resolved constant indices in datatypes (see @(see
vl2014::rangeresolve)).</li>
</ul>

<p>(We'll refer to these three kinds of transformations collectively as
\"elaboration;\" commercial implementations use that term to mean something
somewhat similar.)</p>

<p>The problem with this series of transformations is that there may be
complicated relationships among functions, parameters, and datatypes -- a
function, parameter, or datatype definition may use functions, parameters, and
datatypes.  Consider the following sequence of declarations:</p>

@({
 function integer f1 (logic a);
    f1 = a ? 3 : 5;
 endfunction

 parameter p1 = f1(1);

 typedef logic [p1-1:0] t1;

 function t1 f2 (integer b);
    f2 = ~b;
 endfunction

 parameter t1 p2 = f2(p1);

 })

<p>From the example we can see that it won't suffice to use our three
transformations once each in any order.  One solution might be to try the
tranformations repeatedly in a cycle.  Our solution is instead to allow
parameters, functions, and types to be resolved as needed while resolving other
parameters, functions, and types.  We use a lookup table to store previously
resolved items as a form of memoization.</p>

<p>The lookup table in which we store these values is a @(see vl-svexconf),
which contains a scopestack and additionally holds the following four
tables:</p>

<ul>

<li>@('typeov'), mapping from function, parameter, and type names to resolved
datatypes.  These datatypes have all indices and usertypes resolved.  Functions
map to their return types, value parameters map to their types, type parameters
map to their (datatype) values, and type names map to their definitions.</li>

<li>@('fns'), mapping from function names to @(see svex) expressions for
their return values in terms of their inputs.</li>

<li>@('fnports'), mapping from function names to their resolved list of
ports (containing resolved datatypes).</li>

<li>@('params'), mapping from parameter names to @(see svex) expressions for
their values, which should be constant.</li>

</ul>

<p>The elaboration algorithm calls subsidiary algorithms @(see vl-expr-to-svex)
and @(see vl-fundecl-to-svex), which each use the svexconf lookup tables in a
read-only manner.  Before translating an expression (or, similarly, function
declaration) to svex, the elaboration algorithm walks over the expression and
collects the information it needs to successfully resolve it to an svex
expression: the types, svex translations, and port lists of functions that the
expression calls, and types and values of parameters referenced in the
expression.  This information is stored in the svexconf before translating the
expression with @(see vl-expr-to-svex).</p>

")
  
  (fty::defvisitors :template elaborate
    :dep-types (vl-fundecl)
    :order-base 1
    :measure (acl2::nat-list-measure
              (list reclimit :order :count 0))
    ;; BOZO Block and loop statements should perhaps also get their own scopes pushed
    )


  (fty::defvisitor :template elaborate
    :type vl-fundecl
    :renames ((vl-fundecl vl-fundecl-elaborate-aux))
    :type-fns ((vl-fundecl vl-fundecl-elaborate-fn))
    :order 100
    :measure (acl2::nat-list-measure
              (list reclimit :order :count 0)))

;; (trace$ #!vl (vl-fundecl-elaborate-fn
;;               :cond (equal (Vl-fundecl->name x) "DWF_lzd")
;;               :entry (list 'vl-fundecl-elaborate
;;                            "DWF_lzd"
;;                            (with-local-ps (vl-pp-fundecl x))
;;                            (b* (((vl-svexconf conf)))
;;                              (list :typeov (strip-cars conf.typeov)
;;                                    :params (strip-cars conf.params)
;;                                    :fns (strip-cars conf.fns))))
;;               :exit (list 'vl-fundecl-elaborate
;;                           "DWF_lzd"
;;                           (with-local-ps (vl-pp-fundecl (caddr values)))
;;                           (b* (((vl-svexconf conf) (cadddr values)))
;;                             (list :typeov (strip-cars conf.typeov)
;;                                   :params (strip-cars conf.params)
;;                                   :fns (strip-cars conf.fns))))))

;; (trace$ #!vl (vl-fundecl-elaborate-aux-fn
;;               :entry (list 'vl-fundecl-elaborate-aux
;;                            (vl-fundecl->name x)
;;                            (with-local-ps (vl-pp-fundecl x))
;;                            (b* (((vl-svexconf conf)))
;;                              (list :typeov (strip-cars conf.typeov)
;;                                    :params (strip-cars conf.params)
;;                                    :fns (strip-cars conf.fns))))
;;               :exit (list 'vl-fundecl-elaborate-aux
;;                            (vl-fundecl->name x)
;;                            (car values)
;;                            (with-local-ps (vl-print-warnings (cadr values)))
;;                           (with-local-ps (vl-pp-fundecl (caddr values)))
;;                           (b* (((vl-svexconf conf) (cadddr values)))
;;                             (list :typeov (strip-cars conf.typeov)
;;                                   :params (strip-cars conf.params)
;;                                   :fns (strip-cars conf.fns))))))


  (define vl-fundecl-elaborate ((x vl-fundecl-p)
                                (conf vl-svexconf-p)
                                &key ((reclimit natp) '1000))
    :guard-debug t
    :measure (acl2::nat-list-measure
              (list reclimit
                    1000 ;; this is kind of the top-level function, so choose a high order value
                    0 0))
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (new-x vl-fundecl-p)
               (new-conf vl-svexconf-p)) ;; unchanged

    (b* (((vl-svexconf orig-conf) (vl-svexconf-fix conf))
         (fnconf (make-vl-svexconf :ss (vl-scopestack-push (vl-fundecl->blockscope x)
                                                            orig-conf.ss)))
         ((mv ok warnings new-x fnconf)
          (vl-fundecl-elaborate-aux x fnconf :reclimit reclimit))
         ((unless ok)
          (vl-svexconf-free fnconf)
          (mv nil warnings new-x orig-conf))
         ((wmv warnings svex) (vl-fundecl-to-svex new-x fnconf))
         (localname (make-vl-scopeexpr-end
                       :hid (make-vl-hidexpr-end :name (vl-fundecl->name x))))
         ((vl-fundecl new-x))
         (conf (change-vl-svexconf
                orig-conf
                :fns (hons-acons localname svex orig-conf.fns)
                :fnports (hons-acons localname new-x.portdecls orig-conf.fnports)
                :typeov (hons-acons
                         localname new-x.rettype orig-conf.typeov))))
      (vl-svexconf-free fnconf)
      (mv ok warnings new-x conf)))

;; #|
;; (trace$ #!vl (vl-function-compile-and-bind-fn
;;               :entry (list 'vl-function-compile-and-bind
;;                            fnname)
;;               :exit (list 'vl-function-compile-and-bind
;;                           (car values)
;;                           (with-local-ps (vl-print-warnings (cadr values)))
;;                           (strip-cars (vl-svexconf->fns (caddr values))))))

;; |#

  (define vl-function-compile-and-bind ((fnname vl-scopeexpr-p)
                                        (conf vl-svexconf-p)
                                        &key ((reclimit natp) '1000))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-conf vl-svexconf-p))
    :measure (acl2::nat-list-measure
              (list reclimit 0 0 0)) ;; the only recursive call here will decrease the reclimit
    (b* (((vl-svexconf conf) (vl-svexconf-fix conf))
         (fnname (vl-scopeexpr-fix fnname))
         (warnings nil)
         ((mv err trace ?context tail)
          (vl-follow-scopeexpr fnname conf.ss :strictp t))
         ((when err)
          (mv nil
              (fatal :type :vl-function-compile-fail
                     :msg "Couldn't find function ~a0: ~@1"
                     :args (list fnname err))
              conf))
         ((unless (vl-hidexpr-case tail :end))
          (mv nil
              (fatal :type :vl-function-compile-fail
                     :msg "Data select into a function? ~a0"
                     :args (list fnname))
              conf))
         ((vl-hidstep step) (car trace))
         ((unless (eq (tag step.item) :vl-fundecl))
          (mv nil
              (fatal :type :vl-function-compile-fail
                     :msg "Reference to item ~a0 in function name context: ~a1"
                     :args (list step.item fnname))
              conf))
         ((when (zp reclimit))
          (mv nil
              (fatal :type :vl-function-compile-fail
                     :msg "Reclimit ran out on ~a0: dependency loop?"
                     :args (list fnname))
              conf))
         ((vl-fundecl decl) step.item)
         (same-scope (equal step.ss conf.ss))
         (fnconf (if same-scope conf (make-vl-svexconf :ss step.ss)))
         ((wmv ok warnings ?new-decl fnconf)
          (vl-fundecl-elaborate decl fnconf :reclimit (1- reclimit)))
         (conf (if same-scope fnconf conf))
         ((unless ok)
          (and (not same-scope) (vl-svexconf-free fnconf))
          (mv nil warnings conf))
         ((when same-scope) (mv t warnings conf))
         (local-name (make-vl-scopeexpr-end
                      :hid (make-vl-hidexpr-end :name  decl.name)))
         (svex (cdr (hons-get local-name (vl-svexconf->fns fnconf))))
         (type (cdr (hons-get local-name (vl-svexconf->typeov fnconf))))
         (portlook (hons-get local-name (vl-svexconf->fnports fnconf)))
         (conf (if svex
                   (change-vl-svexconf conf :fns (hons-acons fnname svex conf.fns))
                 conf))
         (conf (if type
                   (change-vl-svexconf conf :typeov (hons-acons fnname type conf.typeov))
                 conf))
         (conf (if portlook
                   (change-vl-svexconf conf :fnports (hons-acons fnname (cdr portlook) conf.fnports))
                 conf)))
      (vl-svexconf-free fnconf)
      (mv t warnings conf)))




  (define vl-expr-resolve-to-constant ((x vl-expr-p)
                                       (conf vl-svexconf-p)
                                       &key
                                       ((reclimit natp) '1000)
                                       ((ctxsize maybe-natp) 'nil))
    ;; Just calls vl-expr-maybe-resolve-to-constant, but produces a fatal
    ;; warning if it failed to reduce to a constant.
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-expr-count x) 10))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-expr-p)
                 (svex sv::svex-p)
                 (new-conf vl-svexconf-p))
    (b* ((orig-x (vl-expr-fix x))
         ((mv ok constantp warnings x svex conf)
          (vl-expr-maybe-resolve-to-constant x conf :reclimit reclimit
                                             :ctxsize ctxsize)))
      (mv (and ok constantp)
          (if (and ok (not constantp))
              (fatal :type :vl-expr-consteval-fail
                     :msg "Couldn't resolve ~a0 to constant (original: ~a1)"
                     :args (list x orig-x))
            warnings)
          x svex conf)))

  (define vl-expr-maybe-resolve-to-constant ((x vl-expr-p)
                                             (conf vl-svexconf-p)
                                             &key
                                             ((reclimit natp) '1000)
                                             ((ctxsize maybe-natp) 'nil))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-expr-count x) 9))
    :returns (mv (ok)
                 (constantp)
                 (warnings vl-warninglist-p) 
                 (new-x vl-expr-p)
                 (svex sv::svex-p)
                 (new-conf vl-svexconf-p))
                 
    (b* (((mv ok warnings x conf)
          (vl-expr-elaborate x conf :reclimit reclimit))
         ((unless ok) (mv nil nil warnings x (svex-x) conf))
         ((mv ok constp warnings x svex)
          (vl-elaborated-expr-consteval x conf :ctxsize ctxsize)))
      (mv ok constp warnings x svex conf)))

  (define vl-index-resolve-if-constant ((x vl-expr-p)
                                        (conf vl-svexconf-p)
                                        &key ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-expr-count x) 10))
    :returns (mv (ok)
                 (warnings vl-warninglist-p) 
                 (new-x vl-expr-p)
                 (new-conf vl-svexconf-p))
    (b* (((mv ok ?constantp warnings new-x ?svex new-conf)
          (vl-expr-maybe-resolve-to-constant x conf :reclimit reclimit)))
      (mv ok warnings new-x new-conf)))

  (define vl-index-resolve-constant ((x vl-expr-p)
                                     (conf vl-svexconf-p)
                                     &key ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-expr-count x) 11))
    :returns (mv (ok)
                 (warnings vl-warninglist-p) 
                 (new-x vl-expr-p)
                 (new-conf vl-svexconf-p))
    (b* (((mv ok warnings new-x ?svex new-conf)
          (vl-expr-resolve-to-constant x conf :reclimit reclimit)))
      (mv ok warnings new-x new-conf)))
    
  (define vl-expr-resolve-to-constant-and-bind-param
    ((name vl-scopeexpr-p)
     (expr vl-expr-p)
     (exprconf vl-svexconf-p
               "svexconf for the expression scope")
     (nameconf vl-svexconf-p
               "svexconf for the name scope")
     &key
     ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-expr-count expr) 20))
    
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-nameconf vl-svexconf-p)
                 (new-exprconf vl-svexconf-p))
    (b* (((vl-svexconf nameconf) (vl-svexconf-fix nameconf))
         ((vl-svexconf exprconf) (vl-svexconf-fix exprconf))
         (same-scope (equal exprconf.ss nameconf.ss))
         (name (vl-scopeexpr-fix name))
         (warnings nil)
         (lookup (hons-get name nameconf.params))
         ((when lookup) (mv t warnings nameconf exprconf))
         ((mv ok warnings ?new-x svex exprconf)
          (vl-expr-resolve-to-constant expr exprconf :Reclimit reclimit))
         (nameconf (if same-scope exprconf nameconf))
         ((unless ok) (mv nil warnings nameconf exprconf))
         (nameconf (change-vl-svexconf
                    nameconf
                    :params (hons-acons name svex nameconf.params)))
         (exprconf (if same-scope nameconf exprconf)))
      (mv t warnings nameconf exprconf)))
      



  (define vl-datatype-fully-resolve-and-bind ((name vl-scopeexpr-p)
                                              (type vl-datatype-p)
                                              (typeconf vl-svexconf-p
                                                        "svexconf for the scope
                                                          where the type was
                                                          defined")
                                              (nameconf vl-svexconf-p
                                                        "svexconf for the scope that
                                                     the name is relative to")
                                              &key
                                              ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-datatype-count type) 20))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-type vl-datatype-p)
                 (new-nameconf vl-svexconf-p)
                 (new-typeconf vl-svexconf-p))
    
    (b* (((vl-svexconf nameconf) (vl-svexconf-fix nameconf))
         ((vl-svexconf typeconf) (vl-svexconf-fix typeconf))
         (name (vl-scopeexpr-fix name))
         (lookup (hons-get name nameconf.typeov))
         (warnings nil)
         ((when lookup)
          ;; done already
          (mv t warnings (cdr lookup) nameconf typeconf))
         (same-scope (equal nameconf.ss typeconf.ss))
         ;; resolve the type and add it to the conf
         ((wmv ok warnings new-type typeconf)
          (vl-datatype-elaborate type typeconf :reclimit reclimit))
         (nameconf (if same-scope typeconf nameconf))
         ((unless ok)
          (mv nil warnings new-type nameconf typeconf))
         (nameconf (change-vl-svexconf
                    nameconf
                    :typeov (hons-acons name new-type (vl-svexconf->typeov nameconf))))
         (typeconf (if same-scope nameconf typeconf)))
      (mv t warnings new-type nameconf typeconf)))



  (define vl-index-expr-resolve-paramref ((x vl-expr-p)
                                          (conf vl-svexconf-p)
                                          &key ((reclimit natp) '1000))
    ;; Call this AFTER indices within the hids have been maybe-resolved.
    :measure (acl2::nat-list-measure
              (list reclimit 0 0 10))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-conf vl-svexconf-p))
    :guard (vl-expr-case x :vl-index)

    (b* ((warnings nil)
         ((vl-svexconf conf) (vl-svexconf-fix conf))
         ((vl-index x) (vl-expr-fix x))
         ((unless (mbt (vl-expr-case x :vl-index)))
          (impossible) ;; need this case for measure
          (mv nil warnings conf))
         ((mv err hidtrace ?context tail)
          (vl-follow-scopeexpr x.scope conf.ss))
         ((when err)
          (mv t
              ;; It might just be a variable from a generate that isn't present yet.
              ;; (warn :type :vl-resolve-constants-fail
              ;;        :msg "Couldn't find ~a0"
              ;;        :args (list x))
              warnings
              conf))

         (prefix-name (vl-scopeexpr-replace-hid
                       x.scope
                       (vl-hid-prefix-for-subhid (vl-scopeexpr->hid x.scope) tail)))

         ((vl-hidstep hidstep) (car hidtrace))
         ((when (zp reclimit))
          (mv nil
              (fatal :type :vl-resolve-constants-fail
                     :msg "Recursion limit ran out processing ~a0 -- dependency loop?"
                     :args (list x))
              conf))

         ((when (or (eq (tag hidstep.item) :vl-modinst)
                    (eq (tag hidstep.item) :vl-interfaceport)))
          ;; If it's a modinst, it might be an interface, which is legitimate
          ;; in some situations
          (mv t warnings conf))

         ((when (eq (tag hidstep.item) :vl-vardecl))
          ;; It's not a paramdecl, so we can't resolve it to a constant.  But
          ;; we do want to make sure its type is resolved if it's a vardecl.
          ;; We are now in a different scope, so we can't use our same conf.
          (b* ((same-scope (equal hidstep.ss conf.ss))
               (typeconf (if same-scope conf (make-vl-svexconf :ss hidstep.ss)))
               ((mv ok warnings ?newtype conf typeconf)
                (vl-datatype-fully-resolve-and-bind
                 prefix-name
                 (vl-vardecl->type hidstep.item)
                 typeconf conf
                 :reclimit (1- reclimit))))
            (and (not same-scope) (vl-svexconf-free typeconf))
            (mv ok warnings conf)))

         ((unless (eq (tag hidstep.item) :vl-paramdecl))
          (mv nil
              (fatal :type :vl-resolve-constants-fail
                     :msg "~a0: Bad item for variable reference: ~a1"
                     :args (list x hidstep.item))
              conf))

         ((vl-paramdecl decl) hidstep.item))
      ;; Note: We're potentially in a new scope here, so everything we do needs
      ;; to involve just the hidstep.ss and no 
      (vl-paramtype-case decl.type
        :vl-typeparam
        (mv nil
            (fatal :type :vl-resolve-constants-fail
                   :msg "Type parameter referenced as expression: ~a0"
                   :args (list x))
            conf)
        :vl-explicitvalueparam
        (b* (((unless decl.type.default)
              (mv nil
                  (fatal :type :vl-resolve-constants-fail
                         :msg "Parameter with no default value: ~a0"
                         :args (list x))
                   conf))
             (same-scope (equal conf.ss hidstep.ss))
             (declconf (if same-scope conf (make-vl-svexconf :ss hidstep.ss)))
             ((wmv ok1 warnings ?newtype conf declconf)
              (vl-datatype-fully-resolve-and-bind
               prefix-name
               decl.type.type
               declconf conf :reclimit (1- reclimit)))
             ((wmv ok2 warnings conf ?declconf)
              (vl-expr-resolve-to-constant-and-bind-param
               prefix-name
               decl.type.default
               declconf
               conf
               :reclimit (1- reclimit))))
          (and (not same-scope) (vl-svexconf-free declconf))
          (mv (and ok1 ok2) warnings conf))

        :vl-implicitvalueparam
        (b* (((unless decl.type.default)
              (mv nil
                  (fatal :type :vl-resolve-constants-fail
                         :msg "Parameter with no default value: ~a0"
                         :args (list x))
                  conf))
             (same-scope (equal conf.ss hidstep.ss))
             (declconf (if same-scope conf (make-vl-svexconf :ss hidstep.ss)))
             ((mv ok warnings range declconf)
              (if decl.type.range
                  (b* (((vl-range range) decl.type.range)
                       ((wmv ok warnings msb ?svex declconf)
                        (vl-expr-resolve-to-constant
                         range.msb declconf :reclimit (1- reclimit)))
                       ((unless ok)
                        (mv nil warnings nil declconf))
                       ((wmv ok warnings lsb ?svex declconf)
                        (vl-expr-resolve-to-constant
                         range.lsb declconf :reclimit (1- reclimit))))
                    (mv ok warnings (make-vl-range :msb msb :lsb lsb) declconf))
                (mv t warnings nil declconf)))
             (conf (if same-scope declconf conf))
             ((unless ok)
              (and (not same-scope) (vl-svexconf-free declconf))
              (mv nil warnings conf))
             (paramtype (change-vl-implicitvalueparam decl.type :range range))
             ((wmv ok warnings ?val svex declconf)
              (vl-expr-resolve-to-constant
               decl.type.default declconf :reclimit (1- reclimit)))
             (conf (if same-scope declconf conf))
             ((unless ok)
              (and (not same-scope) (vl-svexconf-free declconf))
              (mv nil warnings conf))
             ((wmv warnings err type)
              (vl-implicitvalueparam-final-type paramtype val declconf))
             ((when err)
              (and (not same-scope) (vl-svexconf-free declconf))
              (mv nil
                  (fatal :type :vl-resolve-constants-fail
                         :msg "Error resolving parameter type for ~a0: ~@1"
                         :args (list x err))
                  conf))
             (conf (change-vl-svexconf
                    conf
                    :params (hons-acons prefix-name svex conf.params)
                    :typeov (hons-acons prefix-name type conf.typeov))))
          (and (not same-scope) (vl-svexconf-free declconf))
          (mv t warnings conf)))))


#||
(trace$ #!vl
        (vl-expr-elaborate-fn
         :entry (list 'vl-expr-elaborate
                      (with-local-ps (vl-pp-expr x)))
         :exit (b* (((list ok warnings new-x) values))
                 (list* 'vl-expr-elaborate
                        ok (with-local-ps (vl-pp-expr new-x))
                        (and warnings (with-local-ps (vl-print-warnings warnings)))))))
                      
                      
                      

||#



  (define vl-expr-elaborate ((x vl-expr-p)
                                     (conf vl-svexconf-p)
                                     &key ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-expr-count x) 8))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-expr-p)
                 (new-conf vl-svexconf-p))
    (b* ((x (vl-expr-fix x))
         (conf (vl-svexconf-fix conf))
         (warnings nil))
      (vl-expr-case x
        :vl-index
        (b* (((wmv ok1 warnings new-scope conf)
              (vl-scopeexpr-elaborate x.scope conf :reclimit reclimit))
             ((wmv ok2 warnings new-indices conf)
              (vl-indexlist-resolve-constants x.indices conf :reclimit reclimit))
             ((wmv ok3 warnings new-partselect conf)
              (vl-partselect-elaborate x.part conf :reclimit reclimit))
             (new-x (change-vl-index x :scope new-scope :indices new-indices :part new-partselect))
             ((unless (and ok1 ok2 ok3))
              (mv nil warnings new-x conf))
             ((wmv ok warnings conf)
              (vl-index-expr-resolve-paramref new-x conf :reclimit reclimit)))
          (mv ok warnings new-x conf))

        :vl-multiconcat
        (b* (((wmv ok1 ?constantp warnings new-reps ?svex conf)
              (vl-expr-maybe-resolve-to-constant x.reps conf :reclimit reclimit))
             ((wmv ok2 warnings new-parts conf)
              (vl-exprlist-elaborate x.parts conf :reclimit reclimit))
             (new-x (change-vl-multiconcat x :reps new-reps :parts new-parts)))
          (mv (and ok1 ok2) warnings new-x conf))

        :vl-call
        (b* (((wmv ok1 warnings new-args conf)
              (vl-exprlist-elaborate x.args conf :reclimit reclimit))
             ((wmv ok2 warnings new-typearg conf)
              (if x.typearg
                  (vl-datatype-elaborate x.typearg conf :reclimit reclimit)
                (mv t nil nil conf)))
             ((wmv ok3 warnings new-fnname conf)
              (vl-scopeexpr-elaborate x.name conf :reclimit reclimit))
             (new-x (change-vl-call x :typearg new-typearg :args new-args :name new-fnname))
             ((when x.systemp) (mv (and ok1 ok2 ok3) warnings new-x conf))
             ((wmv ok4 warnings conf)
              (vl-function-compile-and-bind new-fnname conf :reclimit reclimit)))
          (mv (and ok1 ok2 ok3 ok4) warnings new-x conf))

        :vl-cast
        (b* (((wmv ok1 warnings new-casttype conf)
              (vl-casttype-elaborate x.to conf :reclimit reclimit))
             ((wmv ok2 warnings new-expr conf)
              (vl-expr-elaborate x.expr conf :reclimit reclimit))
             (new-x (change-vl-cast x :to new-casttype :expr new-expr)))
          (mv (and ok1 ok2) warnings new-x conf))

        ;; inside, stream, tagged, pattern
        
        :otherwise
        (vl-expr-elaborate-aux x conf :reclimit reclimit))))

  (define vl-indexlist-resolve-constants ((x vl-exprlist-p)
                                          (conf vl-svexconf-p)
                                          &key ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-exprlist-count x) 12))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-exprlist-p)
                 (new-conf vl-svexconf-p))
    (b* ((conf (vl-svexconf-fix conf))
         ((when (atom x)) (mv t nil nil conf))
         ((mv ok2 warnings rest conf)
          (vl-indexlist-resolve-constants (cdr x) conf :reclimit reclimit))
         ((wmv ok1 ?constantp warnings first ?svex conf)
          (vl-expr-maybe-resolve-to-constant (car x) conf :reclimit reclimit)))
      (mv (and ok1 ok2) warnings (cons first rest) conf)))


  (define vl-datatype-elaborate ((x vl-datatype-p)
                                 (conf vl-svexconf-p)
                                 &key ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-datatype-count x) 12))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-datatype-p)
                 (new-conf vl-svexconf-p))
    (vl-datatype-case x
      :vl-usertype
      (b* (((mv ok warnings res conf)
            (if x.res
                (vl-datatype-elaborate-aux x.res conf :reclimit reclimit)
              (vl-usertype-resolve x conf :reclimit reclimit)))
           ((wmv ok2 warnings pdims conf)
            (vl-packeddimensionlist-elaborate x.pdims conf :reclimit reclimit))
           ((wmv ok3 warnings udims conf)
            (vl-packeddimensionlist-elaborate x.udims conf :reclimit reclimit)))
        (mv (and ok ok2 ok3) warnings
            (change-vl-usertype
             x
             :res (and ok res)
             :pdims pdims :udims udims)
            conf))
      :otherwise
      (vl-datatype-elaborate-aux x conf :reclimit reclimit)))

  (define vl-usertype-resolve ((x vl-datatype-p)
                                 (conf vl-svexconf-p)
                                 &key ((reclimit natp) '1000))
    :guard (vl-datatype-case x :vl-usertype)
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-datatype-count x) 11))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-datatype-p)
                 (new-conf vl-svexconf-p))
    (b* (((vl-usertype x) (vl-datatype-fix x))
         ((vl-svexconf conf) (vl-svexconf-fix conf))
         (warnings nil)
         (hid (vl-scopeexpr->hid x.name))
         ;; BOZO Maybe we should use a different type than scopeexpr for a usertype name
         ((unless (vl-hidexpr-case hid :end))
          (mv nil
              (fatal :type :vl-usertype-resolve-error
                     :msg "Type names cannot be specified with dotted ~
                                   paths, only package scopes: ~a0"
                     :args (list x))
              x conf))
         (look (hons-get x.name conf.typeov))
         ((when look)
          (mv t warnings (cdr look) conf))
         ((mv err trace ?context ?tail)
          (vl-follow-scopeexpr x.name conf.ss))
         ((when err)
          (mv nil
              (fatal :type :vl-usertype-resolve-error
                     :msg "Couldn't find type ~a0"
                     :args (list x))
              x conf))
         ((when (zp reclimit))
          (mv nil
              (fatal :type :vl-usertype-resolve-error
                     :msg "Recursion limit ran out on usertype ~a0"
                     :args (list x))
              x conf))
         ((vl-hidstep ref) (car trace))
         ((when (eq (tag ref.item) :vl-typedef))
          (b* (((vl-typedef item) ref.item)
               (same-scope (equal conf.ss ref.ss))
               (declconf (if same-scope conf (make-vl-svexconf :ss ref.ss)))
               ((wmv ok warnings res-type conf declconf)
                (vl-datatype-fully-resolve-and-bind
                 x.name item.type declconf conf
                 :reclimit (1- reclimit))))
            (and (not same-scope) (vl-svexconf-free declconf))
            (mv ok warnings res-type conf)))
         ((when (eq (tag ref.item) :vl-paramdecl))
          (b* (((vl-paramdecl item) ref.item))
            (vl-paramtype-case item.type
              :vl-typeparam 
              (if item.type.default
                  (b* ((same-scope (equal conf.ss ref.ss))
                       (declconf (if same-scope conf (make-vl-svexconf :ss ref.ss)))
                       ((wmv ok warnings res-type conf ?declconf)
                        (vl-datatype-fully-resolve-and-bind
                         x.name item.type.default declconf conf
                         :reclimit (1- reclimit))))
                    (and (not same-scope) (vl-svexconf-free declconf))
                    (mv ok warnings res-type conf))
                (mv nil
                    (fatal :type :vl-usertype-resolve-error
                           :msg "Reference to unresolved type parameter ~a0"
                           :args (list item))
                    x conf))
              :otherwise
              (mv nil
                  (fatal :type :vl-usertype-resolve-error
                         :msg "Reference to data parameter ~a0 in type context"
                         :args (list item))
                  x conf)))))
      (mv nil
          (fatal :type :vl-usertype-resolve-error
                 :msg "~a0: Didn't find a typedef or parameter reference, instead found ~a1"
                 :args (list x ref.item))
          x conf))))


(fty::defvisitors vl-genelement-deps-elaborate
  :template elaborate
  :dep-types (vl-genelement))

(fty::defvisitor vl-genelement-elaborate
  :template elaborate
  :type vl-genelement
  :omit-types (vl-genarrayblock vl-genarrayblocklist)
  ;; these all need different scopes
  :prod-fns ((vl-genloop (continue :skip)
                         (nextval :skip)
                         (body :skip))
             (vl-genif   (then :skip)
                         (else :skip))
             (vl-gencase (default :skip))
             (vl-genblock (elems :skip))
             (vl-genarray (blocks :skip))
             (vl-gencaselist (:val :skip))))


(fty::defvisitors vl-genblob-elaborate
  :template elaborate
  :types (vl-genblob))

(fty::defvisitors vl-design-elaborate-aux-deps
  :template elaborate
  :dep-types (vl-package vl-module vl-interface vl-design))

(fty::defvisitor vl-design-elaborate-aux
  :template elaborate
  :type vl-design
  :renames ((vl-design vl-design-elaborate-aux)))

(fty::defvisitor vl-package-elaborate-aux
  :template elaborate
  :type vl-package
  :renames ((vl-package vl-package-elaborate-aux)))
              
