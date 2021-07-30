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
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system)
                           nfix natp)))


(local (in-theory (disable member append
                           sv::svarlist-addr-p-when-subsetp-equal
                           vl-warninglist-p-when-not-consp
                           acl2::true-listp-append
                           acl2::subsetp-when-atom-right
                           acl2::subsetp-when-atom-left)))

(defsection elaborate
  :parents (transforms)
  :short "Resolve constant expressions, parameter values, and datatypes."

  :long "<p>In the previous version of VL, we used to do a series of transforms
that:</p>

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

<p>The lookup table in which we store these values is called an @(see
elabindex).</p>

<p>The elaboration algorithm calls subsidiary algorithms of @(see
vl-expr-svex-translation), which use the elabindex lookup tables in a read-only
manner.  Before translating an expression (or, similarly, function declaration)
to svex, the elaboration algorithm walks over the expression and collects the
information it needs to successfully resolve it to an svex expression: the
types, svex translations, and port lists of functions that the expression
calls, and types and values of parameters referenced in the expression.  This
information is stored in the elabindex before translating the expression.</p>")

;; [Jared] Old notes about svexconfs -- do we describe this well for elabscopes
;; now?  Also BOZO need to check that the above description of elabindex is OK.

;; which contains a scopestack and additionally holds the following four
;; tables:</p>

;; <ul>

;; <li>@('typeov'), mapping from function, parameter, and type names to resolved
;; datatypes.  These datatypes have all indices and usertypes resolved.  Functions
;; map to their return types, value parameters map to their types, type parameters
;; map to their (datatype) values, and type names map to their definitions.</li>

;; <li>@('fns'), mapping from function names to @(see sv::svex) expressions for
;; their return values in terms of their inputs.</li>

;; <li>@('fnports'), mapping from function names to their resolved list of
;; ports (containing resolved datatypes).</li>

;; <li>@('params'), mapping from parameter names to @(see sv::svex) expressions for
;; their values, which should be constant.</li>

;; </ul>


(local (xdoc::set-default-parents elaborate))

(fty::defvisitor-template elaborate ((x :object)
                                     elabindex
                                     &key
                                     ((reclimit natp) 'reclimit)
                                     ((config vl-simpconfig-p) 'config))
  :returns (mv (ok (:join (and ok1 ok)
                    :initial t
                    :tmp-var ok1))
               (warnings (:join (append-without-guard warnings1 warnings)
                          :initial nil
                          :tmp-var warnings1)
                         vl-warninglist-p)
               (new-x :update)
               (new-elabindex (:acc elabindex)))
    :renames ((vl-fundecl vl-fundecl-elaborate-aux)
              (vl-expr vl-expr-elaborate-aux)
              (vl-datatype vl-datatype-elaborate-aux)
              (vl-vardecl  vl-vardecl-elaborate-aux)
              (vl-typedef  vl-typedef-elaborate-aux)
              (vl-paramdecl vl-paramdecl-elaborate-aux)
              (vl-stmt   vl-stmt-elaborate-aux)
              (vl-package vl-package-elaborate-aux)
              (vl-design vl-design-elaborate-aux)
              ;; BOZO These are here so that we can add context to warnings
              ;; generated by the elaborate mutual recursion.  This should also
              ;; be done the same way for various other things: aliases,
              ;; taskdecls, initial/finals, assertions, properties, ...
              (vl-assign vl-assign-elaborate-aux)
              (vl-modinst vl-modinst-elaborate-aux)
              (vl-always vl-always-elaborate-aux)
              (vl-atts   :skip))
    :type-fns ((vl-datatype vl-datatype-elaborate-fn)
               (vl-typedef vl-typedef-elaborate-fn)
               (vl-fundecl vl-fundecl-elaborate-fn)
               (vl-paramdecl vl-paramdecl-elaborate-fn)
               (vl-vardecl   vl-vardecl-elaborate-fn)
               (vl-expr     vl-expr-elaborate-fn)
               (vl-stmt     vl-stmt-elaborate-fn)
               (vl-assign vl-assign-elaborate-fn)
               (vl-modinst vl-modinst-elaborate-fn)
               (vl-always vl-always-elaborate-fn)
               (vl-atts   vl-atts-elaborate-fn))
    :prod-fns ((vl-hidindex  (indices vl-indexlist-resolve-constants-fn))
               (vl-range     (msb vl-index-resolve-if-constant-fn)
                             (lsb vl-index-resolve-if-constant-fn))
               (vl-plusminus (base vl-index-resolve-if-constant-fn)
                             (width vl-index-resolve-constant-fn))
               (vl-arrayrange-index (expr vl-index-resolve-if-constant-fn))
               (vl-patternkey-expr   (key vl-index-resolve-if-constant-fn)) ;; BOZO this will break struct field names
               (vl-casttype-size (size vl-index-resolve-if-constant-fn))
               (vl-slicesize-expr (expr vl-index-resolve-if-constant-fn))
               (vl-arrayrange-index (expr vl-index-resolve-if-constant-fn))
               ;; these all need different scopes
               (vl-genloop (continue :skip)
                           (nextval :skip)
                           (body :skip))
               (vl-genif   (then :skip)
                           (else :skip))
               (vl-gencase (default :skip))
               (vl-genblock (elems :skip))
               (vl-genarray (blocks :skip))
               (vl-gencaselist (:val :skip)))
    :field-fns ((atts :skip)
                (mods :skip)
                (interfaces :skip)
                (packages :skip))

  :fnname-template <type>-elaborate)


(define vl-warn-about-negative-indices ((constantp "did it resolve to a constant")
                                        (orig-x vl-expr-p)
                                        (new-x  vl-expr-p)
                                        (warnings vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* (((unless (and constantp
                     (vl-expr-resolved-p new-x)
                     (< (vl-resolved->val new-x) 0)
                     (not (vl-expr-equiv new-x orig-x))))
        (ok)))
    (warn :type :vl-negative-index
          :msg "Index expression ~a0 resolved to ~a1, where a nonnegative value was expected"
          :args (list (vl-expr-fix orig-x)
                      ;; remove the vl-origexpr att so as to print the new expr
                      (vl-expr-update-atts new-x nil)))))




;; (define vl-maybe-svexconf-free (freep elabindex)
;;   :returns nil
;;   ;; Hack to control case splits
;;   (if freep
;;       (vl-svexconf-free conf)
;;     nil))

;; (define vl-choose-svexconf (condition (true vl-svexconf-p) (false vl-svexconf-p))
;;   :returns (choice vl-svexconf-p)
;;   ;; Hack to control case splits
;;   (if condition
;;       (vl-svexconf-fix true)
;;     (vl-svexconf-fix false)))

;; (local (in-theory (disable cons-equal not)))

(include-book "std/lists/len" :dir :system)

(local (in-theory (disable len
                           true-listp
                           acl2::list-fix-when-len-zero
                           acl2::list-fix-when-true-listp
                           acl2::list-fix-when-not-consp
                           set::sets-are-true-lists
                           default-car
                           default-cdr
                           acl2::nfix-when-not-natp
                           nth
                           acl2::member-of-cons
                           acl2::subsetp-append1
                           acl2::append-atom-under-list-equiv
                           acl2::subsetp-trans2
                           acl2::subsetp-trans
                           acl2::consp-of-append
                           cons-equal)))

#!sv
(define svex-constval ((x svex-p))
  :returns (val maybe-4vec-p)
  (svex-case x :quote x.val :otherwise nil))

(local
 (defthm member-singleton
   (iff (member x (list y))
        (equal x y))
   :hints(("Goal" :in-theory (enable acl2::member-of-cons)))))

(fty::defvisitor-multi vl-elaborate
  :defines-args (:ruler-extenders :all
                 ;; :measure-debug t
                 ;; :guard-debug t
                 )

  ;; Note about avoiding measure troubles in this mutual recursion.  Start here
  ;; from lowest dependencies: expressions and datatypes.  Work our way up.
  ;; Reclimit should be decreased when processing a new item we've looked up,
  ;; but shouldn't need to be when processing a part of the current item.  The
  ;; order (second item in the nat-list-measure after reclimit) should be
  ;; increased by a "safe" value (say 100) for each layer.

  ;; ----- Order 0.  Collects functions that are just going to decrease the
  ;; reclimit on any recursive call.
  

  

  (define vl-function-compile-and-bind ((fnname vl-scopeexpr-p)
                                        elabindex
                                        &key
                                        ((reclimit natp) 'reclimit)
                                        ((config vl-simpconfig-p) 'config))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 new-elabindex)
    :measure (acl2::nat-list-measure
              (list reclimit 0 0 0)) ;; the only recursive call here will decrease the reclimit
    (b* ((fnname (vl-scopeexpr-fix fnname))
         (warnings nil)
         ((mv err trace ?context tail)
          (vl-follow-scopeexpr fnname (vl-elabindex->ss elabindex) :strictp t))
         ((when err)
          (mv nil
              (fatal :type :vl-function-compile-fail
                     :msg "Couldn't find function ~a0: ~@1"
                     :args (list fnname err))
              elabindex))
         ((unless (vl-hidexpr-case tail :end))
          (mv nil
              (fatal :type :vl-function-compile-fail
                     :msg "Data select into a function? ~a0"
                     :args (list fnname))
              elabindex))
         ((vl-hidstep step) (car trace))
         ((unless (eq (tag step.item) :vl-fundecl))
          (mv nil
              (fatal :type :vl-function-compile-fail
                     :msg "Reference to item ~a0 in function name context: ~a1"
                     :args (list step.item fnname))
              elabindex))
         ((when (zp reclimit))
          (mv nil
              (fatal :type :vl-function-compile-fail
                     :msg "Reclimit ran out on ~a0: dependency loop?"
                     :args (list fnname))
              elabindex))
         (decl step.item)
         ;; BOZO probably should traverse using the decl.elabpath instead but not yet implemented
         ;; ((vl-fundecl decl) step.item)
         (elabindex (vl-elabindex-traverse step.ss (rev step.elabpath)))
         ((wmv ok warnings ?new-decl elabindex)
          (vl-fundecl-elaborate decl elabindex :reclimit (1- reclimit)))
         (elabindex (vl-elabindex-undo))
         ((unless ok)
          (mv nil warnings elabindex)))
      (mv t warnings elabindex))
    ///
    (in-theory (disable vl-function-compile-and-bind)))


  

  (define vl-usertype-resolve ((x vl-datatype-p)
                               elabindex
                               &key
                               ((reclimit natp) 'reclimit)
                               ((config vl-simpconfig-p) 'config))
    :guard (vl-datatype-case x :vl-usertype)
    :measure (acl2::nat-list-measure
              (list reclimit 0 0 0))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-datatype-p)
                 new-elabindex)
    (b* (((vl-usertype x) (vl-datatype-fix x))
         (warnings nil)
         ((when x.virtual-intfc)
          (mv nil
              (fatal :type :vl-virtual-intfc-unsupported
                     :msg "Virtual interface datatypes aren't yet supported: ~a0"
                     :args (list x))
              x elabindex))
         (hid (vl-scopeexpr->hid x.name))
         ;; BOZO Maybe we should use a different type than scopeexpr for a usertype name
         ((unless (vl-hidexpr-case hid :end))
          (mv nil
              (fatal :type :vl-usertype-resolve-error
                     :msg "Type names cannot be specified with dotted ~
                                   paths, only package scopes: ~a0"
                     :args (list x))
              x elabindex))
         ((mv err trace ?context ?tail)
          (vl-follow-scopeexpr x.name (vl-elabindex->ss elabindex)))
         ((when err)
          (mv nil
              (fatal :type :vl-usertype-resolve-error
                     :msg "Couldn't find type ~a0"
                     :args (list x))
              x elabindex))
         ((when (zp reclimit))
          (mv nil
              (fatal :type :vl-usertype-resolve-error
                     :msg "Recursion limit ran out on usertype ~a0"
                     :args (list x))
              x elabindex))
         (reclimit (1- reclimit))
         ((vl-hidstep ref) (car trace))
         (elabindex (vl-elabindex-traverse ref.ss (rev ref.elabpath)))
         
         ((when (eq (tag ref.item) :vl-typedef))
          (b* (((wmv ok warnings item elabindex)
                (vl-typedef-elaborate ref.item elabindex :reclimit reclimit))
               ((vl-typedef item) item)
               (elabindex (vl-elabindex-undo)))
            (mv ok warnings item.type elabindex)))
         ((when (eq (tag ref.item) :vl-paramdecl))
          (b* (((wmv ok warnings item elabindex)
                (vl-paramdecl-elaborate ref.item elabindex :reclimit reclimit))
               ((vl-paramdecl item) item))
            (vl-paramtype-case item.type
              :vl-typeparam
              (b* (((unless item.type.default)
                    (b* ((elabindex (vl-elabindex-undo)))
                      (mv nil
                          (fatal :type :vl-usertype-resolve-error
                                 :msg "Reference to unresolved type parameter ~a0"
                                 :args (list item))
                          x elabindex)))
                   (elabindex (vl-elabindex-undo)))
                (mv ok warnings item.type.default elabindex))
              :otherwise
              (b* ((elabindex (vl-elabindex-undo)))
                (mv nil
                    (fatal :type :vl-usertype-resolve-error
                           :msg "Reference to data parameter ~a0 in type context"
                           :args (list item))
                    x elabindex)))))
         (elabindex (vl-elabindex-undo)))
      (mv nil
          (fatal :type :vl-usertype-resolve-error
                 :msg "~a0: Didn't find a typedef or parameter reference, instead found ~a1"
                 :args (list x ref.item))
          x elabindex))
    ///
    (in-theory (disable vl-usertype-resolve)))

  



  ;; Order 1 -- expressions/datatypes. Everything here is measured by the size of
  ;; expression/datatype we're working on.  Whenever we have to look up some
  ;; other element we decrease the reclimit.

  (fty::defvisitor :template elaborate
    :type expressions-and-datatypes
    :order 1
    :measure (acl2::nat-list-measure
              (list reclimit :order :count 0)))

  (define vl-datatype-elaborate ((x vl-datatype-p)
                                 elabindex
                                 &key
                                 ((reclimit natp) 'reclimit)
                                 ((config vl-simpconfig-p) 'config))
    :measure (acl2::nat-list-measure
              (list reclimit 1 (vl-datatype-count x) 12))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-datatype-p)
                 new-elabindex)
    (vl-datatype-case x
      :vl-usertype
      (b* (((mv ok warnings res elabindex)
            (if x.res
                (vl-datatype-elaborate-aux x.res elabindex :reclimit reclimit)
              (vl-usertype-resolve x elabindex :reclimit reclimit)))
           ((wmv ok2 warnings pdims elabindex)
            (vl-dimensionlist-elaborate x.pdims elabindex :reclimit reclimit))
           ((wmv ok3 warnings udims elabindex)
            (vl-dimensionlist-elaborate x.udims elabindex :reclimit reclimit)))
        (mv (and* ok ok2 ok3) warnings
            (change-vl-usertype
             x
             :res (and ok res)
             :pdims pdims :udims udims)
            elabindex))
      :vl-enum
      ;; need to resolve the values to indices
      (b* (((mv ok1 warnings basetype elabindex)
            (vl-datatype-elaborate x.basetype elabindex :reclimit reclimit))
           ((wmv ok2 warnings items elabindex)
            (vl-enumitemlist-elaborate x.items elabindex :reclimit reclimit))
           ((wmv ok3 warnings values elabindex)
            (vl-indexlist-resolve-constants x.values elabindex :reclimit reclimit))
           ((wmv ok4 warnings pdims elabindex)
            (vl-dimensionlist-elaborate x.pdims elabindex :reclimit reclimit))
           ((wmv ok5 warnings udims elabindex)
            (vl-dimensionlist-elaborate x.udims elabindex :reclimit reclimit)))
        (mv (and* ok1 ok2 ok3 ok4 ok5) warnings
            (change-vl-enum
             x
             :basetype basetype
             :items items
             :values values
             :pdims pdims
             :udims udims)
            elabindex))
      :otherwise
      (vl-datatype-elaborate-aux x elabindex :reclimit reclimit))
    ///
    (in-theory (disable vl-datatype-elaborate)))

  (define vl-expr-resolve-to-constant ((x vl-expr-p)
                                       elabindex
                                       &key
                                       ((reclimit natp) 'reclimit)
                                       ((config vl-simpconfig-p) 'config)
                                       ((ctxsize maybe-natp) 'nil)
                                       ((type vl-maybe-datatype-p) 'nil)
                                       ((lhs vl-maybe-expr-p) 'nil))
    ;; Just calls vl-expr-maybe-resolve-to-constant, but produces a fatal
    ;; warning if it failed to reduce to a constant.
    :measure (acl2::nat-list-measure
              (list reclimit 1 (vl-expr-count x) 10))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-expr-p)
                 (svex sv::svex-p)
                 new-elabindex)
    (b* ((orig-x (vl-expr-fix x))
         ((mv ok constantp warnings x svex elabindex)
          (vl-expr-maybe-resolve-to-constant x elabindex :reclimit reclimit
                                             :ctxsize ctxsize
                                             :type type
                                             :lhs lhs)))
      (mv (and ok constantp)
          (if (and ok (not constantp))
              (fatal :type :vl-expr-consteval-fail
                     :msg "Couldn't resolve ~a0 to constant (original: ~a1)"
                     :args (list x orig-x))
            warnings)
          x svex elabindex))
    ///
    (in-theory (disable vl-expr-resolve-to-constant)))

  (define vl-rhs-resolve-to-constant ((x vl-rhs-p)
                                      elabindex
                                      &key
                                      ((reclimit natp) 'reclimit)
                                      ((config vl-simpconfig-p) 'config)
                                      ((ctxsize maybe-natp) 'nil)
                                      ((type vl-maybe-datatype-p) 'nil)
                                      ((lhs vl-maybe-expr-p) 'nil))
    :measure (acl2::nat-list-measure
              (list reclimit 2 nil nil))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-rhs-p)
                 (svex sv::svex-p)
                 new-elabindex)
    (b* ((x (vl-rhs-fix x))
         (warnings nil))
      (vl-rhs-case x
        :vl-rhsexpr
        (b* (((mv ok warnings new-guts svex elabindex)
              (vl-expr-resolve-to-constant x.guts elabindex
                                           :ctxsize ctxsize
                                           :type type
                                           :lhs lhs))
             (new-x (change-vl-rhsexpr x :guts new-guts)))
          (mv ok warnings new-x svex elabindex))
        :vl-rhsnew
        (mv nil
            (fatal :type :vl-expr-consteval-fail
                   :msg "Couldn't resolve rhs ~a0 to constant."
                   :args (list (vl-rhs-fix x)))
            x
            (svex-x)
            elabindex))))

  ;; (define vl-expr-resolve-to-constant-top ((x vl-expr-p)
  ;;                                          elabindex
  ;;                                          &key
  ;;                                          ((reclimit natp) 'reclimit)
  ;;                                          ((config vl-simpconfig-p) 'config)
  ;;                                          ((ctxsize maybe-natp) 'nil)
  ;;                                          ((type vl-maybe-datatype-p) 'nil))
  
  ;;   ;; Just calls vl-expr-resolve-to-constant, but also decrements the reclimit
  ;;   ;; so it can be easily called from anywhere in the mutual recursion.
  ;;   :measure (acl2::nat-list-measure
  ;;             (list reclimit 1 0 0))
  ;;   :returns (mv (ok)
  ;;                (warnings vl-warninglist-p)
  ;;                (new-x vl-expr-p)
  ;;                (svex sv::svex-p)
  ;;                new-elabindex)
  ;;   (b* ((warnings nil)
  ;;        ((when (zp reclimit))
  ;;         (mv nil
  ;;             (fatal :type :vl-elaborate-fail
  ;;                    :msg "Reclimit ran out on ~a0: dependency loop?"
  ;;                    :args (list (vl-expr-fix x)))
  ;;             (vl-expr-fix x) (svex-x)
  ;;             elabindex)))
  ;;     (vl-expr-resolve-to-constant x elabindex :reclimit (1- reclimit)
  ;;                                  :ctxsize ctxsize
  ;;                                  :type type))
  ;;   ///
  ;;   (in-theory (disable vl-expr-resolve-to-constant-top)))

  (define vl-expr-maybe-resolve-to-constant ((x vl-expr-p)
                                             elabindex
                                             &key
                                             ((reclimit natp) 'reclimit)
                                             ((config vl-simpconfig-p) 'config)
                                             ((ctxsize maybe-natp) 'nil)
                                             ((type vl-maybe-datatype-p) 'nil)
                                             ((lhs vl-maybe-expr-p) 'nil))
    :measure (acl2::nat-list-measure
              (list reclimit 1 (vl-expr-count x) 9))
    :returns (mv (ok)
                 (constantp)
                 (warnings vl-warninglist-p)
                 (new-x vl-expr-p)
                 (svex sv::svex-p)
                 new-elabindex)

    (b* (((mv ok warnings x elabindex)
          (vl-expr-elaborate x elabindex :reclimit reclimit))
         ((unless ok) (mv nil nil warnings x (svex-x) elabindex))
         (elabindex (vl-elabindex-sync-scopes))
         ((vl-elabindex elabindex))
         ((mv ok constp warnings x svex)
          (vl-elaborated-expr-consteval x elabindex.ss elabindex.scopes
                                        :ctxsize ctxsize :type type :lhs lhs)))
      (mv ok constp warnings x svex elabindex))
    ///
    (in-theory (disable vl-expr-maybe-resolve-to-constant)))

  (define vl-index-resolve-if-constant ((x vl-expr-p)
                                        elabindex
                                        &key
                                        ((reclimit natp) 'reclimit)
                                        ((config vl-simpconfig-p) 'config))
    :measure (acl2::nat-list-measure
              (list reclimit 1 (vl-expr-count x) 10))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-expr-p)
                 new-elabindex)
    (b* (((mv ok ?constantp warnings new-x ?svex elabindex)
          (vl-expr-maybe-resolve-to-constant x elabindex :reclimit reclimit))
         (warnings (vl-warn-about-negative-indices constantp x new-x warnings)))
      (mv ok warnings new-x elabindex))
    ///
    (in-theory (disable vl-index-resolve-if-constant)))

  (define vl-index-resolve-constant ((x vl-expr-p)
                                     elabindex
                                     &key
                                     ((reclimit natp) 'reclimit)
                                     ((config vl-simpconfig-p) 'config))
    :measure (acl2::nat-list-measure
              (list reclimit 1 (vl-expr-count x) 11))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-expr-p)
                 new-elabindex)
    (b* (((mv ok warnings new-x ?svex elabindex)
          (vl-expr-resolve-to-constant x elabindex :reclimit reclimit))
         (warnings (vl-warn-about-negative-indices ok x new-x warnings)))
      (mv ok warnings new-x elabindex))
    ///
    (in-theory (disable vl-index-resolve-constant)))


  (define vl-index-expr-resolve-paramref ((x vl-expr-p)
                                          elabindex
                                          &key
                                          ((reclimit natp) 'reclimit)
                                          ((config vl-simpconfig-p) 'config))
    ;; Call this AFTER indices within the hids have been maybe-resolved.
    :measure (acl2::nat-list-measure
              (list reclimit 1 0 10))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 new-elabindex)
    :guard (vl-expr-case x :vl-index)

    (b* ((warnings nil)
         (ss (vl-elabindex->ss elabindex))
         ((vl-index x) (vl-expr-fix x))
         ((unless (mbt (vl-expr-case x :vl-index)))
          (impossible) ;; need this case for measure
          (mv nil warnings elabindex))
         ((mv err hidtrace ?context ?tail)
          (vl-follow-scopeexpr x.scope ss))
         ((when err)
          (mv t
              ;; It might just be a variable from a generate that isn't present yet.
              ;; (warn :type :vl-resolve-constants-fail
              ;;        :msg "Couldn't find ~a0"
              ;;        :args (list x))
              warnings
              elabindex))

         ;; ;; Strip structure/array indexing off the end of the hid.
         ;; (prefix-name (vl-scopeexpr-replace-hid
         ;;               x.scope
         ;;               (vl-hid-prefix-for-subhid (vl-scopeexpr->hid x.scope) tail)))

         ((vl-hidstep hidstep) (car hidtrace))

         ((when (or (eq (tag hidstep.item) :vl-modinst)
                    (eq (tag hidstep.item) :vl-interfaceport)))
          ;; If it's a modinst, it might be an interface, which is legitimate
          ;; in some situations
          (mv t warnings elabindex))

         ((unless (or (eq (tag hidstep.item) :vl-paramdecl)
                      (eq (tag hidstep.item) :vl-vardecl)))
          (mv nil
              (fatal :type :vl-resolve-constants-fail
                     :msg "~a0: Bad item for variable reference: ~a1"
                     :args (list x hidstep.item))
              elabindex))

         ;; From here on out we're going to need to look up the item as a
         ;; variable or parameter, so check that the reclimit hasn't run out.
         ((when (zp reclimit))
          (mv nil
              (fatal :type :vl-elaborate-fail
                     :msg "Reclimit ran out looking up ~a0: dependency loop?"
                     :args (list hidstep.item))
              elabindex))
         (reclimit (1- reclimit))

         (elabindex (vl-elabindex-traverse hidstep.ss (rev hidstep.elabpath)))
         
         ((when (eq (tag hidstep.item) :vl-vardecl))
          (b* (((wmv ok warnings ?decl elabindex)
                (vl-vardecl-elaborate hidstep.item elabindex :reclimit reclimit))
               (elabindex (vl-elabindex-undo)))
            ;; It's not a paramdecl, so we can't resolve it to a constant.  But
            ;; we do want to make sure its type is resolved if it's a vardecl.
            (mv ok warnings elabindex)))

         ((wmv ok warnings decl elabindex)
          (vl-paramdecl-elaborate hidstep.item elabindex :reclimit reclimit))
         (elabindex (vl-elabindex-undo))

         ((vl-paramdecl decl)))

      (vl-paramtype-case decl.type
        :vl-typeparam
        (mv nil
            (fatal :type :vl-resolve-constants-fail
                   :msg "Type parameter referenced as expression: ~a0"
                   :args (list x))
            elabindex)
        :vl-implicitvalueparam
        (mv nil
            (fatal :type :vl-resolve-constants-fail
                   :msg "Parameter not resolved to explicitly typed constant: ~a0"
                   :args (list x))
            elabindex)

        :vl-explicitvalueparam
        (if (and decl.type.default
                 ;; (vl-expr-case decl.type.default :vl-literal)
                 )
            (mv ok warnings elabindex)
          (mv nil
              (fatal :type :vl-resolve-constants-fail
                     :msg "Parameter was not resolved to a constant: ~a0"
                     :args (list decl))
              elabindex))))
    ///
    (in-theory (disable vl-index-expr-resolve-paramref)))


  (define vl-atts-elaborate ((x vl-atts-p)
                             elabindex
                             &key ((reclimit natp) '1000) ((config vl-simpconfig-p) 'config))
    :measure (acl2::nat-list-measure
              (list reclimit 1 (vl-atts-count x) 0))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-atts-p)
                 new-elabindex)
    (b* ((x (vl-atts-fix x))
         ((when (atom x)) (mv t nil nil elabindex))
         ((mv ok warnings val elabindex)
          (if (equal (caar x) "VL_ORIG_EXPR")
              (mv t nil (cdar x) elabindex)
            (vl-maybe-expr-elaborate (cdar x) elabindex :reclimit reclimit)))
         ((mv ok1 warnings1 cdr elabindex)
          (vl-atts-elaborate (cdr x) elabindex :reclimit reclimit)))
      (mv (and ok1 ok)
          (append-without-guard warnings1 warnings)
          (cons (cons (caar x) val) cdr)
          elabindex)))
         


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
                             elabindex
                             &key
                             ((reclimit natp) 'reclimit)
                             ((config vl-simpconfig-p) 'config))
    :measure (acl2::nat-list-measure
              (list reclimit 1 (vl-expr-count x) 8))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-expr-p)
                 new-elabindex)
    (b* ((x (vl-expr-fix x))
         (warnings nil))
      (vl-expr-case x
        :vl-index
        (b* (((wmv ok1 warnings new-scope elabindex)
              (vl-scopeexpr-elaborate x.scope elabindex :reclimit reclimit))
             ((wmv ok2 warnings new-indices elabindex)
              (vl-indexlist-resolve-constants x.indices elabindex :reclimit reclimit))
             ((wmv ok3 warnings new-partselect elabindex)
              (vl-partselect-elaborate x.part elabindex :reclimit reclimit))
             (new-x (change-vl-index x :scope new-scope :indices new-indices :part new-partselect))
             ((unless (and* ok1 ok2 ok3))
              (mv nil warnings new-x elabindex))
             ((wmv ok warnings elabindex)
              (vl-index-expr-resolve-paramref new-x elabindex :reclimit reclimit)))
          (mv ok warnings new-x elabindex))

        :vl-multiconcat
        (b* (((wmv ok1 ?constantp warnings new-reps ?svex elabindex)
              (vl-expr-maybe-resolve-to-constant x.reps elabindex :reclimit reclimit))
             ((wmv ok2 warnings new-parts elabindex)
              (vl-exprlist-elaborate x.parts elabindex :reclimit reclimit))
             (new-x (change-vl-multiconcat x :reps new-reps :parts new-parts)))
          (mv (and* ok1 ok2) warnings new-x elabindex))

        :vl-call
        (b* (((wmv ok1 warnings new-plainargs elabindex)
              ;; Heuristic decision: Resolve arguments to constants iff this is
              ;; a system call.  That way we get the dimension resolved for
              ;; things like $size.
              (if x.systemp
                  (vl-maybe-indexlist-resolve-constants x.plainargs elabindex :reclimit reclimit)
                (vl-maybe-exprlist-elaborate x.plainargs elabindex :reclimit reclimit)))
             ((wmv ok2 warnings new-namedargs elabindex)
              (vl-call-namedargs-elaborate x.namedargs elabindex :reclimit reclimit))
             ((wmv ok3 warnings new-typearg elabindex)
              (if x.typearg
                  (vl-datatype-elaborate x.typearg elabindex :reclimit reclimit)
                (mv t nil nil elabindex)))
             ((wmv ok4 warnings new-fnname elabindex)
              (vl-scopeexpr-elaborate x.name elabindex :reclimit reclimit))
             (new-x (change-vl-call x
                                    :typearg new-typearg
                                    :plainargs new-plainargs
                                    :namedargs new-namedargs
                                    :name new-fnname))
             ((when x.systemp) (mv (and* ok1 ok2 ok3) warnings new-x elabindex))
             ((wmv ok5 warnings elabindex)
              (vl-function-compile-and-bind new-fnname elabindex :reclimit reclimit)))
          (mv (and* ok1 ok2 ok3 ok4 ok5) warnings new-x elabindex))

        :vl-cast
        ;; what is different here from elaborate-aux?
        (b* (((wmv ok1 warnings new-casttype elabindex)
              (vl-casttype-elaborate x.to elabindex :reclimit reclimit))
             ((wmv ok2 warnings new-expr elabindex)
              (vl-expr-elaborate x.expr elabindex :reclimit reclimit))
             (new-x (change-vl-cast x :to new-casttype :expr new-expr)))
          (mv (and* ok1 ok2) warnings new-x elabindex))

        ;; inside, stream, tagged, pattern

        :otherwise
        (vl-expr-elaborate-aux x elabindex :reclimit reclimit)))
    ///
    (in-theory (disable vl-expr-elaborate)))

  (define vl-indexlist-resolve-constants ((x vl-exprlist-p)
                                          elabindex
                                          &key
                                          ((reclimit natp) 'reclimit)
                                          ((config vl-simpconfig-p) 'config))
    :measure (acl2::nat-list-measure
              (list reclimit 1 (vl-exprlist-count x) 12))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-exprlist-p)
                 new-elabindex)
    (b* (((when (atom x)) (mv t nil nil elabindex))
         ((mv ok2 warnings rest elabindex)
          (vl-indexlist-resolve-constants (cdr x) elabindex))
         ((wmv ok1 ?constantp warnings first ?svex elabindex)
          (vl-expr-maybe-resolve-to-constant (car x) elabindex)))
      (mv (and* ok1 ok2) warnings (cons first rest) elabindex))
    ///
    (in-theory (disable vl-indexlist-resolve-constants)))

  (define vl-maybe-indexlist-resolve-constants ((x vl-maybe-exprlist-p)
                                                elabindex
                                                &key
                                                ((reclimit natp) 'reclimit)
                                                ((config vl-simpconfig-p) 'config))
    :measure (acl2::nat-list-measure
              (list reclimit 1 (vl-maybe-exprlist-count x) 12))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-maybe-exprlist-p)
                 new-elabindex)
    (b* (((when (atom x)) (mv t nil nil elabindex))
         ((mv ok2 warnings rest elabindex)
          (vl-maybe-indexlist-resolve-constants (cdr x) elabindex))
         ((unless (car x))
          (mv ok2 warnings (cons nil rest) elabindex))
         ((wmv ok1 ?constantp warnings first ?svex elabindex)
          (vl-expr-maybe-resolve-to-constant (car x) elabindex)))
      (mv (and* ok1 ok2) warnings (cons first rest) elabindex))
    ///
    (in-theory (disable vl-maybe-indexlist-resolve-constants)))


  ;; Order 100.  We are done with the expr/datatype nest; on to vardecls,
  ;; typedefs, and paramdecls.

  (fty::defvisitors :template elaborate
    :types (vl-vardecl vl-typedef vl-paramdecl)
    :order-base 100
    :measure (acl2::nat-list-measure (list reclimit :order :count 0)))

  ;; Hrmn, turns out we don't actually need these...

  ;; (define vl-rhs-elaborate ((x vl-rhs-p)
  ;;                           (elabindex "in the scope where x is declared")
  ;;                           &key
  ;;                           ((reclimit natp) 'reclimit)
  ;;                           ((config vl-simpconfig-p) 'config))
  ;;   :measure (acl2::nat-list-measure (list reclimit 140 0 0))
  ;;   :returns (mv (ok)
  ;;                (warnings vl-warninglist-p)
  ;;                (new-x vl-rhs-p)
  ;;                new-elabindex)
  ;;   (b* ((warnings nil))
  ;;     (vl-rhs-case x
  ;;       :vl-rhsexpr
  ;;       (b* (((wmv ok warnings new-guts elabindex)
  ;;             (vl-expr-elaborate x.guts elabindex))
  ;;            (new-x (change-vl-rhsexpr x :guts new-guts)))
  ;;         (mv ok warnings new-x elabindex))
  ;;       :vl-rhsnew
  ;;       (b* (((wmv ok1 warnings new-arrsize elabindex)
  ;;             (vl-expr-elaborate x.arrsize elabindex))
  ;;            ((wmv ok2 warnings new-args elabindex)
  ;;             (vl-exprlist-elaborate x.args elabindex))
  ;;            (new-x (change-vl-rhsnew x
  ;;                                     :arrsize new-arrsize
  ;;                                     :args new-args)))
  ;;         (mv (and* ok1 ok2) warnings new-x elabindex)))))

  ;; (define vl-maybe-rhs-elaborate ((x vl-maybe-rhs-p)
  ;;                                 (elabindex "in the scope where x is declared")
  ;;                                 &key
  ;;                                 ((reclimit natp) 'reclimit)
  ;;                                 ((config vl-simpconfig-p) 'config))
  ;;   :measure (acl2::nat-list-measure (list reclimit 141 0 0))
  ;;   :returns (mv (ok)
  ;;                (warnings vl-warninglist-p)
  ;;                (new-x vl-rhs-p)
  ;;                new-elabindex)
  ;;   (b* ((x (vl-maybe-rhs-fix x)))
  ;;     (if x
  ;;         (vl-rhs-elaborate x elabindex)
  ;;       (mv t nil nil elabindex))))

  (define vl-vardecl-elaborate ((x vl-vardecl-p)
                                (elabindex "in the scope where x is declared")
                                &key
                                ((reclimit natp) 'reclimit)
                                ((config vl-simpconfig-p) 'config))
    :measure (acl2::nat-list-measure (list reclimit 150 0 0))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-vardecl-p)
                 new-elabindex)
    (b* ((warnings nil)
         ((vl-vardecl x) (vl-vardecl-fix x))
         (item (vl-elabscopes-item-info x.name (vl-elabindex->scopes)))
         ((when item)
          (if (eq (tag item) :vl-vardecl)
              (mv t warnings item elabindex)
            (mv nil
                (fatal :type :vl-programming-error
                       :msg "Found ~a0 stored in place of the elaborated version of ~a1"
                       :args (list item (vl-vardecl-fix x)))
                (vl-vardecl-fix x)
                elabindex)))
         ((mv ok warnings new-x elabindex)
          (vl-vardecl-elaborate-aux x elabindex :reclimit reclimit))
         (warnings (vl-warninglist-add-ctx warnings (vl-vardecl-fix x)))
         ((unless ok)
          (mv nil warnings new-x elabindex))
         ((vl-vardecl new-x))
         ((unless (and new-x.constp new-x.initval))
          (b* ((elabindex (vl-elabindex-update-item-info x.name new-x)))
            (mv ok warnings new-x elabindex)))
         ;; analogous to the explicitvalueparam case in paramdecl-elaborate
         ((wmv ok1 warnings ?new-expr svex elabindex :ctx x)
          (vl-rhs-resolve-to-constant new-x.initval elabindex
                                      :reclimit reclimit
                                      :type new-x.type
                                      :lhs (vl-idexpr x.name)))

         (val (sv::svex-constval svex))
         ((unless (and ok1 val))
          (mv nil
              (fatal :type :vl-resolve-constants-fail
                     :msg "Couldn't resolve const variable ~a0.  Other ~
                                 warnings should explain why."
                     :args (list x))
              new-x
              elabindex))

         (new-x (change-vl-vardecl new-x :constval val))

         (elabindex (vl-elabindex-update-item-info x.name new-x)))

      (mv ok warnings new-x elabindex)))

  (define vl-typedef-elaborate ((x vl-typedef-p)
                                (elabindex "in the scope where x is declared")
                                &key
                                ((reclimit natp) 'reclimit)
                                ((config vl-simpconfig-p) 'config))
    :measure (acl2::nat-list-measure (list reclimit 150 0 0))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-typedef-p)
                 new-elabindex)
    (b* ((warnings nil)
         (name  (vl-typedef->name x))
         (item (vl-elabscopes-item-info name (vl-elabindex->scopes)))
         ((when item)
          (if (eq (tag item) :vl-typedef)
              (mv t warnings item elabindex)
            (mv nil
                (fatal :type :vl-programming-error
                       :msg "Found ~a0 stored in place of the elaborated version of ~a1"
                       :args (list item (vl-typedef-fix x)))
                (vl-typedef-fix x)
                elabindex)))
         ((mv ok warnings new-x elabindex)
          (vl-typedef-elaborate-aux x elabindex :reclimit reclimit))
         (warnings (vl-warninglist-add-ctx warnings (vl-typedef-fix x)))
         ((unless ok)
          (mv nil warnings new-x elabindex))
         (elabindex (vl-elabindex-update-item-info name new-x)))
      (mv ok warnings new-x elabindex)))

  (define vl-paramdecl-elaborate ((x vl-paramdecl-p)
                                  elabindex
                                  &key
                                  ((reclimit natp) 'reclimit)
                                  ((config vl-simpconfig-p) 'config))
    :measure (acl2::nat-list-measure
              ;; order of paramdecl-elaborate-aux is 2
              (list reclimit 150 0 0))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-paramdecl-p)
                 new-elabindex)
    (b* ((x (vl-paramdecl-fix x))
         (warnings nil)
         (name  (vl-paramdecl->name x))
         (item (vl-elabscopes-item-info name (vl-elabindex->scopes)))
         ((when item)
          (if (eq (tag item) :vl-paramdecl)
              (mv t warnings item elabindex)
            (mv nil
                (fatal :type :vl-programming-error
                       :msg "Found ~a0 stored in place of the elaborated version of ~a1"
                       :args (list item x))
                x
                elabindex)))

         ((mv ok warnings decl elabindex)
          (vl-paramdecl-elaborate-aux x elabindex :reclimit reclimit))
         (warnings (vl-warninglist-add-ctx warnings x))
         ((vl-paramdecl decl)))

      (vl-paramtype-case decl.type
        :vl-typeparam
        ;; Nothing to resolve.
        (b* ((elabindex (vl-elabindex-update-item-info name decl)))
          (mv ok warnings decl elabindex))
        :vl-explicitvalueparam
        (b* (((unless decl.type.default)
              (mv nil
                  (fatal :type :vl-resolve-constants-fail
                         :msg "Parameter with no default value: ~a0"
                         :args (list x))
                  decl
                  elabindex))
             ((wmv ok1 warnings new-expr svex elabindex :ctx x)
              (vl-expr-resolve-to-constant
               decl.type.default elabindex :reclimit reclimit
               :type decl.type.type
               :lhs (vl-idexpr name)))

             (val (sv::svex-constval svex))
             ((unless (and ok1 val))
              (mv nil
                  (fatal :type :vl-resolve-constants-fail
                         :msg "Couldn't resolve parameter: ~a0.  Other ~
                                 warnings should explain why."
                         :args (list x))
                  decl
                  elabindex))

             (new-x (change-vl-paramdecl decl
                                         :type (change-vl-explicitvalueparam
                                                decl.type
                                                :default new-expr
                                                :final-value val)))

             (elabindex (vl-elabindex-update-item-info name new-x)))

          (mv ok warnings new-x elabindex))

        :vl-implicitvalueparam
        ;; Examples:
        ;;   parameter foo = 5;              // no type info at all
        ;;   parameter [3:0] foo = 5;        // range info but not a full datatype
        ;;   parameter signed [3:0] foo = 5; // signedness and width but not a full type
        (b* (((unless decl.type.default)
              (mv nil
                  (fatal :type :vl-resolve-constants-fail
                         :msg "Parameter with no default value: ~a0"
                         :args (list x))
                  decl
                  elabindex))

             ;; Try to resolve the range of the parameter declaration if
             ;; applicable.  Note that the range should be resolved relative to
             ;; the scope where the declaration occurs.
             ((mv ok warnings range size elabindex)
              (if decl.type.range
                  (b* (((vl-range range) decl.type.range)
                       ((wmv ok warnings msb ?svex elabindex :ctx x)
                        (vl-expr-resolve-to-constant
                         range.msb elabindex :reclimit reclimit))
                       ((unless ok)
                        (mv nil warnings nil nil elabindex))
                       ((wmv ok warnings lsb ?svex elabindex :ctx x)
                        (vl-expr-resolve-to-constant
                         range.lsb elabindex :reclimit reclimit))
                       ((unless ok)
                        (mv nil warnings nil nil elabindex))
                       (range (make-vl-range :msb msb :lsb lsb))
                       (size (and (vl-range-resolved-p range)
                                  (vl-range-size range))))
                    (mv ok warnings range size elabindex))
                (mv t warnings nil nil elabindex)))
             ((unless ok)
              (mv nil
                  (fatal :type :vl-resolve-constants-fail
                         :msg "Couldn't resolve parameter ~a0 because its ~
                                 range was not resolved"
                         :args (list x))
                  decl
                  elabindex))
             (paramtype (change-vl-implicitvalueparam decl.type :range range))

             ;; Next, try to resolve the actual value for this parameter.
             ((wmv ok warnings val-expr svex elabindex :ctx x)
              (vl-expr-resolve-to-constant
               ;; The following is confusingly named, but it's just the value
               ;; of the parameter.
               decl.type.default
               ;; Resolve it relative to 
               elabindex :reclimit reclimit :ctxsize size))
             (val (sv::svex-constval svex))
             ((unless (and ok val))
              (mv nil
                  (fatal :type :vl-resolve-constants-fail
                         :msg "Couldn't resolve parameter ~a0.  See other warnings."
                         :args (list x))
                  decl
                  elabindex))

             (elabindex (vl-elabindex-sync-scopes))
             (scopes (vl-elabindex->scopes elabindex))

             ;; We've resolved the range and value and can now somehow use that
             ;; to get the final type for this parameter.
             ((wmv warnings err type :ctx x)
              (vl-implicitvalueparam-final-type paramtype val-expr
                                                (vl-elabindex->ss elabindex)
                                                scopes))
             ((when err)
              (mv nil
                  (fatal :type :vl-resolve-constants-fail
                         :msg "Error resolving parameter type for ~a0: ~@1"
                         :args (list x err))
                  decl
                  elabindex))
             (new-x (change-vl-paramdecl decl
                                         :type (make-vl-explicitvalueparam
                                                :type type
                                                :default val-expr
                                                :final-value val)))

             (elabindex (vl-elabindex-update-item-info name new-x)))
          (mv t warnings new-x elabindex)))))

  (fty::defvisitors :template elaborate
    :dep-types (vl-stmt)
    :order-base 200
    :measure (acl2::nat-list-measure
              (list reclimit :order :count 0)))

  (fty::defvisitors :template elaborate
    :types (vl-stmt)
    :order-base 250
    :measure (acl2::nat-list-measure
              (list reclimit :order :count 0)))



  (define vl-stmt-elaborate ((x vl-stmt-p)
                             elabindex
                             &key
                             ((reclimit natp) 'reclimit)
                             ((config vl-simpconfig-p) 'config))
    :measure (acl2::nat-list-measure
              (list reclimit 250 (vl-stmt-count x) 1))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-stmt-p)
                 new-elabindex)
    (b* ((warnings nil)
         ((when (zp reclimit))
          (mv nil
              (fatal :type :vl-resolve-constants-fail
                     :msg "Recursion limit ran out processing ~a0 -- dependency loop?"
                     :args (list (vl-stmt-fix x)))
              (vl-stmt-fix x)
              elabindex))
         (reclimit (1- reclimit)))
      (vl-stmt-case x
        :vl-blockstmt
        (b* ((elabindex (vl-elabindex-push (vl-blockstmt->blockscope x)))
             ((wmv ok1 warnings paramdecls elabindex)
              (vl-paramdecllist-elaborate x.paramdecls elabindex :reclimit reclimit))
             ((wmv ok2 warnings typedefs elabindex)
              (vl-typedeflist-elaborate x.typedefs elabindex :reclimit reclimit))
             ((wmv ok3 warnings vardecls elabindex)
              (vl-vardecllist-elaborate x.vardecls elabindex :reclimit reclimit))
             ((wmv ok4 warnings stmts elabindex)
              (vl-stmtlist-elaborate x.stmts elabindex :reclimit reclimit))
             (elabindex (vl-elabindex-undo)))

          (mv (and ok1 ok2 ok3 ok4)
              warnings
              (change-vl-blockstmt x
                                   :paramdecls paramdecls
                                   :vardecls vardecls
                                   :typedefs typedefs
                                   :stmts stmts)
              elabindex))
        :vl-forstmt
        (b* ((elabindex (vl-elabindex-push (vl-forstmt->blockscope x)))
             ((wmv ok1 warnings initdecls elabindex)
              (vl-vardecllist-elaborate x.initdecls elabindex :reclimit reclimit))
             ((wmv ok2 warnings initassigns elabindex)
              (vl-stmtlist-elaborate x.initassigns elabindex :reclimit reclimit))
             ((wmv ok3 warnings test elabindex)
              (vl-expr-elaborate x.test elabindex :reclimit reclimit))
             ((wmv ok4 warnings stepforms elabindex)
              (vl-stmtlist-elaborate x.stepforms elabindex :reclimit reclimit))
             ((wmv ok5 warnings body elabindex)
              (vl-stmt-elaborate x.body elabindex :reclimit reclimit))
             (elabindex (vl-elabindex-undo)))
          (mv (and ok1 ok2 ok3 ok4 ok5)
              warnings
              (change-vl-forstmt x
                                 :initdecls initdecls
                                 :initassigns initassigns
                                 :test test
                                 :stepforms stepforms
                                 :body body)
              elabindex))
        :vl-foreachstmt
        (mv nil
            (fatal :type :vl-resolve-constants-fail
                   :msg "Not yet implemented: elaboration support for foreach statements"
                   :args (list (vl-stmt-fix x)))
            (vl-stmt-fix x)
            elabindex)
        :otherwise
        (vl-stmt-elaborate-aux x elabindex :reclimit reclimit)))
    ///
    (in-theory (disable vl-stmt-elaborate)))


  (fty::defvisitors :template elaborate
    :dep-types (vl-fundecl)
    :order-base 300
    :measure (acl2::nat-list-measure
              (list reclimit :order :count 0)))

  (fty::defvisitors :template elaborate
    :types (vl-fundecl)
    :order-base 350
    :measure (acl2::nat-list-measure
              (list reclimit :order :count 0)))

  (define vl-fundecl-elaborate ((x vl-fundecl-p)
                                elabindex
                                &key
                                ((reclimit natp) 'reclimit)
                                ((config vl-simpconfig-p) 'config))
    ;; :guard-debug t
    :measure (acl2::nat-list-measure
              (list reclimit 350 0 1))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-fundecl-p)
                 new-elabindex) ;; unchanged
    (b* ((x (vl-fundecl-fix x))
         (warnings nil)
         (name  (vl-fundecl->name x))
         (item (vl-elabscopes-item-info name (vl-elabindex->scopes)))
         ((when item)
          (if (eq (tag item) :vl-fundecl)
              (mv t warnings item elabindex)
            (mv nil
                (fatal :type :vl-programming-error
                       :msg "Found ~a0 stored in place of the elaborated version of ~a1"
                       :args (list item x))
                x
                elabindex)))

         (elabindex (vl-elabindex-push (vl-fundecl->blockscope x)))
         ((mv ok warnings decl elabindex)
          (vl-fundecl-elaborate-aux x elabindex :reclimit reclimit))
         (warnings (vl-warninglist-add-ctx warnings x))

         ((unless ok)
          (b* ((elabindex (vl-elabindex-undo)))
            (mv nil warnings decl elabindex)))

         ;; Pop the old function off and push the new function on to get the return type
         (elabindex (vl-elabindex-sync-scopes))         
         ((wmv warnings svex constraints :ctx x)
          (vl-fundecl-to-svex decl
                              (vl-elabindex->ss elabindex)
                              (vl-elabindex->scopes elabindex)
                              config))
         (new-x (change-vl-fundecl decl :function svex :constraints constraints))
         (elabindex (vl-elabindex-undo))  ;; leave the function body scope
         (elabindex (vl-elabindex-update-item-info name new-x)))
      (mv ok warnings new-x elabindex))
    ///
    (in-theory (disable vl-fundecl-elaborate))))

;; #|


;; (trace$ #!vl (vl-fundecl-elaborate-fn
;;               :cond (equal (Vl-fundecl->name x) "DWF_lzd")
;;               :entry (list 'vl-fundecl-elaborate
;;                            "DWF_lzd"
;;                            (with-local-ps (vl-pp-fundecl x))
;;                            (b* (((vl-svexconf elabindex)))
;;                              (list :typeov (strip-cars conf.typeov)
;;                                    :params (strip-cars conf.params)
;;                                    :fns (strip-cars conf.fns))))
;;               :exit (list 'vl-fundecl-elaborate
;;                           "DWF_lzd"
;;                           (with-local-ps (vl-pp-fundecl (caddr values)))
;;                           (b* (((vl-svexconf elabindex) (cadddr values)))
;;                             (list :typeov (strip-cars conf.typeov)
;;                                   :params (strip-cars conf.params)
;;                                   :fns (strip-cars conf.fns))))))

;; (trace$ #!vl (vl-fundecl-elaborate-aux-fn
;;               :entry (list 'vl-fundecl-elaborate-aux
;;                            (vl-fundecl->name x)
;;                            (with-local-ps (vl-pp-fundecl x))
;;                            (b* (((vl-svexconf elabindex)))
;;                              (list :typeov (strip-cars conf.typeov)
;;                                    :params (strip-cars conf.params)
;;                                    :fns (strip-cars conf.fns))))
;;               :exit (list 'vl-fundecl-elaborate-aux
;;                            (vl-fundecl->name x)
;;                            (car values)
;;                            (with-local-ps (vl-print-warnings (cadr values)))
;;                           (with-local-ps (vl-pp-fundecl (caddr values)))
;;                           (b* (((vl-svexconf elabindex) (cadddr values)))
;;                             (list :typeov (strip-cars conf.typeov)
;;                                   :params (strip-cars conf.params)
;;                                   :fns (strip-cars conf.fns))))))


;; (trace$ #!vl (vl-function-compile-and-bind-fn
;;               :entry (list 'vl-function-compile-and-bind
;;                            fnname)
;;               :exit (list 'vl-function-compile-and-bind
;;                           (car values)
;;                           (with-local-ps (vl-print-warnings (cadr values)))
;;                           (strip-cars (vl-svexconf->fns (caddr values))))))

;; |#







  ;; (define vl-expr-resolve-to-constant-and-bind-param
  ;;   ;; BOZO come back to this
  ;;   ((name stringp)
  ;;    (expr vl-expr-p)
  ;;    elabindex
  ;;    &key
  ;;    ((reclimit natp) 'reclimit) ((config vl-simpconfig-p) 'config))
  ;;   :measure (acl2::nat-list-measure
  ;;             (list reclimit 0 (vl-expr-count expr) 20))

  ;;   :returns (mv (ok)
  ;;                (warnings vl-warninglist-p)
  ;;                (new-nameconf vl-svexconf-p)
  ;;                (new-exprconf vl-svexconf-p))
  ;;   (b* ((name (string-fix name))
  ;;        (warnings nil)
  ;;        (info (vl-elabscopes-item-info name (vl-elabindex->scopes elabindex)))
  ;;        ((when lookup) (mv t warnings elabindex))
  ;;        ((mv ok warnings ?new-x svex elabindex)
  ;;         (vl-expr-resolve-to-constant expr elabindex :Reclimit reclimit))
  ;;        ((unless ok) (mv nil warnings elabindex))
  ;;        (elabindex (vl-elabindex-update-item-info
  ;;                    name (make-vl-elabinfo-param
  ;;        (exprconf (vl-choose-svexconf same-scope nameconf exprconf)))
  ;;     (mv t warnings nameconf exprconf))
  ;;   ///
  ;;   (in-theory (disable vl-expr-resolve-to-constant-and-bind-param)))

  ;; (define vl-datatype-fully-resolve-and-bind ((name stringp)
  ;;                                             (type vl-datatype-p)
  ;;                                             elabindex
  ;;                                             &key
  ;;                                             ((reclimit natp) 'reclimit) ((config vl-simpconfig-p) 'config))
  ;;   :measure (acl2::nat-list-measure
  ;;             (list reclimit 0 (vl-datatype-count type) 20))
  ;;   :returns (mv (ok)
  ;;                (warnings vl-warninglist-p)
  ;;                (new-type vl-datatype-p)
  ;;                elabindex)

  ;;   (b* ((name (string-fix name))
  ;;        (info (vl-elabscopes-item-info name (vl-elabindex->scopes elabindex)))
  ;;        (warnings nil)
  ;;        ((when (and info (eq (tag info) :vl-typedef)))
  ;;         ;; done already
  ;;         (mv t warnings (vl-elabinfo-type->type info) elabindex))
  ;;        ((wmv ok warnings new-type elabindex)
  ;;         (vl-datatype-elaborate type elabindex :reclimit reclimit))
  ;;        ((unless ok)
  ;;         (mv nil warnings new-type elabindex))
  ;;        (elabindex (vl-elabindex-update-item-info name
  ;;                                                  (make-vl-elabinfo-type :type new-type))))
  ;;     (mv t warnings new-type elabindex))
  ;;   ///
  ;;   (in-theory (disable vl-datatype-fully-resolve-and-bind)))

  ;; (define vl-scopeitem-elaborate ((x vl-scopeitem-p)
  ;;                                 (elabindex "must be in the scope where x is declared")
  ;;                                 &key ((reclimit natp) 'reclimit) ((config vl-simpconfig-p) 'config))
  ;;   :measure-debug t
  ;;   :measure
  ;;   ;; we're just going to decrease the reclimit on every call
  ;;   (acl2::nat-list-measure (list reclimit 0 0 0))
  ;;   :returns (mv (ok)
  ;;                (warnings vl-warninglist-p)
  ;;                (new-x vl-scopeitem-p
  ;;                       ;; (and (vl-scopeitem-p new-x)
  ;;                       ;;      (equal (tag new-x) (tag x)))
  ;;                       ;; :hints ('(:expand ((:free (reclimit)
  ;;                       ;;                     (vl-scopeitem-elaborate-aux
  ;;                       ;;                      x elabindex :reclimit reclimit)))
  ;;                       ;;           :in-theory (enable tag-reasoning)))
  ;;                       )
  ;;                new-elabindex)
  ;;   (b* ((name (vl-scopeitem->name x))
  ;;        (x (vl-scopeitem-fix x))
  ;;        (warnings nil)
  ;;        ((unless name)
  ;;         (mv nil
  ;;             (fatal :type :vl-programming-error
  ;;                    :msg "Called vl-scopeitem-elaborate on nameless item: ~a0"
  ;;                    :args (list x))
  ;;             (vl-scopeitem-fix x) elabindex))
  ;;        (info (vl-elabscopes-item-info name (vl-elabindex->scopes)))
  ;;        ((when info)
  ;;         (if (eq (tag info) (tag x))
  ;;             ;; ok memoized result
  ;;             (mv t nil info elabindex)
  ;;           (mv nil
  ;;               (fatal :type :vl-programming-error
  ;;                      :msg "Elaboration index error: ~a0 stored for ~a1"
  ;;                      :args (list info x))
  ;;               (vl-scopeitem-fix x)
  ;;               elabindex)))
  ;;        ((when (zp reclimit))
  ;;         (mv nil
  ;;             (fatal :type :vl-resolve-constants-fail
  ;;                    :msg "Recursion limit ran out processing ~a0 -- dependency loop?"
  ;;                    :args (list x))
  ;;             (vl-scopeitem-fix x)
  ;;             elabindex))
  ;;        ((mv ok warnings item elabindex)
  ;;         (vl-scopeitem-elaborate-aux x elabindex :reclimit (1- reclimit)))
  ;;        ((unless ok)
  ;;         (mv nil warnings (vl-scopeitem-fix x) elabindex))
  ;;        (elabindex (vl-elabindex-update-item-info name item)))
  ;;     (mv t warnings item elabindex))
  ;;   ///
  ;;   (in-theory (disable vl-scopeitem-elaborate)))
         


;; (fty::defvisitors vl-genelement-deps-elaborate
;;   :template elaborate
;;   :dep-types (vl-genelement))

;; (fty::defvisitor vl-genelement-elaborate
;;   :template elaborate
;;   :type vl-genelement
;;   :omit-types (vl-genarrayblock vl-genarrayblocklist))

; Added by Matt K. 2/20/2016, pending possible mod by Sol to defvisitor.
(set-bogus-measure-ok t)

(fty::defvisitors vl-modelements-elaborate
  :template elaborate
  :types (vl-assign vl-modinst vl-always))

(defmacro def-elaborate-ctxitem (type)
  (template-subst
   '(define vl-<<type>>-elaborate ((x vl-<<type>>-p)
                                   (elabindex "in the scope where x is declared")
                                   &key
                                   ((reclimit natp) 'reclimit)
                                   ((config vl-simpconfig-p) 'config))
      :measure (acl2::nat-list-measure (list reclimit 150 0 0))
      :returns (mv (ok)
                   (warnings vl-warninglist-p)
                   (new-x vl-<<type>>-p)
                   new-elabindex)
      (b* (((mv ok warnings new-x elabindex)
            (vl-<<type>>-elaborate-aux x elabindex :reclimit reclimit))
           (warnings (vl-warninglist-add-ctx warnings (vl-<<type>>-fix x))))
        (mv ok warnings new-x elabindex)))
   :str-alist `(("<<TYPE>>" ,(symbol-name type) . vl-foo-p))))

(def-elaborate-ctxitem assign)
(def-elaborate-ctxitem always)
(def-elaborate-ctxitem modinst)


(fty::defvisitors vl-genblob-elaborate
  :template elaborate
  :types (vl-genblob))

(fty::defvisitors vl-design-elaborate-aux-deps
  :template elaborate
  :dep-types (vl-package vl-module vl-interface vl-design))

(fty::defvisitor vl-design-elaborate-aux
  :template elaborate
  :type vl-design)

(fty::defvisitor vl-package-elaborate-aux
  :template elaborate
  :type vl-package)

