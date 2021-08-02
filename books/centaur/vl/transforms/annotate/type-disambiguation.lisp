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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "VL")

(include-book "../../mlib/hid-tools")
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "../../util/default-hints"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))


;; Certain constructs in SystemVerilog may either be a type or expression.  We
;; can't easily tell the difference at parse time, but once we have a full
;; module hierarchy we can use scopestacks to determine which is which.  In the
;; parser, we always parse an expression if possible and then a datatype if
;; that doesn't work, so we only need to convert expressions to datatypes, not
;; vice versa.

(define vl-expr-to-datatype ((x vl-expr-p)
                             (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p
                         "Warning if we couldn't make sense of something.")
               (type (iff (vl-datatype-p type) type)
                     "The resulting datatype, if it is one."))
  (b* ((warnings nil)
       (x (vl-expr-fix x)))
    (vl-expr-case x
      :vl-index (b* (((mv err trace ?context tail)
                      (vl-follow-scopeexpr x.scope ss))
                     ((when err)
                      (mv (warn :type :vl-expr-to-datatype-fail
                                :msg "Couldn't look up variable ~a0: ~@1"
                                :args (list x err))
                          nil))
                     ((vl-hidstep decl) (car trace))
                     ((unless (or (eq (tag decl.item) :vl-typedef)
                                  (eq (tag decl.item) :vl-paramdecl)))
                      ;; not a type
                      (mv nil nil))
                     ((when (and (eq (tag decl.item) :vl-paramdecl)
                                 (b* (((vl-paramdecl param) decl.item))
                                   (not (vl-paramtype-case param.type :vl-typeparam)))))
                      (mv nil nil))
                     ;; We have either a typedef or paramdecl.  It's weird if we
                     ;; have indices.  It might be a little less weird to have a
                     ;; partselect bc it could look like a packed dimension, but
                     ;; I don't think it's allowed and it'd still be weird if
                     ;; e.g. the type was unpacked.
                     ((when (consp x.indices))
                      (mv (warn :type :vl-expr-to-datatype-fail
                                :msg "Type name with indices: ~a0"
                                :args (list x))
                          nil))
                     ((unless (vl-partselect-case x.part :none))
                      (mv (warn :type :vl-expr-to-datatype-fail
                                :msg "Type name with partselect: ~a0"
                                :args (list x))
                          nil))
                     ;; It's also weird if there's a tail, i.e. some sort of
                     ;; selects into the type.
                     ((unless (vl-hidexpr-case tail :end))
                      (mv (warn :type :vl-expr-to-datatype-fail
                                :msg "Type name with field selects: ~a0"
                                :args (list x))
                          nil)))
                  (mv nil (make-vl-usertype :name x.scope)))
      :otherwise (mv nil nil))))

(fty::defvisitor-template type-disambiguate ((x :object)
                                             (ss vl-scopestack-p))
  :returns (mv (warnings (:join (append-without-guard warnings1 warnings)
                          :tmp-var warnings1
                          :initial nil)
                         vl-warninglist-p)
               (new-x :update))
  :fnname-template <type>-type-disambiguate
  :type-fns ((vl-fundecl vl-fundecl-type-disambiguate)
             (vl-taskdecl vl-taskdecl-type-disambiguate)
             (vl-paramvalue vl-paramvalue-type-disambiguate)))

(local (in-theory (disable cons-equal
                           acl2::true-listp-append
                           (:t append)
                           append)))

; Added by Matt K. 2/20/2016, pending possible mod by Sol to defvisitor.
(set-bogus-measure-ok t)

(fty::defvisitor vl-expr-type-disambiguate
  :template type-disambiguate
  :type expressions-and-datatypes
  :renames ((vl-expr vl-expr-type-disambiguate-aux)
            (vl-patternkey vl-patternkey-type-disambiguate-aux)
            (vl-slicesize vl-slicesize-type-disambiguate-aux)
            (vl-casttype vl-casttype-type-disambiguate-aux)
            (vl-paramvalue vl-paramvalue-type-disambiguate-aux))
  :type-fns ((vl-expr vl-expr-type-disambiguate)
             (vl-patternkey vl-patternkey-type-disambiguate)
             (vl-slicesize vl-slicesize-type-disambiguate)
             (vl-casttype vl-casttype-type-disambiguate)
             (vl-paramvalue vl-paramvalue-type-disambiguate))
  :field-fns ((atts :skip))
  :measure (two-nats-measure :count 0)

  (define vl-expr-type-disambiguate ((x vl-expr-p)
                                     (ss vl-scopestack-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-expr-p))
    :measure (two-nats-measure (vl-expr-count x) 1)
    (b* (((mv warnings x1) (vl-expr-type-disambiguate-aux x ss)))
      (vl-expr-case x1
        :vl-call (if (and x1.systemp (not x1.typearg) (consp x1.plainargs) (car x1.plainargs))
                     ;; System calls' first argument may be a type
                     (b* (((wmv warnings typearg)
                           (vl-expr-to-datatype (car x1.plainargs) ss)))
                       (mv warnings
                           (if typearg
                               (change-vl-call x1 :typearg typearg :plainargs (cdr x1.plainargs))
                             x1)))
                   (mv warnings x1))
        :otherwise (mv warnings x1))))

  (define vl-patternkey-type-disambiguate ((x vl-patternkey-p)
                                           (ss vl-scopestack-p))

    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-patternkey-p))
    :measure (two-nats-measure (vl-patternkey-count x) 1)
    (b* (((mv warnings x1) (vl-patternkey-type-disambiguate-aux x ss)))
      (vl-patternkey-case x1
        :expr (b* (((wmv warnings type)
                    (vl-expr-to-datatype x1.key ss)))
                (mv warnings
                    (if type
                        (make-vl-patternkey-type :type type)
                      x1)))
        :otherwise (mv warnings x1))))

  (define vl-slicesize-type-disambiguate ((x vl-slicesize-p)
                                           (ss vl-scopestack-p))

    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-slicesize-p))
    :measure (two-nats-measure (vl-slicesize-count x) 1)
    (b* (((mv warnings x1) (vl-slicesize-type-disambiguate-aux x ss)))
      (vl-slicesize-case x1
        :expr (b* (((wmv warnings type)
                    (vl-expr-to-datatype x1.expr ss)))
                (mv warnings
                    (if type
                        (make-vl-slicesize-type :type type)
                      x1)))
        :otherwise (mv warnings x1))))

  (define vl-casttype-type-disambiguate ((x vl-casttype-p)
                                           (ss vl-scopestack-p))

    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-casttype-p))
    :measure (two-nats-measure (vl-casttype-count x) 1)
    (b* (((mv warnings x1) (vl-casttype-type-disambiguate-aux x ss)))
      (vl-casttype-case x1
        :size (b* (((wmv warnings type)
                    (vl-expr-to-datatype x1.size ss)))
                (mv warnings
                    (if type
                        (make-vl-casttype-type :type type)
                      x1)))
        :otherwise (mv warnings x1))))

  (define vl-paramvalue-type-disambiguate ((x vl-paramvalue-p)
                                           (ss vl-scopestack-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-paramvalue-p))
    :measure (two-nats-measure (vl-paramvalue-count x) 1)
    (vl-paramvalue-case x
      :type (b* (((mv warnings type)
                  (vl-datatype-type-disambiguate x.type ss)))
              (mv warnings (change-vl-paramvalue-type x :type type)))
      :expr (b* (((mv warnings expr)
                  (vl-expr-type-disambiguate x.expr ss))
                 ((wmv warnings type)
                  (vl-expr-to-datatype expr ss)))
              (mv warnings
                  (if type
                      (make-vl-paramvalue-type :type type)
                    (change-vl-paramvalue-expr x :expr expr)))))))

(fty::defvisitors vl-stmt-type-disambiguate-deps
  :template type-disambiguate
  :dep-types (vl-stmt))

(fty::defvisitor vl-stmt-type-disambiguate
  :template type-disambiguate
  :type statements
  :renames ((vl-stmt vl-stmt-type-disambiguate-aux))
  :type-fns ((vl-stmt vl-stmt-type-disambiguate))
  :measure (two-nats-measure :count 0)

  (define vl-stmt-type-disambiguate ((x vl-stmt-p)
                                     (ss vl-scopestack-p))

    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-stmt-p))
    :measure (two-nats-measure (vl-stmt-count x) 1)
    (b* ((ss (vl-stmt-case x
               :vl-blockstmt (vl-scopestack-push (vl-blockstmt->blockscope x) ss)
               :vl-forstmt
               ;; BOZO this is probably not right.  We probably need to fix up types
               ;; in the initial declarations before pushing the scope.  Think about it.
               (vl-scopestack-push (vl-forstmt->blockscope x) ss)
               :vl-foreachstmt
               (vl-scopestack-push (vl-foreachstmt->blockscope x) ss)
               :otherwise ss)))
      (vl-stmt-case x
        :vl-callstmt
        ;; The first argument might be a datatype.
        (b* ((arg-to-disambiguate (and (not x.typearg)
                                       (consp x.args)
                                       (car x.args)))
             ((unless arg-to-disambiguate)
              (vl-stmt-type-disambiguate-aux x ss))
             (warnings nil)
             ((wmv warnings type)
              (vl-expr-to-datatype arg-to-disambiguate ss))
             ((unless type)
              ;; It wasn't a type, so there's nothing special to do.
              (vl-stmt-type-disambiguate-aux x ss))
             ;; Move arg1 over to become the typearg.
             ((wmv warnings id) (vl-scopeexpr-type-disambiguate x.id ss))
             ((wmv warnings other-args) (vl-maybe-exprlist-type-disambiguate (cdr x.args) ss))
             (new-x (change-vl-callstmt x
                                        :id id
                                        :typearg type
                                        :args other-args)))
          (mv warnings new-x))
        :otherwise
        (vl-stmt-type-disambiguate-aux x ss)))))


;; (fty::defvisitors vl-paramvalue-type-disambiguate-deps
;;   :template type-disambiguate
;;   :dep-types (vl-paramvalue))




(fty::defvisitors vl-fundecl-type-disambiguate-deps
  :template type-disambiguate
  :dep-types (vl-fundecl vl-taskdecl))

(define vl-fundecl-type-disambiguate ((x  vl-fundecl-p)
                                      (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x vl-fundecl-p))
  ;; See the comments in scopestack.lisp.  We follow the One True Way to
  ;; process a Function: we must process the return type in the outer scope,
  ;; then push the scope, then process everything else, even the ports.
  (b* (((vl-fundecl x) (vl-fundecl-fix x))
       (warnings nil)
       ((wmv warnings rettype)    (vl-datatype-type-disambiguate x.rettype ss))
       (ss                        (vl-scopestack-push (vl-fundecl->blockscope x) ss))
       ((wmv warnings portdecls)  (vl-portdecllist-type-disambiguate x.portdecls ss))
       ((wmv warnings vardecls)   (vl-vardecllist-type-disambiguate x.vardecls ss))
       ((wmv warnings paramdecls) (vl-paramdecllist-type-disambiguate x.paramdecls ss))
       ((wmv warnings typedefs)   (vl-typedeflist-type-disambiguate x.typedefs ss))
       ((wmv warnings body)       (vl-stmt-type-disambiguate x.body ss))
       (new-x (change-vl-fundecl x
                                 :rettype rettype
                                 :portdecls portdecls
                                 :vardecls vardecls
                                 :paramdecls paramdecls
                                 :typedefs typedefs
                                 :body body)))
    (mv warnings new-x)))

(define vl-taskdecl-type-disambiguate ((x  vl-taskdecl-p)
                                       (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x vl-taskdecl-p))
  ;; See the comments in scopestack.lisp.  We follow the One True Way to
  ;; process a Task: we push the whole thing and then process all of it.
  (b* (((vl-taskdecl x) (vl-taskdecl-fix x))
       (warnings nil)
       (ss                        (vl-scopestack-push (vl-taskdecl->blockscope x) ss))
       ((wmv warnings portdecls)  (vl-portdecllist-type-disambiguate x.portdecls ss))
       ((wmv warnings vardecls)   (vl-vardecllist-type-disambiguate x.vardecls ss))
       ((wmv warnings paramdecls) (vl-paramdecllist-type-disambiguate x.paramdecls ss))
       ((wmv warnings typedefs)   (vl-typedeflist-type-disambiguate x.typedefs ss))
       ((wmv warnings body)       (vl-stmt-type-disambiguate x.body ss))
       (new-x (change-vl-taskdecl x
                                  :portdecls portdecls
                                  :vardecls vardecls
                                  :paramdecls paramdecls
                                  :typedefs typedefs
                                  :body body)))
    (mv warnings new-x)))

(fty::defvisitors vl-genelement-type-disambiguate-deps
  :template type-disambiguate
  :dep-types (vl-genelement))

(fty::defvisitor vl-genelement-type-disambiguate
  :template type-disambiguate
  :type vl-genelement
  :renames ((vl-genblock vl-genblock-type-disambiguate-aux)
            (vl-genelement vl-genelement-type-disambiguate-aux))
  :type-fns ((vl-genblock vl-genblock-type-disambiguate)
             (vl-genelement vl-genelement-type-disambiguate))
  :measure (two-nats-measure :count 0)

  (define vl-genblock-type-disambiguate ((x vl-genblock-p)
                                         (ss vl-scopestack-p))
    
    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-genblock-p))
    :measure (two-nats-measure (vl-genblock-count x) 1)
    ;; BOZO This isn't following the scoping discipline for genarrays but we
    ;; don't expect them to exist yet when we run this transform.  To correct
    ;; this we'd just add a special case for genarrays (customize
    ;; vl-genelement-type-disambiguate) that pushes the scope like in
    ;; vl-follow-hidexpr-aux.
    (b* ((ss (vl-scopestack-push (vl-sort-genelements (vl-genblock->elems x)
                                                      :scopetype :vl-genblock
                                                      :id (vl-genblock->name x))
                                 ss)))
      (vl-genblock-type-disambiguate-aux x ss)))

  (define vl-genelement-type-disambiguate ((x vl-genelement-p)
                                         (ss vl-scopestack-p))
    
    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-genelement-p))
    :measure (two-nats-measure (vl-genelement-count x) 1)
    (vl-genelement-case x
      :vl-genloop
      (b* (((unless x.genvarp)
            (vl-genelement-type-disambiguate-aux x ss))
           (loop-scope (vl-sort-genelements
                        (list (vl-genbase
                               (make-vl-genvar :name x.var :loc x.loc)))
                        :scopetype :vl-genarray
                        :id (vl-genblock->name x.body)))
           (ss (vl-scopestack-push loop-scope ss)))
        (vl-genelement-type-disambiguate-aux x ss))
      :otherwise (vl-genelement-type-disambiguate-aux x ss))))

(fty::defvisitors vl-module-type-disambiguate-deps
  :template type-disambiguate
  :dep-types (vl-module))

(set-bogus-mutual-recursion-ok t)
(fty::defvisitor vl-module-type-disambiguate
  :template type-disambiguate
  :type vl-module
  :renames ((vl-module vl-module-type-disambiguate-aux))
  :type-fns ((vl-module vl-module-type-disambiguate))
  :measure 0

  (define vl-module-type-disambiguate ((x vl-module-p)
                                       (ss vl-scopestack-p))

    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-module-p))
    :measure 1
    ;; Note: this obeys the One True Way to Process a Module described in
    ;; vl-scopestack-push.
    (b* ((ss (vl-scopestack-push (vl-module-fix x) ss))
         ((mv warnings new-x)
          (vl-module-type-disambiguate-aux x ss))
         ((vl-module new-x))
         (warnings (append-without-guard warnings new-x.warnings)))
      (mv nil (change-vl-module new-x :warnings warnings)))))

(fty::defvisitors vl-interface-type-disambiguate-deps
  :template type-disambiguate
  :dep-types (vl-interface))

(fty::defvisitor vl-interface-type-disambiguate
  :template type-disambiguate
  :type vl-interface
  :renames ((vl-interface vl-interface-type-disambiguate-aux))
  :type-fns ((vl-interface vl-interface-type-disambiguate))
  :measure 0

  (define vl-interface-type-disambiguate ((x vl-interface-p)
                                          (ss vl-scopestack-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-interface-p))
    :measure 1
    ;; Note: this obeys the One True Way to Process a Module described in
    ;; vl-scopestack-push.
    (b* ((ss (vl-scopestack-push (vl-interface-fix x) ss))
         ((mv warnings new-x)
          (vl-interface-type-disambiguate-aux x ss))
         ((vl-interface new-x))
         (warnings (append-without-guard warnings new-x.warnings)))
      (mv nil (change-vl-interface new-x :warnings warnings)))))

(fty::defvisitors vl-package-type-disambiguate-deps
  :template type-disambiguate
  :dep-types (vl-package))

(fty::defvisitor vl-package-type-disambiguate
  :template type-disambiguate
  :type vl-package
  :renames ((vl-package vl-package-type-disambiguate-aux))
  :type-fns ((vl-package vl-package-type-disambiguate))
  :measure 0

  (define vl-package-type-disambiguate ((x vl-package-p)
                                       (ss vl-scopestack-p))

    :returns (mv (warnings vl-warninglist-p)
                 (new-x vl-package-p))
    :measure 1
    (b* ((ss (vl-scopestack-push (vl-package-fix x) ss))
         ((mv warnings new-x)
          (vl-package-type-disambiguate-aux x ss))
         ((vl-package new-x))
         (warnings (append-without-guard warnings new-x.warnings)))
      (mv nil (change-vl-package new-x :warnings warnings)))))


(fty::defvisitors vl-design-type-disambiguate-deps
  :template type-disambiguate
  :dep-types (vl-design))

(fty::defvisitor vl-design-type-disambiguate-aux
  :template type-disambiguate
  :type vl-design
  :renames ((vl-design vl-design-type-disambiguate-aux)))



(define vl-design-type-disambiguate ((x vl-design-p))

  :returns (new-x vl-design-p)
  :measure 1
  (b* ((ss (vl-scopestack-init x))
       ((mv warnings new-x)
        (vl-design-type-disambiguate-aux x ss))
       ((vl-design new-x)))
    (change-vl-design new-x :warnings (append-without-guard warnings new-x.warnings))))

