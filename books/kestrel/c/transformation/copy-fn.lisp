; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "../syntax/abstract-syntax-operations")
(include-book "deftrans")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ copy-fn
  :parents (transformation-tools)
  :short "A C-to-C transformation to copy a function."
  :long
  (xdoc::topstring
    (xdoc::p
      "This transformation introduces a new function which is the duplicate of
      another.")
    (xdoc::p
      "For instance, consider the following C code:")
    (xdoc::codeblock
      "int fibonacci(int x) {"
      "  if (x <= 1) {"
      "    return x;"
      "  }"
      "  return fibonacci(x - 1) + fibonacci(x - 2);"
      "}")
    (xdoc::p
      "Copying @('fibonacci') and creating a new function @('fib') yields the
       following:")
    (xdoc::codeblock
      "int fibonacci(int x) {"
      "  if (x <= 1) {"
      "    return x;"
      "  }"
      "  return fibonacci(x - 1) + fibonacci(x - 2);"
      "}"
      "int fib(int x) {"
      "  if (x <= 1) {"
      "    return x;"
      "  }"
      "  return fib(x - 1) + fib(x - 2);"
      "}")
    (xdoc::p
      "This transformation is not likely to be useful in isolation. Most often
       it is an initial step before applying different transformations to the
       two duplicates."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines rename-fn-funcall-fun
  (define rename-fn-funcall-fun
    ((expr exprp)
     (old-fn identp)
     (new-fn identp))
    :short "Rename a function within a @('funcall') function expression."
    :returns (new-expr exprp)
    (expr-case
     expr
     :ident (if (equal expr.ident old-fn)
                (make-expr-ident :ident new-fn :info nil)
              (expr-fix expr))
     :paren (expr-paren (rename-fn-funcall-fun expr.inner old-fn new-fn))
     :gensel
     (make-expr-gensel
       :control expr.control
       :assocs (rename-fn-funcall-fun-genassoc-list expr.assocs old-fn new-fn))
     :cast (make-expr-cast :type expr.type
                           :arg (rename-fn-funcall-fun expr.arg old-fn new-fn))
     :otherwise (expr-fix expr))
    :measure (expr-count expr))

  (define rename-fn-funcall-fun-genassoc
    ((genassoc genassocp)
     (old-fn identp)
     (new-fn identp))
    :returns (new-genassoc genassocp)
    (genassoc-case
     genassoc
     :type (make-genassoc-type :type genassoc.type
                               :expr (rename-fn-funcall-fun genassoc.expr old-fn new-fn))
     :default (genassoc-default (rename-fn-funcall-fun genassoc.expr old-fn new-fn)))
    :measure (genassoc-count genassoc))

  (define rename-fn-funcall-fun-genassoc-list
    ((genassocs genassoc-listp)
     (old-fn identp)
     (new-fn identp))
    :returns (new-genassocs genassoc-listp)
    (if (endp genassocs)
        nil
      (cons (rename-fn-funcall-fun-genassoc (first genassocs) old-fn new-fn)
            (rename-fn-funcall-fun-genassoc-list (rest genassocs) old-fn new-fn)))
    :measure (genassoc-list-count genassocs))

  :hints (("Goal" :in-theory '(deftrans-measure-theory)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftrans rename-fn
  :extra-args ((old-fn identp) (new-fn identp))
  :expr
  (lambda (expr old-fn new-fn)
    (expr-case
      expr
      :paren (expr-paren (rename-fn-expr expr.inner old-fn new-fn))
      :gensel
      (make-expr-gensel :control (rename-fn-expr expr.control old-fn new-fn)
                        :assocs (rename-fn-genassoc-list expr.assocs old-fn new-fn))
      :arrsub (make-expr-arrsub :arg1 (rename-fn-expr expr.arg1 old-fn new-fn)
                                :arg2 (rename-fn-expr expr.arg2 old-fn new-fn))
      ;; This is the interesting case
      :funcall (make-expr-funcall :fun (rename-fn-funcall-fun expr.fun old-fn new-fn)
                                  :args (rename-fn-expr-list expr.args old-fn new-fn))
      :member (make-expr-member :arg (rename-fn-expr expr.arg old-fn new-fn)
                                :name expr.name)
      :memberp (make-expr-memberp :arg (rename-fn-expr expr.arg old-fn new-fn)
                                  :name expr.name)
      :complit
      (make-expr-complit :type expr.type
                         :elems (rename-fn-desiniter-list expr.elems old-fn new-fn)
                         :final-comma expr.final-comma)
      :unary (make-expr-unary :op expr.op
                              :arg (rename-fn-expr expr.arg old-fn new-fn))
      :sizeof (expr-sizeof (rename-fn-tyname expr.type old-fn new-fn))
      :alignof (make-expr-alignof :type (rename-fn-tyname expr.type old-fn new-fn)
                                  :uscores expr.uscores)
      :cast (make-expr-cast :type (rename-fn-tyname expr.type old-fn new-fn)
                            :arg (rename-fn-expr expr.arg old-fn new-fn))
      :binary (make-expr-binary :op expr.op
                                :arg1 (rename-fn-expr expr.arg1 old-fn new-fn)
                                :arg2 (rename-fn-expr expr.arg2 old-fn new-fn))
      :cond (make-expr-cond :test (rename-fn-expr expr.test old-fn new-fn)
                            :then (rename-fn-expr-option expr.then old-fn new-fn)
                            :else (rename-fn-expr expr.else old-fn new-fn))
      :comma (make-expr-comma :first (rename-fn-expr expr.first old-fn new-fn)
                              :next (rename-fn-expr expr.next old-fn new-fn))
      :stmt (expr-stmt (rename-fn-block-item-list expr.items old-fn new-fn))
      :tycompat (make-expr-tycompat :type1 (rename-fn-tyname expr.type1 old-fn new-fn)
                                    :type2 (rename-fn-tyname expr.type2 old-fn new-fn))
      :offsetof
      (make-expr-offsetof :type (rename-fn-tyname expr.type old-fn new-fn)
                          :member (rename-fn-member-designor expr.member old-fn
                                                             new-fn))
      :sizeof-ambig (prog2$ (raise "Misusage error: ~x0." (expr-fix expr))
                            (expr-fix expr))
      :cast/call-ambig (prog2$ (raise "Misusage error: ~x0." (expr-fix expr))
                               (expr-fix expr))
      :cast/mul-ambig (prog2$ (raise "Misusage error: ~x0." (expr-fix expr))
                              (expr-fix expr))
      :cast/add-ambig (prog2$ (raise "Misusage error: ~x0." (expr-fix expr))
                              (expr-fix expr))
      :cast/sub-ambig (prog2$ (raise "Misusage error: ~x0." (expr-fix expr))
                              (expr-fix expr))
      :cast/and-ambig (prog2$ (raise "Misusage error: ~x0." (expr-fix expr))
                              (expr-fix expr))
      :otherwise (expr-fix expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-fundef
  ((fundef fundefp)
   (target-fn identp)
   (new-fn identp))
  :short "Transform a function definition."
  :returns (fundef? fundef-optionp)
  (b* (((fundef fundef) fundef)
       ((declor fundef.declor) fundef.declor))
    (dirdeclor-case
      fundef.declor.direct
      :function-params
      (if (equal target-fn
                 (c$::dirdeclor->ident fundef.declor.direct.declor))
          ;; Return
          (make-fundef
            :extension fundef.extension
            :spec fundef.spec
            :declor (make-declor
                      :pointers fundef.declor.pointers
                      :direct (make-dirdeclor-function-params
                               :declor (dirdeclor-ident new-fn)
                               :params fundef.declor.direct.params
                               :ellipsis fundef.declor.direct.ellipsis))
            :decls fundef.decls
            :body (rename-fn-stmt fundef.body target-fn new-fn))
        nil)
      :otherwise nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-extdecl
  ((extdecl extdeclp)
   (target-fn identp)
   (new-fn identp))
  :short "Transform an external declaration."
  :returns (mv (found booleanp)
               (extdecls extdecl-listp))
  (extdecl-case
   extdecl
   :fundef (b* ((fundef?
                 (copy-fn-fundef
                   extdecl.unwrap
                   target-fn
                   new-fn)))
             (if fundef?
                 (mv t (list (extdecl-fix extdecl) (extdecl-fundef fundef?)))
               (mv nil (list (extdecl-fix extdecl)))))
   :decl (mv nil (list (extdecl-fix extdecl)))
   :empty (mv nil (list (extdecl-fix extdecl)))
   :asm (mv nil (list (extdecl-fix extdecl)))))

(define copy-fn-extdecl-list
  ((extdecls extdecl-listp)
   (target-fn identp)
   (new-fn identp))
  :short "Transform a list of external declarations."
  :returns (new-extdecls extdecl-listp)
  (b* (((when (endp extdecls))
        nil)
       ((mv found new-extdecls)
        (copy-fn-extdecl (first extdecls) target-fn new-fn)))
    (append new-extdecls
            (if found
                (extdecl-list-fix (rest extdecls))
              (copy-fn-extdecl-list (rest extdecls) target-fn new-fn)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-transunit
  ((tunit transunitp)
   (target-fn identp)
   (new-fn identp))
  :short "Transform a translation unit."
  :returns (new-tunit transunitp)
  (b* (((transunit tunit) tunit))
    (make-transunit :decls (copy-fn-extdecl-list tunit.decls target-fn new-fn)
                    :info tunit.info)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-filepath-transunit-map
  ((map filepath-transunit-mapp)
   (target-fn identp)
   (new-fn identp))
  :short "Transform a filepath."
  :returns (new-map filepath-transunit-mapp
                    :hyp (filepath-transunit-mapp map))
  (b* (((when (omap::emptyp map))
        nil)
       ((mv path tunit) (omap::head map)))
    (omap::update (c$::filepath-fix path)
                  (copy-fn-transunit tunit target-fn new-fn)
                  (copy-fn-filepath-transunit-map (omap::tail map)
                                                  target-fn
                                                  new-fn)))
  :verify-guards :after-returns)

(define copy-fn-transunit-ensemble
  ((tunits transunit-ensemblep)
   (target-fn identp)
   (new-fn identp))
  :short "Transform a translation unit ensemble."
  :returns (new-tunits transunit-ensemblep)
  (b* (((transunit-ensemble tunits) tunits))
    (transunit-ensemble
      (copy-fn-filepath-transunit-map tunits.unwrap
                                      target-fn
                                      new-fn))))
