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

(include-book "kestrel/fty/deffold-map" :dir :system)

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/code-ensembles")

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

;; This takes longer than one would hope. One issue is printing, which may be
;; solved easily by deffold-map wrapping its events in a with-output.
;; Another issue is that many "useless" maps are generated for types in the
;; clique we do not care about (i.e. those whose maps are not actually mutually
;; recursive with those we explicitly care about). Perhaps the :types argument
;; could take members of a type clique instead of generating maps for an entire
;; clique. E.g., the list here could be (c$::expr c$::genassoc
;; c$::genassoc-list).
(fty::deffold-map funcall-fun-rename-fn
  :types (c$::exprs/decls/stmts)
  :extra-args ((old-fn identp) (new-fn identp))
  :short "Rename a function within a @('funcall') function expression."
  :override
  ((c$::expr
     (b* ((old-fn (ident-fix old-fn))
          (new-fn (ident-fix new-fn)))
       (expr-case
         c$::expr
         :ident (if (equal expr.ident old-fn)
                    (make-expr-ident :ident new-fn :info nil)
                  (expr-fix c$::expr))
         :paren (expr-paren
                  (expr-funcall-fun-rename-fn expr.inner old-fn new-fn))
         :gensel
         (make-expr-gensel
           :control expr.control
           :assocs (genassoc-list-funcall-fun-rename-fn
                     expr.assocs old-fn new-fn))
         :cast (make-expr-cast :type expr.type
                               :arg (expr-funcall-fun-rename-fn
                                      expr.arg old-fn new-fn))
         :otherwise (expr-fix c$::expr))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename-fn
  :types (c$::exprs/decls/stmts)
  :extra-args ((old-fn identp) (new-fn identp))
  :override
  ((c$::expr
     :funcall
     (make-expr-funcall
       :fun (expr-funcall-fun-rename-fn expr.fun old-fn new-fn)
       :args (expr-list-rename-fn expr.args old-fn new-fn)))))

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
            :body (block-item-list-rename-fn fundef.body target-fn new-fn)
            :info fundef.info)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-code-ensemble
  ((code code-ensemblep)
   (target-fn identp)
   (new-fn identp))
  :returns (new-code code-ensemblep)
  :short "Transform a code ensemble."
  (b* (((code-ensemble code) code))
    (change-code-ensemble
     code
     :transunits
     (copy-fn-transunit-ensemble code.transunits target-fn new-fn))))
