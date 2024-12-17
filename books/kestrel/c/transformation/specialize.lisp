; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
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
(include-book "utilities/free-vars")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ specialize
  :parents (transformation-tools)
  :short "A C-to-C transformation to specialize a function."
  :long
  (xdoc::topstring
    (xdoc::p
      "This transformation specializes a function by moving one of its
       parameters to a declaration at the top of the function body, initialized to
       some constant.")
    (xdoc::p
      "For a concrete example, consider the following C code:")
    (xdoc::codeblock
      "int foo(int y, int z) {"
      "  int x = 5;"
      "  return x + y - z;"
      "}")
    (xdoc::p
      "Specializing parameter @('y') with the constant @('1') yields the
       following:")
    (xdoc::codeblock
      "int foo(int z) {"
      "  int y = 1;"
      "  int x = 5;"
      "  return x + y - z;"
      "}")
    (xdoc::p
      "Clearly a call of @('foo(z)'), where @('z') is arbitrary and @('foo') is
       the specialized function, is equal to @('foo(1, z)') for the old
       function @('foo').")
    (xdoc::p
      "Note that this modifies the target function; it does not make a copy of
       the function. If you want to specialize a copy of a function, first
       employ the @(see copy-fn) transformation.")
    (xdoc::p
      "It is often desirable to propagate constants and eliminate dead code
       after specializing. The @(see specialize) transformation does not
       implement such behavior. Eventually, we will want to implement separate
       constant propagation and dead code elimination transformations."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident-from-paramdecl
  ((paramdecl paramdeclp))
  :short "Get the identifier from a parameter declaration."
  :long
  (xdoc::topstring
   (xdoc::p
     "This may return @('nil') when the parameter declaration is unnamed."))
  :returns (ident ident-optionp)
  (b* (((paramdecl paramdecl) paramdecl))
    (paramdeclor-case
      paramdecl.decl
      :declor (declor-get-ident paramdecl.decl.unwrap)
      :otherwise nil)))

(define paramdecl-to-decl
  ((paramdecl paramdeclp)
   (init? initer-optionp))
  :short "Convert a parameter declaration to a regular declaration."
  :returns (mv (success booleanp)
               (decl declp))
  (b* (((paramdecl paramdecl) paramdecl))
    (paramdeclor-case
      paramdecl.decl
      :declor (mv t
                  (make-decl-decl
                    :extension nil
                    :specs paramdecl.spec
                    :init (cons (initdeclor paramdecl.decl.unwrap nil nil init?) nil)))
      ;; TODO: add irr-decl to exported symbols
      :otherwise (mv nil (c$::irr-decl)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define paramdecl-list-remove-param-by-ident
  ((params paramdecl-listp)
   (param-to-remove identp))
  :returns (mv (success booleanp)
               (new-params paramdecl-listp)
               (removed-param paramdeclp))
  :short "Remove a parameter from a list of parameter declarations."
  (b* ((params (paramdecl-list-fix params))
       ((when (endp params))
        ;; TODO: add irr-paramdecl to exported symbols
        (mv nil params (c$::irr-paramdecl)))
       (param (first params))
       (param-name (ident-from-paramdecl param))
       ((when (equal param-name param-to-remove))
        (mv t (rest params) param))
       ((mv success new-params removed-param)
        (paramdecl-list-remove-param-by-ident (rest params) param-to-remove)))
    (mv success
        (cons param new-params)
        removed-param))
  :measure (paramdecl-list-count params)
  :hints (("Goal" :in-theory (enable o< o-finp endp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define specialize-fundef
  ((fundef fundefp)
   (target-fn identp)
   (target-param identp)
   (const exprp))
  :short "Transform a function definition."
  :returns (mv (found booleanp)
               (new-fundef fundefp))
  (b* (((fundef fundef) fundef)
       ((declor fundef.declor) fundef.declor))
    (stmt-case
      fundef.body
      :compound
      (dirdeclor-case
        fundef.declor.direct
        :function-params
        (b* (((unless (equal target-fn
                             (dirdeclor-get-ident fundef.declor.direct.decl)))
              (mv nil (fundef-fix fundef)))
             ((mv success new-params removed-param)
              (paramdecl-list-remove-param-by-ident fundef.declor.direct.params target-param))
             ((unless success)
              (prog2$ (raise "Function ~x0 did not have a parameter ~x1"
                             target-fn
                             target-param)
                      (mv nil (fundef-fix fundef))))
             (dirdeclor-params
               (make-dirdeclor-function-params
                 :decl fundef.declor.direct.decl
                 :params new-params
                 :ellipsis fundef.declor.direct.ellipsis))
             ((mv - decl)
              (paramdecl-to-decl removed-param (initer-single const))))
          (mv t
              (make-fundef
                :extension fundef.extension
                :spec fundef.spec
                :declor (make-declor
                          :pointers fundef.declor.pointers
                          :direct dirdeclor-params)
                :decls fundef.decls
                :body (stmt-compound (cons (block-item-decl decl)
                                           fundef.body.items)))))
        :otherwise
        ;; TODO: check when non-function-params dirdeclor still has name target-fn
        (mv nil (fundef-fix fundef)))
      :otherwise
      (prog2$ (raise "Function definition body is not a compound statement.")
              (mv nil (fundef-fix fundef))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define specialize-extdecl
  ((extdecl extdeclp)
   (target-fn identp)
   (target-param identp)
   (const exprp))
  :short "Transform an external declaration."
  :returns (mv (found booleanp)
               (new-extdecl extdeclp))
  (extdecl-case
   extdecl
   :fundef (b* (((mv found fundef)
                 (specialize-fundef
                   extdecl.unwrap
                   target-fn
                   target-param
                   const)))
             (mv found (extdecl-fundef fundef)))
   :decl (mv nil (extdecl-fix extdecl))
   :empty (mv nil (extdecl-fix extdecl))
   :asm (mv nil (extdecl-fix extdecl))))

(define specialize-extdecl-list
  ((extdecls extdecl-listp)
   (target-fn identp)
   (target-param identp)
   (const exprp))
  :short "Transform a list of external declarations."
  :returns (new-extdecls extdecl-listp)
  (b* (((when (endp extdecls))
        nil)
       ((mv found extdecl)
        (specialize-extdecl (first extdecls) target-fn target-param const)))
    (cons extdecl
          (if found
              (extdecl-list-fix (rest extdecls))
            (specialize-extdecl-list (rest extdecls) target-fn target-param const)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define specialize-transunit
  ((tunit transunitp)
   (target-fn identp)
   (target-param identp)
   (const exprp))
  :short "Transform a translation unit."
  :returns (new-tunit transunitp)
  (b* (((transunit tunit) tunit))
    (transunit (specialize-extdecl-list tunit.decls target-fn target-param const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define specialize-filepath-transunit-map
  ((map filepath-transunit-mapp)
   (target-fn identp)
   (target-param identp)
   (const exprp))
  :short "Transform a filepath."
  :returns (new-map filepath-transunit-mapp
                    :hyp (filepath-transunit-mapp map))
  (b* (((when (omap::emptyp map))
        nil)
       ((mv path tunit) (omap::head map)))
    (omap::update (deftrans-filepath path "SPECIALIZE")
                  (specialize-transunit tunit target-fn target-param const)
                  (specialize-filepath-transunit-map (omap::tail map)
                                                     target-fn
                                                     target-param
                                                     const)))
  :verify-guards :after-returns)

(define specialize-transunit-ensemble
  ((tunits transunit-ensemblep)
   (target-fn identp)
   (target-param identp)
   (const exprp))
  :short "Transform a translation unit ensemble."
  :returns (new-tunits transunit-ensemblep)
  (b* (((transunit-ensemble tunits) tunits))
    (transunit-ensemble
      (specialize-filepath-transunit-map tunits.unwrap
                                         target-fn
                                         target-param
                                         const))))
