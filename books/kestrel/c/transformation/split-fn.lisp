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

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)
(include-book "std/system/constant-value" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/code-ensembles")
(include-book "utilities/free-vars")
(include-book "utilities/subst-free")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (tau-system))))
(set-induction-depth-limit 0)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/system/w" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation split-fn
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled ident-listp-when-ident-setp
  (implies (ident-setp set)
           (ident-listp set))
  :induct t
  :enable ident-setp)

(local (in-theory (enable ident-listp-when-ident-setp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap ident-param-declon-map
  :key-type ident
  :val-type param-declon
  :pred ident-param-declon-mapp)

(defrulel ident-listp-of-keys-when-ident-param-declon-mapp
  (implies (ident-param-declon-mapp map)
           (ident-listp (omap::keys map)))
  :induct t
  :enable omap::keys)

(defrulel param-declon-listp-of-strip-cdrs-when-ident-param-declon-mapp
  (implies (ident-param-declon-mapp map)
           (param-declon-listp (strip-cdrs map)))
  :induct t
  :enable (strip-cdrs
           ident-param-declon-mapp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define map-address-ident-list
  ((idents ident-listp))
  :short "Map @(tsee c$::expr-unary) @(tsee c$::unop-address) over a list of
          identifiers."
  :returns (exprs expr-listp)
  (if (endp idents)
      nil
    (cons (make-expr-unary :op (c$::unop-address)
                           :arg (make-expr-ident :ident (first idents)))
          (map-address-ident-list (rest idents)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-declon-to-ident-param-declon-map
  ((paramdecl param-declonp))
  :short "Convert a parameter declaration into a singleton omap associating the
          declared identifier to the declaration."
  :long
  (xdoc::topstring
   (xdoc::p
     "If the parameter declaration is unnamed, or if it has not been
      disambiguated, the empty map is returned instead."))
  :returns (map ident-param-declon-mapp)
  (b* (((param-declon paramdecl) paramdecl))
    (param-declor-case
      paramdecl.declor
      :nonabstract (omap::update (declor->ident paramdecl.declor.declor)
                                 (param-declon-fix paramdecl)
                                 nil)
      :otherwise nil)))

(define param-declon-list-to-ident-param-declon-map
  ((paramdecls param-declon-listp))
  :short "Fold @(tsee param-declon-to-ident-param-declon-map) over a list."
  :returns (map ident-param-declon-mapp)
  (if (endp paramdecls)
        nil
    (omap::update* (param-declon-to-ident-param-declon-map (first paramdecls))
                   (param-declon-list-to-ident-param-declon-map (rest paramdecls))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decl-to-ident-param-declon-map
  ((decl declp))
  :short "Convert a regular declaration into an omap of identifiers to
          parameter declarations."
  :long
  (xdoc::topstring
   (xdoc::p
     "The resulting parameter declarations represent the same variables, with
      the same types and qualifiers. The keys to the omap are the identifiers
      bound by each parameter declaration.")
   (xdoc::p
     "A declaration which introduces multiple variables is converted to an omap
      of equal length to the number of identifiers. For instance, the
      declaration @('int x = 0, y = 0;') is converted to the omap associating
      @('x') to parameter declaration @('int x'), and @('y') to @('int y').")
   (xdoc::p
     "Only variable declarations are converted. Static assertions result in
     @('nil').")
   (xdoc::p
     "This is used by @(tsee split-fn) to track declared variables and to
      create parameters for the newly generated function (with the subset of
      declared variables which are used)."))
  :returns (map ident-param-declon-mapp)
  (decl-case
   decl
   :decl (decl-to-ident-param-declon-map0 decl.specs decl.init)
   :statassert nil)
  :prepwork
  ((define decl-to-ident-param-declon-map0
     ((declspecs decl-spec-listp)
      (initdeclors initdeclor-listp))
     :returns
     (map ident-param-declon-mapp)
     (b* (((when (endp initdeclors))
           nil)
          ((initdeclor initdeclor) (first initdeclors))
          (ident (declor->ident initdeclor.declor)))
       (omap::update
         ident
         (make-param-declon
           :specs declspecs
           :declor (param-declor-nonabstract initdeclor.declor))
         (decl-to-ident-param-declon-map0 declspecs (rest initdeclors))))
     :verify-guards :after-returns)))

(define decl-list-to-ident-param-declon-map
  ((decls decl-listp))
  :short "Fold @(tsee decl-to-ident-param-declon-map) over a list."
  :returns (map ident-param-declon-mapp)
  (if (endp decls)
        nil
    (omap::update* (decl-to-ident-param-declon-map (first decls))
                   (decl-list-to-ident-param-declon-map (rest decls))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: avoid excessive parentheses
(defines add-pointer-declor/dirdeclor
  (define add-pointer-declor
    ((declor declorp))
    :returns (declor$ declorp)
    (b* (((declor declor) declor))
      (dirdeclor-case
        declor.direct
        :ident (make-declor
                 :pointers (append declor.pointers (list nil))
                 :direct declor.direct)
        :otherwise (make-declor
                     :pointers declor.pointers
                     :direct (add-pointer-dirdeclor declor.direct))))
    :measure (declor-count declor))

  (define add-pointer-dirdeclor
    ((dirdeclor dirdeclorp))
    :returns (dirdeclor$ dirdeclorp)
    (dirdeclor-case
     dirdeclor
     :ident (dirdeclor-paren (make-declor :pointers (list nil)
                                          :direct (dirdeclor-fix dirdeclor)))
     :paren (dirdeclor-paren (add-pointer-declor dirdeclor.inner))
     :array (make-dirdeclor-array
              :declor (add-pointer-dirdeclor dirdeclor.declor)
              :qualspecs dirdeclor.qualspecs
              :size? dirdeclor.size?)
     :array-static1 (make-dirdeclor-array-static1
                      :declor (add-pointer-dirdeclor dirdeclor.declor)
                      :qualspecs dirdeclor.qualspecs
                      :size dirdeclor.size)
     :array-static2 (make-dirdeclor-array-static2
                      :declor (add-pointer-dirdeclor dirdeclor.declor)
                      :qualspecs dirdeclor.qualspecs
                      :size dirdeclor.size)
     :array-star (make-dirdeclor-array-star
                   :declor (add-pointer-dirdeclor dirdeclor.declor)
                   :qualspecs dirdeclor.qualspecs)
     :function-params (make-dirdeclor-function-params
                        :declor (add-pointer-dirdeclor dirdeclor.declor)
                        :params dirdeclor.params
                        :ellipsis dirdeclor.ellipsis)
     :function-names (make-dirdeclor-function-names
                        :declor (add-pointer-dirdeclor dirdeclor.declor)
                        :names dirdeclor.names))
    :measure (dirdeclor-count dirdeclor))

  :verify-guards :after-returns)

(define add-pointer-param-declon
  ((param-declon param-declonp))
  :returns (param-declon$ param-declonp)
  (b* (((param-declon param-declon) param-declon))
    (make-param-declon
      :specs param-declon.specs
      :declor (param-declor-case
                param-declon.declor
                :nonabstract (param-declor-nonabstract
                               (add-pointer-declor param-declon.declor.declor))
                ;; TODO (not used here, but should be implemented for a general
                ;; utility).
                :abstract (param-declor-fix param-declon.declor)
                :none (param-declor-fix param-declon.declor)
                :ambig (param-declor-fix param-declon.declor)))))

(define map-add-pointer-param-declon
  ((param-declons param-declon-listp))
  :returns (param-declons$ param-declon-listp)
  (if (endp param-declons)
      nil
    (cons (add-pointer-param-declon (first param-declons))
          (map-add-pointer-param-declon (rest param-declons)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-deref-subst
  ((idents ident-listp))
  :returns (subst ident-expr-mapp)
  (if (endp idents)
      nil
    (omap::update (ident-fix (first idents))
                  (expr-paren
                    (c$::make-expr-unary
                      :op (c$::unop-indir)
                      :arg (make-expr-ident :ident (first idents))))
                  (make-deref-subst (rest idents))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abstract-fn
  ((new-fn-name identp)
   (spec decl-spec-listp)
   (pointers typequal/attribspec-list-listp)
   (items block-item-listp)
   (decls ident-param-declon-mapp))
  :short "Create a new function from the block items following the @(tsee
          split-fn) split point."
  :long
  (xdoc::topstring
   (xdoc::p
     "The new function will be created with same return type as the original.")
   (xdoc::p
     "Arguments to the function are determined by taking the variable
      declarations of the original function which appear free in the block
      items, which will constitute the body of the new function. (Note that
      arguments are not currently taken by reference, but this may be necessary
      for general equivalence. It may be sufficient to take an argument by
      reference when its address is taken in an expression of the new function
      body.)"))
  :returns (mv (idents ident-listp
                       "The identifiers appearing in argument @('decls')
                        corresponding to the function parameters (in the same
                        order).")
               (new-fn fundefp
                       "The new function definition."))
  (b* (((mv idents -)
        (free-vars-block-item-list items nil))
       (decls (ident-param-declon-map-filter decls idents))
       (idents (omap::keys decls))
       ;; We use strip-cdrs instead of omap::values because we need these in
       ;; the same order as idents.
       (params (strip-cdrs decls))
       (deref-subst (make-deref-subst idents))
       ((mv items -)
        (block-item-list-subst-free items deref-subst nil)))
    (mv
      idents
      (make-fundef
        :spec spec
        :declor (make-declor
                  :pointers pointers
                  :direct (make-dirdeclor-function-params
                            :declor (dirdeclor-ident new-fn-name)
                            :params (map-add-pointer-param-declon params)))
        :body (stmt-compound items))))
  :guard-hints (("Goal" :in-theory (enable omap::alistp-when-mapp)))
  :prepwork
  ((define ident-param-declon-map-filter
     ((map ident-param-declon-mapp)
      (idents ident-setp))
     :returns (new-map ident-param-declon-mapp)
     (b* ((map (ident-param-declon-map-fix map))
          ((when (omap::emptyp map))
           nil)
          ((mv key val)
           (omap::head map)))
       (if (in key idents)
           (omap::update key
                         val
                         (ident-param-declon-map-filter (omap::tail map) idents))
         (ident-param-declon-map-filter
           (omap::tail map)
           idents)))
     :measure (acl2-count (ident-param-declon-map-fix map))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-block-item-list
  ((new-fn-name identp)
   (items block-item-listp)
   (spec decl-spec-listp)
   (pointers typequal/attribspec-list-listp)
   (decls ident-param-declon-mapp)
   (split-point natp))
  :short "Transform a list of block items."
  :long
  (xdoc::topstring
   (xdoc::p
     "This function will walk over a list of block items until it reaches the
      designated split point. Until then, it processes each declaration,
      associating locally introduced identifers to parameter declarations
      compatible with their original declaration. When the split point is
      reached, @(tsee abstract-fn) is invoked to generate the new function with
      parameters derived from this parameter declaration map. The previous
      function is truncated at this point, and a return statement added calling
      the newly split-out function."))
  :returns (mv (er? maybe-msgp)
               (new-fn fundefp)
               (truncated-items block-item-listp))
  (b* ((items (block-item-list-fix items))
       ((reterr) (c$::irr-fundef) items)
       ((when (zp split-point))
        (b* (((mv idents new-fn)
              (abstract-fn new-fn-name spec pointers items decls)))
          (retok new-fn
                 (list
                   (make-block-item-stmt
                    :stmt
                     (stmt-return
                       (make-expr-funcall
                         :fun (make-expr-ident :ident new-fn-name :info nil)
                         :args (map-address-ident-list idents)))
                     :info nil)))))
       ((when (endp items))
        (retmsg$ "Bad split point specifier"))
       (item (first items))
       (decls
        (block-item-case
          item
          :decl (omap::update* (decl-to-ident-param-declon-map item.unwrap)
                               (ident-param-declon-map-fix decls))
          :otherwise decls))
       ((erp new-fn truncated-items)
        (split-fn-block-item-list new-fn-name
                              (rest items)
                              spec
                              pointers
                              decls
                              (- split-point 1))))
    (retok new-fn
           (cons (first items)
                 truncated-items)))
  :measure (block-item-list-count items)
  :hints (("Goal" :in-theory (enable block-item-list-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-fundef
  ((target-fn identp)
   (new-fn-name identp)
   (fundef fundefp)
   (split-point natp))
  :short "Transform a function definition, splitting it if matches the target
          identifier, or else leaving it untouched."
  :returns (mv (er? maybe-msgp)
               (fundef1 fundefp)
               (fundef2 fundef-optionp))
  (b* (((reterr) (c$::irr-fundef) nil)
       ((fundef fundef) fundef)
       ((declor fundef.declor) fundef.declor))
    (stmt-case
      fundef.body
      :compound
      (b* (((mv well-formedp fundef-name params)
             (dirdeclor-case
               fundef.declor.direct
               :function-params
               (mv t
                   (c$::dirdeclor->ident fundef.declor.direct.declor)
                   fundef.declor.direct.params)
               :function-names
               (mv t
                   (c$::dirdeclor->ident fundef.declor.direct.declor)
                   nil)
               :otherwise (mv nil nil nil)))
           ((unless (and well-formedp
                         (equal target-fn fundef-name)))
            (retok (fundef-fix fundef) nil))
           ((erp new-fn truncated-items)
              (split-fn-block-item-list
                new-fn-name
                fundef.body.items
                fundef.spec
                fundef.declor.pointers
                (param-declon-list-to-ident-param-declon-map params)
                split-point)))
        (retok new-fn
                 (make-fundef
                   :extension fundef.extension
                   :spec fundef.spec
                   :declor fundef.declor
                   :decls fundef.decls
                   :body (stmt-compound truncated-items))))
      :otherwise (retok (fundef-fix fundef) nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-extdecl
  ((target-fn identp)
   (new-fn-name identp)
   (extdecl extdeclp)
   (split-point natp))
  :short "Transform an external declaration."
  :returns (mv (er? maybe-msgp)
               (target-found booleanp)
               (extdecls extdecl-listp))
  (b* (((reterr) nil nil))
    (extdecl-case
      extdecl
      :fundef (b* (((erp fundef1 fundef2)
                    (split-fn-fundef
                      target-fn
                      new-fn-name
                      extdecl.unwrap
                      split-point)))
                (fundef-option-case
                  fundef2
                  :some (retok t (list (extdecl-fundef fundef1)
                                       (extdecl-fundef fundef2.val)))
                  :none (retok nil (list (extdecl-fundef fundef1)))))
      :decl (retok nil (list (extdecl-fix extdecl)))
      :empty (retok nil (list (extdecl-fix extdecl)))
      :asm (retok nil (list (extdecl-fix extdecl)))))
  ///
  (more-returns
   (extdecls true-listp :rule-classes :type-prescription)))

(define split-fn-extdecl-list
  ((target-fn identp)
   (new-fn-name identp)
   (extdecls extdecl-listp)
   (split-point natp))
  :short "Transform a list of external declarations."
  :returns (mv (er? maybe-msgp)
               (new-extdecls extdecl-listp))
  (b* (((reterr) nil)
       ((when (endp extdecls))
        (retok nil))
       ((erp target-found extdecls1)
        (split-fn-extdecl target-fn new-fn-name (first extdecls) split-point))
       ((when target-found)
        (retok (append extdecls1 (extdecl-list-fix (rest extdecls)))))
       ((erp extdecls2)
        (split-fn-extdecl-list target-fn new-fn-name (rest extdecls) split-point)))
    (retok (append extdecls1 extdecls2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-transunit
  ((target-fn identp)
   (new-fn-name identp)
   (tunit transunitp)
   (split-point natp))
  :short "Transform a translation unit."
  :returns (mv (er? maybe-msgp)
               (new-tunit transunitp))
  (b* (((transunit tunit) tunit)
       ((mv er extdecls)
        (split-fn-extdecl-list target-fn new-fn-name tunit.decls split-point)))
    (mv er (make-transunit :decls extdecls :info tunit.info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-filepath-transunit-map
  ((target-fn identp)
   (new-fn-name identp)
   (map filepath-transunit-mapp)
   (split-point natp))
  :short "Transform a filepath."
  :returns (mv (er? maybe-msgp)
               (new-map filepath-transunit-mapp
                        :hyp (filepath-transunit-mapp map)))
  (b* (((reterr) nil)
       ((when (omap::emptyp map))
        (retok nil))
       ((mv path tunit) (omap::head map))
       ((erp new-tunit)
        (split-fn-transunit target-fn new-fn-name tunit split-point))
       ((erp new-map)
        (split-fn-filepath-transunit-map target-fn
                                         new-fn-name
                                         (omap::tail map)
                                         split-point)))
    (retok (omap::update (c$::filepath-fix path)
                         new-tunit
                         new-map)))
  :verify-guards :after-returns)

(define split-fn-transunit-ensemble
  ((target-fn identp)
   (new-fn-name identp)
   (tunits transunit-ensemblep)
   (split-point natp))
  :short "Transform a translation unit ensemble."
  :returns (mv (er? maybe-msgp)
               (new-tunits transunit-ensemblep))
  (b* (((transunit-ensemble tunits) tunits)
       ((mv er map)
        (split-fn-filepath-transunit-map target-fn
                                         new-fn-name
                                         tunits.unwrap
                                         split-point)))
    (mv er (transunit-ensemble map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-code-ensemble
  ((target-fn identp)
   (new-fn-name identp)
   (code code-ensemblep)
   (split-point natp))
  :returns (mv (er? maybe-msgp)
               (new-code code-ensemblep))
  :short "Transform a code ensemble."
  (b* (((code-ensemble code) code)
       ((reterr) (irr-code-ensemble))
       ((erp tunits) (split-fn-transunit-ensemble target-fn
                                                  new-fn-name
                                                  code.transunits
                                                  split-point)))
    (retok (change-code-ensemble code :transunits tunits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing split-fn)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-process-inputs
  (const-old
   const-new
   target
   new-fn
   split-point
   (wrld plist-worldp))
  :returns (mv (er? maybe-msgp)
               (code (code-ensemblep code))
               (const-new$ symbolp)
               (target$ identp)
               (new-fn$ identp)
               (split-point natp))
  :short "Process the inputs."
  (b* (((reterr)
        (irr-code-ensemble) nil (c$::irr-ident) (c$::irr-ident) 0)
       ((unless (symbolp const-old))
        (retmsg$ "~x0 must be a symbol." const-old))
       (code (acl2::constant-value const-old wrld))
       ((unless (code-ensemblep code))
        (retmsg$ "~x0 must be a code ensemble." const-old))
       ((unless (symbolp const-new))
        (retmsg$ "~x0 must be a symbol." const-new))
       ((unless (stringp target))
        (retmsg$ "~x0 must be a string." target))
       (target (ident target))
       ((unless (stringp new-fn))
        (retmsg$ "~x0 must be a string." new-fn))
       (new-fn (ident new-fn))
       ((unless (natp split-point))
        (retmsg$ "~x0 must be a natural number." split-point)))
    (retok code const-new target new-fn split-point)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation split-fn)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-gen-everything
  ((code code-ensemblep)
   (const-new symbolp)
   (target identp)
   (new-fn identp)
   (split-point natp))
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :short "Generate all the events."
  (b* (((reterr) '(_))
       ((erp code)
        (split-fn-code-ensemble
          target
          new-fn
          code
          split-point))
       (defconst-event
         `(defconst ,const-new
            ',code)))
    (retok defconst-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-process-inputs-and-gen-everything
  (const-old
   const-new
   target
   new-fn
   split-point
   (wrld plist-worldp))
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp code const-new target new-fn split-point)
        (split-fn-process-inputs
          const-old const-new target new-fn split-point wrld))
       ((erp event)
        (split-fn-gen-everything code const-new target new-fn split-point)))
    (retok event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-fn-fn
  (const-old
   const-new
   target
   new-fn
   split-point
   (ctx ctxp)
   state)
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (event pseudo-event-formp)
               state)
  :short "Event expansion of @(tsee split-fn)."
  (b* (((mv erp event)
        (split-fn-process-inputs-and-gen-everything
          const-old const-new target new-fn split-point (w state)))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection split-fn-macro-definition
  :short "Definition of @(tsee split-fn)."
  (defmacro split-fn
    (const-old
     const-new
     &key
     target
     new-fn
     split-point)
    `(make-event (split-fn-fn ',const-old
                              ',const-new
                              ',target
                              ',new-fn
                              ',split-point
                              'split-fn
                              state))))
