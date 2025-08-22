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

(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)
(include-book "std/system/constant-value" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/code-ensembles")

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

(xdoc::evmac-topic-implementation specialize
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident-from-param-declon
  ((paramdecl param-declonp))
  :short "Get the identifier from a parameter declaration."
  :long
  (xdoc::topstring
   (xdoc::p
     "This may return @('nil') when the parameter declaration is unnamed."))
  :returns (ident ident-optionp)
  (b* (((param-declon paramdecl) paramdecl))
    (param-declor-case
      paramdecl.declor
      :nonabstract (declor->ident paramdecl.declor.declor)
      :otherwise nil)))

(define param-declon-to-decl
  ((paramdecl param-declonp)
   (init? initer-optionp))
  :short "Convert a parameter declaration to a regular declaration."
  :returns (mv (success booleanp)
               (decl declp))
  (b* (((param-declon paramdecl) paramdecl))
    (param-declor-case
      paramdecl.declor
      :nonabstract (mv t
                       (make-decl-decl
                        :extension nil
                        :specs paramdecl.specs
                        :init (cons (initdeclor paramdecl.declor.declor nil nil init?) nil)))
      :otherwise (mv nil (irr-decl)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-declon-list-remove-param-by-ident
  ((params param-declon-listp)
   (param-to-remove identp))
  :returns (mv (success booleanp)
               (new-params param-declon-listp)
               (removed-param param-declonp))
  :short "Remove a parameter from a list of parameter declarations."
  (b* ((params (param-declon-list-fix params))
       ((when (endp params))
        (mv nil params (irr-param-declon)))
       (param (first params))
       (param-name (ident-from-param-declon param))
       ((when (equal param-name param-to-remove))
        (mv t (rest params) param))
       ((mv success new-params removed-param)
        (param-declon-list-remove-param-by-ident (rest params) param-to-remove)))
    (mv success
        (cons param new-params)
        removed-param))
  :measure (param-declon-list-count params)
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
    (dirdeclor-case
     fundef.declor.direct
     :function-params
     (b* (((unless (equal target-fn
                          (c$::dirdeclor->ident fundef.declor.direct.declor)))
           (mv nil (fundef-fix fundef)))
          ((mv success new-params removed-param)
           (param-declon-list-remove-param-by-ident fundef.declor.direct.params target-param))
          ((unless success)
           ;; TODO: use error-value-tuples
           (prog2$ (raise "Function ~x0 did not have a parameter ~x1"
                          target-fn
                          target-param)
                   (mv nil (fundef-fix fundef))))
          (dirdeclor-params
           (make-dirdeclor-function-params
            :declor fundef.declor.direct.declor
            :params new-params
            :ellipsis fundef.declor.direct.ellipsis))
          ((mv - decl)
           (param-declon-to-decl removed-param (initer-single const))))
       (mv t
           (make-fundef
            :extension fundef.extension
            :spec fundef.spec
            :declor (make-declor
                     :pointers fundef.declor.pointers
                     :direct dirdeclor-params)
            :decls fundef.decls
            :body (cons (make-block-item-decl :decl decl :info nil)
                        fundef.body)
            :info fundef.info)))
     :otherwise
     ;; TODO: check when non-function-params dirdeclor still has name target-fn
     (mv nil (fundef-fix fundef))))
  :no-function nil)

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
    (make-transunit
     :decls (specialize-extdecl-list tunit.decls target-fn target-param const)
     :info tunit.info)))

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
    (omap::update (c$::filepath-fix path)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define specialize-code-ensemble
  ((code code-ensemblep)
   (target-fn identp)
   (target-param identp)
   (const exprp))
  :short "Transform a code ensemble."
  :returns (new-code code-ensemblep)
  (b* (((code-ensemble code) code))
    (make-code-ensemble
     :transunits (specialize-transunit-ensemble code.transunits
                                                target-fn
                                                target-param
                                                const)
     :ienv code.ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing specialize)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define specialize-process-inputs
  (const-old
   const-new
   target
   param
   const
   (wrld plist-worldp))
  :returns (mv (er? maybe-msgp)
               (code (code-ensemblep code))
               (const-new$ symbolp)
               (target$ identp)
               (param$ identp)
               (const exprp))
  :short "Process the inputs."
  (b* (((reterr)
        (irr-code-ensemble)
        nil
        (c$::irr-ident)
        (c$::irr-ident)
        (c$::irr-expr))
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
       ((unless (stringp param))
        (retmsg$ "~x0 must be a string." param))
       (param (ident param))
       ((unless (exprp const))
        (retmsg$ "~x0 must be a C expression." const)))
    (retok code const-new target param const)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation specialize)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define specialize-gen-everything
  ((code code-ensemblep)
   (const-new symbolp)
   (target identp)
   (param identp)
   (const exprp))
  :returns (event pseudo-event-formp)
  :short "Generate all the events."
  (b* ((code (specialize-code-ensemble code target param const))
       (defconst-event
         `(defconst ,const-new
            ',code)))
    defconst-event))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define specialize-process-inputs-and-gen-everything
  (const-old
   const-new
   target
   param
   const
   (wrld plist-worldp))
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp code const-new target param const)
        (specialize-process-inputs
          const-old const-new target param const wrld))
       (event (specialize-gen-everything code const-new target param const)))
    (retok event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define specialize-fn
  (const-old
   const-new
   target
   param
   const
   (ctx ctxp)
   state)
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (event pseudo-event-formp)
               state)
  :short "Event expansion of @(tsee specialize)."
  (b* (((mv erp event)
        (specialize-process-inputs-and-gen-everything
          const-old const-new target param const (w state)))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection specialize-macro-definition
  :short "Definition of @(tsee specialize)."
  (defmacro specialize
    (const-old
     const-new
     &key
     target
     param
     const)
    `(make-event (specialize-fn ',const-old
                                ',const-new
                                ',target
                                ',param
                                ,const
                                'specialize
                                state))))
