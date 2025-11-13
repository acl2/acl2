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
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "kestrel/utilities/messages" :dir :system)
(include-book "std/system/constant-value" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "kestrel/fty/string-option" :dir :system)

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/code-ensembles")
(include-book "../syntax/validation-information")
(include-book "../syntax/validator")
(include-book "utilities/collect-idents")
(include-book "utilities/fresh-ident")
(include-book "utilities/rename-fn")

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/system/w" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Additional FTY types

(fty::defalist string-string-option-alist
  :short "Fixtype of alists from strings to optional strings."
  :key-type string
  :val-type acl2::string-option
  :true-listp t
  :pred string-string-option-alistp
  :prepwork ((set-induction-depth-limit 1)))

(fty::defomap ident-ident-option-map
  :short "Fixtype of omaps from identifiers to optional identifiers."
  :key-type ident
  :val-type ident-option
  :pred ident-ident-option-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation wrap-fn :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define wrap-fn-process-param-declon-list-loop
  ((params param-declon-listp)
   (fresh-ident-base identp)
   (blacklist ident-setp))
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (blacklist$ ident-setp)
               (params$ param-declon-listp)
               (idents ident-listp))
  (b* (((reterr) nil nil nil)
       (blacklist (ident-set-fix blacklist))
       ((when (endp params))
        (retok (ident-set-fix blacklist) nil nil))
       (param-declor (c$::param-declon->declor (first params)))
       ((erp blacklist param-declon ident)
        (b* (((reterr) nil nil nil))
          (param-declor-case
            param-declor
            :nonabstract
            (retok blacklist
                   (param-declon-fix (first params))
                   (declor->ident param-declor.declor))
            :abstract
            (b* ((ident (fresh-ident fresh-ident-base blacklist)))
              (retok (insert ident blacklist)
                     (c$::change-param-declon
                       (first params)
                       :declor (make-param-declor-nonabstract
                                 :declor (c$::absdeclor-to-declor
                                           param-declor.declor
                                           ident)))
                     ident))
            :none
            (b* ((ident (fresh-ident fresh-ident-base blacklist)))
              (retok (insert ident blacklist)
                     (c$::change-param-declon
                       (first params)
                       :declor (make-param-declor-nonabstract
                                 :declor (make-declor
                                           :pointers nil
                                           :direct (c$::make-dirdeclor-ident
                                                     :ident ident))))
                     ident))
            :ambig (reterr t))))
       ((erp blacklist params idents)
        (wrap-fn-process-param-declon-list-loop (rest params)
                                                fresh-ident-base
                                                blacklist)))
    (retok blacklist
           (cons param-declon params)
           (cons ident idents)))
  ///

  (more-returns
   (idents true-listp :rule-classes :type-prescription)))

(define wrap-fn-process-param-declon-list
  ((params param-declon-listp)
   (fresh-ident-base identp)
   (blacklist ident-setp))
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (blacklist$ ident-setp)
               (params$ param-declon-listp)
               (idents ident-listp))
  :short "Check that the parameter list is supported and add parameter names as
          necessary."
  (b* (((reterr) nil nil nil)
       (blacklist (ident-set-fix blacklist))
       (params (param-declon-list-fix params))
       ((when (equal params
                     (list (make-param-declon
                             :specs (list (decl-spec-typespec
                                            (c$::type-spec-void)))
                             :declor (param-declor-none)
                             :attribs nil))))
        ;; Special (void) case
        (retok blacklist params nil)))
    (wrap-fn-process-param-declon-list-loop params
                                            fresh-ident-base
                                            blacklist))
  ///

  (more-returns
   (idents true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;

(defines declor/dirdeclor-wrap-fn-make-wrapper
  (define declor-wrap-fn-make-wrapper
    ((declor declorp)
     (wrapper-name identp)
     (arg-base-name identp)
     (blacklist ident-setp))
    :returns (mv (blacklist ident-setp)
                 (found-paramsp booleanp :rule-classes :type-prescription)
                 (can-create-wrapperp booleanp :rule-classes :type-prescription)
                 (declor$ declorp)
                 (idents ident-listp))
    :short "Make the wrapper function declarator if the parameter list is
            supported."
    :long
    (xdoc::topstring
     (xdoc::p
       "Also returns an updated blacklist and identifier list corresponding to
        the parameters.")
     (xdoc::p
       "The @('found-paramsp') return value is @('t') iff function parameters
        were found, as expected. The @('can-create-wrapperp') return is @('t')
        iff the parameter list was in the supported set."))
    (b* (((mv blacklist found-paramsp can-create-wrapperp dirdeclor idents)
          (dirdeclor-wrap-fn-make-wrapper
            (declor->direct declor) wrapper-name arg-base-name blacklist)))
      (mv blacklist
          found-paramsp
          can-create-wrapperp
          (c$::change-declor
            declor
            :direct dirdeclor)
          idents))
    :measure (declor-count declor)
    ///

    (more-returns
     (idents true-listp
      :rule-classes :type-prescription
      :hints (("Goal" :use return-type-of-declor-wrap-fn-make-wrapper.idents
                      :in-theory (disable return-type-of-declor-wrap-fn-make-wrapper.idents))))))

  (define dirdeclor-wrap-fn-make-wrapper
    ((dirdeclor dirdeclorp)
     (wrapper-name identp)
     (arg-base-name identp)
     (blacklist ident-setp))
    :returns (mv (blacklist ident-setp)
                 (found-paramsp booleanp :rule-classes :type-prescription)
                 (can-create-wrapperp booleanp :rule-classes :type-prescription)
                 (dirdeclor$ dirdeclorp)
                 (idents ident-listp))
    :short "Make the wrapper function direct declarator if the parameter list is
            supported."
    :long
    (xdoc::topstring
     (xdoc::p
       "See @(tsee declor-wrap-fn-make-wrapper)."))
    (dirdeclor-case
      dirdeclor
      :paren
      (b* (((mv blacklist found-paramsp can-create-wrapperp declor idents)
            (declor-wrap-fn-make-wrapper
              dirdeclor.inner wrapper-name arg-base-name blacklist)))
        (mv blacklist
            found-paramsp
            can-create-wrapperp
            (c$::change-dirdeclor-paren
              dirdeclor
              :inner declor)
            idents))
      :function-params
      (b* (((mv blacklist found-paramsp can-create-wrapperp dirdeclor$ idents)
            (dirdeclor-wrap-fn-make-wrapper
              dirdeclor.declor wrapper-name arg-base-name blacklist))
           ((when found-paramsp)
            (mv blacklist
                found-paramsp
                can-create-wrapperp
                (c$::change-dirdeclor-function-params
                  dirdeclor
                  :declor dirdeclor$)
                idents))
           ((when dirdeclor.ellipsis)
            (mv blacklist t nil (dirdeclor-fix dirdeclor) nil))
           ((mv erp blacklist params idents)
            (wrap-fn-process-param-declon-list
              dirdeclor.params arg-base-name blacklist))
           ((when erp)
            (mv blacklist t nil (dirdeclor-fix dirdeclor) nil)))
        (mv blacklist
            t
            t
            (c$::change-dirdeclor-function-params
              dirdeclor
              :declor (c$::dirdeclor-rename dirdeclor.declor wrapper-name)
              :params params)
            idents))
      :function-names (mv (ident-set-fix blacklist)
                          t
                          nil
                          (dirdeclor-fix dirdeclor)
                          nil)
      :otherwise (mv (ident-set-fix blacklist)
                     nil
                     nil
                     (dirdeclor-fix dirdeclor)
                     nil))
    :measure (dirdeclor-count dirdeclor)
    ///

    (more-returns
     (idents true-listp
      :rule-classes :type-prescription
      :hints (("Goal" :use return-type-of-dirdeclor-wrap-fn-make-wrapper.idents
                      :in-theory (disable return-type-of-dirdeclor-wrap-fn-make-wrapper.idents))))))

  :verify-guards :after-returns
  ///

  (fty::deffixequiv-mutual declor/dirdeclor-wrap-fn-make-wrapper))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define declor-wrap-fn-add-wrapper-def
  ((declor declorp)
   (target-name identp)
   (wrapper-name? ident-optionp)
   (blacklist ident-setp)
   (specs decl-spec-listp))
  :returns (mv (er? maybe-msgp)
               (foundp booleanp :rule-classes :type-prescription)
               (wrapper? fundef-optionp)
               (wrapper-name?$ ident-optionp))
  :short "Check if a declarator matches the target, and create the function
          wrapper if so."
  :long
  (xdoc::topstring
   (xdoc::p
     "If the @('foundp') return value is @('t') but @('wrapper?') is @('nil'),
      that means the declarator matched the target, but some aspect of it is
      unsupported by the current implementation."))
  (b* (((reterr) nil nil nil)
       ((unless (c$::ident-equiv (declor->ident declor) target-name))
        (retok nil nil nil))
       (wrapper-base-name
         (or wrapper-name?
             (ident (concatenate
                      'string
                      "wrapper_"
                      (let ((target-name-str (ident->unwrap target-name)))
                        (if (stringp target-name-str)
                            target-name-str
                          ""))))))
       (wrapper-name (fresh-ident wrapper-base-name blacklist))
       (arg-base-name
         (ident (concatenate
                  'string
                  (let ((wrapper-name-str (ident->unwrap wrapper-name)))
                    (if (stringp wrapper-name-str)
                        wrapper-name-str
                      ""))
                  "_arg")))
       ((mv - found-paramsp can-create-wrapperp wrapper-declor idents)
        (declor-wrap-fn-make-wrapper
          declor wrapper-name arg-base-name blacklist))
       ((unless found-paramsp)
        (retok nil nil nil))
       ((unless can-create-wrapperp)
        (retok t nil nil))
       (wrapper-body
         (make-comp-stmt
           :items
           (list
             (make-block-item-stmt
               :stmt (make-stmt-return
                       :expr? (make-expr-funcall
                                :fun (make-expr-ident
                                       :ident target-name)
                                :args (c$::ident-list-map-expr-ident idents))))
             ))))
    (retok t
           (make-fundef
             :spec (c$::declor-spec-list-make-static specs)
             :declor wrapper-declor
             :body wrapper-body
             :info nil)
           wrapper-name))
  ///

  (defret fundefp-of-declor-wrap-fn-add-wrapper-def.wrapper?-under-iff
    (iff (fundefp wrapper?)
         wrapper?))

  (defret identp-of-declor-wrap-fn-add-wrapper-def.wrapper-name?$
    (equal (identp wrapper-name?$)
           (fundefp wrapper?))))

(define initdeclor-list-wrap-fn-add-wrapper-def
  ((init initdeclor-listp)
   (target-name identp)
   (wrapper-name? ident-optionp)
   (blacklist ident-setp)
   (specs decl-spec-listp))
  :guard (c$::initdeclor-list-annop init)
  :returns (mv (er? maybe-msgp)
               (uid? c$::uid-optionp)
               (wrapper? fundef-optionp)
               (wrapper-name?$ ident-optionp))
  :short "Check if a initializer declarator matches the target, and create the
          function wrapper if so."
  :long
  (xdoc::topstring
   (xdoc::p
     "The returned @('uid?') value, if it is not @('nil'), is the @(see
      c$::uid) of the matched function.")
   (xdoc::p
     "If @('uid?') return value is non-@('nil') but @('wrapper?') is @('nil'),
      that means the initializer declarator matched the target, but some aspect
      of it is unsupported by the current implementation."))
  (b* (((reterr) nil nil nil)
       ((when (endp init))
        (retok nil nil nil))
       (declor (initdeclor->declor (first init)))
       ((erp foundp wrapper? wrapper-name?$)
        (declor-wrap-fn-add-wrapper-def declor
                                         target-name
                                         wrapper-name?
                                         blacklist
                                         specs))
       ((unless foundp)
        (initdeclor-list-wrap-fn-add-wrapper-def (rest init)
                                                target-name
                                                wrapper-name?
                                                blacklist
                                                specs))
       ((erp uid?)
         (b* (((reterr) nil)
             ((unless (c$::initdeclor-infop (c$::initdeclor->info (first init))))
              (retmsg$ "Initializer declarator does not have ~
                        initdeclor-info metadata: ~x0"
                       (initdeclor-fix (first init)))))
           (retok (c$::initdeclor-info->uid?
                    (c$::initdeclor->info (first init)))))))
    (retok uid? wrapper? wrapper-name?$))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules)))
  ///

  (defret fundefp-of-initdeclor-list-wrap-fn-add-wrapper-def.wrapper?-under-iff
    (iff (fundefp wrapper?)
         wrapper?))

  (defret identp-of-initdeclor-list-wrap-fn-add-wrapper-def.wrapper-name?$
    (equal (identp wrapper-name?$)
           (fundefp wrapper?))
    :hints (("Goal" :induct t))))

(define decl-wrap-fn-add-wrapper-def
  ((decl declp)
   (target-name identp)
   (wrapper-name? ident-optionp)
   (blacklist ident-setp))
  :guard (c$::decl-annop decl)
  :returns (mv (er? maybe-msgp)
               (uid? c$::uid-optionp)
               (wrapper? fundef-optionp)
               (wrapper-name?$ ident-optionp))
  :short "Check if a declaration matches the target, and create the function
          wrapper if so."
  :long
  (xdoc::topstring
   (xdoc::p
     "The returned @('uid?') value, if it is not @('nil'), is the @(see
      c$::uid) of the matched function.")
   (xdoc::p
     "If @('uid?') return value is non-@('nil') but @('wrapper?') is @('nil'),
      that means the declaration matched the target, but some aspect of it is
      unsupported by the current implementation."))
  (decl-case
    decl
    :decl (initdeclor-list-wrap-fn-add-wrapper-def
            decl.init
            target-name
            wrapper-name?
            blacklist
            decl.specs)
    :otherwise (retok nil nil nil))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules)))
  ///

  (defret fundefp-of-decl-wrap-fn-add-wrapper-def.wrapper?-under-iff
    (iff (fundefp wrapper?)
         wrapper?))

  (defret identp-of-decl-wrap-fn-add-wrapper-def.wrapper-name?$
    (equal (identp wrapper-name?$)
           (fundefp wrapper?))))

(define fundef-wrap-fn-add-wrapper-def
  ((fundef fundefp)
   (target-name identp)
   (wrapper-name? ident-optionp)
   (blacklist ident-setp))
  :guard (c$::fundef-annop fundef)
  :returns (mv (er? maybe-msgp)
               (uid? c$::uid-optionp)
               (wrapper? fundef-optionp)
               (wrapper-name?$ ident-optionp))
  :short "Check if a function definition matches the target, and create the
          function wrapper if so."
  :long
  (xdoc::topstring
   (xdoc::p
     "The returned @('uid?') value, if it is not @('nil'), is the @(see
      c$::uid) of the matched function.")
   (xdoc::p
     "If @('uid?') return value is non-@('nil') but @('wrapper?') is @('nil'),
      that means the function definition matched the target, but some aspect of
      it is unsupported by the current implementation."))
  (b* (((reterr) nil nil nil)
       ((fundef fundef) fundef)
       ((erp foundp wrapper? wrapper-name?)
        (declor-wrap-fn-add-wrapper-def fundef.declor
                                        target-name
                                        wrapper-name?
                                        blacklist
                                        fundef.spec))
       ((erp uid?)
        (b* (((reterr) nil)
             ((unless foundp)
              (retok nil))
             ((unless (fundef-infop (c$::fundef->info fundef)))
              (retmsg$ "Function definition does not have ~
                        fundef-info metadata: ~x0"
                       (fundef-fix fundef))))
          (retok (c$::fundef-info->uid (c$::fundef->info fundef))))))
    (retok uid?
           wrapper?
           wrapper-name?))
  ///

  (defret fundefp-of-fundef-wrap-fn-add-wrapper-def.wrapper?-under-iff
    (iff (fundefp wrapper?)
         wrapper?))

  (defret identp-of-fundef-wrap-fn-add-wrapper-def.wrapper-name?$
    (equal (identp wrapper-name?$)
           (fundefp wrapper?))))

(define extdecl-wrap-fn-add-wrapper-def
  ((extdecl extdeclp)
   (target-name identp)
   (wrapper-name? ident-optionp)
   (blacklist ident-setp))
  :guard (c$::extdecl-annop extdecl)
  :returns (mv (er? maybe-msgp)
               (uid? c$::uid-optionp)
               (wrapper? fundef-optionp)
               (wrapper-name?$ ident-optionp))
  :short "Check if an external declaration matches the target, and create the
          function wrapper if so."
  :long
  (xdoc::topstring
   (xdoc::p
     "The returned @('uid?') value, if it is not @('nil'), is the @(see
      c$::uid) of the matched function.")
   (xdoc::p
     "If @('uid?') return value is non-@('nil') but @('wrapper?') is @('nil'),
      that means the external declaration matched the target, but some aspect
      of it is unsupported by the current implementation."))
  (extdecl-case
    extdecl
    :fundef (fundef-wrap-fn-add-wrapper-def
              extdecl.unwrap target-name wrapper-name? blacklist)
    :decl (decl-wrap-fn-add-wrapper-def
            extdecl.unwrap target-name wrapper-name? blacklist)
    :otherwise (retok nil nil nil))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules)))
  ///

  (defret fundefp-of-extdecl-wrap-fn-add-wrapper-def.wrapper?-under-iff
    (iff (fundefp wrapper?)
         wrapper?))

  (defret identp-of-extdecl-wrap-fn-add-wrapper-def.wrapper-name?$
    (equal (identp wrapper-name?$)
           (fundefp wrapper?))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extdecl-list-wrap-fn
  ((extdecls extdecl-listp)
   (target-name identp)
   (wrapper-name? ident-optionp)
   (blacklist ident-setp))
  :guard (c$::extdecl-list-annop extdecls)
  :returns (mv (er? maybe-msgp)
               (foundp booleanp :rule-classes :type-prescription)
               (found-satp booleanp :rule-classes :type-prescription)
               (extdecls$ extdecl-listp))
  :short "Transform an external declaration list."
  :long
  (xdoc::topstring
   (xdoc::p
     "This searches for an external declaration matching the target function.
      When it finds one, it creates the function wrapper. It then substitutes
      the wrapper function for the original function in direct function calls
      occurring in the remainder of the translation unit."))
  (b* (((reterr) nil nil nil)
       ((when (endp extdecls))
        (retok nil nil nil))
       (extdecl (extdecl-fix (first extdecls)))
       ((erp uid? wrapper? wrapper-name?$)
        (extdecl-wrap-fn-add-wrapper-def
          extdecl target-name wrapper-name? blacklist))
       ((when (and uid? wrapper?))
        (retok t
               t
               (list* extdecl
                      (extdecl-fundef wrapper?)
                      (extdecl-list-rename-fn (rest extdecls)
                                              uid?
                                              wrapper-name?$))))
       ((erp foundp$ found-satp extdecls$)
        (extdecl-list-wrap-fn
          (rest extdecls) target-name wrapper-name? blacklist)))
    (retok (if uid?
               t
             foundp$)
           found-satp
           (cons extdecl extdecls$)))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules)))
  ///

  (more-returns
   (extdecls$ true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transunit-wrap-fn
  ((transunit transunitp)
   (target-name identp)
   (wrapper-name? ident-optionp)
   (blacklist ident-setp))
  :guard (c$::transunit-annop transunit)
  :returns (mv (er? maybe-msgp)
               (warnings? maybe-msgp)
               (foundp booleanp :rule-classes :type-prescription)
               (transunit$ transunitp))
  :short "Transform a translation unit."
  (b* (((reterr) nil nil (c$::transunit-fix transunit))
       ((transunit transunit) transunit)
       ((erp foundp found-satp extdecls)
        (extdecl-list-wrap-fn
          transunit.decls target-name wrapper-name? blacklist))
       (warnings?
         (if (and foundp (not found-satp))
             (msg$ "Declaration of ~x0 found, but couldn't create a wrapper."
                   (ident->unwrap target-name))
           nil)))
    (retok warnings?
           foundp
           (c$::change-transunit
             transunit
             :decls extdecls
             :info nil)))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

(define filepath-transunit-map-wrap-fn
  ((map filepath-transunit-mapp)
   (target-name identp)
   (wrapper-name? ident-optionp)
   (blacklist ident-setp))
  :guard (c$::filepath-transunit-map-annop map)
  :returns (mv (er? maybe-msgp)
               (any-foundp booleanp :rule-classes :type-prescription)
               (map$ filepath-transunit-mapp))
  :short "Transform an omap of file paths to translation units."
  (b* ((map (c$::filepath-transunit-map-fix map))
       ((reterr) nil map)
       ((when (omap::emptyp map))
        (retok nil nil))
       ((erp warnings? foundp transunit)
        (transunit-wrap-fn
          (omap::head-val map) target-name wrapper-name? blacklist))
       (-
         (if warnings?
             (cw "Warning in ~x0: ~@1~%"
                 (filepath->unwrap (omap::head-key map))
                 warnings?)
           nil))
       ((erp any-foundp map$)
        (filepath-transunit-map-wrap-fn
          (omap::tail map) target-name wrapper-name? blacklist)))
    (retok (or foundp any-foundp)
           (omap::update (omap::head-key map) transunit map$)))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules)))
  :verify-guards :after-returns)

(define transunit-ensemble-wrap-fn
  ((transunits transunit-ensemblep)
   (target-name identp)
   (wrapper-name? ident-optionp))
  :guard (c$::transunit-ensemble-annop transunits)
  :returns (mv (er? maybe-msgp)
               (transunits$ transunit-ensemblep))
  :short "Transform a translation unit ensemble."
  (b* (((reterr) (c$::transunit-ensemble-fix transunits))
       ((transunit-ensemble transunits) transunits)
       (blacklist (filepath-transunit-map-collect-idents transunits.unwrap))
       ((erp any-foundp map)
        (filepath-transunit-map-wrap-fn
          transunits.unwrap target-name wrapper-name? blacklist))
       (-
         (if any-foundp
             nil
           (cw "Warning: No declaration found for ~x0.~%"
               (ident->unwrap target-name)))))
    (retok (c$::change-transunit-ensemble
             transunits
             :unwrap map)))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

(define code-ensemble-wrap-fn
  ((code code-ensemblep)
   (target-name identp)
   (wrapper-name? ident-optionp))
  :guard (c$::code-ensemble-annop code)
  :returns (mv (er? maybe-msgp)
               (code$ code-ensemblep))
  :short "Transform a code ensemble."
  :long
  (xdoc::topstring
   (xdoc::p
     "The @('target-name') is the function to be wrapped. @('wrapper-name?'),
      if it is non-@('nil'), is the suggested name of the wrapper function. If
      no suggestion is provided, a name will be generated."))
  (b* (((reterr) (c$::code-ensemble-fix code))
       ((code-ensemble code) code)
       ((erp transunits)
        (transunit-ensemble-wrap-fn
          code.transunits target-name wrapper-name?)))
    (retok (c$::change-code-ensemble
             code
             :transunits transunits)))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

(define code-ensemble-wrap-fn-multiple
  ((code code-ensemblep)
   (targets ident-ident-option-mapp))
  :guard (and ;; (code-ensemble-unambp code)
              (c$::code-ensemble-annop code))
  :returns (mv (er? maybe-msgp)
               (code$ code-ensemblep))
  :short "Transform a code ensemble."
  :long
  (xdoc::topstring
   (xdoc::p
     "The @('target-name') is the function to be wrapped. @('wrapper-name?'),
      if it is non-@('nil'), is the suggested name of the wrapper function. If
      no suggestion is provided, a name will be generated."))
  (b* (((reterr) (c$::code-ensemble-fix code))
       (targets (ident-ident-option-map-fix targets))
       ((when (omap::emptyp targets))
        (retok (c$::code-ensemble-fix code)))
       ((erp code)
        (code-ensemble-wrap-fn code
                               (omap::head-key targets)
                               (omap::head-val targets)))
       ;; TODO: prove the above preserves disambiguation.
       ((unless (code-ensemble-unambp code))
        (retmsg$ "Internal error: code has not been disambiguated."))
       ((erp valid-transunits)
        (c$::valid-transunit-ensemble (code-ensemble->transunits code)
                                      (code-ensemble->ienv code)
                                      nil))
       ;; TODO: remove after it is proved that validation produces an annotated
       ;; term.
       ((unless (transunit-ensemble-annop valid-transunits))
        (retmsg$ "Internal error: code is invalid."))
       (code (change-code-ensemble
               code
               :transunits valid-transunits)))
    (code-ensemble-wrap-fn-multiple code (omap::tail targets)))
  :measure (acl2-count (ident-ident-option-map-fix targets))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules
                                            c$::abstract-syntax-unambp-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing wrap-fn)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-string-option-alist-to-ident-ident-option-map
  ((alist string-string-option-alistp))
  :returns (map ident-ident-option-mapp)
  :parents (wrap-fn-input-processing)
  (b* ((alist (string-string-option-alist-fix alist))
       ((when (endp alist))
        nil)
       (ident (ident (car (first alist))))
       (string-option (cdr (first alist)))
       (ident-option (if string-option (ident string-option) nil)))
    (omap::update
      ident
      ident-option
      (string-string-option-alist-to-ident-ident-option-map (rest alist))))
  :measure (acl2-count (string-string-option-alist-fix alist))
  :verify-guards :after-returns)

(define string-list-to-ident-ident-option-map
  ((list string-listp))
  :returns (map ident-ident-option-mapp)
  :parents (wrap-fn-input-processing)
  (b* ((list (str::string-list-fix list))
       ((when (atom list))
        nil))
    (omap::update
      (ident (first list))
      nil
      (string-list-to-ident-ident-option-map (rest list))))
  :measure (acl2-count (str::string-list-fix list))
  :guard-hints (("Goal" :in-theory (enable string-listp)))
  :verify-guards :after-returns)

(define wrap-fn-process-inputs (const-old
                                const-new
                                targets
                                (wrld plist-worldp))
  :returns (mv (er? maybe-msgp)
               (code (and (code-ensemblep code)
                          (c$::code-ensemble-annop code))
                     :hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))
               (const-new$ symbolp)
               (targets ident-ident-option-mapp))
  :parents (wrap-fn-input-processing)
  :short "Process the inputs."
  (b* (((reterr) (c$::irr-code-ensemble) nil nil)
       ((unless (symbolp const-old))
        (retmsg$ "~x0 must be a symbol" const-old))
       (code (acl2::constant-value const-old wrld))
       ((unless (code-ensemblep code))
        (retmsg$ "~x0 must be a code ensemble." const-old))
       ((unless (c$::code-ensemble-annop code))
        (retmsg$ "~x0 must be an annotated with validation information."
                 const-old))
       ((unless (symbolp const-new))
        (retmsg$ "~x0 must be a symbol" const-new))
       ((erp targets)
        (b* (((reterr) nil))
          (cond ((string-listp targets)
                 (retok (string-list-to-ident-ident-option-map targets)))
                ((string-string-option-alistp targets)
                 (retok (string-string-option-alist-to-ident-ident-option-map
                          targets)))
                (t (retmsg$ "~x0 must be a list of strings ~
                             or an alist from strings to optional strings."
                            targets))))))
    (retok code
           const-new
           targets)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation wrap-fn)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define wrap-fn-gen-everything
  ((code code-ensemblep)
   (const-new symbolp)
   (targets ident-ident-option-mapp))
  :guard (c$::code-ensemble-annop code)
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :parents (wrap-fn-event-generation)
  :short "Generate all the events."
  (b* (((reterr) '(_))
       (const-new (mbe :logic (acl2::symbol-fix const-new) :exec const-new))
       ((erp code)
        (code-ensemble-wrap-fn-multiple code targets))
       (defconst-event
         `(defconst ,const-new
            ',code)))
    (retok defconst-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define wrap-fn-process-inputs-and-gen-everything
  (const-old
   const-new
   targets
   (wrld plist-worldp))
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :parents (wrap-fn-event-generation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp code const-new targets)
        (wrap-fn-process-inputs const-old const-new targets wrld))
       ((erp event)
        (wrap-fn-gen-everything code const-new targets)))
    (retok event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define wrap-fn-fn (const-old
                     const-new
                     targets
                     (ctx ctxp)
                     state)
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (event pseudo-event-formp)
               state)
  :parents (wrap-fn-event-generation)
  :short "Event expansion of @(tsee wrap-fn)."
  (b* (((mv erp event)
        (wrap-fn-process-inputs-and-gen-everything const-old
                                                   const-new
                                                   targets
                                                   (w state)))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection wrap-fn-macro-definition
  :parents (wrap-fn-event-generation)
  :short "Definition of @(tsee wrap-fn)."
  (defmacro wrap-fn
    (const-old
     const-new
     &key
     targets)
    `(make-event (wrap-fn-fn ',const-old
                              ',const-new
                              ',targets
                              'wrap-fn
                              state))))
