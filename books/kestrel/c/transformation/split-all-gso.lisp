; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/utilities/messages" :dir :system)

(include-book "../syntax/disambiguator")
(include-book "../syntax/validator")
(include-book "splitgso")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (tau-system))))
(set-induction-depth-limit 0)

(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/state" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation split-all-gso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-declon-get-ident
  ((struct-declon struct-declonp))
  :returns (ident? ident-optionp)
  (struct-declon-case
   struct-declon
   ;; TODO: properly handle struct declarations with multiple declarators
   ;;   instead of returning error.
   :member (b* (((mv erp ident)
                 (struct-declor-list-get-ident struct-declon.declor)))
             (if erp
                 nil
               ident))
   :statassert nil
   :empty nil))

;; TODO: needs to ensure that struct-declons doesn't contain static asserts or empty
(define struct-declons-find-first-field-name
  ((struct-declons struct-declon-listp))
  :returns (ident? ident-optionp)
  (b* (((when (or (endp struct-declons)
                  (endp (rest struct-declons))))
        nil)
       (struct-declon (struct-declon-fix (first struct-declons)))
       (ident? (struct-declon-get-ident struct-declon)))
    (or ident?
        (struct-declons-find-first-field-name (rest struct-declons)))))

(define decl-find-first-field-name
  ((decl declp)
   (struct-tag identp))
  :returns (ident? ident-optionp)
  (decl-case
   decl
   :decl
   (b* ((type-spec? (type-spec-from-decl-specs decl.specs))
        ((unless (and type-spec? (all-no-init decl.init)))
         nil))
     (type-spec-case
       type-spec?
       :struct (b* (((struni-spec struni-spec) type-spec?.spec))
                 (if (equal struni-spec.name? struct-tag)
                     (struct-declons-find-first-field-name struni-spec.members)
                   nil))
       :otherwise nil))
   :statassert nil))

(define extdecl-find-first-field-name
  ((extdecl extdeclp)
   (struct-tag identp))
  :returns (ident? ident-optionp)
  (extdecl-case
   extdecl
   :decl (decl-find-first-field-name extdecl.unwrap struct-tag)
   :otherwise nil))

(define extdecl-list-find-first-field-name
  ((extdecls extdecl-listp)
   (struct-tag identp))
  :returns (ident? ident-optionp)
  (b* (((when (endp extdecls))
        nil)
       (field-name?
        (extdecl-find-first-field-name (first extdecls) struct-tag)))
    (or field-name?
        (extdecl-list-find-first-field-name (rest extdecls) struct-tag))))

(define transunit-find-first-field-name
  ((tunit transunitp)
   (struct-tag identp))
  :returns (ident? ident-optionp)
  (b* (((transunit tunit) tunit))
    (extdecl-list-find-first-field-name tunit.decls struct-tag)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines declor/dirdeclor-get-simple-ident
  :parents (split-all-gso-implementation)
  :short "Get the identifier of a simple (direct) declarator."
  :long
  (xdoc::topstring
   (xdoc::p
     "We define a \"simple\" declarator as an identifier, potentially in nested
      parentheses. It does not have any pointer qualifiers."))

  (define declor-get-simple-ident
    ((declor declorp))
    :returns (ident? ident-optionp)
    (and (endp (c$::declor->pointers declor))
         (dirdeclor-get-simple-ident (declor->direct declor)))
    :measure (declor-count declor))

  (define dirdeclor-get-simple-ident
    ((dirdeclor dirdeclorp))
    :returns (ident? ident-optionp)
    (dirdeclor-case
     dirdeclor
     :ident dirdeclor.ident
     :paren (declor-get-simple-ident dirdeclor.inner)
     :array nil
     :array-static1 nil
     :array-static2 nil
     :array-star nil
     :function-params nil
     :function-names nil)
    :measure (dirdeclor-count dirdeclor))

  :hints (("Goal" :in-theory (enable o< o-finp))))

(define initdeclor-find-gso-candidate
  ((initdeclor initdeclorp))
  :returns (ident? ident-optionp)
  (b* (((initdeclor initdeclor) initdeclor))
    (declor-get-simple-ident initdeclor.declor)))

(define initdeclor-list-find-gso-candidate
  ((initdeclors initdeclor-listp))
  :returns (ident? ident-optionp)
  ;; Only accepts singletons for now
  ;; TODO: broaden this
  (if (or (endp initdeclors)
          (not (endp (rest initdeclors))))
      nil
    (initdeclor-find-gso-candidate (first initdeclors))))

(define decl-find-gso-candidate
  ((decl declp)
   (blacklist ident-setp))
  :returns (ident? ident-optionp)
  (decl-case
   decl
   :decl
   (b* ((type-spec? (type-spec-from-decl-specs decl.specs))
        ((unless type-spec?)
         nil)
        (ident?
          (type-spec-case
            type-spec?
            :struct (initdeclor-list-find-gso-candidate decl.init)
            :typedef (initdeclor-list-find-gso-candidate decl.init)
            :otherwise nil)))
     (if (and ident?
              (in ident? blacklist))
         nil
       ident?))
   :statassert nil))

(define extdecl-find-gso-candidate
  ((extdecl extdeclp)
   (blacklist ident-setp))
  :returns (ident? ident-optionp)
  (extdecl-case
   extdecl
   :fundef nil
   :decl (decl-find-gso-candidate extdecl.unwrap blacklist)
   :empty nil
   :asm nil))

(define extdecl-list-find-gso-candidate
  ((extdecls extdecl-listp)
   (blacklist ident-setp))
  :returns (ident? ident-optionp)
  (b* (((when (endp extdecls))
        nil)
       (ident? (extdecl-find-gso-candidate (first extdecls) blacklist)))
    (or ident?
        (extdecl-list-find-gso-candidate (rest extdecls) blacklist))))

(define transunit-find-gso-candidate
  ((tunit transunitp)
   (blacklist ident-setp))
  :guard (c$::transunit-annop tunit)
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (gso identp)
               (field-name identp)
               (internal booleanp :rule-classes :type-prescription))
  (transunit-find-gso-candidate0
   tunit
   blacklist
   (acl2::the-fixnat (- (expt 2 acl2::*fixnat-bits*) 1)))

  :prepwork
  ((define transunit-find-gso-candidate0
     ((tunit transunitp)
      (blacklist ident-setp)
      (steps :type #.acl2::*fixnat-type*))
     :guard (c$::transunit-annop tunit)
     :returns (mv (erp booleanp :rule-classes :type-prescription)
                  (gso identp)
                  (field-name identp)
                  (internal booleanp :rule-classes :type-prescription))
     (b* (((reterr) (c$::irr-ident) (c$::irr-ident) nil)
          ((transunit tunit) tunit)
          ((when (= 0 (mbe :logic (nfix steps)
                           :exec (acl2::the-fixnat steps))))
           (reterr t))
          (gso (extdecl-list-find-gso-candidate tunit.decls blacklist))
          ((unless gso)
           (reterr t))
          ((mv erp linkage tag?)
           (get-gso-linkage-from-valid-table
             gso
             (c$::transunit-info->table-end (c$::transunit->info tunit))))
          ((when erp)
           (transunit-find-gso-candidate0 tunit
                                          (insert gso blacklist)
                                          (- steps 1)))
          ((unless tag?)
           (reterr t))
          (field-name (transunit-find-first-field-name tunit tag?))
          ((unless field-name)
           (reterr t)))
       (retok gso field-name (equal linkage (c$::linkage-internal))))
     :measure (nfix steps)
     :hints (("Goal" :in-theory (enable o< o-finp nfix)))
     :guard-hints (("Goal" :in-theory (enable nfix c$::transunit-annop))))))

(define filepath-transunit-map-find-gso-candidate
  ((map filepath-transunit-mapp)
   (blacklist ident-setp))
  :guard (c$::filepath-transunit-map-annop map)
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (filepath? c$::filepath-optionp)
               (gso identp)
               (field-name identp))
  (b* (((reterr) nil (c$::irr-ident) (c$::irr-ident))
       (map (c$::filepath-transunit-map-fix map))
       ((when (omap::emptyp map))
        (reterr t))
       ((mv erp gso field-name internal)
        (transunit-find-gso-candidate
          (omap::head-val map)
          blacklist))
       ((unless erp)
        (retok (and internal (omap::head-key map)) gso field-name)))
    (filepath-transunit-map-find-gso-candidate (omap::tail map) blacklist))
  :guard-hints
  (("Goal" :in-theory (acl2::enable* c$::abstract-syntax-annop-rules))))

(define transunit-ensemble-find-gso-candidate
  ((tunits transunit-ensemblep)
   (blacklist ident-setp))
  :guard (c$::transunit-ensemble-annop tunits)
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (filepath? c$::filepath-optionp)
               (gso identp)
               (field-name identp))
  (b* (((transunit-ensemble tunits) tunits))
    (filepath-transunit-map-find-gso-candidate tunits.unwrap blacklist))
  :guard-hints (("Goal" :in-theory (enable c$::transunit-ensemble-annop))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transunit-ensemble-split-any-gso
  ((tunits transunit-ensemblep)
   (blacklist ident-setp))
  :guard (c$::transunit-ensemble-annop tunits)
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (blacklist$ ident-setp)
               (tunits$ transunit-ensemblep))
  (transunit-ensemble-split-any-gso0
    tunits
    blacklist
    (acl2::the-fixnat (- (expt 2 acl2::*fixnat-bits*) 1)))

  :prepwork
  ((define transunit-ensemble-split-any-gso0
     ((tunits transunit-ensemblep)
      (blacklist ident-setp)
      (steps :type #.acl2::*fixnat-type*))
     :guard (c$::transunit-ensemble-annop tunits)
     :returns (mv (erp booleanp :rule-classes :type-prescription)
                  (blacklist$ ident-setp)
                  (tunits$ transunit-ensemblep))
     (b* (((reterr) nil (c$::transunit-ensemble-fix tunits))
          (blacklist (ident-set-fix blacklist))
          ((when (= 0 (mbe :logic (nfix steps)
                           :exec (acl2::the-fixnat steps))))
           (reterr t))
          ((erp filepath? gso field-name)
           (transunit-ensemble-find-gso-candidate tunits blacklist))
          ((mv erp tunits$)
           (splitgso-transunit-ensemble filepath?
                                        gso
                                        nil
                                        nil
                                        nil
                                        nil
                                        (list field-name)
                                        tunits))
          ((when erp)
           (transunit-ensemble-split-any-gso0 tunits
                                              (insert gso blacklist)
                                              (- steps 1))))
       (retok blacklist tunits$))
     :measure (nfix steps)
     :hints (("Goal" :in-theory (enable o< o-finp nfix)))
     :guard-hints (("Goal" :in-theory (enable nfix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transunit-ensemble-split-all-gso
  ((tunits transunit-ensemblep)
   (blacklist ident-setp)
   (ienv c$::ienvp))
  :guard (c$::transunit-ensemble-annop tunits)
  :returns (mv (er? maybe-msgp)
               (blacklist$ ident-setp)
               (tunits$ transunit-ensemblep))
  (transunit-ensemble-split-all-gso0
   tunits
   blacklist
   ienv
   (acl2::the-fixnat (- (expt 2 acl2::*fixnat-bits*) 1)))

  :prepwork
  ((define transunit-ensemble-split-all-gso0
     ((tunits transunit-ensemblep)
      (blacklist ident-setp)
      (ienv c$::ienvp)
      (steps :type #.acl2::*fixnat-type*))
     :guard (c$::transunit-ensemble-annop tunits)
     :returns (mv (er? maybe-msgp)
                  (blacklist$ ident-setp)
                  ;; add annop
                  (tunits$ transunit-ensemblep))
     (b* ((tunits (c$::transunit-ensemble-fix tunits))
          (blacklist (ident-set-fix blacklist))
          ((reterr) nil tunits)
          ((when (int= 0 (mbe :logic (nfix steps)
                              :exec (acl2::the-fixnat steps))))
           (retmsg$ "Out of steps."))
          ((mv erp blacklist tunits$)
           (transunit-ensemble-split-any-gso
             tunits
             blacklist))
          ((when erp)
           (retok blacklist tunits))
          ;; TODO: prove that splitgso preserves unambiguity and validity
          ;;   (it likely doesn't preserve the latter currently).
          ((erp tunits$)
           (c$::dimb-transunit-ensemble tunits$ (c$::ienv->gcc ienv)))
          ((erp tunits$)
           (c$::valid-transunit-ensemble tunits$ ienv))
          ;; TODO: c$::valid-transunit-ensemble should return an annop
          ((unless (c$::transunit-ensemble-annop tunits$))
           (retmsg$ "Invalid translation unit ensemble.")))
       (transunit-ensemble-split-all-gso0 tunits$
                                          blacklist
                                          ienv
                                          (- steps 1)))
     :measure (nfix steps)
     :hints (("Goal" :in-theory (enable o< o-finp nfix)))
     :guard-hints (("Goal" :in-theory (enable nfix))))))

(define code-ensemble-split-all-gso
  ((code code-ensemblep)
   (blacklist ident-setp))
  :guard (c$::transunit-ensemble-annop (code-ensemble->transunits code))
  :returns (mv (er? maybe-msgp)
               (blacklist$ ident-setp)
               (code$ code-ensemblep))
  (b* (((reterr) nil (irr-code-ensemble))
       ((code-ensemble code) code)
       ((erp blacklist tunits)
        (transunit-ensemble-split-all-gso code.transunits
                                          blacklist
                                          code.ienv)))
    (retok blacklist (change-code-ensemble code :transunits tunits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing split-all-gso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-all-gso-process-inputs
  (const-old
   const-new
   (wrld plist-worldp))
  :returns (mv (er? maybe-msgp)
               (code (and (code-ensemblep code)
                          (c$::transunit-ensemble-annop
                           (code-ensemble->transunits code)))
                     :hints (("Goal" :in-theory (enable irr-code-ensemble
                                                        irr-transunit-ensemble))))
               (const-new$ symbolp :rule-classes :type-prescription))
  :short "Process the inputs."
  (b* (((reterr) (irr-code-ensemble) nil)
       ((unless (symbolp const-old))
        (retmsg$ "~x0 must be a symbol" const-old))
       (code (acl2::constant-value const-old wrld))
       ((unless (code-ensemblep code))
        (retmsg$ "~x0 must be a code ensemble." const-old))
       ((unless (c$::transunit-ensemble-annop (code-ensemble->transunits code)))
        (retmsg$ "~x0 must be an annotated with validation information." const-old))
       ((unless (symbolp const-new))
        (retmsg$ "~x0 must be a symbol" const-new)))
    (retok code const-new)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation split-all-gso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-all-gso-gen-everything
  ((code code-ensemblep)
   (const-new symbolp))
  :guard (c$::transunit-ensemble-annop (code-ensemble->transunits code))
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :short "Generate all the events."
  (b* (((reterr) '(_))
       ((erp - code)
        (code-ensemble-split-all-gso code nil))
       (defconst-event
         `(defconst ,const-new
            ',code)))
    (retok defconst-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-all-gso-process-inputs-and-gen-everything
  (const-old
   const-new
   (wrld plist-worldp))
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :parents (split-all-gso-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp code const-new)
        (split-all-gso-process-inputs const-old const-new wrld))
       ((erp event)
        (split-all-gso-gen-everything code const-new)))
    (retok event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-all-gso-fn (const-old
                          const-new
                          (ctx ctxp)
                          state)
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (event pseudo-event-formp)
               state)
  :parents (split-all-gso-implementation)
  :short "Event expansion of @(tsee split-all-gso)."
  (b* (((mv erp event)
        (split-all-gso-process-inputs-and-gen-everything
          const-old
          const-new
          (w state)))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection split-all-gso-macro-definition
  :parents (split-all-gso-implementation)
  :short "Definition of @(tsee split-all-gso)."
  (defmacro split-all-gso
    (const-old
     const-new)
    `(make-event (split-all-gso-fn ',const-old
                                   ',const-new
                                   'split-all-gso
                                   state))))
