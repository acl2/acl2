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

(include-book "centaur/fty/deftypes" :dir :system)

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/code-ensembles")
(include-book "../syntax/stringization")
(include-book "utilities/add-attributes")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/system/w" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation add-section-attr
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist qualified-ident-string-alist
  :key-type qualified-ident
  :val-type string
  :fix qualified-ident-string-alist-fix
  :pred qualified-ident-string-alistp
  :true-listp t
  :prepwork ((set-induction-depth-limit 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define elaborate-qualified-ident-string-alist
  ((alist qualified-ident-string-alistp))
  :returns (map qualified-ident-attrib-spec-list-mapp)
  (b* ((alist (qualified-ident-string-alist-fix alist))
       ((when (endp alist))
        nil)
       (key (car (first alist)))
       (val (cdr (first alist)))
       (attrib-name (c$::attrib-name-ident (ident "section")))
       (attrib-param
         (make-expr-string
           :strings (list (c$::make-stringlit
                            :prefix? nil
                            :schars (c$::stringize-astring val)))))
       (attrib-spec
         (c$::make-attrib-spec
           :uscores t
           :attribs (list (c$::make-attrib-name-params
                            :name attrib-name
                            :params (list attrib-param))))))
    (omap::update key
                  (list attrib-spec)
                  (elaborate-qualified-ident-string-alist (rest alist))))
  :measure (acl2-count (qualified-ident-string-alist-fix alist))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-ensemble-add-section-attr
  ((code code-ensemblep)
   (attrs qualified-ident-string-alistp))
  :guard (code-ensemble-annop code)
  :returns (mv (er? maybe-msgp)
               (new-code code-ensemblep))
  :short "Transform a code ensemble."
  (b* (((code-ensemble code) code)
       ((reterr) (irr-code-ensemble))
       (attrs (elaborate-qualified-ident-string-alist attrs))
       ((transunit-ensemble transunits) code.transunits)
       ((erp transunits)
        (transunit-ensemble-add-attributes-with-qualified-idents
          transunits
          attrs)))
    (retok (change-code-ensemble code :transunits transunits)))
  :verbosep t
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing add-section-attr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-section-attr-process-inputs
  (const-old
   const-new
   attrs
   (wrld plist-worldp))
  :returns (mv (er? maybe-msgp)
               (code (code-ensemblep code))
               (const-new$ symbolp)
               (attrs$ qualified-ident-string-alistp))
  :short "Process the inputs."
  (b* (((reterr) (irr-code-ensemble) nil nil)
       ((unless (symbolp const-old))
        (retmsg$ "~x0 must be a symbol." const-old))
       (code (acl2::constant-value const-old wrld))
       ((unless (code-ensemblep code))
        (retmsg$ "~x0 must be a code ensemble." const-old))
       ((unless (code-ensemble-annop code))
        (retmsg$ "~x0 must be annotated with validation information."
                 const-old))
       ((unless (symbolp const-new))
        (retmsg$ "~x0 must be a symbol." const-new))
       ((unless (qualified-ident-string-alistp attrs))
        (retmsg$ "~x0 must be an alist from qualified identifiers to strings."
                 attrs)))
    (retok code const-new attrs))
  ///

  (defret code-ensemble-annop-of-add-section-attr-process-inputs.code
    (implies (not er?)
             (code-ensemble-annop code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation add-section-attr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-section-attr-gen-everything
  ((code code-ensemblep)
   (const-new symbolp)
   (attrs qualified-ident-string-alistp))
  :guard (code-ensemble-annop code)
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :short "Generate all the events."
  (b* (((reterr) '(_))
       (const-new (mbe :logic (acl2::symbol-fix const-new)
                       :exec const-new))
       ((erp code)
        (code-ensemble-add-section-attr code attrs))
       (defconst-event
         `(defconst ,const-new
            ',code)))
    (retok defconst-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-section-attr-process-inputs-and-gen-everything
  (const-old
   const-new
   attrs
   (wrld plist-worldp))
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp code const-new attrs)
        (add-section-attr-process-inputs const-old const-new attrs wrld))
       ((erp event)
        (add-section-attr-gen-everything code const-new attrs)))
    (retok event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-section-attr-fn
  (const-old
   const-new
   attrs
   (ctx ctxp)
   state)
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (event pseudo-event-formp)
               state)
  :short "Event expansion of @(tsee add-section-attr)."
  (b* (((mv erp event)
        (add-section-attr-process-inputs-and-gen-everything
          const-old const-new attrs (w state)))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection add-section-attr-macro-definition
  :short "Definition of @(tsee add-section-attr)."
  (defmacro add-section-attr
    (const-old
     const-new
     &key
     attrs)
    `(make-event (add-section-attr-fn ',const-old
                                      ',const-new
                                      ,attrs
                                      'add-section-attr
                                      state))))
