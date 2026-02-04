; C Library
;
; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
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

(include-book "std/util/error-value-tuples" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)

(include-book "../../syntax/abstract-syntax-operations")
(include-book "../../syntax/validation-information")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod qualified-ident
  :parents (utilities)
  :short "Fixtype for fully qualified identifiers."
  :long
  (xdoc::topstring
    (xdoc::p
      "This fixtype tags an identifier with an optional filepath. If present,
       the filepath names the translation unit in which the identifier is
       declared/defined.")
    (xdoc::p
      "Qualified identifiers are used to refer unambiguously to a file-scope
       identifier when working with a translation unit ensemble. Identifiers
       with internal linkage require the filepath to disambiguate them from
       other possible objects/functions of the same name defined in different
       translation units. Identifiers with external linkage do not require a
       filepath since they must be unique across the translation unit ensemble.
       However, a filepath may be provided nonetheless."))
  ((filepath? c$::filepath-option)
   (ident ident))
  :pred qualified-identp)

(fty::defoption qualified-ident-option
  qualified-ident
  :pred qualified-ident-optionp)

(fty::defset qualified-ident-option-set
  :elt-type qualified-ident-option
  :elementp-of-nil t
  :pred qualified-ident-option-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define qualified-ident-externalp
  ((ident qualified-identp))
  (declare (xargs :type-prescription
                  (booleanp (qualified-ident-externalp ident))))
  :parents (qualified-ident)
  (not (qualified-ident->filepath? ident)))

;; TODO: rename. A qualified identifier with an explicit filepath may still
;; have external linkage.
(define qualified-ident-internalp
  ((ident qualified-identp))
  (declare (xargs :type-prescription
                  (booleanp (qualified-ident-internalp ident))))
  :parents (qualified-ident)
  (and (qualified-ident->filepath? ident) t))

(defrule qualified-ident-internalp-becomes-not-qualified-ident-externalp
  (equal (qualified-ident-internalp ident)
         (not (qualified-ident-externalp ident)))
  :enable (qualified-ident-internalp
           qualified-ident-externalp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define external-ident
  ((ident identp))
  :returns (qualified-ident qualified-identp)
  :parents (qualified-ident)
  (make-qualified-ident
   :ident ident))

(defrule qualified-ident-externalp-of-external-ident
  (qualified-ident-externalp (external-ident ident))
  :enable (qualified-ident-externalp
           external-ident))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define internal-ident
  ((filepath filepathp)
   (ident identp))
  :returns (qualified-ident qualified-identp)
  :parents (qualified-ident)
  (make-qualified-ident
   :filepath? (c$::filepath-fix filepath)
   :ident ident))

(defrule qualified-ident-internalp-of-internal-ident
  (qualified-ident-internalp (internal-ident filepath ident))
  :enable (qualified-ident-internalp
           internal-ident)
  :disable qualified-ident-internalp-becomes-not-qualified-ident-externalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-declor-list-resolve-qualified-ident
  ((qual-ident qualified-identp)
   (declors init-declor-listp))
  :guard (init-declor-list-annop declors)
  :returns (mv (er? maybe-msgp)
               (uid? c$::uid-optionp))
  (b* (((reterr) nil)
       ((qualified-ident qual-ident) qual-ident)
       ((when (endp declors))
        (retok nil))
       ((init-declor declor) (first declors))
       ((when (equal (declor->ident declor.declor) qual-ident.ident))
        (b* (((unless (c$::init-declor-infop declor.info))
              (retmsg$ "Initializer declarator info is not well-formed."))
             (uid? (c$::init-declor-info->uid? declor.info))
             ((unless uid?)
              ;; TODO: should this be an error?
              (retok nil)))
          (retok uid?))))
    (init-declor-list-resolve-qualified-ident qual-ident
                                              (rest declors)))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

(define ext-declon-resolve-qualified-ident
  ((qual-ident qualified-identp)
   (declon ext-declonp))
  :guard (ext-declon-annop declon)
  :returns (mv (er? maybe-msgp)
               (uid? c$::uid-optionp))
  (b* (((reterr) nil)
       ((qualified-ident qual-ident) qual-ident))
    (ext-declon-case
      declon
      :fundef
      (b* (((fundef declon.fundef) declon.fundef)
           ((unless (equal (declor->ident declon.fundef.declor) qual-ident.ident))
            (retok nil))
           ((unless (fundef-infop declon.fundef.info))
            (retmsg$ "Function definition info is not well-formed.")))
        (retok (c$::fundef-info->uid declon.fundef.info)))
      :declon
      (declon-case
        declon.declon
        :declon (init-declor-list-resolve-qualified-ident
                  qual-ident
                  (declon-declon->declors declon.declon))
        :statassert (retok nil))
      :otherwise (retok nil)))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

(define ext-declon-list-resolve-qualified-ident
  ((qual-ident qualified-identp)
   (declons ext-declon-listp))
  :guard (ext-declon-list-annop declons)
  :returns (mv (er? maybe-msgp)
               (uid c$::uidp))
  (b* (((reterr) (c$::irr-uid))
       ((qualified-ident qual-ident) qual-ident)
       ((when (endp declons))
        (retmsg$ "~x0 is not an object or function ~
                  with internal linkage in translation unit ~x1."
                 qual-ident.ident
                 qual-ident.filepath?))
       ((erp uid?)
        (ext-declon-resolve-qualified-ident qual-ident (first declons)))
       ((when uid?)
        (retok uid?)))
    (ext-declon-list-resolve-qualified-ident qual-ident
                                             (rest declons)))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

(define transunit-resolve-qualified-ident
  ((qual-ident qualified-identp)
   (transunit transunitp))
  :guard (transunit-annop transunit)
  :returns (mv (er? maybe-msgp)
               (uid c$::uidp))
  (ext-declon-list-resolve-qualified-ident qual-ident
                                           (transunit->declons transunit))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

;; MOVE
(defrule transunit-annop-of-cdr-assoc
  (implies (and (filepath-transunit-map-annop map)
                (filepath-transunit-mapp map)
                (omap::assoc filepath map))
           (transunit-annop (cdr (omap::assoc filepath map))))
  :induct t
  :enable (omap::assoc
           filepath-transunit-map-annop))

(define resolve-qualified-ident
  ((qual-ident qualified-identp)
   (ensemble transunit-ensemblep))
  :guard (transunit-ensemble-annop ensemble)
  :returns (mv (er? maybe-msgp)
               (uid c$::uidp))
  (b* (((reterr) (c$::irr-uid))
       ((qualified-ident qual-ident) qual-ident)
       ((unless qual-ident.filepath?)
        (b* (((c$::valid-table valid-table)
              (c$::transunit-ensemble-info->table-end
                (c$::transunit-ensemble->info ensemble)))
             (info? (omap::assoc qual-ident.ident valid-table.externals))
             ((unless info?)
              (retmsg$ "~x0 is not an object or function ~
                        with external linkage."
                       qual-ident.ident))
             ((c$::valid-ext-info info) (cdr info?)))
          (retok info.uid)))
       ((unless qual-ident.filepath?)
        (retmsg$ "~x0 is not an object or function ~
                  with external linkage."
                 qual-ident.ident))
       (transunit? (omap::assoc qual-ident.filepath?
                                (transunit-ensemble->units ensemble)))
       ((unless transunit?)
        (retmsg$ "~x0 is not a translation unit in the ensemble."
                 qual-ident.filepath?)))
    (transunit-resolve-qualified-ident qual-ident (cdr transunit?)))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))
