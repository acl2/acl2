; C Library
;
; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

;; (include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)
;; (include-book "std/basic/two-nats-measure" :dir :system)

(include-book "../../syntax/abstract-syntax-operations")
;; (include-book "../../syntax/validaton-information")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(acl2::controlled-configuration)

;; (local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

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
