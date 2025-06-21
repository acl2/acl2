; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "files")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ input-files
  :parents (abstract-syntax)
  :short "Leo input files."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides files with code, formalized by @(tsee file),
     Leo includes files with inputs.
     These are formalized here,
     in abstract syntax form,
     based on the ABNF input grammar."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod input-type
  :short "Fixtype of input types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is currently a wrapper of any type,
     but it may be more restricted in the future;
     thus, we introduce a separate fixtype for easier future change."))
  ((get type))
  :tag :input-type
  :pred input-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult input-type-result
  :short "Fixtype of errors and Leo input files."
  :ok input-type
  :pred input-type-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod input-expression
  :short "Fixtype of input expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a wrapper of expression,
     but only "
    (xdoc::seetopic "value-expressions" "value expressions")
    " are allowed, which is enforced in the static semantics."))
  ((get expression))
  :tag :input-expression
  :pred input-expressionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult input-expression-result
  :short "Fixtype of errors and Leo input expressions."
  :ok input-expression
  :pred input-expression-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod input-item
  :short "Fixtype of input items."
  ((name identifier)
   (type input-type)
   (value input-expression))
  :tag :input-item
  :pred input-itemp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist input-item-list
  :short "Fixtype of input items."
  :elt-type input-item
  :true-listp t
  :elementp-of-nil nil
  :pred input-item-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult input-item-result
  :short "Fixtype of errors and Leo input items."
  :ok input-item
  :pred input-item-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult input-item-list-result
  :short "Fixtype of errors and lists of Leo input items."
  :ok input-item-list
  :pred input-item-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod input-title
  :short "Fixtype of input titles."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a wrapper of @(tsee var/const-sort)."))
  ((sort var/const-sort))
  :tag :input-title
  :pred input-titlep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist input-title-list
  :short "Fixtype of lists of input titles."
  :elt-type input-title
  :true-listp t
  :elementp-of-nil nil
  :pred input-title-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption input-title-option
  input-title
  :short "Fixtype of optional input titles."
  :pred input-title-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult input-title-result
  :short "Fixtype of errors and Leo input titles."
  :ok input-title
  :pred input-title-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult input-title-option-result
  :short "Fixtype of errors and optional input titles."
  :ok input-title-option
  :pred input-title-option-resultp
  :prepwork ((local (in-theory (enable input-titlep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod input-section
  :short "Fixtype of input sections."
  ((title input-title)
   (items input-item-list))
  :tag :input-section
  :pred input-sectionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist input-section-list
  :short "Fixtype of input sections."
  :elt-type input-section
  :true-listp t
  :elementp-of-nil nil
  :pred input-section-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption input-section-option
  input-section
  :short "Fixtype of optional input sections."
  :pred input-section-optionp)

;;;;;;;;;;;;;;;;;;;;

(std::defprojection input-section-list->title-list (x)
  :guard (input-section-listp x)
  :returns (titles input-title-listp)
  :short "Lift @(tsee input-section->title) to lists."
  (input-section->title x)
  ///
  (fty::deffixequiv input-section-list->title-list
    :args ((x input-section-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult input-section-result
  :short "Fixtype of errors and Leo input sections."
  :ok input-section
  :pred input-section-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult input-section-option-result
  :short "Fixtype of errors and optional input sections."
  :ok input-section-option
  :pred input-section-option-resultp
  :prepwork ((local (in-theory (enable input-sectionp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult input-section-list-result
  :short "Fixtype of errors and lists of Leo input sections."
  :ok input-section-list
  :pred input-section-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod input-file
  :short "Fixtype of input files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just a wrapper of a list of input sections."))
  ((sections input-section-list))
  :tag :input-file
  :pred input-filep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult input-file-result
  :short "Fixtype of errors and Leo input files."
  :ok input-file
  :pred input-file-resultp)
