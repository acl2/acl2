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

(include-book "expressions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ output-files
  :parents (abstract-syntax)
  :short "Leo output files."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides files with code, formalized by @(tsee file),
     and files with inputs, formalized by @(tsee input-file),
     Leo includes files with outputs.
     These are formalized here,
     in abstract syntax form,
     based on the ABNF output grammar."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod output-expression
  :short "Fixtype of output expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a wrapper of expression,
     but only "
    (xdoc::seetopic "value-expressions" "value expressions")
    " are allowed, which is enforced in the static semantics."))
  ((get expression))
  :tag :output-expression
  :pred output-expressionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult output-expression-result
  :short "Fixtype of errors and Leo output expressions."
  :ok output-expression
  :pred output-expression-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod output-item
  :short "Fixtype of output items."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a wrapper of output expressions."))
  ((get output-expression))
  :tag :output-item
  :pred output-itemp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult output-item-result
  :short "Fixtype of errors and Leo output items."
  :ok output-item
  :pred output-item-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod output-section
  :short "Fixtype of output sections."
  :long
  (xdoc::topstring
   (xdoc::p
    "We just wrap an output item,
     because the output title carries no information."))
  ((item output-item))
  :tag :output-section
  :pred output-sectionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult output-section-result
  :short "Fixtype of errors and Leo output sections."
  :ok output-section
  :pred output-section-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod output-file
  :short "Fixtype of output files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just a wrapper of an output section."))
  ((get output-section))
  :tag :output-file
  :pred output-filep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult output-file-result
  :short "Fixtype of errors and Leo output files."
  :ok output-file
  :pred output-file-resultp)
