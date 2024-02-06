; JSON Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSON")

(include-book "syntax")
(include-book "values")
(include-book "operations")
(include-book "parser-output-to-values")
(include-book "light-value-check")
(include-book "json-bstar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ json
  :parents (acl2::kestrel-books acl2::projects)
  :short "A library for JSON."
  :long
  (xdoc::topstring
   (xdoc::p
    "The JavaScript Object Notation (JSON) is described by:")
   (xdoc::ul
    (xdoc::li
     "The " (xdoc::ahref "http://www.json.org" "JSON web site") ".")
    (xdoc::li
     "The "
     (xdoc::ahref
      "https://www.ecma-international.org/publications-and-standards/standards/ecma-404"
      "ECMA-404 Standard (2nd Edition, December 2017)")
     ".")
    (xdoc::li
     "The "
     (xdoc::ahref "https://www.iso.org/standard/71616.html"
                  "ISO/IEC 21778:2017 Standard")
     ".")
    (xdoc::li
     "The "
     (xdoc::ahref "https://tools.ietf.org/html/rfc8259"
                  "RFC 8259")
     ", including "
     (xdoc::ahref "https://www.rfc-editor.org/errata/rfc8259"
                  "errata")
     "."))
   (xdoc::p
    "These are all meant to be consistent,
     at least in defining the JSON format,
     although they may contain
     slightly different notations and recommendations.")
   (xdoc::p
    "Currently this library contains:")
   (xdoc::ul
    (xdoc::li
     "A formalization of the syntax of JSON,
      based on the ABNF grammar in the RFC.")
    (xdoc::li
     "A formalization of JSON values.")
    (xdoc::li
     "Some operations on JSON values,
      including some lightweight checkers.")
    (xdoc::li
     "A translator from the output of
      the JSON parser in @('kestrel/json-parser/')
      to the JSON value representation defined in this library.")
    (xdoc::li
     "@(tsee b*) binders for
      the representation of JSON values defined in this library.")))
  :order-subtopics t
  :default-parent t)
