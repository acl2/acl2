; JSON Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSON")

(include-book "abstract-syntax")
(include-book "parser-output-to-abstract-syntax")
(include-book "light-ast-check")
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
      "http://www.ecma-international.org/publications/files/ECMA-ST/ECMA-404.pdf"
      "ECMA-404 Standard (2nd Edition)")
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
     "."))
   (xdoc::p
    "These are all meant to be consistent,
     at least in defining the JSON format,
     although they may contain slightly different recommendations."))
  :order-subtopics t
  :default-parent t)
