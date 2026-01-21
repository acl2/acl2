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

(include-book "std/util/defval" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ symbols
  :parents (concrete-syntax abstract-syntax)
  :short "Leo symbols."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we capture the Leo symbols in ACL2.
     Since they all consist of ASCII characters,
     we can use ACL2 strings for this purpose."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *symbols*
  :short "List of Leo symbols."
  (list "!"
        "&&"
        "||"
        "=="
        "!="
        "<"
        "<="
        ">"
        ">="
        "&"
        "|"
        "^"
        "<<"
        ">>"
        "+"
        "-"
        "*"
        "/"
        "%"
        "**"
        "="
        "+="
        "-="
        "*="
        "/="
        "%="
        "**="
        "<<="
        ">>="
        "&="
        "|="
        "^="
        "&&="
        "||="
        "("
        ")"
        "["
        "]"
        "{"
        "}"
        ","
        "."
        ".."
        ";"
        ":"
        "::"
        "?"
        "->"
        "=>"
        "_"
        ")group")
  ///
  (assert-event (string-listp *symbols*))
  (assert-event (no-duplicatesp-equal *symbols*)))
