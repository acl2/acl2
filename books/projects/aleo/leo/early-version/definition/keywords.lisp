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

(defxdoc+ keywords
  :parents (concrete-syntax abstract-syntax)
  :short "Leo keywords."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we capture the Leo keywords in ACL2.
     Since they all consist of ASCII characters,
     we can use ACL2 strings for this purpose."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *keywords*
  :short "List of Leo keywords."
  (list "address"
        "async"
        "bool"
        "console"
        "const"
        "constant"
        "decrement"
        "else"
        "field"
        "finalize"
        "for"
        "function"
        "group"
        "i8"
        "i16"
        "i32"
        "i64"
        "i128"
        "if"
        "import"
        "in"
        "increment"
        "let"
        "mapping"
        "program"
        "public"
        "record"
        "return"
        "scalar"
        "string"
        "struct"
        "transition"
        "u8"
        "u16"
        "u32"
        "u64"
        "u128")
  ///
  (assert-event (string-listp *keywords*))
  (assert-event (no-duplicatesp-equal *keywords*)))
