; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2020 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "std/util/defval" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ keywords
  :parents (language)
  :short "Keywords of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are listed in [C:6.4.1].")
   (xdoc::p
    "They consist of all ASCII characters,
     and therefore they are directly representable as ACL2 strings.")
   (xdoc::p
    "Given that ACL2 has keywords,
     we use `@('ckeyword')' (instead of just `@('keyword')')
     in the names of functions, constants, and fixtypes
     related to C keywords."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *ckeywords*
  :short "List of the keywords of C, as ACL2 strings."
  '("auto"
    "break"
    "case"
    "char"
    "const"
    "continue"
    "default"
    "do"
    "double"
    "else"
    "enum"
    "extern"
    "float"
    "for"
    "goto"
    "if"
    "inline"
    "int"
    "long"
    "register"
    "restrict"
    "return"
    "short"
    "signed"
    "sizeof"
    "static"
    "struct"
    "switch"
    "typedef"
    "union"
    "unsigned"
    "void"
    "volatile"
    "while"
    "_Alignas"
    "_Alignof"
    "_Atomic"
    "_Bool"
    "_Complex"
    "_Generic"
    "_Imaginary"
    "_Noreturn"
    "_Static_assert"
    "_Thread_local")
  ///
  (assert-event (string-listp *ckeywords*))
  (assert-event (no-duplicatesp-equal *ckeywords*)))
