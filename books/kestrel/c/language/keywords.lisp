; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
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
    "These are listed in [C17:6.4.1]:")
   (xdoc::codeblock
    "auto       extern     short      while"
    "break      float      signed     _Alignas"
    "case       for        sizeof     _Alignof"
    "char       goto       static     _Atomic"
    "const      if         struct     _Bool"
    "continue   inline     switch     _Complex"
    "default    int        typedef    _Generic"
    "do         long       union      _Imaginary"
    "double     register   unsigned   _Noreturn"
    "else       restrict   void       _Static_assert"
    "enum       return     volatile   _Thread_local")
   (xdoc::p
    "They consist of all ASCII characters,
     and therefore they are directly representable as ACL2 strings."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *keywords*
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
  (assert-event (string-listp *keywords*))
  (assert-event (no-duplicatesp-equal *keywords*)))
