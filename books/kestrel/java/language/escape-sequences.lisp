; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "kestrel/fty/ubyte8" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum escape-sequence
  :parents (syntax)
  :short "Fixtype of escape sequences [JLS:3.10.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the escape sequences for character and string literals,
     not the Unicode escapes
     formalized " (xdoc::seetopic "unicode-escapes" "here") ".")
   (xdoc::p
    "There are eight escape sequences each of which
     consist of a backslash followed by another character (e.g. @('\\b')),
     and 256 octal escape sequences.
     Here we formalize them at a slightly more abstract level
     than their concrete syntactic representation in the grammar.
     Our fixtype should be isomorphic to
     the set of grammar strings or trees;
     but this remains to be formally proved."))
  (:b ())
  (:t ())
  (:n ())
  (:f ())
  (:r ())
  (:double-quote ())
  (:single-quote ())
  (:backslash ())
  (:octal ((value ubyte8))))
