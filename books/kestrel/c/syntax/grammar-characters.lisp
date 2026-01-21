; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "std/typed-lists/nat-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-characters
  :parents (concrete-syntax)
  :short "Characters allowed by the grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce predicates to check whether character codes
     correspond to characters allowed by the grammar.
     Recall that we commit to Unicode characters,
     so these are Unicode scalar values."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define grammar-character-p ((char natp))
  :returns (yes/no booleanp)
  :short "Check if a character (code) is valid according to the ABNF grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is based on the definition of @('character') in the ABNF grammar.
     At some point we should prove that
     this definition is consistent with that ABNF grammar rule."))
  (or (and (<= 9 char) (<= char 13))
      (and (<= 32 char) (<= char 126))
      (and (<= #x80 char) (<= char #x2029))
      (and (<= #x202f char) (<= char #x2065))
      (and (<= #x206a char) (<= char #xd7ff))
      (and (<= #xe000 char) (<= char #x10ffff))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist grammar-character-listp (x)
  :guard (nat-listp x)
  :short "Check if all the characters (codes) in a list
          are valid according to the ABNF grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee grammar-character-p) to lists of natural numbers."))
  (grammar-character-p x))
