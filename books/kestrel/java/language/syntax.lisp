; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

; the order of the following INCLUDE-BOOKs determines
; the order of the subtopics of the SYNTAX topic below:
(include-book "unicode-characters")
(include-book "grammar")
(include-book "unicode-input-characters")
(include-book "floating-point-literals")
(include-book "integer-literals")
(include-book "null-literal")
(include-book "null-literal-validation")
(include-book "boolean-literals")
(include-book "boolean-literals-validation")
(include-book "keywords")
(include-book "keywords-validation")
(include-book "identifiers")
(include-book "decimal-digits")
(include-book "decimal-digits-validation")
(include-book "decimal-digits-std-strings-theorems")
(include-book "hexadecimal-digits")
(include-book "hexadecimal-digits-validation")
(include-book "hexadecimal-digits-std-strings-theorems")
(include-book "octal-digits")
(include-book "octal-digits-validation")
(include-book "octal-digits-std-strings-theorems")
(include-book "binary-digits")
(include-book "binary-digits-validation")
(include-book "binary-digits-std-strings-theorems")
(include-book "escape-sequences")
(include-book "character-literals")
(include-book "string-literals")
(include-book "literals")
(include-book "package-names")
(include-book "primitive-types")
(include-book "reference-types")
(include-book "unicode-escapes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ syntax
  :parents (language)
  :short "A formal model of some aspects of the syntax of Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is expected that more aspects of the syntax of Java
     will be formalized here over time."))
  :order-subtopics t)
