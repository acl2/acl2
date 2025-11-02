; Java Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "unicode-characters")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ keywords
  :parents (syntax)
  :short "The Java keywords [JLS25:3.9]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some character sequences are Java keywords in all contexts,
     namely the reserved keywords.
     Other character sequences are Java keywords
     only in certain module-related contexts,
     namely the contextual keywords."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *reserved-keywords*
  :short "The reserved Java keywords, as ACL2 strings."
  (list "abstract"
        "assert"
        "boolean"
        "break"
        "byte"
        "case"
        "catch"
        "char"
        "class"
        "const"
        "continue"
        "default"
        "do"
        "double"
        "else"
        "enum"
        "extends"
        "final"
        "finally"
        "float"
        "for"
        "if"
        "goto"
        "implements"
        "import"
        "instanceof"
        "int"
        "interface"
        "long"
        "native"
        "new"
        "package"
        "private"
        "protected"
        "public"
        "return"
        "short"
        "static"
        "strictfp"
        "super"
        "switch"
        "synchronized"
        "this"
        "throw"
        "throws"
        "transient"
        "try"
        "void"
        "volatile"
        "while"
        "_")

  ///

  (assert-event (string-listp *reserved-keywords*))

  (assert-event (= (len *reserved-keywords*) 51))

  (assert-event (no-duplicatesp-equal *reserved-keywords*))

  (defruled ascii-listp-of-*keywords*
    (implies (member-equal keyword *reserved-keywords*)
             (ascii-listp (string=>unicode keyword)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *contextual-keywords*
  :short "The contextual Java keywords, as ACL2 strings."
  (list "exports"
        "module"
        "non-sealed"
        "open"
        "opens"
        "permits"
        "provides"
        "record"
        "requires"
        "sealed"
        "to"
        "transitive"
        "uses"
        "var"
        "when"
        "with"
        "yield")

  ///

  (assert-event (string-listp *contextual-keywords*))

  (assert-event (= (len *contextual-keywords*) 17))

  (assert-event (no-duplicatesp-equal *contextual-keywords*))

  (defruled ascii-listp-of-*contextual-keywords*
    (implies (member-equal keyword *contextual-keywords*)
             (ascii-listp (string=>unicode keyword)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define reserved-keywordp (x)
  :returns (yes/no booleanp)
  :short "Recognize reserved Java keywords."
  :long
  (xdoc::topstring
   (xdoc::p
    "A reserved Java keyword is a list of Java Unicode characters
     that consist of the (ASCII) codes of
     some element in @(tsee *reserved-keywords*)."))
  (and (ascii-listp x)
       (member-equal (ascii=>string x) *reserved-keywords*)
       t)) ; turn result of MEMBER-EQUAL into boolean

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define contextual-keywordp (x)
  :returns (yes/no booleanp)
  :short "Recognize contextual Java keywords."
  :long
  (xdoc::topstring
   (xdoc::p
    "A contextual Java keyword is a list of Java Unicode characters
     that consist of the (ASCII) codes of
     some element in @(tsee *contextual-keywords*)."))
  (and (ascii-listp x)
       (member-equal (ascii=>string x) *contextual-keywords*)
       t)) ; turn result of MEMBER-EQUAL into boolean
