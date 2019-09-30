; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "unicode")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ keywords
  :parents (language)
  :short "The Java keywords [JLS:3.9]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some character sequences are Java keywords in all contexts,
     namely the ones listed in the grammar production in [JLS:3.9].
     Other character sequences are Java keywords
     only in certain module-related contexts,
     as described in [JLS:3.9] in prose (i.e. without grammar productions);
     these are called `restricted keywords'."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *keywords*
  :short "The (non-restricted) Java keywords, as ACL2 strings."
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

  (assert-event (string-listp *keywords*))

  (assert-event (= (len *keywords*) 51))

  (assert-event (no-duplicatesp-equal *keywords*))

  (defruled ascii-listp-of-keywords
    (implies (member-equal keyword *keywords*)
             (ascii-listp (string=>unicode keyword)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *restricted-keywords*
  :short "The restricted Java keywords, as ACL2 strings."
  (list "open"
        "module"
        "requires"
        "transitive"
        "exports"
        "opens"
        "to"
        "uses"
        "provides"
        "with")
  ///

  (assert-event (string-listp *restricted-keywords*))

  (assert-event (= (len *restricted-keywords*) 10))

  (assert-event (no-duplicatesp-equal *restricted-keywords*))

  (defruled ascii-listp-of-restricted-keywords
    (implies (member-equal keyword *restricted-keywords*)
             (ascii-listp (string=>unicode keyword)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jkeywordp (x)
  :returns (yes/no booleanp)
  :short "Recognize (non-restricted) Java keywords."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java keyword is a list of Java Unicode characters
     that consist of the (ASCII) codes of
     some element in @(tsee *keywords*).")
   (xdoc::p
    "The @('j') in front of @('jkeywordp') avoids
     a conflict with the built-in @(tsee keywordp)."))
  (and (ascii-listp x)
       (member-equal (ascii=>string x) *keywords*)
       t)) ; turn result of MEMBER-EQUAL into boolean

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restricted-keyword-p (x)
  :returns (yes/no booleanp)
  :short "Recognize restricted Java keywords."
  :long
  (xdoc::topstring
   (xdoc::p
    "A restricted Java keyword is a list of Java Unicode characters
     that consist of the (ASCII) codes of
     some element in @(tsee *restricted-keywords*)."))
  (and (ascii-listp x)
       (member-equal (ascii=>string x) *restricted-keywords*)
       t)) ; turn result of MEMBER-EQUAL into boolean
