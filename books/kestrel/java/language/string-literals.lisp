; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "unicode-input-characters")
(include-book "escape-sequences")

(include-book "kestrel/std/util/deffixer" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ string-literals
  :parents (syntax)
  :short "Java string literals [JLS:3.10.5]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unicode-stringlit-char
  :short "Fixtype of Unicode input characters usable in string literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to the first alternative of
     the grammar rule for @('string-character') [JLS:3.10.5],
     which is @('input-character')
     except for double quote and backslash,
     where @('input-character') is defined in [JLS:3.4] as
     a @('unicode-input-character') except for CR and LF.")
   (xdoc::p
    "Since @('unicode-input-character') is captured
     by @(tsee unicode-input-char-p) in our formalization,
     we define a Unicode character for a string literal
     (as conveyed by the @('stringlit') part of the type and function names)
     as a Unicode input character
     that is not CR, LF, double quote, and backslash."))

  (define unicode-stringlit-char-p (x)
    :returns (yes/no booleanp)
    :short "Recognizer for @(tsee unicode-stringlit-char)."
    (and (unicode-input-char-p x)
         (not (member (unicode-input-char->unicode x)
                      (list (char-code #\Return)
                            (char-code #\Newline)
                            (char-code #\")
                            (char-code #\\))))))

  (assert-event (equal (char-code #\Return) 13))
  (assert-event (equal (char-code #\Newline) 10))

  (std::deffixer unicode-stringlit-char-fix
    :short "Fixer for @(tsee unicode-stringlit-char)."
    :pred unicode-stringlit-char-p
    :body-fix (make-unicode-input-char :unicode 0 :umarker 0))

  (fty::deffixtype unicode-stringlit-char
    :pred unicode-stringlit-char-p
    :fix unicode-stringlit-char-fix
    :equiv unicode-stringlit-char-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum string-literal-char
  :short "Fixtype of characters for string literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to the grammar rule for @('string-character') [JLS:3.10.5],
     a character for a string literal is
     either a Unicode input character with some exceptions
     (see @(tsee unicode-stringlit-char))
     or an escape sequence (see @(tsee escape-sequence)).")
   (xdoc::p
    "We prefer the nomenclature `string literal character',
     on which this type name is based,
     to the nomenclature `string character' suggested by the grammar."))
  (:char ((get unicode-stringlit-char)))
  (:escape ((get escape-sequence))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist string-literal
  :short "Fixtype of string literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to the grammar rule for @('string-literal') [JLS:3.10.5],
     a string literal consists of zero or more @('string-character')s
     (which we formalize via @(tsee string-literal-char))
     between double quotes.
     Abstractly, but without losing any information,
     we leave the surrounding double quotes implicit,
     and define string literals as lists.")
   (xdoc::p
    "The set of values of this fixtype should be isomorphic to
     the set of strings (or parse trees) defined by
     the Java grammar rule @('string-literal').
     This remains to be proved formally."))
  :elt-type string-literal-char
  :true-listp t
  :elementp-of-nil nil
  :pred string-literalp)
