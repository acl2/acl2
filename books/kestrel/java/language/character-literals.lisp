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

(defxdoc+ character-literals
  :parents (syntax)
  :short "Java character literals [JLS:3.10.4]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unicode-charlit-char
  :short "Fixtype of Unicode input characters usable in character literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to
     the grammar rule for @('single-character') [JLS:3.10.4],
     whose definiens is @('input-character')
     except for single quote and backslash,
     where @('input-character') is defined in [JLS:3.4] as
     a @('unicode-input-character') except for CR and LF.")
   (xdoc::p
    "Since @('unicode-input-character') is captured
     by @(tsee unicode-input-char-p) in our formalization,
     we define a Unicode character for a character literal
     (as conveyed by the @('charlit') part of the type name)
     as a Unicode input character
     that is not CR, LF, single quote, and backslash.")
   (xdoc::p
    "We prefer the nomenclature `Unicode character for a character literal',
     on which this type name is based,
     to the nomenclature `single character' suggested by the grammar."))

  (define unicode-charlit-char-p (x)
    :returns (yes/no booleanp)
    :short "Recognizer for @(tsee unicode-charlit-char)."
    (and (unicode-input-char-p x)
         (not (member (unicode-input-char->unicode x)
                      (list (char-code #\Return)
                            (char-code #\Newline)
                            (char-code #\')
                            (char-code #\\))))))

  (assert-event (equal (char-code #\Return) 13))
  (assert-event (equal (char-code #\Newline) 10))

  (std::deffixer unicode-charlit-char-fix
    :short "Fixer for @(tsee unicode-charlit-char)."
    :pred unicode-charlit-char-p
    :body-fix (make-unicode-input-char :unicode 0 :umarker 0))

  (fty::deffixtype unicode-charlit-char
    :pred unicode-charlit-char-p
    :fix unicode-charlit-char-fix
    :equiv unicode-charlit-char-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum char-literal
  :short "Fixtype of character literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to the grammar rule for @('character-literal') [JLS:3.10.4],
     a character literal is
     either a @('single-character') (see @(tsee unicode-charlit-char))
     or an escape sequence (see @(tsee escape-sequence)),
     between single quotes.
     Abstractly, but without losing any information,
     we leave the surrounding single quotes implicit,
     and define character literals via a tagged sum.")
   (xdoc::p
    "The set of values of this fixtype should be isomorphic to
     the set of strings (or parse trees) defined by
     the Java grammar rule @('character-literal').
     This remains to be proved formally."))
  (:char ((get unicode-charlit-char)))
  (:escape ((get escape-sequence)))
  :pred char-literalp)
