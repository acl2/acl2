; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "projects/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "projects/abnf/grammar-definer/deftreeops" :dir :system)
(include-book "projects/abnf/operations/in-terminal-set" :dir :system)
(include-book "kestrel/utilities/integers-from-to-as-set" :dir :system)

(include-book "portcullis")

; (depends-on "grammar.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar
  :parents (remora)
  :short "ABNF grammar of Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use our "
    (xdoc::seetopic "abnf::grammar-parser" "verified ABNF grammar parser")
    " to parse the ABNF grammar of Remora
     into a representation in ACL2.")
   (xdoc::p
    "ABNF source is restricted to US-ASCII (RFC 5234),
     so the non-ASCII operators that Remora accepts
     (&lambda;, &rarr;, &forall;, &Pi;, &Sigma;)
     are referenced in the grammar via numeric value notation
     (e.g. @('%x03BB') for &lambda;)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::defgrammar *grammar*
  :short "The parsed ABNF grammar of Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "We parse the grammar file to obtain an ABNF grammar value.
     Since @(tsee abnf::defgrammar) does not currently provide
     an option to import the standard ABNF core rules,
     the file @('grammar.abnf') copies the definitions of
     @('DIGIT'), @('DQUOTE'), and @('HEXDIG') from RFC 5234
     so that the grammar is self-contained.")
   (xdoc::p
    "We prove that the grammar is "
    (xdoc::seetopic "abnf::well-formedness" "well-formed")
    ", is "
    (xdoc::seetopic "abnf::closure" "closed")
    ", and only "
    (xdoc::seetopic "abnf::in-terminal-set" "generates terminals")
    " in the Unicode character set excluding surrogates, as represented
     by the natural numbers in @('#x0-#xD7FF') union @('#xE000-#x10FFFF').
     The input to the grammar is assumed to be
     a sequence of code point integers;
     decoding bytes into code point integers is outside the scope of the grammar."))
  :file "grammar.abnf"
  :untranslate t
  :well-formed t
  :closed t

  ///

  (defruled unicode-only-*grammar*
    (abnf::rulelist-in-termset-p
     *grammar*
     (set::union (acl2::integers-from-to 0 #xD7FF)
                 (acl2::integers-from-to #xE000 #x10FFFF)))
    :enable (abnf::rule-in-termset-p
             abnf::repetition-in-termset-p
             abnf::element-in-termset-p
             abnf::num-val-in-termset-p
             abnf::char-val-in-termset-p
             abnf::char-insensitive-in-termset-p
             abnf::char-sensitive-in-termset-p
             set::list-in-of-union-2-left
             set::list-in-of-union-2-right)
    :disable ((:e acl2::integers-from-to)
              (:e set::union))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::deftreeops *grammar* :prefix cst)
