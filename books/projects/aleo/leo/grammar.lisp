; Leo Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO")

(include-book "projects/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "projects/abnf/grammar-definer/deftreeops" :dir :system)
(include-book "projects/abnf/operations/in-terminal-set" :dir :system)
(include-book "kestrel/utilities/integers-from-to-as-set" :dir :system)

; (depends-on "grammar.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar
  :parents (leo)
  :short "ABNF grammar of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use our "
    (xdoc::seetopic "abnf::grammar-parser" "verified ABNF grammar parser")
    " to parse the ABNF grammar of Leo into a representation in ACL2.")
   (xdoc::p
    "The grammar consists of two sub-grammars:
     the lexical grammar and the syntactic grammar.
     We put them together, in one ACL2 constant for the whole grammar."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::defgrammar *grammar*
  :short "The parsed ABNF grammar of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "We parse the grammar file to obtain an ABNF grammar value.")
   (xdoc::p
    "We prove that the grammar is "
    (xdoc::seetopic "abnf::well-formedness" "well-formed")
    ", is "
    (xdoc::seetopic "abnf::closure" "closed")
    ", and only "
    (xdoc::seetopic "abnf::in-terminal-set" "generates terminals")
    " in the Unicode character set."))
  :file "grammar.abnf"
  :untranslate t
  :well-formed t
  :closed t
  ///

  (defruled unicode-only-*grammar*
    (abnf::rulelist-in-termset-p *grammar* (integers-from-to 0 #x10ffff))
    :enable (abnf::rule-in-termset-p
             abnf::repetition-in-termset-p
             abnf::element-in-termset-p
             abnf::num-val-in-termset-p
             abnf::char-val-in-termset-p
             abnf::char-insensitive-in-termset-p
             abnf::char-sensitive-in-termset-p)
    :disable ((:e integers-from-to))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::deftreeops *grammar* :prefix cst)
