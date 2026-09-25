; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "projects/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "projects/abnf/tree-operations/deftreeops" :dir :system)
(include-book "projects/abnf/grammar-operations/in-terminal-set" :dir :system)

(include-book "portcullis")

; (depends-on "lexicon.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lexicon
  :parents (concrete-syntax)
  :short "Lexicon of Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "parsing" "syntax specification of Remora")
    " has been formalized based on [impl].
     However, an effort is underway to provide a precise specification
     of the Remora syntax (as well as of its semantics eventually)
     outside of both [impl] and our ACL2 formalization,
     as an official formal definition of the language,
     which our ACL2 formalization will formalize (and implement)
     and that [impl] will implement.
     The new definition is not expected to differ much from the current one.")
   (xdoc::p
    "Although the new syntax definition is still in flux,
     we start formalizing it in ACL2.
     The file @('lexicon.abnf') contains an ABNF grammar
     of the lexicon for the new syntax definition.
     It is an initial version/subset,
     because in particular it is limited to ASCII,
     while the new syntax definition is meant to extend to all Unicode."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::defgrammar *lexicon*
  :short "The parsed ABNF grammar of the new Remora lexicon."
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
    " in the ASCII character set (for now)."))
  :file "lexicon.abnf"
  :untranslate t
  :well-formed t
  :closed t

  ///

  (defruled ascii-only-*lexicon*
    (abnf::rulelist-in-termset-p *lexicon* (acl2::integers-from-to 0 #x7f))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::deftreeops *lexicon* :prefix lcst)
