; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "projects/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "projects/abnf/grammar-definer/deftreeops" :dir :system)
(include-book "projects/abnf/operations/in-terminal-set" :dir :system)

(local (include-book "kestrel/utilities/integers-from-to-as-set" :dir :system))

; (depends-on "grammar-old.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-old
  :parents (concrete-syntax)
  :short "Old ABNF grammar of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use our "
    (xdoc::seetopic "abnf::grammar-parser" "verified ABNF grammar parser")
    " to parse the old ABNF grammar of Yul into a representation in ACL2.")
   (xdoc::p
    "This is the old grammar of Yul; see @(see concrete-syntax)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::defgrammar *grammar-old*
  :short "The parsed old ABNF grammar of Yul."
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
  :file "grammar-old.abnf"
  :untranslate t
  :well-formed t
  :closed t
  ///

  (defruled unicode-only-*grammar-old*
    (abnf::rulelist-in-termset-p *grammar-old*
                                 (integers-from-to 0 #x10ffff))
    :enable (abnf::rule-in-termset-p
             abnf::repetition-in-termset-p
             abnf::element-in-termset-p
             abnf::num-val-in-termset-p
             abnf::char-val-in-termset-p
             abnf::char-insensitive-in-termset-p
             abnf::char-sensitive-in-termset-p)
    :disable ((:e integers-from-to))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We use the prefix OCST, where 'O' stands for 'old',
; to distinguish it from the prefix CST used in grammar.lisp,
; which is the primary grammar (the one that our parser matches).
; This old grammar is here mainly for historical and testing purposes.
(abnf::deftreeops *grammar-old* :prefix ocst)
