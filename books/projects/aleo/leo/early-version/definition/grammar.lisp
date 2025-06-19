; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "projects/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "projects/abnf/grammar-definer/deftreeops" :dir :system)
(include-book "projects/abnf/operations/in-terminal-set" :dir :system)
(include-book "tools/rulesets" :dir :system)

(local (include-book "kestrel/utilities/integers-from-to-as-set" :dir :system))

; (depends-on "grammar.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar
  :parents (concrete-syntax)
  :short "ABNF grammar of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use our "
    (xdoc::seetopic "abnf::grammar-parser" "verified ABNF grammar parser")
    " to parse the ABNF grammar of Leo into a representation in ACL2.")
   (xdoc::p
    "The grammar consists of three sub-grammars:
     the lexical grammar,
     the syntactic grammar,
     and the format string grammar.
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abnf-tree-with-root-p (tree (rulename stringp))
  :returns (yes/no booleanp)
  :short "Recognize CSTs whose root is the given rule name,
          for the ABNF grammar of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "This implements the definition of
     sets of CSTs that match given rule names.")
   (xdoc::p
    "This is a useful abbreviation for
     a more verbose conjunction of ABNF predicates
     with more verbose arguments.")
   (xdoc::p
    "The tree is terminated,
     i.e. it has natural numbers at its leaves,
     not rule names.
     These natural numbers are (code points of) Unicode characters,
     because the grammar satisfies @(tsee abnf::rulelist-in-termset-p)
     for the set @('(integers-from-to 0 #10xffff)')
     as proved in @(tsee *grammar*)."))
  (and (abnf::treep tree)
       (abnf::tree-terminatedp tree)
       (abnf::tree-match-element-p tree
                                   (abnf::element-rulename
                                    (abnf::rulename rulename))
                                   *grammar*))
  :no-function t
  :hooks (:fix)
  ///

  (defrule abnf-treep-when-abnf-tree-with-root-p
    (implies (abnf-tree-with-root-p tree rulename) ; free var RULENAME
             (abnf::treep tree)))

  ;; to prove :ELEMENTP-OF-NIL NIL in the STD::DEFLIST below:
  (defrule not-abnf-tree-with-root-p-of-nil
    (not (abnf-tree-with-root-p nil rulename))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist abnf-tree-list-with-root-p (x rulename)
  :guard (stringp rulename)
  :short "Lift @(tsee abnf-tree-with-root-p) to lists."
  (abnf-tree-with-root-p x rulename)
  :true-listp t
  :elementp-of-nil nil
  ///

  (defrule abnf-tree-listp-when-abnf-tree-list-with-root-p
    (implies (abnf-tree-list-with-root-p trees rulename) ; free var RULENAME
             (abnf::tree-listp trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection abnf-tree-wrap
  :short "Wrap a CST into a nest of CSTs
          with the given rule names as roots (in the order given)
          and each with a single subtree, ending with the original tree."
  :long "@(def abnf-tree-wrap)"

  (defmacro abnf-tree-wrap (tree &rest rulenames)
    `(abnf-tree-wrap-fn ,tree (list ,@rulenames)))

  (define abnf-tree-wrap-fn ((tree abnf::treep) (rulenames string-listp))
    :returns (wrapped-tree abnf::treep)
    (cond ((endp rulenames) (abnf::tree-fix tree))
          (t (abnf-tree-wrap-fn (abnf::make-tree-nonleaf
                                 :rulename? (abnf::rulename (car rulenames))
                                 :branches (list (list tree)))
                                (cdr rulenames))))
    :hooks (:fix)))
