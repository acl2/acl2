; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "projects/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "projects/abnf/grammar-definer/deftreeops" :dir :system)
(include-book "projects/abnf/operations/in-terminal-set" :dir :system)

; These may speed things up.
(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

(include-book "tools/rulesets" :dir :system)

; (depends-on "grammar.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar
  :parents (concrete-syntax)
  :short "ABNF grammar for PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "As in other languages,
     the grammar consists of two sub-grammars:
     a lexical (sub)grammar and a syntactic (sub)grammar.
     These are both in the same ABNF grammar file."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::defgrammar *grammar*
  :short "The grammar of PFCSes, in ACL2."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use our verified ABNF grammar parser and our ABNF grammar abstractor
     to turn the grammar in the @('grammar.abnf') file
     into an ACL2 representation.")
   (xdoc::p
    "We use @(tsee acl2::add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output.")
   (xdoc::p
    "We show that the grammar is well-formed, closed, and ASCII."))
  :file "grammar.abnf"
  :untranslate t
  :well-formed t
  :closed t
  ///

  (defruled ascii-only-*grammar*
    (abnf::rulelist-in-termset-p *grammar* (acl2::integers-from-to 0 127))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Define constant lists of keywords for operators and separators.
;; These must match the productions
;; operator = "+" / "*" / ":=" / "=="
;; separator = "(" / ")" / "{" / "}" / ","

(defconst *operators* '("+" "*" ":=" "=="))

(defconst *separators* '("(" ")" "{" "}" ","))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Introduce tree-building macros along with theorems.
;; See syntax-abstraction.lisp for experimental use.

(abnf::deftreeops *grammar* :prefix cst)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abnf-tree-with-root-p (tree (rulename stringp))
  :returns (yes/no booleanp)
  :short "Recognize CSTs whose root is the given rule name,
          for the ABNF grammar of PFCS."
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
     These natural numbers are ascii codes
     because the grammar satisfies @(tsee abnf::rulelist-in-termset-p)
     for the set @('(integers-from-to 0 127)')
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
