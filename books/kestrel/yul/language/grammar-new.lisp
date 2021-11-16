; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "kestrel/abnf/parser" :dir :system)
(include-book "kestrel/abnf/abstractor" :dir :system)

; (depends-on "abnf-grammar-new.txt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-new
  :parents (concrete-syntax)
  :short "ABNF old grammar of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use our "
    (xdoc::seetopic "abnf::grammar-parser" "verified ABNF grammar parser")
    " to parse the ABNF grammar of Yul into a representation in ACL2.")
   (xdoc::p
    "This is the new grammar of Yul; see @(see concrete-syntax)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection *grammar-new*
  :short "The parsed ABNF grammar of Yul."
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
    " in the ASCII character set."))

  (make-event
   (mv-let (tree state)
     (abnf::parse-grammar-from-file (str::cat (cbd) "abnf-grammar-new.txt")
                                    state)
     (acl2::value `(defconst *grammar-new*
                     (abnf::abstract-rulelist ',tree)))))

  (defruled rulelist-wfp-of-*grammar-new*
    (abnf::rulelist-wfp *grammar-new*))

  (defruled rulelist-closedp-of-*grammar-new*
    (abnf::rulelist-closedp *grammar-new*))

  (defruled ascii-only-*grammar-new*
    (abnf::rulelist-in-termset-p *grammar-new*
                                 (acl2::integers-from-to 0 #x7f))
    :enable (abnf::rule-in-termset-p
             abnf::repetition-in-termset-p
             abnf::element-in-termset-p
             abnf::num-val-in-termset-p
             abnf::char-val-in-termset-p
             abnf::char-insensitive-in-termset-p
             abnf::char-sensitive-in-termset-p)
    :disable ((:e acl2::integers-from-to))
    :prep-books
    ((local
      (include-book "kestrel/utilities/integers-from-to-as-set" :dir :system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abnf-tree-with-root-p (tree (rulename stringp))
  :returns (yes/no booleanp)
  :short "Recognize terminated ABNF trees rooted at rulename,
          for the ABNF grammar of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "The tree has ASCII codes at its leaves."))
  (and (abnf::treep tree)
       (abnf::tree-terminatedp tree)
       (abnf::tree-match-element-p tree
                                   (abnf::element-rulename
                                    (abnf::rulename rulename))
                                   *grammar-new*))
  :no-function t
  :hooks (:fix)
  ///

  (defrule abnf-treep-when-abnf-tree-with-root-p
    (implies (abnf-tree-with-root-p tree rulename) ; RULENAME intentionally free variable
             (abnf::treep tree)))

  (defrule not-abnf-tree-with-root-p-of-nil
    (not (abnf-tree-with-root-p nil rulename))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist abnf-tree-list-with-root-p (x rulename)
  :guard (stringp rulename)
  :short "Lift @(tsee abnf-tree-with-root-p) to lists"
  (abnf-tree-with-root-p x rulename)
  :true-listp t
  :elementp-of-nil nil
  ///
  (defrule abnf-tree-listp-when-abnf-tree-list-with-root-p
    (implies (abnf-tree-list-with-root-p trees rulename)
             (abnf::tree-listp trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection abnf-tree-wrap
  :short "Wrap an ABNF tree into a nest of ABNF trees
          with the given rule names as roots."
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
