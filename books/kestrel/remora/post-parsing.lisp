; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "parser")

;; Pulls in *remora-keywords-as-natlists* and remora-keyword-p, which
;; are consulted by check-tree-no-keyword-identifiers below.
(include-book "identifier-syntax")

;; Certifies that the grammar's `keyword` rule and
;; *remora-keywords-as-natlists* list the same keywords.  This book
;; has no exported definitions used here; it is included for its
;; assert-event side effect at certification time.
(include-book "check-keywords")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ post-parsing
  :parents (concrete-syntax parsing-and-printing)
  :short "Post-parsing checks for the Remora parser."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ABNF grammar defines the concrete syntax of Remora,
     but certain extra-grammatical constraints cannot be expressed in ABNF.
     This file implements those constraints as post-parse checks
     on the CST produced by @(tsee parse-program).
     Currently the only such check is [SC2] (keyword exclusion).")
   (xdoc::p
    "User-facing entry points that bundle this check into a complete
     parsing pipeline (UTF-8 decode + parse + [SC2] + input exhaustion +
     CST&rarr;AST abstraction) live in @(see parser-interface) &mdash;
     see @(tsee parse-from-string) and @(tsee parse-from-file)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ---- SC2: Keyword exclusion from identifiers ----
;;
;; The ABNF grammar's "identifier" rule accepts any id-start *id-continue
;; sequence, including reserved keywords.  This post-parse check walks the
;; CST and rejects any identifier node whose text matches a keyword.
;; See grammar.abnf [SC2] for details.  The keyword list itself
;; (*remora-keywords-as-natlists*) and the membership predicate
;; (remora-keyword-p) live in identifier-syntax.lisp (xdoc topic
;; identifier-syntax).

;; Walking the CST to check for keyword identifiers.
;; Uses abnf::tree->string to collect leaf terminals from a subtree.

(defines check-no-keyword-identifiers
  :short "Walk a CST and check that no identifier matches a keyword."
  :verify-guards nil

  (define check-tree-no-keyword-identifiers ((tree abnf::treep))
    :returns (errmsg abnf::tree-resultp)
    :short "Check a single tree node."
    (abnf::tree-case tree
      :leafterm (abnf::tree-fix tree)
      :leafrule (abnf::tree-fix tree)
      :nonleaf
      (b* (;; If this is an identifier node, check its text
           ((when (equal tree.rulename?
                         (abnf::rulename "identifier")))
            (b* ((text (abnf::tree->string tree))
                 ;; NOTE: abnf::tree->string returns an ABNF::STRINGP
                 ;; which is a list of nats.
                 ((when (remora-keyword-p text))
                  (reserrf (cons :keyword-as-identifier text))))
              (abnf::tree-fix tree))))
        ;; Otherwise, recurse into branches
        (check-tree-list-list-no-keyword-identifiers tree.branches)))
    :measure (abnf::tree-count tree))

  (define check-tree-list-no-keyword-identifiers ((trees abnf::tree-listp))
    :returns (errmsg abnf::tree-resultp)
    :short "Check a list of trees."
    (if (endp trees)
        (abnf::tree-nonleaf nil nil)
      (b* ((result (check-tree-no-keyword-identifiers (car trees)))
           ((when (reserrp result)) result))
        (check-tree-list-no-keyword-identifiers (cdr trees))))
    :measure (abnf::tree-list-count trees))

  (define check-tree-list-list-no-keyword-identifiers
    ((treess abnf::tree-list-listp))
    :returns (errmsg abnf::tree-resultp)
    :short "Check a list of lists of trees."
    (if (endp treess)
        (abnf::tree-nonleaf nil nil)
      (b* ((result (check-tree-list-no-keyword-identifiers (car treess)))
           ((when (reserrp result)) result))
        (check-tree-list-list-no-keyword-identifiers (cdr treess))))
    :measure (abnf::tree-list-list-count treess))

  ///
  (verify-guards check-tree-no-keyword-identifiers
    :hints (("Goal" :in-theory (enable remora-keyword-p)))))

;; The user-facing entry points that bundle the SC2 check above into a
;; complete parsing pipeline live in parser-interface.lisp (xdoc topic
;; parser-interface) -- see parse-from-string and parse-from-file.
