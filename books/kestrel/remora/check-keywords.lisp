; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "grammar")
(include-book "identifier-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ check-keywords
  :parents (post-parsing)
  :short "Consistency check between the grammar's @('keyword') rule and
          the keyword list used by the parser."
  :long
  (xdoc::topstring
   (xdoc::p
    "The reserved keywords of Remora are listed in two places:")
   (xdoc::ul
    (xdoc::li
     "The @('keyword') rule in @('grammar.abnf'), which enumerates the
      keywords in case-sensitive ABNF notation (@('%s\"...\"')).  This
      rule is not invoked directly by the parser; it exists so that the
      grammar file documents the full keyword set in one place.")
    (xdoc::li
     "The constant @(tsee *remora-keywords-as-natlists*) in
      @('identifier-syntax.lisp'), as a list of code-point sequences.
      This constant is consulted by the post-parsing CST walk
      @(tsee check-tree-no-keyword-identifiers) (enforcing side
      condition [SC2]) and by the AST-level identifier validator
      @(tsee valid-identifier-codepoints-p)."))
   (xdoc::p
    "Keeping these two listings in sync by hand is fragile.  This book
     extracts the keyword sequences from the parsed @(tsee *grammar*)'s
     @('keyword') rule and certifies via @(tsee assert-event) that the
     extracted list equals @(tsee *remora-keywords-as-natlists*).  If
     the two ever drift apart, this book will fail to certify.")
   (xdoc::p
    "We deliberately do not redefine @(tsee *remora-keywords-as-natlists*)
     in terms of the grammar.  Doing so would force every book that
     consumes the keyword list (e.g. @(tsee fresh-variables),
     @(tsee abstract-syntax-well-formed)) to transitively include the
     grammar and the ABNF machinery.  Keeping the two listings
     independent and cross-checking them here preserves the lightweight
     dependency story for AST-side code."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Walking the parsed grammar's `keyword` rule to extract code-point
;; sequences.
;;
;; The `keyword` rule in grammar.abnf consists entirely of alternatives
;; built from case-sensitive char-vals (%s"...") and direct num-vals
;; (%xNN).  Each alternative is either a single such element, or a
;; concatenation of two of them (used to encode "t<lambda>" and
;; "i<lambda>" as the character "t" or "i" followed by the lambda
;; code point).  No groups, options, or rule references appear.  The
;; extractor below handles the cases that occur; other element kinds
;; return nil, which would cause the equality check to fail loudly.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define keyword-rep->codepoints ((rep abnf::repetitionp))
  :returns (codepoints nat-listp)
  :short "Extract the code-point sequence from one repetition of the
          @('keyword') rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a case-sensitive @('char-val'), the string's characters are
     the code points.  For a direct @('num-val'), the explicit
     code-point list is returned.  All other element kinds (rulename,
     group, option, prose-val, case-insensitive char-val, range
     num-val) do not occur in the @('keyword') rule; if one does, we
     return @('nil') so the downstream equality check fails."))
  (b* ((elem (abnf::repetition->element rep)))
    (abnf::element-case
     elem
     :char-val (abnf::char-val-case
                elem.get
                :sensitive (string=>nats elem.get.get)
                :insensitive nil)
     :num-val (abnf::num-val-case
               elem.get
               :direct (acl2::nat-list-fix elem.get.get)
               :range nil)
     :rulename nil
     :group nil
     :option nil
     :prose-val nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define keyword-conc->codepoints ((conc abnf::concatenationp))
  :returns (codepoints nat-listp)
  :short "Concatenate the code-point sequences of each repetition in
          one concatenation."
  :long
  (xdoc::topstring
   (xdoc::p
    "An alternative of the @('keyword') rule that is a sequence of
     elements (e.g. @('%s\"t\" %x03BB')) yields the code points
     produced by appending the per-element results."))
  (cond ((endp conc) nil)
        (t (append (keyword-rep->codepoints (car conc))
                   (keyword-conc->codepoints (cdr conc))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define keyword-alt->codepoint-lists ((alt abnf::alternationp))
  :returns (codepoint-lists true-list-listp)
  :short "Collect one code-point sequence per alternative."
  (cond ((endp alt) nil)
        (t (cons (keyword-conc->codepoints (car alt))
                 (keyword-alt->codepoint-lists (cdr alt))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-rule-by-name ((name stringp) (rules abnf::rulelistp))
  :returns (rule abnf::rule-optionp)
  :short "Find the first rule with the given name, or @('nil') if absent."
  (cond ((endp rules) nil)
        ((equal (abnf::rule->name (car rules))
                (abnf::rulename name))
         (abnf::rule-fix (car rules)))
        (t (find-rule-by-name name (cdr rules)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define grammar-keywords ((rules abnf::rulelistp))
  :returns (kws true-list-listp)
  :short "Extract the keyword code-point sequences from a grammar's
          @('keyword') rule."
  (b* ((rule (find-rule-by-name "keyword" rules))
       ((unless rule) nil))
    (keyword-alt->codepoint-lists (abnf::rule->definiens rule))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; The check.
;;
;; assert-event certifies the equality at book-certification time.  If
;; the `keyword` rule in grammar.abnf and *remora-keywords-as-natlists*
;; ever drift apart (additions, deletions, or reordering), this book
;; will fail to certify.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (grammar-keywords *grammar*)
        *remora-keywords-as-natlists*)
 :msg "The keywords listed in grammar.abnf's `keyword` rule do not ~
       match *remora-keywords-as-natlists* in identifier-syntax.lisp. ~
       Update one or the other so the two are in sync.")
