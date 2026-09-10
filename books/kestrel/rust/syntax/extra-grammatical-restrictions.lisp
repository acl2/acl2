; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "grammar")

(include-book "projects/abnf/tree-operations/tree-utilities" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/lists/prefixp" :dir :system)
(include-book "kestrel/utilities/strings/chars-codes" :dir :system)

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

; The results of the abnf::check-tree-... utilities are values of
; fty::defresult types; this (disabled by default) rule bridges
; "not an error" to the value type, as in lexer.lisp.
(local (in-theory (enable abnf::treep-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ extra-grammatical-restrictions
  :parents (grammar)
  :short "Declarative specifications of
          the extra-grammatical side conditions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar files label, with @('[SCn]') tags,
     the constraints that ABNF cannot express.
     This book gives each formalized side condition
     a declarative specification,
     so that satisfaction of the side conditions
     by the results of lexing (and later parsing)
     can be stated and eventually proved as theorems.")
   (xdoc::p
    "Current status of the side conditions
     of the lexical grammar:")
   (xdoc::ul
    (xdoc::li
     "[SC1] Maximal munch: formalized here,
      as @(tsee lexeme-cst-maximal-p) (one lexeme cannot be extended)
      and @(tsee lexing-okp)
      (a whole lexing is valid and maximal).")
    (xdoc::li
     "[SC2] Block comment closing: formalized here,
      as @(tsee block-comment-string-p),
      incorporated into lexeme validity
      via @(tsee lexeme-cst-okp).")
    (xdoc::li
     "[SC3] Bare carriage return in doc comments: not yet formalized.")
    (xdoc::li
     "[SC4] Unicode XID identifiers with NFC normalization:
      not yet formalized (awaiting the XID table books;
      the grammar is ASCII-only for identifiers meanwhile).")
    (xdoc::li
     "[SC5] Raw identifier exclusions
      (@('crate'), @('self'), @('super'), @('Self')):
      not yet formalized.")
    (xdoc::li
     "[SC6] Edition-dependent keyword classification:
      the tables and classification functions are in @(see keywords);
      the connection to lexing results is not yet formalized.")
    (xdoc::li
     "[SC7] Reserved numeric forms: not yet formalized
      (the executable lexer rejects them).")
    (xdoc::li
     "[SC8] Reserved prefixes: formalized here,
      as @(tsee lexeme-cst-reserved-prefix-okp),
      incorporated into @(tsee lexing-okp)."))
   (xdoc::p
    "An important structural point:
     the side conditions constrain the set of valid lexeme trees
     (see @(tsee lexeme-cst-okp)),
     and the maximal-munch condition [SC1] maximizes
     over that constrained set.
     For example, without [SC2] in the candidate set,
     maximal munch would extend a block comment
     past its first balanced closing @('*/')
     to a later one."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC2] Block comment closing.

(define bc-rest-closes-p ((nats nat-listp) (depth natp))
  :returns (yes/no booleanp)
  :short "Check if a character sequence closes
          a given block comment nesting depth exactly at its end."
  :long
  (xdoc::topstring
   (xdoc::p
    "We scan the sequence left to right,
     tracking the number of open block comments still to close:
     @('*/') decreases it and @('/*') increases it.
     When the depth reaches zero, the sequence must be exhausted:
     this is what makes a valid block comment end
     at its first balanced closing @('*/');
     see @(tsee block-comment-string-p)."))
  :measure (len nats)
  (b* ((nats (nat-list-fix nats))
       (depth (nfix depth)))
    (cond ((zp depth) (endp nats))
          ((endp nats) nil)
          ((prefixp (list #x2A #x2F) nats) ; starts with */
           (bc-rest-closes-p (cddr nats) (1- depth)))
          ((prefixp (list #x2F #x2A) nats) ; starts with /*
           (bc-rest-closes-p (cddr nats) (1+ depth)))
          (t (bc-rest-closes-p (cdr nats) depth)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define block-comment-string-p ((nats nat-listp))
  :returns (yes/no booleanp)
  :short "Check if a character sequence is exactly one
          complete block comment [SC2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The sequence must start with @('/*')
     and reach balanced nesting
     exactly at its end."))
  (b* ((nats (nat-list-fix nats)))
    (and (prefixp (list #x2F #x2A) nats) ; starts with /*
         (bc-rest-closes-p (cddr nats) 1))))

;;;;;;;;;;;;;;;;;;;;

(assert-event (block-comment-string-p (string=>nats "/**/")))
(assert-event (block-comment-string-p (string=>nats "/****/")))
(assert-event (block-comment-string-p (string=>nats "/* a /* b */ c */")))
(assert-event (block-comment-string-p (string=>nats "/* a
multi-line */")))
(assert-event (not (block-comment-string-p (string=>nats "/*/"))))
(assert-event (not (block-comment-string-p (string=>nats "/* a */ b */"))))
(assert-event (not (block-comment-string-p (string=>nats "/* /* */"))))
(assert-event (not (block-comment-string-p (string=>nats "// nope"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is a lexeme CST:
          a terminated tree matching the rule @('lexeme')."
  (and (abnf::tree-terminatedp tree)
       (abnf::tree-match-element-p tree
                                   (abnf::element-rulename
                                    (abnf::rulename "lexeme"))
                                   *lexical-grammar*)
       t)

  ///

  (defret tree-terminatedp-when-lexeme-cst-p
    (implies yes/no
             (abnf::tree-terminatedp tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-okp ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is a valid lexeme CST:
          a lexeme CST satisfying the side conditions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently this conjoins the grammar match
     with [SC2] (block comment closing):
     if the lexeme's string starts with @('/*'),
     the lexeme can only be a block comment
     (no other lexeme's string starts that way),
     and its string must be exactly one complete block comment.
     Further side conditions will be added as conjuncts
     as they are formalized."))
  (and (lexeme-cst-p tree)
       (b* ((string (abnf::tree->string tree)))
         (implies (prefixp (list #x2F #x2A) string) ; starts with /*
                  (block-comment-string-p string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC8] Reserved prefixes.

(define identifier-or-keyword-lexeme-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is a lexeme CST holding
          a plain (non-raw) identifier-or-keyword token."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the lexemes subject to
     the reserved-prefix side condition [SC8]:
     CSTs of the form
     @('lexeme -> token -> identifier-or-keyword').
     A raw identifier instead has @('raw-identifier')
     as the subtree under @('token')
     (its @('identifier-or-keyword') is nested
     under the @('r#') prefix),
     so raw identifiers are correctly not covered."))
  (b* ((sub1 (abnf::check-tree-nonleaf-1-1 tree "lexeme"))
       ((when (reserrp sub1)) nil)
       (sub2 (abnf::check-tree-nonleaf-1-1 sub1 "token"))
       ((when (reserrp sub2)) nil))
    (not (reserrp (abnf::check-tree-nonleaf
                   sub2 "identifier-or-keyword")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-reserved-prefix-okp ((tree abnf::treep)
                                        (rest-input nat-listp))
  :returns (yes/no booleanp)
  :short "Check that a lexeme CST does not form
          a reserved prefix with the remaining input [SC8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "An identifier-or-keyword lexeme
     (see @(tsee identifier-or-keyword-lexeme-cst-p))
     must not be immediately followed by
     @('#') (U+0023), @('\\'') (U+0027), or @('\"') (U+0022):
     such forms are reserved prefixes
     in both supported editions (Rust 2021 and later).")
   (xdoc::p
    "Note that this condition rejects the whole lexing
     rather than steering maximal munch to a shorter lexeme:
     in Rust, @('foo#bar') is a lexing error,
     not an alternative lexing.
     Accordingly, this condition is a conjunct of
     @(tsee lexing-okp) about the chosen lexemes,
     and is not part of the candidate set
     @(tsee lexeme-cst-okp)
     over which @(tsee lexeme-cst-maximal-p) maximizes
     (also, it could not be, since it depends on
     the input that follows the lexeme)."))
  (b* ((rest-input (nat-list-fix rest-input)))
    (implies (identifier-or-keyword-lexeme-cst-p tree)
             (and (not (prefixp (list #x23) rest-input)) ; #
                  (not (prefixp (list #x27) rest-input)) ; '
                  (not (prefixp (list #x22) rest-input)))))) ; "

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC1] Maximal munch.

(define-sk lexeme-cst-maximal-p ((tree abnf::treep) (rest-input nat-listp))
  :returns (yes/no booleanp)
  :short "Check if a valid lexeme CST cannot be extended:
          no valid lexeme CST covers its string
          plus a nonempty prefix of the remaining input [SC1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The quantification is over valid lexeme CSTs,
     i.e. trees satisfying @(tsee lexeme-cst-okp),
     which includes the other side conditions;
     see the discussion in
     @(see extra-grammatical-restrictions)."))
  (forall (tree2)
          (implies (and (abnf::treep tree2)
                        (lexeme-cst-okp tree2)
                        (prefixp (abnf::tree->string tree)
                                 (abnf::tree->string tree2))
                        (prefixp (abnf::tree->string tree2)
                                 (append (abnf::tree->string tree)
                                         (nat-list-fix rest-input))))
                   (equal (abnf::tree->string tree2)
                          (abnf::tree->string tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexing-okp ((trees abnf::tree-listp) (input nat-listp))
  :returns (yes/no booleanp)
  :short "Declarative specification of correct lexing [SC1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The trees are a correct lexing of the input if:
     each is a valid lexeme CST (see @(tsee lexeme-cst-okp));
     each covers a nonempty prefix of the remaining input
     and is maximal against what follows
     (see @(tsee lexeme-cst-maximal-p));
     no identifier-or-keyword lexeme forms a reserved prefix
     with what follows
     (see @(tsee lexeme-cst-reserved-prefix-okp));
     and together they cover the input exactly.")
   (xdoc::p
    "The lexer book defines the executable lexer;
     proving that it satisfies this specification
     is future work."))
  :measure (len trees)
  (b* ((trees (abnf::tree-list-fix trees))
       (input (nat-list-fix input))
       ((when (endp trees)) (endp input))
       (tree (car trees))
       (string (abnf::tree->string tree)))
    (and (lexeme-cst-okp tree)
         (consp string)
         (prefixp string input)
         (lexeme-cst-maximal-p tree (nthcdr (len string) input))
         (lexeme-cst-reserved-prefix-okp tree (nthcdr (len string) input))
         (lexing-okp (cdr trees) (nthcdr (len string) input))))

  ///

  (assert-event (lexing-okp nil nil)))
