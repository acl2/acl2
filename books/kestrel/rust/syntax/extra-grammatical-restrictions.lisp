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
(include-book "keywords")
(include-book "unicode-characters")

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
; fty::defresult types; these (disabled by default) rules bridge
; "not an error" to the value type, as in lexer.lisp.
(local (in-theory (enable abnf::treep-when-result-not-error
                          abnf::tree-list-tuple2p-when-result-not-error
                          abnf::tree-list-tuple3p-when-result-not-error
                          abnf::tree-list-tuple4p-when-result-not-error
                          abnf::tree-list-tuple5p-when-result-not-error)))

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
     "[SC3] Carriage return in doc comments:
      formalized here,
      as @(tsee lexeme-cst-doc-comment-cr-okp),
      incorporated into @(tsee lexing-okp).")
    (xdoc::li
     "[SC4] Unicode XID identifiers with NFC normalization:
      not yet formalized.
      The XID tables are in @(see unicode-xid),
      but the grammar and lexer do not use them yet,
      so identifiers are ASCII-only meanwhile.
      The tables are those of Unicode 16.0.0, as in rustc 1.87.0;
      rustc moved to Unicode 17.0.0 in its version 1.94.0.")
    (xdoc::li
     "[SC5] Raw identifier and raw lifetime exclusions
      (@('crate'), @('self'), @('super'), @('Self')):
      formalized here,
      as @(tsee lexeme-cst-raw-name-okp).
      The lexer accepts these lexemes and the tokenizer rejects them,
      so the condition is not part of @(tsee lexing-okp);
      it is incorporated into @(tsee lexing-in-edition-okp).")
    (xdoc::li
     "[SC6] Edition-dependent keyword classification:
      formalized here,
      as @(tsee keyword-lexeme-cst-p),
      which says which lexemes are keywords in each edition,
      from the tables in @(see keywords).
      It depends on the edition,
      so it is not part of @(tsee lexing-okp);
      the tokenizer classifies the lexemes.")
    (xdoc::li
     "[SC7] Reserved numeric forms
      (text with a radix prefix that is not a literal in that radix;
      a literal with a radix prefix followed by a period of its own;
      and a number literal followed by @('e') or @('E')):
      formalized here,
      as @(tsee lexeme-cst-reserved-number-okp),
      incorporated into @(tsee lexing-okp).")
    (xdoc::li
     "[SC8] Reserved prefixes
      (an identifier or keyword, or a lone underscore,
      immediately followed by @('#'), a single quote, or a double quote;
      and a lifetime other than a raw one
      immediately followed by @('#')):
      formalized here,
      as @(tsee lexeme-cst-reserved-prefix-okp),
      incorporated into @(tsee lexing-okp).")
    (xdoc::li
     "[SC9] Unicode escape values
      (Unicode scalar values, and nonzero in C strings):
      formalized here,
      as @(tsee lexeme-cst-unicode-escapes-okp),
      incorporated into @(tsee lexing-okp).")
    (xdoc::li
     "[SC10] Raw string termination, and at most 255 @('#')
      before the opening double quote:
      formalized here,
      as @(tsee raw-content-string-p),
      incorporated into lexeme validity
      via @(tsee lexeme-cst-okp).")
    (xdoc::li
     "[SC11] Underscore after a character or string literal:
      formalized here,
      as @(tsee lexeme-cst-literal-underscore-okp),
      incorporated into @(tsee lexing-okp).")
    (xdoc::li
     "[SC12] Single quote after a lifetime:
      formalized here,
      as @(tsee lexeme-cst-lifetime-quote-okp),
      incorporated into @(tsee lexing-okp).")
    (xdoc::li
     "[SC13] String continuations take all the whitespace after them:
      formalized here,
      as @(tsee lexeme-cst-string-continues-okp),
      incorporated into lexeme validity
      via @(tsee lexeme-cst-okp).")
    (xdoc::li
     "[SC14] Float literals ending with a period
      are not followed by a period, an underscore,
      or the start of an identifier:
      formalized here,
      as @(tsee lexeme-cst-float-period-okp),
      incorporated into @(tsee lexeme-cst-maximal-p)
      and @(tsee lexing-okp).")
    (xdoc::li
     "[SC15] Reserved guards of edition 2024
      (a @('#') immediately followed by
      another @('#') or by a double quote):
      formalized here,
      as @(tsee lexeme-cst-reserved-guard-okp).
      It depends on the edition,
      so it is not part of @(tsee lexing-okp):
      the lexer accepts these forms,
      and the tokenizer rejects them in edition 2024.
      It is incorporated into @(tsee lexing-in-edition-okp)."))
   (xdoc::p
    "Some of these side conditions are there
     because rustc and the Rust Reference differ,
     and we follow rustc;
     see @(see reference-vs-rustc).")
   (xdoc::p
    "An important structural point:
     the side conditions constrain the set of valid lexeme trees
     (see @(tsee lexeme-cst-okp)),
     and the maximal-munch condition [SC1] maximizes
     over that constrained set.
     For example, without [SC2] in the candidate set,
     maximal munch would extend a block comment
     past its first balanced closing @('*/')
     to a later one.
     One side condition on the candidates, [SC14],
     depends on the input after the candidate,
     so it is not part of @(tsee lexeme-cst-okp),
     but @(tsee lexeme-cst-maximal-p) applies it to the candidates.")
   (xdoc::p
    "Other side conditions, like [SC7] and [SC8],
     do not restrict the candidates:
     they reject an input
     because of the lexemes that maximal munch chooses for it.")
   (xdoc::p
    "There are two predicates for a whole lexing.
     The first, @(tsee lexing-okp), does not take the edition:
     lexing does not depend on it,
     and this predicate is the specification of the lexer.
     It leaves out two of the conditions that reject an input,
     which the tokenizer checks instead:
     [SC5], in both supported editions, 2021 and 2024,
     and [SC15], in edition 2024.
     So it accepts @('r#crate') and @('##'),
     which tokenization then rejects,
     the first in both editions and the second in edition 2024.
     The second predicate, @(tsee lexing-in-edition-okp),
     adds those two conditions:
     it is the specification of
     the inputs that are lexically valid in an edition.")
   (xdoc::p
    "Maximal munch is our reading of how the rules combine:
     the Reference at version 1.87.0 does not state it,
     and the descriptions whose alternatives are tried in order
     do not need it (see @(see related-lexer-descriptions),
     which also says what plays the part of
     each side condition in those descriptions).
     It decides between texts of different lengths, and nothing else.
     So where rustc's token is not the longest text that matches a rule,
     a side condition must take the longer texts out of the candidates:
     that is what [SC2], [SC10], and [SC14] do.
     And where the rules give one text two readings,
     maximal munch does not choose between them:
     the grammar or a side condition must exclude one.
     We know of three such cases.
     Text that starts with a radix prefix also reads as
     the decimal literal @('0') with a suffix,
     as in @('0x3') with suffix @('x3');
     [SC7] excludes that reading.
     The whitespace after a string continuation also reads as
     characters of the string;
     [SC13] excludes that reading.
     And in the Reference a hexadecimal literal also reads as
     a shorter one with a suffix,
     as in @('0x1f') with suffix @('f');
     our grammar excludes that reading:
     the suffix of a hexadecimal literal has a rule of its own,
     @('suffix-no-hex-digit'),
     which does not start with a hexadecimal digit."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC13] String continuations.

(define string-continue-item-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is an item of the body of a string literal
          that holds a string continuation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The body of a string, byte string, or C string literal
     is a repetition of a group of alternatives.
     So each item of the body is a CST without a rule name
     that has a single subtree;
     here that subtree is a @('string-continue')."))
  (b* ((sub (abnf::check-tree-nonleaf-1-1 tree nil))
       ((when (reserrp sub)) nil))
    (not (reserrp (abnf::check-tree-nonleaf sub "string-continue")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-continues-maximal-p ((items abnf::tree-listp))
  :returns (yes/no booleanp)
  :short "Check that, among the items of the body of a string literal,
          no string continuation is immediately followed by
          whitespace that it could have taken."
  :long
  (xdoc::topstring
   (xdoc::p
    "The item after a string continuation must not start with
     a tab, a line feed, a carriage return, or a space,
     which are the characters of @('skipped-whitespace-char').
     An item that starts with one of them
     consists of just that character,
     as a character of the literal;
     so the string continuation before it would not have taken
     the whole run of whitespace after its line feed.
     (No item actually starts with a carriage return,
     which the grammar excludes from the characters of these literals;
     we include it here to match the rule.)"))
  :measure (len items)
  (b* ((items (abnf::tree-list-fix items))
       ((when (endp items)) t)
       ((when (endp (cdr items))) t)
       (next (abnf::tree->string (cadr items)))
       ((when (and (string-continue-item-cst-p (car items))
                   (or (prefixp (list #x9) next) ; tab
                       (prefixp (list #xA) next) ; line feed
                       (prefixp (list #xD) next) ; carriage return
                       (prefixp (list #x20) next)))) ; space
        nil))
    (string-continues-maximal-p (cdr items))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-string-continues-okp ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check that the string continuations in a lexeme CST
          take all the whitespace that follows them [SC13]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is about CSTs of the form @('lexeme -> token -> R')
     where @('R') is one of the rules for
     string, byte string, and C string literals,
     which are the rules that have string continuations:
     the items of the body of the literal must satisfy
     @(tsee string-continues-maximal-p).
     Every other lexeme CST satisfies this condition.")
   (xdoc::p
    "A string continuation consists of a backslash, a line feed,
     and the run of tabs, line feeds, carriage returns, and spaces
     that follows.
     That whole run is skipped when the literal is evaluated.
     Since tabs, line feeds, and spaces
     are also characters of these literals,
     the grammar alone has several CSTs for a literal with such a run,
     which differ in where the string continuation ends.
     This condition leaves only the CST
     in which the string continuation takes the whole run,
     so that the @('string-continue') subtrees of a valid CST
     cover exactly the text that is skipped.")
   (xdoc::p
    "Unlike [SC2], this condition does not change
     which strings have valid lexeme CSTs:
     a literal with a CST that violates it
     also has a CST that satisfies it.
     So it has no effect on maximal munch [SC1]."))
  (b* ((sub1 (abnf::check-tree-nonleaf-1-1 tree "lexeme"))
       ((when (reserrp sub1)) t)
       (sub2 (abnf::check-tree-nonleaf-1-1 sub1 "token"))
       ((when (reserrp sub2)) t)
       (branches (abnf::check-tree-nonleaf-4 sub2 "string-literal"))
       ((when (not (reserrp branches)))
        (string-continues-maximal-p
         (abnf::tree-list-tuple4->2nd branches)))
       (branches (abnf::check-tree-nonleaf-5 sub2 "byte-string-literal"))
       ((when (not (reserrp branches)))
        (string-continues-maximal-p
         (abnf::tree-list-tuple5->3rd branches)))
       (branches (abnf::check-tree-nonleaf-5 sub2 "c-string-literal"))
       ((when (not (reserrp branches)))
        (string-continues-maximal-p
         (abnf::tree-list-tuple5->3rd branches))))
    t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC10] Raw string termination.

(define leading-pound-count ((nats nat-listp))
  :returns (count natp)
  :short "Number of @('#') at the start of a character sequence."
  :measure (len nats)
  (b* ((nats (nat-list-fix nats)))
    (if (prefixp (list #x23) nats) ; #
        (1+ (leading-pound-count (cdr nats)))
      0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define raw-rest-closes-p ((nats nat-listp) (pounds natp))
  :returns (yes/no booleanp)
  :short "Check if a character sequence closes a raw literal
          with a given number of @('#') exactly at its end."
  :long
  (xdoc::topstring
   (xdoc::p
    "The sequence is what follows the opening double quote.
     A raw literal with @('n') @('#') before that double quote
     ends at the first double quote that is followed by @('n') @('#'):
     that is its terminator.
     We scan the sequence left to right for the terminator;
     where we find it, it must be all that is left of the sequence.
     This is what makes a valid raw literal end
     at its first terminator;
     see @(tsee raw-content-string-p).")
   (xdoc::p
    "A double quote is followed by @('n') @('#')
     when at least @('n') @('#') come right after it."))
  :measure (len nats)
  (b* ((nats (nat-list-fix nats))
       ((when (endp nats)) nil)
       ((when (and (eql (car nats) #x22) ; double quote
                   (<= (nfix pounds) (leading-pound-count (cdr nats)))))
        (equal (len (cdr nats)) (nfix pounds))))
    (raw-rest-closes-p (cdr nats) pounds)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define raw-content-string-p ((nats nat-listp))
  :returns (yes/no booleanp)
  :short "Check if a character sequence is exactly
          the content of one raw literal [SC10]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The content of a raw literal is what is between
     its prefix (@('r'), @('br'), or @('cr')) and its suffix, if any:
     some number @('n') of @('#'), a double quote, the body,
     a double quote, and @('n') @('#') again.
     The sequence must start with at most 255 @('#')
     and a double quote,
     and what follows must close the literal exactly at its end
     (see @(tsee raw-rest-closes-p)).
     So the body contains no double quote followed by @('n') @('#').")
   (xdoc::p
    "Which characters the body may contain
     depends on the kind of raw literal;
     the grammar rules say that, and this predicate does not."))
  (b* ((nats (nat-list-fix nats))
       (pounds (leading-pound-count nats))
       (rest (nthcdr pounds nats)))
    (and (<= pounds 255)
         (prefixp (list #x22) rest) ; double quote
         (raw-rest-closes-p (cdr rest) pounds))))

;;;;;;;;;;;;;;;;;;;;

(assert-event (raw-content-string-p (string=>nats "\"\"")))
(assert-event (raw-content-string-p (string=>nats "\"a\"")))
(assert-event (raw-content-string-p (string=>nats "#\"a\"#")))
(assert-event (raw-content-string-p (string=>nats "#\"a\"\"#")))
(assert-event (raw-content-string-p (string=>nats "##\"a\"#b\"##")))
(assert-event (raw-content-string-p (string=>nats "#\"a
multi-line\"#")))
(assert-event (not (raw-content-string-p (string=>nats "\"a\" \"b\""))))
(assert-event (not (raw-content-string-p (string=>nats "#\"a\"#\"#"))))
(assert-event (not (raw-content-string-p (string=>nats "#\"a\"##"))))
(assert-event (not (raw-content-string-p (string=>nats "##\"a\"#"))))
(assert-event (not (raw-content-string-p (string=>nats "#\"a\""))))
(assert-event (not (raw-content-string-p (string=>nats "a\"\""))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define raw-content-branch-okp ((trees abnf::tree-listp))
  :returns (yes/no booleanp)
  :short "Check that the branch of a raw literal CST that holds its content
          has text that is exactly the content of one raw literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "The branch consists of one tree,
     for @('raw-string-content'), @('raw-byte-string-content'),
     or @('raw-c-string-content');
     see @(tsee raw-content-string-p) for the condition on its text."))
  (b* (((unless (abnf::tree-list-terminatedp trees)) t)) ; never
    ;; (a lexeme CST is terminated, and so are its subtrees)
    (raw-content-string-p (abnf::tree-list->string trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-raw-termination-okp ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check that a lexeme CST holding a raw literal
          ends the literal at its first terminator,
          and has at most 255 @('#')
          before the opening double quote [SC10]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is about CSTs of the form @('lexeme -> token -> R')
     where @('R') is one of the rules for
     raw string, raw byte string, and raw C string literals.
     Each has three branches:
     the prefix, the content, and the optional suffix.
     The content must satisfy @(tsee raw-content-branch-okp).
     Every other lexeme CST satisfies this condition.")
   (xdoc::p
    "The rules for the content put the same number @('n') of @('#')
     before the opening double quote and after the closing one,
     but they let the body be any characters.
     So for the input @('r\"a\" \"b\"'),
     not only @('r\"a\"') but also the whole input
     matches the rule for raw string literals,
     with the body @('a\" \"b').
     A raw literal ends at the first double quote
     that is followed by @('n') @('#'),
     as a block comment ends at its first balanced @('*/').
     So, like [SC2], this condition restricts
     the candidates of maximal munch [SC1]:
     without it, maximal munch would take the longer text.")
   (xdoc::p
    "A raw literal with more than 255 @('#')
     before its opening double quote is not valid either.
     rustc rejects an input with one.
     So does this specification,
     although here the text is just not a lexeme:
     the longest lexeme at its start is then
     the identifier @('r'), @('br'), or @('cr'),
     which is followed by @('#'),
     and that is a reserved prefix [SC8]."))
  (b* ((sub1 (abnf::check-tree-nonleaf-1-1 tree "lexeme"))
       ((when (reserrp sub1)) t)
       (sub2 (abnf::check-tree-nonleaf-1-1 sub1 "token"))
       ((when (reserrp sub2)) t)
       (branches (abnf::check-tree-nonleaf-3 sub2 "raw-string-literal"))
       ((when (not (reserrp branches)))
        (raw-content-branch-okp (abnf::tree-list-tuple3->2nd branches)))
       (branches (abnf::check-tree-nonleaf-3 sub2 "raw-byte-string-literal"))
       ((when (not (reserrp branches)))
        (raw-content-branch-okp (abnf::tree-list-tuple3->2nd branches)))
       (branches (abnf::check-tree-nonleaf-3 sub2 "raw-c-string-literal"))
       ((when (not (reserrp branches)))
        (raw-content-branch-okp (abnf::tree-list-tuple3->2nd branches))))
    t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-okp ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is a valid lexeme CST:
          a lexeme CST satisfying the side conditions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This conjoins the grammar match
     with [SC2] (block comment closing),
     [SC10] (raw string termination),
     and [SC13] (string continuations).
     For [SC2], if the lexeme's string starts with @('/*'),
     the lexeme can only be a block comment, doc comment or not
     (no other lexeme's string starts that way),
     and its string must be exactly one complete block comment.
     For [SC10], see @(tsee lexeme-cst-raw-termination-okp).
     For [SC13], see @(tsee lexeme-cst-string-continues-okp).
     The side condition [SC14] also restricts the valid lexemes,
     but according to the input that follows them,
     so it is a separate predicate,
     @(tsee lexeme-cst-float-period-okp).")
   (xdoc::p
    "These are the side conditions that say which trees are lexemes,
     for maximal munch [SC1] to choose among.
     The side conditions that reject an input
     because of the lexemes chosen for it
     are conjuncts of @(tsee lexing-okp) instead."))
  (and (lexeme-cst-p tree)
       (b* ((string (abnf::tree->string tree)))
         (implies (prefixp (list #x2F #x2A) string) ; starts with /*
                  (block-comment-string-p string)))
       (lexeme-cst-raw-termination-okp tree)
       (lexeme-cst-string-continues-okp tree)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC3] Carriage return in doc comments.

(define doc-comment-lexeme-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is a lexeme CST holding a doc comment."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the lexemes subject to
     the side condition [SC3]:
     CSTs of the form @('lexeme -> comment -> R')
     where @('R') is one of the four rules for doc comments,
     line or block, outer or inner."))
  (b* ((sub1 (abnf::check-tree-nonleaf-1-1 tree "lexeme"))
       ((when (reserrp sub1)) nil)
       (sub2 (abnf::check-tree-nonleaf-1-1 sub1 "comment"))
       ((when (reserrp sub2)) nil)
       (rulename? (abnf::check-tree-nonleaf? sub2)))
    (and (member-equal rulename?
                       '("outer-line-doc"
                         "inner-line-doc"
                         "outer-block-doc"
                         "inner-block-doc"))
         t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-doc-comment-cr-okp ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check that a lexeme CST holding a doc comment
          has no carriage return [SC3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A doc comment lexeme
     (see @(tsee doc-comment-lexeme-cst-p))
     must not contain a carriage return (U+000D).
     rustc rejects an input with such a doc comment.
     A carriage return before a line feed does not count:
     the two become a line feed before lexing,
     so they do not reach the lexer.
     Other comments may contain carriage returns.")
   (xdoc::p
    "Like [SC8], this condition rejects the whole lexing,
     so it is a conjunct of @(tsee lexing-okp)
     rather than part of the candidate set @(tsee lexeme-cst-okp).
     The rules let a doc comment extend over a carriage return,
     and maximal munch takes that longer comment,
     which this condition then rejects.
     If the condition restricted the candidates instead,
     maximal munch would take the line doc comment
     that ends just before the carriage return,
     and the input @('///a'), carriage return, @('b') would lex,
     as a doc comment, whitespace, and an identifier."))
  (implies (doc-comment-lexeme-cst-p tree)
           (not (member-equal #xd (abnf::tree->string tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC9] Unicode escape values.

(define hex-digit-code-value ((code natp))
  :returns (value? acl2::maybe-natp
                   :rule-classes :type-prescription
                   :hints (("Goal" :in-theory (enable acl2::maybe-natp
                                                      natp))))
  :short "Value of a character as a hexadecimal digit, if it is one."
  (b* ((code (nfix code)))
    (cond ((and (<= #x30 code) (<= code #x39)) (- code #x30)) ; 0-9
          ((and (<= #x41 code) (<= code #x46)) (- code #x37)) ; A-F
          ((and (<= #x61 code) (<= code #x66)) (- code #x57)) ; a-f
          (t nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hex-digits/underscores-value ((nats nat-listp) (value natp))
  :returns (new-value natp)
  :short "Value of a sequence of hexadecimal digits and underscores,
          read as a hexadecimal number after the digits already read."
  :long
  (xdoc::topstring
   (xdoc::p
    "The second argument is the value of the digits already read:
     it is 0 for a whole number.
     Each digit multiplies the value so far by 16 and adds its own.
     The underscores are ignored,
     and so is any other character that is not a hexadecimal digit."))
  :measure (len nats)
  (b* ((nats (nat-list-fix nats))
       (value (nfix value))
       ((when (endp nats)) value)
       (digit? (hex-digit-code-value (car nats))))
    (hex-digits/underscores-value (cdr nats)
                                  (if digit?
                                      (+ (* 16 value) digit?)
                                    value))))

;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (hex-digits/underscores-value (string=>nats "0") 0) 0))
(assert-event
 (equal (hex-digits/underscores-value (string=>nats "7f") 0) #x7f))
(assert-event
 (equal (hex-digits/underscores-value (string=>nats "1_F6_00") 0) #x1f600))
(assert-event
 (equal (hex-digits/underscores-value (string=>nats "10FFFF") 0) #x10ffff))
(assert-event
 (equal (hex-digits/underscores-value (string=>nats "0_0_d_8_0_0_") 0) #xd800))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unicode-escape-item-value ((tree abnf::treep))
  :returns (value? acl2::maybe-natp)
  :short "Value of the unicode escape
          that an item of the body of a literal holds, if it holds one."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each item of the body of a string or C string literal
     is a CST without a rule name that has a single subtree
     (see @(tsee string-continue-item-cst-p));
     so is what a character literal has between its quotes.
     Here that subtree is a @('unicode-escape'),
     which has three branches:
     the characters @('\\u{'),
     the hexadecimal digits, each with the underscores after it,
     and the closing brace.
     The value is that of the digits,
     read as a hexadecimal number
     (see @(tsee hex-digits/underscores-value))."))
  (b* ((sub (abnf::check-tree-nonleaf-1-1 tree nil))
       ((when (reserrp sub)) nil)
       (branches (abnf::check-tree-nonleaf-3 sub "unicode-escape"))
       ((when (reserrp branches)) nil)
       (digits (abnf::tree-list-tuple3->2nd branches))
       ((unless (abnf::tree-list-terminatedp digits)) nil)) ; never
    (hex-digits/underscores-value (abnf::tree-list->string digits) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unicode-escape-items-okp ((items abnf::tree-listp)
                                  (nonzerop booleanp))
  :returns (yes/no booleanp)
  :short "Check that the unicode escapes
          among the items of the body of a literal
          have valid values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The value of each unicode escape
     (see @(tsee unicode-escape-item-value))
     must be a Unicode scalar value:
     at most @('10FFFF'), and not a surrogate
     (see @(tsee uni-scalar-value-p)).
     If the flag is set, it must also be nonzero."))
  :measure (len items)
  (b* ((items (abnf::tree-list-fix items))
       ((when (endp items)) t)
       (value? (unicode-escape-item-value (car items))))
    (and (or (not value?)
             (and (uni-scalar-value-p value?)
                  (not (and nonzerop
                            (eql value? 0)))))
         (unicode-escape-items-okp (cdr items) nonzerop))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-unicode-escapes-okp ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check that the unicode escapes in a lexeme CST
          have valid values [SC9]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is about CSTs of the form @('lexeme -> token -> R')
     where @('R') is one of the rules for
     character, string, and C string literals,
     which are the rules that have unicode escapes.
     The rule for unicode escapes
     allows any number of up to six hexadecimal digits.
     The value of each unicode escape must be a Unicode scalar value;
     in a C string literal, which cannot contain a zero,
     it must also be nonzero
     (see @(tsee unicode-escape-items-okp)).
     Every other lexeme CST satisfies this condition.")
   (xdoc::p
    "Like [SC8], this condition rejects the whole lexing,
     so it is a conjunct of @(tsee lexing-okp)
     rather than part of the candidate set @(tsee lexeme-cst-okp).
     In rustc, whether an escape is valid
     never affects where a literal ends:
     the text @('\"\\u{110000}\"') is one string literal,
     and an error."))
  (b* ((sub1 (abnf::check-tree-nonleaf-1-1 tree "lexeme"))
       ((when (reserrp sub1)) t)
       (sub2 (abnf::check-tree-nonleaf-1-1 sub1 "token"))
       ((when (reserrp sub2)) t)
       (branches (abnf::check-tree-nonleaf-4 sub2 "char-literal"))
       ((when (not (reserrp branches)))
        (unicode-escape-items-okp (abnf::tree-list-tuple4->2nd branches)
                                  nil))
       (branches (abnf::check-tree-nonleaf-4 sub2 "string-literal"))
       ((when (not (reserrp branches)))
        (unicode-escape-items-okp (abnf::tree-list-tuple4->2nd branches)
                                  nil))
       (branches (abnf::check-tree-nonleaf-5 sub2 "c-string-literal"))
       ((when (not (reserrp branches)))
        (unicode-escape-items-okp (abnf::tree-list-tuple5->3rd branches)
                                  t)))
    t))

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

(define underscore-lexeme-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is a lexeme CST holding a lone underscore."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lone underscore is a punctuation token,
     also subject to the reserved-prefix side condition [SC8].
     No other lexeme consists of just an underscore
     (an identifier starting with an underscore has more characters),
     so it suffices to check the string of the tree."))
  (equal (abnf::tree->string tree) (list #x5f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define non-raw-lifetime-lexeme-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is a lexeme CST holding
          a lifetime token that is not a raw lifetime."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the lifetime lexemes subject to
     the reserved-prefix side condition [SC8]:
     CSTs of the form @('lexeme -> token -> lifetime-token')
     whose @('lifetime-token') does not consist of
     a single @('raw-lifetime') subtree."))
  (b* ((sub1 (abnf::check-tree-nonleaf-1-1 tree "lexeme"))
       ((when (reserrp sub1)) nil)
       (sub2 (abnf::check-tree-nonleaf-1-1 sub1 "token"))
       ((when (reserrp sub2)) nil)
       ((when (reserrp (abnf::check-tree-nonleaf sub2 "lifetime-token")))
        nil)
       (sub3 (abnf::check-tree-nonleaf-1-1 sub2 "lifetime-token")))
    (or (reserrp sub3)
        (not (equal (abnf::check-tree-nonleaf? sub3) "raw-lifetime")))))

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
     (see @(tsee identifier-or-keyword-lexeme-cst-p)),
     or a lone underscore
     (see @(tsee underscore-lexeme-cst-p)),
     must not be immediately followed by
     @('#') (U+0023), @(''') (U+0027), or @('\"') (U+0022):
     such forms are reserved prefixes
     in both supported editions, 2021 and 2024.
     Likewise, a lifetime lexeme that is not a raw lifetime
     (see @(tsee non-raw-lifetime-lexeme-cst-p))
     must not be immediately followed by @('#'):
     such forms are reserved lifetime prefixes.
     The Reference exempts @(''r'),
     but rustc rejects @(''r#') when no raw lifetime follows,
     and so does this condition:
     when a raw lifetime follows, maximal munch makes it the lexeme.")
   (xdoc::p
    "Note that this condition rejects the whole lexing
     rather than steering maximal munch to a shorter lexeme:
     in Rust, @('foo#bar') is a lexing error,
     not an alternative lexing.
     Accordingly, this condition is a conjunct of
     @(tsee lexing-okp) about the chosen lexemes,
     and is not part of the candidate set
     @(tsee lexeme-cst-okp)
     over which @(tsee lexeme-cst-maximal-p) maximizes."))
  (b* ((rest-input (nat-list-fix rest-input)))
    (and (implies (or (identifier-or-keyword-lexeme-cst-p tree)
                      (underscore-lexeme-cst-p tree))
                  (and (not (prefixp (list #x23) rest-input)) ; #
                       (not (prefixp (list #x27) rest-input)) ; '
                       (not (prefixp (list #x22) rest-input)))) ; "
         (implies (non-raw-lifetime-lexeme-cst-p tree)
                  (not (prefixp (list #x23) rest-input)))))) ; #

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC6] Keyword classification.

(define keyword-lexeme-cst-p ((tree abnf::treep) (edition rust::editionp))
  :returns (yes/no booleanp)
  :short "Check if a tree is a lexeme CST holding
          a keyword of a given edition [SC6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A keyword is an identifier-or-keyword lexeme
     (see @(tsee identifier-or-keyword-lexeme-cst-p))
     whose text is a strict or reserved keyword of the edition
     (see @(tsee keyword-p)).
     The token of such a lexeme is a keyword token;
     the token of every other identifier-or-keyword lexeme
     is an identifier token, weak keywords included.
     A raw identifier is never a keyword:
     @('r#fn') is an identifier.")
   (xdoc::p
    "This condition classifies lexemes; it rejects none.
     It depends on the edition:
     @('gen') is a keyword in edition 2024
     and an identifier in edition 2021.
     Lexing does not depend on the edition,
     so this condition has no part in @(tsee lexing-okp):
     the tokenizer, which takes the edition, classifies the lexemes
     (see @(tsee abs-identifier-or-keyword)).")
   (xdoc::p
    "Every keyword consists of ASCII characters,
     so text with any other character is not a keyword."))
  (b* (((unless (identifier-or-keyword-lexeme-cst-p tree)) nil)
       (string (abnf::tree->string tree))
       ((unless (acl2::unsigned-byte-listp 8 string)) nil))
    (keyword-p (nats=>string string) edition)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC11] Underscore after a literal.

(define char-or-string-literal-lexeme-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is a lexeme CST holding
          a character, byte, or string literal token,
          of any kind, raw or not."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the lexemes subject to
     the side condition [SC11]:
     CSTs of the form @('lexeme -> token -> R')
     where @('R') is one of the eight rules
     for character, byte, string, byte string, and C string literals
     and their raw forms."))
  (b* ((sub1 (abnf::check-tree-nonleaf-1-1 tree "lexeme"))
       ((when (reserrp sub1)) nil)
       (sub2 (abnf::check-tree-nonleaf-1-1 sub1 "token"))
       ((when (reserrp sub2)) nil)
       (rulename? (abnf::check-tree-nonleaf? sub2)))
    (and (member-equal rulename?
                       '("char-literal"
                         "byte-literal"
                         "string-literal"
                         "byte-string-literal"
                         "c-string-literal"
                         "raw-string-literal"
                         "raw-byte-string-literal"
                         "raw-c-string-literal"))
         t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-literal-underscore-okp ((tree abnf::treep)
                                           (rest-input nat-listp))
  :returns (yes/no booleanp)
  :short "Check that a lexeme CST holding a character or string literal
          is not immediately followed by an underscore [SC11]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A character, byte, or string literal lexeme
     (see @(tsee char-or-string-literal-lexeme-cst-p))
     must not be immediately followed by @('_') (U+005F).
     rustc's lexer reads such an underscore as the suffix of the literal,
     and rejects it (\"underscore literal suffix is not allowed\").
     In the grammar, a suffix is an identifier or keyword,
     which excludes a lone underscore, as in the Reference;
     so the grammar alone would lex the underscore as a separate token.
     We follow rustc.
     Since suffixes are lexed greedily,
     an underscore right after a literal
     is never followed by an identifier-continue character.")
   (xdoc::p
    "Number literals need no such condition:
     after one, maximal munch absorbs an underscore
     into the digits or the suffix,
     and a float literal that ends with its period
     is not followed by an underscore, by [SC14].")
   (xdoc::p
    "Like [SC8], this condition rejects the whole lexing,
     so it is a conjunct of @(tsee lexing-okp)
     rather than part of the candidate set @(tsee lexeme-cst-okp)."))
  (implies (char-or-string-literal-lexeme-cst-p tree)
           (not (prefixp (list #x5f) (nat-list-fix rest-input))))) ; _

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC12] Single quote after a lifetime.

(define lifetime-lexeme-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is a lexeme CST holding a lifetime token,
          raw or not."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the lexemes subject to
     the side condition [SC12]:
     CSTs of the form @('lexeme -> token -> lifetime-token')."))
  (b* ((sub1 (abnf::check-tree-nonleaf-1-1 tree "lexeme"))
       ((when (reserrp sub1)) nil)
       (sub2 (abnf::check-tree-nonleaf-1-1 sub1 "token"))
       ((when (reserrp sub2)) nil))
    (not (reserrp (abnf::check-tree-nonleaf sub2 "lifetime-token")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-lifetime-quote-okp ((tree abnf::treep)
                                       (rest-input nat-listp))
  :returns (yes/no booleanp)
  :short "Check that a lexeme CST holding a lifetime
          is not immediately followed by a single quote [SC12]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lifetime lexeme (see @(tsee lifetime-lexeme-cst-p)),
     raw or not,
     must not be immediately followed by @(''') (U+0027).
     rustc reads such text, e.g. @(''ab''),
     as a character literal with more than one character,
     and rejects it.")
   (xdoc::p
    "Like [SC8] and [SC11], this condition rejects the whole lexing,
     so it is a conjunct of @(tsee lexing-okp).
     The Reference states it inside the lifetime token rule
     (\"not immediately followed by '\");
     read as a restriction on the candidate lexemes,
     it would let maximal munch pick a shorter lifetime instead:
     @(''ab' '') would lex as
     the lifetime @(''a') followed by the byte literal @('b' ''),
     which rustc rejects."))
  (implies (lifetime-lexeme-cst-p tree)
           (not (prefixp (list #x27) (nat-list-fix rest-input))))) ; '

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC14] Float literals ending with a period.

(define number-literal-lexeme-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is a lexeme CST holding
          an integer literal or a float literal token."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the lexemes subject to
     the side conditions [SC7] and [SC14]:
     CSTs of the form @('lexeme -> token -> R')
     where @('R') is @('integer-literal') or @('float-literal')."))
  (b* ((sub1 (abnf::check-tree-nonleaf-1-1 tree "lexeme"))
       ((when (reserrp sub1)) nil)
       (sub2 (abnf::check-tree-nonleaf-1-1 sub1 "token"))
       ((when (reserrp sub2)) nil)
       (rulename? (abnf::check-tree-nonleaf? sub2)))
    (and (member-equal rulename?
                       '("integer-literal"
                         "float-literal"))
         t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-period-lexeme-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is a lexeme CST holding
          a float literal that ends with its period."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the lexemes subject to
     the side condition [SC14]:
     CSTs of the form @('lexeme -> token -> float-literal')
     whose text ends with a period.
     They are the CSTs for the first alternative
     of the @('float-literal') rule:
     the text of the other alternatives ends with
     a digit, an underscore, or the last character of a suffix."))
  (b* ((sub1 (abnf::check-tree-nonleaf-1-1 tree "lexeme"))
       ((when (reserrp sub1)) nil)
       (sub2 (abnf::check-tree-nonleaf-1-1 sub1 "token"))
       ((when (reserrp sub2)) nil)
       ((when (reserrp (abnf::check-tree-nonleaf sub2 "float-literal")))
        nil))
    (equal (car (last (abnf::tree->string tree))) #x2e))) ; .

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-start-code-p ((code natp))
  :returns (yes/no booleanp)
  :short "Check if a character is one that can start an identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the characters of the rule @('identifier-start'):
     for now, the ASCII letters [SC4]."))
  (b* ((code (nfix code)))
    (or (and (<= #x41 code) (<= code #x5a)) ; A-Z
        (and (<= #x61 code) (<= code #x7a))))) ; a-z

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define number-period-follower-okp ((nats nat-listp))
  :returns (yes/no booleanp)
  :short "Check that a character sequence may follow
          the period of a number literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "A period right after the digits of a number literal
     belongs to the literal
     unless it is immediately followed by
     another period, an underscore,
     or a character that can start an identifier.
     So @('1..2') has a range operator
     and @('1.max(2)') a method call,
     while the period of @('1.') and @('1.+2')
     belongs to a float literal.
     The end of the input may follow such a period too."))
  (b* ((nats (nat-list-fix nats))
       ((when (endp nats)) t)
       (code (car nats)))
    (not (or (eql code #x2e) ; .
             (eql code #x5f) ; _
             (identifier-start-code-p code)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-float-period-okp ((tree abnf::treep)
                                     (rest-input nat-listp))
  :returns (yes/no booleanp)
  :short "Check that a lexeme CST holding
          a float literal that ends with its period
          is followed by input that leaves the period to it [SC14]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A float literal lexeme that ends with its period
     (see @(tsee float-period-lexeme-cst-p))
     must be followed by input that satisfies
     @(tsee number-period-follower-okp).
     Every other lexeme CST satisfies this condition.")
   (xdoc::p
    "Like [SC2], and unlike [SC8], [SC11], and [SC12],
     this condition restricts the candidates of maximal munch [SC1]:
     in @('1..2'), the text @('1.') is not a lexeme at all,
     so that the longest lexeme at the start is @('1'),
     and the input is not rejected.
     But unlike [SC2], it depends on the input after the candidate,
     so it cannot be a conjunct of @(tsee lexeme-cst-okp),
     which sees only the tree.
     Instead, @(tsee lexeme-cst-maximal-p) requires it of the candidates,
     and @(tsee lexing-okp) of the chosen lexemes."))
  (implies (float-period-lexeme-cst-p tree)
           (number-period-follower-okp rest-input)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC7] Reserved numeric forms.

(define dec-integer-literal-lexeme-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is a lexeme CST holding
          an integer literal whose digits form a @('dec-literal')."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the CSTs of the form
     @('lexeme -> token -> integer-literal')
     in which the first branch of the @('integer-literal'),
     a group, holds a @('dec-literal')
     rather than one of the literals with a radix prefix."))
  (b* ((sub1 (abnf::check-tree-nonleaf-1-1 tree "lexeme"))
       ((when (reserrp sub1)) nil)
       (sub2 (abnf::check-tree-nonleaf-1-1 sub1 "token"))
       ((when (reserrp sub2)) nil)
       (branches (abnf::check-tree-nonleaf-2 sub2 "integer-literal"))
       ((when (reserrp branches)) nil)
       (group (abnf::check-tree-list-1
               (abnf::tree-list-tuple2->1st branches)))
       ((when (reserrp group)) nil)
       (sub3 (abnf::check-tree-nonleaf-1-1 group nil))
       ((when (reserrp sub3)) nil))
    (not (reserrp (abnf::check-tree-nonleaf sub3 "dec-literal")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define radix-prefix-p ((nats nat-listp))
  :returns (yes/no booleanp)
  :short "Check if a character sequence starts with a radix prefix:
          @('0b'), @('0o'), or @('0x')."
  (b* ((nats (nat-list-fix nats)))
    (or (prefixp (list #x30 #x62) nats) ; 0b
        (prefixp (list #x30 #x6f) nats) ; 0o
        (prefixp (list #x30 #x78) nats)))) ; 0x

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digits/underscores-p ((nats nat-listp) (hexp booleanp))
  :returns (yes/no booleanp)
  :short "Check if a character sequence consists of
          digits and underscores."
  :long
  (xdoc::topstring
   (xdoc::p
    "The digits are the decimal digits,
     and also the hexadecimal digits if the flag is set."))
  :measure (len nats)
  (b* ((nats (nat-list-fix nats))
       ((when (endp nats)) t)
       (code (car nats)))
    (and (or (and (<= #x30 code) (<= code #x39)) ; 0-9
             (eql code #x5f) ; _
             (and hexp
                  (or (and (<= #x41 code) (<= code #x46)) ; A-F
                      (and (<= #x61 code) (<= code #x66))))) ; a-f
         (digits/underscores-p (cdr nats) hexp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define radix-literal-string-p ((nats nat-listp))
  :returns (yes/no booleanp)
  :short "Check if a character sequence consists of a radix prefix
          followed only by digits and underscores."
  :long
  (xdoc::topstring
   (xdoc::p
    "After @('0b') and @('0o') the digits are the decimal digits,
     and after @('0x') the hexadecimal digits.
     A lexeme that holds a literal with a radix prefix
     has such text exactly when the literal has no suffix:
     a suffix starts with a letter,
     which after a hexadecimal literal is not a hexadecimal digit."))
  (b* ((nats (nat-list-fix nats)))
    (cond ((or (prefixp (list #x30 #x62) nats) ; 0b
               (prefixp (list #x30 #x6f) nats)) ; 0o
           (digits/underscores-p (cddr nats) nil))
          ((prefixp (list #x30 #x78) nats) ; 0x
           (digits/underscores-p (cddr nats) t))
          (t nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-reserved-number-okp ((tree abnf::treep)
                                        (rest-input nat-listp))
  :returns (yes/no booleanp)
  :short "Check that a lexeme CST holding a number literal
          is not a reserved numeric form,
          by itself or with the remaining input [SC7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A number literal lexeme
     (see @(tsee number-literal-lexeme-cst-p))
     must not be any of the following.")
   (xdoc::ol
    (xdoc::li
     "Text that starts with a radix prefix
      (see @(tsee radix-prefix-p)),
      in a CST that reads it as the decimal literal @('0') with a suffix
      (see @(tsee dec-integer-literal-lexeme-cst-p)).
      For text that is a literal in the radix of its prefix,
      possibly with a suffix,
      there is also a CST that reads it that way,
      and that CST is the valid one.
      For other text, like @('0b') (no digits),
      @('0b12') (a digit that is not binary),
      and @('0o7e1') (a float literal with a radix prefix),
      there is only the CST with the decimal literal @('0'),
      which maximal munch makes the lexeme;
      such text is rejected.")
    (xdoc::li
     "A literal with a radix prefix and no suffix
      (see @(tsee radix-literal-string-p)),
      immediately followed by a period
      that would belong to the literal
      (see @(tsee number-period-follower-okp)),
      as in @('0x1.5') and @('0b1.').
      After a decimal literal, such a period makes a float literal;
      there are no float literals in the other radixes.")
    (xdoc::li
     "An integer or float literal
      immediately followed by @('e') or @('E'),
      as in @('1e'), @('1.0e+'), and @('2em').
      After a decimal integer literal,
      or after the fraction of a float literal,
      these letters start an exponent.
      With an exponent that has at least one digit,
      the longer float literal is the lexeme, by maximal munch;
      so a number literal followed by one of these letters
      has an exponent without digits after it.
      (No other kind of number literal that maximal munch chooses
      is followed by these letters:
      a suffix would extend over them,
      and so would the digits of a hexadecimal literal;
      a float literal that ends with its period
      is not followed by a letter, by [SC14];
      and a binary or octal literal followed by them
      falls under the first case.)"))
   (xdoc::p
    "Like [SC8], these conditions reject the whole lexing,
     so they are a conjunct of @(tsee lexing-okp)
     rather than part of the candidate set @(tsee lexeme-cst-okp):
     @('0b12') is an error, not @('0b1') followed by @('2')."))
  (b* (((unless (number-literal-lexeme-cst-p tree)) t)
       ((unless (abnf::tree-terminatedp tree)) t) ; never, for a lexeme CST
       (string (abnf::tree->string tree))
       (rest-input (nat-list-fix rest-input)))
    (and (not (and (radix-prefix-p string)
                   (dec-integer-literal-lexeme-cst-p tree)))
         (not (and (radix-literal-string-p string)
                   (prefixp (list #x2e) rest-input) ; .
                   (number-period-follower-okp (cdr rest-input))))
         (not (prefixp (list #x65) rest-input)) ; e
         (not (prefixp (list #x45) rest-input))))) ; E

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC5] Raw identifier and raw lifetime exclusions.

(define lexeme-cst-raw-name-okp ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check that a lexeme CST does not hold
          a raw identifier or a raw lifetime
          with an excluded name [SC5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The names @('crate'), @('self'), @('super'), and @('Self')
     cannot be the name of a raw identifier or of a raw lifetime.
     So the text of a lexeme must not be
     @('r#') or @(''r#') followed by one of those names.
     No other lexeme has such text,
     so it suffices to check the string of the tree.")
   (xdoc::p
    "Like [SC8], this condition rejects the whole lexing:
     @('r#crate') is an error, in both supported editions, 2021 and 2024;
     it is not @('r'), @('#'), and @('crate').")
   (xdoc::p
    "Unlike [SC8], this condition is not a conjunct of @(tsee lexing-okp),
     although it does not depend on the edition.
     The lexer accepts these lexemes,
     and the tokenizer, which is where the name of an identifier
     is looked at, rejects them
     (see @(tsee abs-raw-identifier) and @(tsee abs-lifetime-token)).
     rustc is organized the same way:
     its low-level lexer returns a raw identifier for @('r#crate'),
     and the next layer, which makes the tokens, reports the error.
     The condition is part of @(tsee tokenization-conditions-okp),
     and so of @(tsee lexing-in-edition-okp)."))
  (b* ((string (abnf::tree->string tree))
       (names (list (string=>nats "crate")
                    (string=>nats "self")
                    (string=>nats "super")
                    (string=>nats "Self"))))
    (not (or (and (prefixp (list #x72 #x23) string) ; r#
                  (member-equal (nthcdr 2 string) names))
             (and (prefixp (list #x27 #x72 #x23) string) ; 'r#
                  (member-equal (nthcdr 3 string) names))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC15] Reserved guards of edition 2024.

(define pound-lexeme-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a tree is a lexeme CST holding a lone @('#')."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lone @('#') is a punctuation token,
     subject to the side condition [SC15].
     No other lexeme consists of just a @('#'),
     so it suffices to check the string of the tree."))
  (equal (abnf::tree->string tree) (list #x23)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-reserved-guard-okp ((tree abnf::treep)
                                       (rest-input nat-listp))
  :returns (yes/no booleanp)
  :short "Check that a lexeme CST holding a @('#') does not form
          a reserved guard with the remaining input [SC15]."
  :long
  (xdoc::topstring
   (xdoc::p
    "In edition 2024, two forms are reserved for future use:
     two or more @('#') in a row,
     and one or more @('#') immediately followed by a string literal.
     Both start with a @('#') lexeme
     (see @(tsee pound-lexeme-cst-p))
     that is immediately followed by @('#') (U+0023)
     or by @('\"') (U+0022);
     and after a @('#'), a double quote can only start a string literal.
     So the condition is that no @('#') lexeme is followed in that way.
     Like [SC8], it rejects the whole lexing:
     in edition 2024, @('##') is an error,
     while in edition 2021 it is two tokens.")
   (xdoc::p
    "This condition holds in edition 2024 only.
     Lexing does not depend on the edition,
     so the condition is not a conjunct of @(tsee lexing-okp):
     the lexer accepts these forms,
     and the tokenizer, which takes the edition,
     rejects them in edition 2024
     (see @(tsee lexeme-csts-to-lexemes)).
     The condition is part of @(tsee tokenization-conditions-okp),
     and so of @(tsee lexing-in-edition-okp)."))
  (b* ((rest-input (nat-list-fix rest-input)))
    (implies (pound-lexeme-cst-p tree)
             (and (not (prefixp (list #x23) rest-input)) ; #
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
     @(see extra-grammatical-restrictions).
     A candidate is a valid lexeme CST together with
     the input that follows it,
     where the two make up the same input
     as the given tree and the input that follows that;
     the candidate must also satisfy [SC14]
     against the input that follows it
     (see @(tsee lexeme-cst-float-period-okp))."))
  (forall (tree2 rest-input2)
          (implies (and (abnf::treep tree2)
                        (nat-listp rest-input2)
                        (lexeme-cst-okp tree2)
                        (lexeme-cst-float-period-okp tree2 rest-input2)
                        (prefixp (abnf::tree->string tree)
                                 (abnf::tree->string tree2))
                        (equal (append (abnf::tree->string tree2)
                                       rest-input2)
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
     no doc comment lexeme contains a carriage return
     (see @(tsee lexeme-cst-doc-comment-cr-okp));
     every unicode escape in a lexeme has a valid value
     (see @(tsee lexeme-cst-unicode-escapes-okp));
     no float literal lexeme that ends with its period
     is followed by input that takes the period from it
     (see @(tsee lexeme-cst-float-period-okp));
     no number literal lexeme is a reserved numeric form,
     by itself or with what follows
     (see @(tsee lexeme-cst-reserved-number-okp));
     no lexeme forms a reserved prefix with what follows
     (see @(tsee lexeme-cst-reserved-prefix-okp));
     no character or string literal lexeme is followed by an underscore
     (see @(tsee lexeme-cst-literal-underscore-okp));
     no lifetime lexeme is followed by a single quote
     (see @(tsee lexeme-cst-lifetime-quote-okp));
     and together they cover the input exactly.")
   (xdoc::p
    "This predicate does not take the edition,
     since lexing does not depend on it.
     It is the specification of the lexer.
     It is not, by itself, the specification of
     the inputs that are lexically valid:
     it accepts two kinds of lexings that tokenization then rejects.")
   (xdoc::ul
    (xdoc::li
     "A lexing with a raw identifier or a raw lifetime
      whose name is @('crate'), @('self'), @('super'), or @('Self'),
      as in @('r#crate') and @(''r#self') [SC5].
      Tokenization rejects it
      in both supported editions, 2021 and 2024.")
    (xdoc::li
     "A lexing with a @('#') immediately followed by
      another @('#') or by a double quote,
      as in @('##') and @('#\"a\"') [SC15].
      Tokenization rejects it in edition 2024;
      in edition 2021 it is valid."))
   (xdoc::p
    "The predicate @(tsee lexing-in-edition-okp)
     adds these two conditions
     (see @(tsee tokenization-conditions-okp)):
     it is the specification of
     the inputs that are lexically valid in an edition.
     No other side condition is left to tokenization as a rejection:
     [SC6], which also depends on the edition,
     classifies lexemes and rejects none
     (see @(tsee keyword-lexeme-cst-p)).")
   (xdoc::p
    "Identifiers are ASCII-only here, as in the grammar,
     whose identifier rules stand for the Unicode ones for now [SC4].")
   (xdoc::p
    "The lexer book defines the executable lexer.
     That it satisfies this specification
     is proved in @(see lexer-correctness),
     except for the maximal munch conjunct, which is future work."))
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
         (lexeme-cst-doc-comment-cr-okp tree)
         (lexeme-cst-unicode-escapes-okp tree)
         (lexeme-cst-float-period-okp tree (nthcdr (len string) input))
         (lexeme-cst-reserved-number-okp tree (nthcdr (len string) input))
         (lexeme-cst-reserved-prefix-okp tree (nthcdr (len string) input))
         (lexeme-cst-literal-underscore-okp tree
                                            (nthcdr (len string) input))
         (lexeme-cst-lifetime-quote-okp tree (nthcdr (len string) input))
         (lexing-okp (cdr trees) (nthcdr (len string) input))))

  ///

  (assert-event (lexing-okp nil nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lexing in an edition: the conditions that tokenization checks.

(define lexeme-cst-list-raw-names-okp ((trees abnf::tree-listp))
  :returns (yes/no booleanp)
  :short "Check that no lexeme of a lexing is
          a raw identifier or a raw lifetime
          with an excluded name [SC5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee lexeme-cst-raw-name-okp) for the condition on a lexeme."))
  :measure (len trees)
  (b* ((trees (abnf::tree-list-fix trees))
       ((when (endp trees)) t))
    (and (lexeme-cst-raw-name-okp (car trees))
         (lexeme-cst-list-raw-names-okp (cdr trees)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-list-reserved-guards-okp ((trees abnf::tree-listp)
                                             (input nat-listp))
  :returns (yes/no booleanp)
  :short "Check that no lexeme of a lexing
          forms a reserved guard with what follows it [SC15]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The trees are the lexemes of the input, in order,
     so that the input after a lexeme is
     what is left of the input after the lexemes up to that one.
     See @(tsee lexeme-cst-reserved-guard-okp)
     for the condition on a lexeme and the input that follows it."))
  :measure (len trees)
  (b* ((trees (abnf::tree-list-fix trees))
       (input (nat-list-fix input))
       ((when (endp trees)) t)
       (tree (car trees))
       (rest-input (nthcdr (len (abnf::tree->string tree)) input)))
    (and (lexeme-cst-reserved-guard-okp tree rest-input)
         (lexeme-cst-list-reserved-guards-okp (cdr trees) rest-input))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tokenization-conditions-okp ((trees abnf::tree-listp)
                                     (input nat-listp)
                                     (edition rust::editionp))
  :returns (yes/no booleanp)
  :short "Check the conditions on a lexing that tokenization checks,
          in a given edition [SC5] [SC15]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the two side conditions that reject an input
     and that the lexer does not check:")
   (xdoc::ul
    (xdoc::li
     "[SC5], in both supported editions, 2021 and 2024:
      no lexeme is a raw identifier or a raw lifetime
      with an excluded name
      (see @(tsee lexeme-cst-list-raw-names-okp)).")
    (xdoc::li
     "[SC15], in edition 2024 only:
      no @('#') lexeme forms a reserved guard with what follows it
      (see @(tsee lexeme-cst-list-reserved-guards-okp))."))
   (xdoc::p
    "The trees are the lexemes of the input, in order.")
   (xdoc::p
    "On the lexer's output,
     the tokenizer is tested to fail
     exactly when these conditions do not hold
     (see @(see differential-testing));
     proving that is future work."))
  (and (lexeme-cst-list-raw-names-okp trees)
       (rust::edition-case
        edition
        :2021 t
        :2024 (lexeme-cst-list-reserved-guards-okp trees input))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexing-in-edition-okp ((trees abnf::tree-listp)
                               (input nat-listp)
                               (edition rust::editionp))
  :returns (yes/no booleanp)
  :short "Declarative specification of correct lexing in a given edition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The trees are a correct lexing of the input in the edition
     if they are a correct lexing of it
     (see @(tsee lexing-okp)), which does not depend on the edition,
     and they satisfy the conditions that tokenization checks
     (see @(tsee tokenization-conditions-okp)).
     An input is lexically valid in an edition
     when it has such a lexing.")
   (xdoc::p
    "So the lexings that @(tsee lexing-okp) accepts
     and this predicate rejects
     are those that the lexer produces and the tokenizer then rejects:
     in both supported editions, 2021 and 2024,
     those with a raw identifier or a raw lifetime
     named @('crate'), @('self'), @('super'), or @('Self') [SC5];
     and in edition 2024,
     those with a @('#') immediately followed by
     another @('#') or by a double quote [SC15].")
   (xdoc::p
    "The edition has one more effect on tokenization,
     which rejects nothing:
     it decides which identifier-or-keyword lexemes are keywords [SC6]
     (see @(tsee keyword-lexeme-cst-p))."))
  (and (lexing-okp trees input)
       (tokenization-conditions-okp trees input edition))

  ///

  (assert-event (lexing-in-edition-okp nil nil (rust::edition-2021)))
  (assert-event (lexing-in-edition-okp nil nil (rust::edition-2024))))
