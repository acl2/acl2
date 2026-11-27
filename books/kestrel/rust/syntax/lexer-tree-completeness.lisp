; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "lexer-correctness")

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lexer-tree-completeness
  :parents (lexer-correctness)
  :short "What the lexing functions do on the strings of
          the trees that match their rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "The other theorems in @(see lexer-correctness) are about
     the trees that the lexer returns.
     The specification of lexing also speaks of
     all the trees that the grammar and the side conditions allow:
     maximal munch (see @(tsee lexeme-cst-maximal-p))
     compares each lexeme with every valid lexeme CST
     whose string starts the same input.
     The theorems here relate the lexing functions to those trees.")
   (xdoc::p
    "For each lexing function,
     we prove what it does on an input that consists of
     the string of a tree that matches the function's rule
     followed by any remaining input:
     it leaves exactly the remaining input,
     if the rule fixes where a match ends;
     or it leaves at most the remaining input,
     if the function takes as much input as it can
     (as for a run of whitespace, or the suffix of a literal).
     This is the form of the completeness theorems of
     the parser of ABNF grammars
     (see @(see abnf::grammar-parser-completeness)),
     except that the conclusions are about the remaining input
     and not about the tree that is returned:
     the grammar gives some strings more than one tree
     (see @(see lexing-uniqueness)).")
   (xdoc::p
    "There are such theorems for the lexing functions of:
     the character classes;
     whitespace;
     line comments;
     punctuation and delimiters;
     escapes, including unicode escapes and string continuations;
     identifiers and suffixes;
     and character, byte, string, byte string, and C string literals.
     The functions that check the value of a unicode escape [SC9]
     may fail on the string of a tree that matches their rule,
     so their theorems are about the remaining input when they do not fail.
     The theorems for string literals use [SC13],
     which is part of @(tsee lexeme-cst-okp).")
   (xdoc::p
    "The theorem for a lexing function is named after the function,
     with @('-when-tree-match') added,
     or with @('-when-tree-list-match') for a function that
     lexes a repetition.
     With them are theorems about
     the first characters of the strings of trees,
     and about the first characters on which lexing functions fail,
     which say that the alternatives of a rule do not overlap.
     All these theorems are disabled.
     The proof that the lexer satisfies maximal munch
     is built on them (see @(see lexer-maximal-munch))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Trees that match the terminal elements of the grammar.

; A tree matches a terminal element (a numeric value or a character value)
; exactly when it is a leaf with certain natural numbers.
; These rules say which, for the constant elements of the grammar,
; so that the proofs below need not open the matching predicates.

(defruled tree-match-element-p-of-num-val
  (implies (and (syntaxp (quotep elem))
                (abnf::element-case elem :num-val))
           (equal (abnf::tree-match-element-p tree elem rules)
                  (abnf::tree-match-num-val-p
                   tree (abnf::element-num-val->get elem))))
  :expand (abnf::tree-match-element-p tree elem rules))

(defruled tree-match-element-p-of-char-val
  (implies (and (syntaxp (quotep elem))
                (abnf::element-case elem :char-val))
           (equal (abnf::tree-match-element-p tree elem rules)
                  (abnf::tree-match-char-val-p
                   tree (abnf::element-char-val->get elem))))
  :expand (abnf::tree-match-element-p tree elem rules))

(defruled tree-match-num-val-p-of-direct
  (implies (and (syntaxp (quotep num-val))
                (abnf::num-val-case num-val :direct))
           (equal (abnf::tree-match-num-val-p tree num-val)
                  (and (abnf::tree-case tree :leafterm)
                       (equal (abnf::tree-leafterm->get tree)
                              (abnf::num-val-direct->get num-val)))))
  :enable abnf::tree-match-num-val-p)

(defruled tree-match-num-val-p-of-range
  (implies (and (syntaxp (quotep num-val))
                (abnf::num-val-case num-val :range))
           (equal (abnf::tree-match-num-val-p tree num-val)
                  (and (abnf::tree-case tree :leafterm)
                       (consp (abnf::tree-leafterm->get tree))
                       (not (consp (cdr (abnf::tree-leafterm->get tree))))
                       (natp (car (abnf::tree-leafterm->get tree)))
                       (<= (abnf::num-val-range->min num-val)
                           (car (abnf::tree-leafterm->get tree)))
                       (<= (car (abnf::tree-leafterm->get tree))
                           (abnf::num-val-range->max num-val)))))
  :enable (abnf::tree-match-num-val-p
           len)
  :disable acl2::len-of-cdr)

(defruled nats-match-sensitive-chars-p-is-equal
  (implies (and (nat-listp nats)
                (character-listp chars))
           (equal (abnf::nats-match-sensitive-chars-p nats chars)
                  (equal nats (acl2::chars=>nats chars))))
  :induct (abnf::nats-match-sensitive-chars-p nats chars)
  :expand (acl2::chars=>nats chars)
  :enable (abnf::nats-match-sensitive-chars-p
           abnf::nat-match-sensitive-char-p
           acl2::chars=>nats
           character-listp
           nat-listp
           nfix))

(defruled nats-match-insensitive-chars-p-is-equal
  (implies (and (nat-listp nats)
                (character-listp chars)
                (caseless-chars-p chars))
           (equal (abnf::nats-match-insensitive-chars-p nats chars)
                  (equal nats (acl2::chars=>nats chars))))
  :induct (abnf::nats-match-insensitive-chars-p nats chars)
  :expand (acl2::chars=>nats chars)
  :enable (abnf::nats-match-insensitive-chars-p
           abnf::nat-match-insensitive-char-p
           acl2::chars=>nats
           caseless-chars-p
           character-listp
           nat-listp
           nfix))

(defruled tree-match-char-val-p-of-sensitive
  (implies (and (syntaxp (quotep char-val))
                (abnf::char-val-case char-val :sensitive))
           (equal (abnf::tree-match-char-val-p tree char-val)
                  (and (abnf::tree-case tree :leafterm)
                       (equal (abnf::tree-leafterm->get tree)
                              (acl2::chars=>nats
                               (str::explode
                                (abnf::char-val-sensitive->get char-val)))))))
  :enable (abnf::tree-match-char-val-p
           nats-match-sensitive-chars-p-is-equal))

(defruled tree-match-char-val-p-of-insensitive
  (implies (and (syntaxp (quotep char-val))
                (abnf::char-val-case char-val :insensitive)
                (caseless-chars-p
                 (str::explode (abnf::char-val-insensitive->get char-val))))
           (equal (abnf::tree-match-char-val-p tree char-val)
                  (and (abnf::tree-case tree :leafterm)
                       (equal (abnf::tree-leafterm->get tree)
                              (acl2::chars=>nats
                               (str::explode
                                (abnf::char-val-insensitive->get
                                 char-val)))))))
  :enable (abnf::tree-match-char-val-p
           nats-match-insensitive-chars-p-is-equal))

; A tree matches a group or an option
; exactly when it has no rule name and its branches match the alternation,
; or, for an option, when it has no branches.
; These two rules apply to any tree.
; They are for the proofs about lexing functions that
; lex a group or an option of their rule themselves:
; the subtree for that group or option is then opened.
; When a group or an option has a lexing function of its own,
; the subtree must stay closed, for the theorem of that function to apply;
; then the proof just expands the matching of the main tree,
; as the proofs for all the other rules do.

(defruled tree-match-element-p-of-group
  (implies (and (syntaxp (quotep elem))
                (abnf::element-case elem :group))
           (equal (abnf::tree-match-element-p tree elem rules)
                  (and (abnf::tree-case tree :nonleaf)
                       (null (abnf::tree-nonleaf->rulename? tree))
                       (abnf::tree-list-list-match-alternation-p
                        (abnf::tree-nonleaf->branches tree)
                        (abnf::element-group->get elem)
                        rules))))
  :expand (abnf::tree-match-element-p tree elem rules))

(defruled tree-match-element-p-of-option
  (implies (and (syntaxp (quotep elem))
                (abnf::element-case elem :option))
           (equal (abnf::tree-match-element-p tree elem rules)
                  (and (abnf::tree-case tree :nonleaf)
                       (null (abnf::tree-nonleaf->rulename? tree))
                       (or (abnf::tree-list-list-match-alternation-p
                            (abnf::tree-nonleaf->branches tree)
                            (abnf::element-option->get elem)
                            rules)
                           (null (abnf::tree-nonleaf->branches tree))))))
  :expand (abnf::tree-match-element-p tree elem rules))

(deftheory inline-groups
  '(tree-match-element-p-of-group
    tree-match-element-p-of-option))

; A list of trees matches a repetition of zero or more elements
; exactly when each tree matches the element.

(defruled tree-list-match-repetition-p-of-0+-repetitions
  (implies (and (syntaxp (quotep rep))
                (equal (abnf::repetition->range rep)
                       (abnf::repeat-range 0 (abnf::nati-infinity))))
           (equal (abnf::tree-list-match-repetition-p trees rep rules)
                  (abnf::tree-list-match-element-p
                   trees (abnf::repetition->element rep) rules)))
  :enable (abnf::tree-list-match-repetition-p
           abnf::numrep-match-repeat-range-p))

; The string of a non-empty list of trees.

(defruled tree-list->string-when-consp
  (implies (consp trees)
           (equal (abnf::tree-list->string trees)
                  (append (abnf::tree->string (car trees))
                          (abnf::tree-list->string (cdr trees)))))
  :enable abnf::tree-list->string)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Matching a fixed string against an input that starts with known codes.

; In the proofs below, the input of a lexing function has the form
; (append codes x), where codes is a constant list
; (the string of a subtree that matches a fixed string)
; and x is the rest (the strings of the following subtrees,
; and then the remaining input).
; These rules say what the two matchers of fixed strings do on such an input,
; according to how the codes of the string that is matched
; relate to the known codes:
; if they start the known codes, the match succeeds;
; if they differ from the known codes at some position, it fails;
; if the known codes are a proper prefix of them,
; it depends on the rest in the way that the last rule of each group says.
; The rules keep the input in that form, without splitting into cases.

(defruled append-of-constant-and-append-of-constant
  (implies (syntaxp (and (quotep codes1) (quotep codes2)))
           (equal (append codes1 (append codes2 x))
                  (append (append codes1 codes2) x))))

; The three cases are stated with the tests that
; acl2::prefixp-of-append-arg2 gives for (prefixp pattern (append codes x)),
; which are evaluated when the pattern and the codes are constants.

(defruled parse-ichars-of-append-codes
  (implies (and (syntaxp (and (quotep chars) (quotep codes)))
                (stringp chars)
                (caseless-chars-p (str::explode chars))
                (nat-listp codes)
                (prefixp (acl2::chars=>nats (str::explode chars)) codes))
           (b* (((mv tree rest-input)
                 (abnf::parse-ichars chars (append codes x))))
             (and (not (reserrp tree))
                  (equal rest-input
                         (append (nthcdr (len (str::explode chars)) codes)
                                 (nat-list-fix x))))))
  :use (:instance acl2::len-when-prefixp
                  (x (acl2::chars=>nats (str::explode chars)))
                  (y codes))
  :enable (abnf::parse-ichars
           parse-ichars-aux-when-caseless-chars
           abnf::not-reserrp-when-treep
           not-reserrp-when-nat-listp
           nfix)
  :disable acl2::len-when-prefixp)

(defruled parse-ichars-of-append-codes-when-mismatch
  (implies (and (syntaxp (and (quotep chars) (quotep codes)))
                (stringp chars)
                (caseless-chars-p (str::explode chars))
                (nat-listp codes)
                (not (prefixp (acl2::chars=>nats (str::explode chars)) codes))
                (not (equal (true-list-fix codes)
                            (take (len codes)
                                  (acl2::chars=>nats (str::explode chars))))))
           (reserrp (mv-nth 0 (abnf::parse-ichars chars (append codes x)))))
  :enable (abnf::parse-ichars
           parse-ichars-aux-when-caseless-chars
           abnf::not-reserrp-when-treep))

(defruled parse-ichars-of-append-codes-when-shorter
  (implies (and (syntaxp (and (quotep chars) (quotep codes)))
                (stringp chars)
                (caseless-chars-p (str::explode chars))
                (nat-listp codes)
                (not (prefixp (acl2::chars=>nats (str::explode chars)) codes))
                (equal (true-list-fix codes)
                       (take (len codes)
                             (acl2::chars=>nats (str::explode chars)))))
           (equal (reserrp
                   (mv-nth 0 (abnf::parse-ichars chars (append codes x))))
                  (not (prefixp (nthcdr (len codes)
                                        (acl2::chars=>nats
                                         (str::explode chars)))
                                (nat-list-fix x)))))
  :enable (abnf::parse-ichars
           parse-ichars-aux-when-caseless-chars
           abnf::not-reserrp-when-treep))

(defruled parse-schars-of-append-codes
  (implies (and (syntaxp (and (quotep chars) (quotep codes)))
                (stringp chars)
                (nat-listp codes)
                (prefixp (acl2::chars=>nats (str::explode chars)) codes))
           (b* (((mv tree rest-input)
                 (abnf::parse-schars chars (append codes x))))
             (and (not (reserrp tree))
                  (equal rest-input
                         (append (nthcdr (len (str::explode chars)) codes)
                                 (nat-list-fix x))))))
  :use (:instance acl2::len-when-prefixp
                  (x (acl2::chars=>nats (str::explode chars)))
                  (y codes))
  :enable (abnf::parse-schars
           parse-schars-aux-is-prefix-match
           abnf::not-reserrp-when-treep
           not-reserrp-when-nat-listp
           nfix)
  :disable acl2::len-when-prefixp)

(defruled parse-schars-of-append-codes-when-mismatch
  (implies (and (syntaxp (and (quotep chars) (quotep codes)))
                (stringp chars)
                (nat-listp codes)
                (not (prefixp (acl2::chars=>nats (str::explode chars)) codes))
                (not (equal (true-list-fix codes)
                            (take (len codes)
                                  (acl2::chars=>nats (str::explode chars))))))
           (reserrp (mv-nth 0 (abnf::parse-schars chars (append codes x)))))
  :enable (abnf::parse-schars
           parse-schars-aux-is-prefix-match
           abnf::not-reserrp-when-treep))

(defruled parse-schars-of-append-codes-when-shorter
  (implies (and (syntaxp (and (quotep chars) (quotep codes)))
                (stringp chars)
                (nat-listp codes)
                (not (prefixp (acl2::chars=>nats (str::explode chars)) codes))
                (equal (true-list-fix codes)
                       (take (len codes)
                             (acl2::chars=>nats (str::explode chars)))))
           (equal (reserrp
                   (mv-nth 0 (abnf::parse-schars chars (append codes x))))
                  (not (prefixp (nthcdr (len codes)
                                        (acl2::chars=>nats
                                         (str::explode chars)))
                                (nat-list-fix x)))))
  :enable (abnf::parse-schars
           parse-schars-aux-is-prefix-match
           abnf::not-reserrp-when-treep))

; A list that starts with a given code is not a prefix of an input
; whose first part starts with another code.

(defruled prefixp-of-cons-and-append-when-first-differs
  (implies (and (consp y)
                (not (equal a (car y))))
           (not (prefixp (cons a x) (append y z))))
  :enable (prefixp append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lexing the string of a tree.

; For each lexing function, we prove what it does on an input that
; consists of the string of a tree that matches the function's rule,
; followed by any remaining input.
; This is the form of the completeness theorems of the parser of ABNF
; grammars (see abnf::grammar-parser-completeness), except that the
; conclusions are about the input that the function leaves, and not
; about the tree that it returns: some strings have more than one tree.
; There are two kinds of conclusions.
; For a function whose rule fixes where a match ends,
; the function succeeds and leaves exactly the remaining input.
; For a function that takes as much input as it can,
; the function leaves at most the remaining input;
; and it leaves exactly that if it cannot go on into it.

; The proofs open the matching of the tree against its rule,
; and use the theorems for the functions that the lexing function calls.

(deftheory tree-matching
  '(cst-matchp$
    cst-list-elem-matchp$
    cst-list-rep-matchp$
    abnf::tree->string
    abnf::tree-list->string
    abnf::tree-list-list->string
    abnf::branches-terminated-when-tree-terminated
    abnf::tree-list-match-repetition-p-of-1-repetition
    abnf::tree-list-match-repetition-p-of-1+-repetitions
    tree-list-match-repetition-p-of-0+-repetitions
    tree-list->string-when-consp
    abnf::not-reserrp-when-treep
    acl2::not-reserrp-when-natp
    tree-match-element-p-of-num-val
    tree-match-element-p-of-char-val
    tree-match-num-val-p-of-direct
    tree-match-num-val-p-of-range
    tree-match-char-val-p-of-sensitive
    tree-match-char-val-p-of-insensitive
    append-of-constant-and-append-of-constant
    parse-ichars-of-append-codes
    parse-ichars-of-append-codes-when-mismatch
    parse-ichars-of-append-codes-when-shorter
    parse-schars-of-append-codes
    parse-schars-of-append-codes-when-mismatch
    parse-schars-of-append-codes-when-shorter
    prefixp-of-cons-and-append-when-first-differs))

; The rules that open the matching of a tree against a constant element
; that is not a rule name.
; They are disabled in the proofs by induction on a list of trees,
; where the matching of each tree is used as it is,
; as the hypothesis of the theorem for the function that lexes one tree.

(deftheory tree-matching-openers
  '(tree-match-element-p-of-group
    tree-match-element-p-of-option
    tree-match-element-p-of-num-val
    tree-match-element-p-of-char-val))

; This macro generates the theorem for a lexing function and its rule.
; The kind is :exact for a conclusion of the first kind,
; and :at-most for a conclusion of the second kind.
; The theorem is named after the function, with -when-tree-match;
; it is a pair of rewrite rules for the first kind,
; and a rewrite rule and a linear rule for the second.
; It is disabled.
; The kinds :exact-if-ok and :at-most-if-ok are for the functions
; that may fail on the string of a tree that matches their rule,
; because they check a side condition that the rule does not state
; (the value of a unicode escape, [SC9]):
; the conclusion is then only about the remaining input,
; under the hypothesis that the function does not fail.
; The keyword arguments are another name for the theorem,
; an additional hypothesis
; (about the remaining input, or a side condition on the tree),
; and additions to the hints.
; The rule is in ABNF notation, as for cst-matchp;
; a long one can be given as a list of strings, which are joined.

(defmacro def-lex-when-tree-match (fn rule kind
                                      &key name hyp enable disable expand use)
  (b* ((thm (or name (acl2::packn-pos (list fn '-when-tree-match) fn)))
       (rule (if (stringp rule) rule (acl2::string-append-lst rule)))
       (call `(,fn (append (abnf::tree->string tree) rest)))
       (hyps (if hyp
                 `(and (cst-matchp tree ,rule) ,hyp)
               `(cst-matchp tree ,rule)))
       (hints `(:enable (tree-matching ,fn ,@enable)
                :disable (acl2::append-of-cons
                          acl2::append-of-cons-arg1
                          ,@disable)
                :use ,use
                :expand ((:free (element rules)
                          (abnf::tree-match-element-p tree element rules))
                         (abnf::tree-terminatedp tree)
                         ,@expand))))
    (case kind
      (:exact
       `(defruled ,thm
          (implies ,hyps
                   (and (not (reserrp (mv-nth 0 ,call)))
                        (equal (mv-nth 1 ,call)
                               (nat-list-fix rest))))
          ,@hints))
      (:exact-if-ok
       `(defruled ,thm
          (implies (and ,hyps
                        (not (reserrp (mv-nth 0 ,call))))
                   (equal (mv-nth 1 ,call)
                          (nat-list-fix rest)))
          ,@hints))
      (:at-most
       `(defruled ,thm
          (implies ,hyps
                   (and (not (reserrp (mv-nth 0 ,call)))
                        (<= (len (mv-nth 1 ,call))
                            (len rest))))
          :rule-classes
          ((:rewrite
            :corollary (implies ,hyps
                                (not (reserrp (mv-nth 0 ,call)))))
           (:linear
            :corollary (implies ,hyps
                                (<= (len (mv-nth 1 ,call))
                                    (len rest)))))
          ,@hints))
      (t ; :at-most-if-ok
       `(defruled ,thm
          (implies (and ,hyps
                        (not (reserrp (mv-nth 0 ,call))))
                   (<= (len (mv-nth 1 ,call))
                       (len rest)))
          :rule-classes :linear
          ,@hints)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Character classes.

(defmacro def-lex-char-class-when-tree-match (rulename)
  (b* ((fn (acl2::packn-pos (list 'lex- (acl2::string-upcase rulename))
                            'lex-whitespace-char)))
    `(def-lex-when-tree-match ,fn ,rulename :exact
       :enable (abnf::parse-next nfix))))

(def-lex-char-class-when-tree-match "whitespace-char")
(def-lex-char-class-when-tree-match "ascii-letter")
(def-lex-char-class-when-tree-match "ascii-letter-no-e")
(def-lex-char-class-when-tree-match "ascii-letter-no-hex-digit")
(def-lex-char-class-when-tree-match "dec-digit")
(def-lex-char-class-when-tree-match "bin-digit")
(def-lex-char-class-when-tree-match "oct-digit")
(def-lex-char-class-when-tree-match "not-lf")
(def-lex-char-class-when-tree-match "not-slash-bang-lf")
(def-lex-char-class-when-tree-match "not-slash-lf")
(def-lex-char-class-when-tree-match "not-star-slash")
(def-lex-char-class-when-tree-match "not-star-bang")
(def-lex-char-class-when-tree-match "nonzero-hex-digit")
(def-lex-char-class-when-tree-match "dquote")
(def-lex-char-class-when-tree-match "lf")
(def-lex-char-class-when-tree-match "skipped-whitespace-char")
(def-lex-char-class-when-tree-match "char-literal-char")
(def-lex-char-class-when-tree-match "string-literal-char")
(def-lex-char-class-when-tree-match "c-string-literal-char")
(def-lex-char-class-when-tree-match "raw-string-char")
(def-lex-char-class-when-tree-match "raw-c-string-char")
(def-lex-char-class-when-tree-match "ascii-for-char")
(def-lex-char-class-when-tree-match "ascii-for-string")
(def-lex-char-class-when-tree-match "ascii-for-raw")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Repetitions.

; The repetition functions take as many elements as they can.
; So on the strings of a list of trees that match the element,
; followed by any remaining input,
; a repetition function leaves at most the remaining input;
; and it leaves exactly that if no element starts the remaining input.
; The theorem for the element function must be of the first kind:
; the element fixes where it ends.

(defmacro def-lex-repetition-when-tree-list-match (rep-fn elem-fn elem-string)
  (b* ((elem-thm (acl2::packn-pos (list elem-fn '-when-tree-match) rep-fn))
       (len-thm (acl2::packn-pos (list 'len-of- rep-fn '-when-tree-list-match)
                                 rep-fn))
       (rest-thm (acl2::packn-pos (list rep-fn '-when-tree-list-match)
                                  rep-fn)))
    `(progn
       (defruled ,len-thm
         (implies (cst-list-elem-matchp trees ,elem-string)
                  (<= (len (mv-nth 1 (,rep-fn
                                      (append (abnf::tree-list->string trees)
                                              rest))))
                      (len rest)))
         :rule-classes :linear
         :induct (len trees)
         :enable (tree-matching
                  ,rep-fn
                  ,elem-thm
                  (:induction len))
         :disable tree-matching-openers)
       (defruled ,rest-thm
         (implies (and (cst-list-elem-matchp trees ,elem-string)
                       (reserrp (mv-nth 0 (,elem-fn rest))))
                  (equal (mv-nth 1 (,rep-fn
                                    (append (abnf::tree-list->string trees)
                                            rest)))
                         (nat-list-fix rest)))
         :induct (len trees)
         :enable (tree-matching
                  ,rep-fn
                  ,elem-thm
                  (:induction len))
         :disable tree-matching-openers))))

(def-lex-repetition-when-tree-list-match lex-*-whitespace-char
  lex-whitespace-char "whitespace-char")

(def-lex-repetition-when-tree-list-match lex-*-not-lf
  lex-not-lf "not-lf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Whitespace.

(def-lex-when-tree-match lex-whitespace "whitespace" :at-most
  :enable (lex-whitespace-char-when-tree-match
           len-of-lex-*-whitespace-char-when-tree-list-match))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Line comments.

; Each of the three functions takes the characters up to the next line feed,
; so it leaves at most the remaining input.

(def-lex-when-tree-match lex-inner-line-doc "inner-line-doc" :at-most
  :enable (len-of-lex-*-not-lf-when-tree-list-match))

(def-lex-when-tree-match lex-outer-line-doc "outer-line-doc" :at-most
  :enable (inline-groups
           lex-not-slash-lf-when-tree-match
           len-of-lex-*-not-lf-when-tree-list-match))

; In a plain line comment, a second // may follow the first:
; there the function for the character after the first // fails,
; since that character is a slash.

(defruled lex-not-slash-bang-lf-when-slash
  (implies (and (consp input)
                (equal (car input) #x2f))
           (reserrp (mv-nth 0 (lex-not-slash-bang-lf input))))
  :enable (lex-not-slash-bang-lf
           abnf::parse-next))

(def-lex-when-tree-match lex-line-comment "line-comment" :at-most
  :enable (inline-groups
           lex-not-slash-bang-lf-when-tree-match
           lex-not-slash-bang-lf-when-slash
           len-of-lex-*-not-lf-when-tree-list-match))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Block comments.

; The rules for block comments overapproximate:
; [SC2] says which of the strings that they give are block comments.
; So the theorem for block comments is about
; any string that satisfies [SC2], and not about trees:
; it is rest-input-of-lex-lexeme-when-block-comment-string-p,
; proved with the other theorems about [SC2].
; A valid lexeme CST satisfies [SC2] if its string starts with /*
; (see lexeme-cst-okp).
; The strings of the trees for the three kinds of block comments
; start that way.

(defmacro def-slash-star-prefixp-of-tree->string (rule)
  `(defruled ,(acl2::packn-pos
               (list 'slash-star-prefixp-of-tree->string-when-
                     (acl2::string-upcase rule))
               'lex-whitespace-char)
     (implies (cst-matchp tree ,rule)
              (prefixp '(#x2f #x2a) (abnf::tree->string tree)))
     :enable tree-matching
     :expand ((:free (element rules)
               (abnf::tree-match-element-p tree element rules))
              (abnf::tree-terminatedp tree))))

(def-slash-star-prefixp-of-tree->string "block-comment")
(def-slash-star-prefixp-of-tree->string "outer-block-doc")
(def-slash-star-prefixp-of-tree->string "inner-block-doc")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Punctuation and delimiters.

; The function for punctuation tries a list of strings in order,
; with the longer strings first,
; so on a punctuation string it takes that string or a longer one.
; We prove that for any list of strings without letters
; that is in order of length, longest first:
; if the input starts with (the codes of) a string of the list,
; the string that is taken is that one or an earlier one,
; which is at least as long.

(local
 (defun punctuation-strings-p (strings)
   (or (atom strings)
       (and (stringp (car strings))
            (caseless-chars-p (str::explode (car strings)))
            (or (atom (cdr strings))
                (and (stringp (cadr strings))
                     (<= (len (str::explode (cadr strings)))
                         (len (str::explode (car strings))))))
            (punctuation-strings-p (cdr strings))))))

(local
 (defun punctuation-strings-codes (strings)
   (if (atom strings)
       nil
     (cons (acl2::chars=>nats (str::explode (car strings)))
           (punctuation-strings-codes (cdr strings))))))

(defruledl len-of-car-when-punctuation-strings-p
  (implies (and (punctuation-strings-p strings)
                (member-equal codes (punctuation-strings-codes strings)))
           (<= (len codes)
               (len (str::explode (car strings)))))
  :rule-classes :linear
  :induct (punctuation-strings-p strings)
  :enable (punctuation-strings-p
           punctuation-strings-codes
           member-equal))

(defruledl lex-punctuation-cascade-of-append
  (implies (and (punctuation-strings-p strings)
                (member-equal codes (punctuation-strings-codes strings)))
           (b* (((mv tree1 rest1)
                 (lex-punctuation-cascade strings (append codes rest))))
             (and (not (reserrp tree1))
                  (<= (len rest1) (len rest)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (and (punctuation-strings-p strings)
                  (member-equal codes (punctuation-strings-codes strings)))
             (not (reserrp (mv-nth 0 (lex-punctuation-cascade
                                      strings (append codes rest)))))))
   (:linear
    :corollary
    (implies (and (punctuation-strings-p strings)
                  (member-equal codes (punctuation-strings-codes strings)))
             (<= (len (mv-nth 1 (lex-punctuation-cascade
                                 strings (append codes rest))))
                 (len rest)))))
  :induct (punctuation-strings-p strings)
  :enable (punctuation-strings-p
           punctuation-strings-codes
           member-equal
           lex-punctuation-cascade
           lex-punctuation-string
           abnf::parse-ichars
           parse-ichars-aux-when-caseless-chars
           len-of-car-when-punctuation-strings-p
           abnf::not-reserrp-when-treep
           nfix))

(def-lex-when-tree-match lex-punctuation "punctuation" :at-most
  :enable (lex-punctuation-cascade-of-append))

(def-lex-when-tree-match lex-delimiter "delimiter" :exact
  :enable (abnf::parse-next nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The first character of the string of a tree.

; Where a lexing function tries alternatives in order,
; the proofs need to know that the earlier alternatives fail
; on the string of a tree for a later one.
; For that, these rules give the first character of
; the strings of trees that match certain rules,
; and say on which first characters certain functions fail.

(defmacro def-first-of-tree->string (rule fact &key name linear enable)
  (b* ((rule (if (stringp rule) rule (acl2::string-append-lst rule)))
       (thm (or name
                (acl2::packn-pos
                 (list 'first-of-tree->string-when-
                       (acl2::string-upcase rule))
                 'lex-whitespace-char)))
       (first '(car (abnf::tree->string tree))))
    `(defruled ,thm
       (implies (cst-matchp tree ,rule)
                (and (consp (abnf::tree->string tree))
                     ,(subst first 'first fact)
                     ,@(and linear (list (subst first 'first linear)))))
       :rule-classes
       ,(if linear
            `((:rewrite
               :corollary (implies (cst-matchp tree ,rule)
                                   (and (consp (abnf::tree->string tree))
                                        ,(subst first 'first fact))))
              (:linear
               :corollary (implies (cst-matchp tree ,rule)
                                   ,(subst first 'first linear))))
          :rewrite)
       :enable (tree-matching ,@enable)
       :expand ((:free (element rules)
                 (abnf::tree-match-element-p tree element rules))
                (abnf::tree-terminatedp tree)))))

(def-first-of-tree->string "dquote" (equal first #x22))
(def-first-of-tree->string "lf" (equal first #xa))
(def-first-of-tree->string "dec-digit"
  (natp first)
  :linear (and (<= #x30 first) (<= first #x39)))
(def-first-of-tree->string "oct-digit"
  (natp first)
  :linear (and (<= #x30 first) (<= first #x37)))
(def-first-of-tree->string "nonzero-hex-digit"
  (and (natp first) (not (equal first #x30))))

(defruled lex-dec-digit-when-not-dec-digit
  (implies (and (consp input)
                (natp (car input))
                (not (and (<= #x30 (car input))
                          (<= (car input) #x39))))
           (reserrp (mv-nth 0 (lex-dec-digit input))))
  :enable (lex-dec-digit
           abnf::parse-next
           nfix))

(defruled lex-nonzero-hex-digit-when-zero
  (implies (and (consp input)
                (equal (car input) #x30))
           (reserrp (mv-nth 0 (lex-nonzero-hex-digit input))))
  :enable (lex-nonzero-hex-digit
           abnf::parse-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Hexadecimal digits, and escapes.

(def-lex-when-tree-match lex-hex-digit "hex-digit" :exact
  :enable (lex-dec-digit-when-tree-match
           lex-dec-digit-when-not-dec-digit
           first-of-tree->string-when-dec-digit
           abnf::parse-next
           nfix))

(def-lex-when-tree-match lex-quote-escape "quote-escape" :exact
  :enable (lex-dquote-when-tree-match
           first-of-tree->string-when-dquote))

(def-lex-when-tree-match lex-ascii-escape "ascii-escape" :exact
  :enable (lex-oct-digit-when-tree-match
           lex-hex-digit-when-tree-match))

(def-lex-when-tree-match lex-byte-escape "byte-escape" :exact
  :enable (lex-hex-digit-when-tree-match
           lex-dquote-when-tree-match
           first-of-tree->string-when-dquote))

(def-lex-when-tree-match lex-c-byte-escape "c-byte-escape" :exact
  :enable (inline-groups
           lex-nonzero-hex-digit-when-tree-match
           lex-nonzero-hex-digit-when-zero
           lex-hex-digit-when-tree-match
           lex-dquote-when-tree-match
           first-of-tree->string-when-dquote))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unicode escapes.

; A unicode escape has one to six groups,
; each a hexadecimal digit followed by underscores.
; A group is followed by another group or by the closing brace,
; neither of which starts with an underscore,
; so the function for a group leaves exactly what follows it.
; The function for the escape fails if the value is not valid [SC9],
; which the rule does not say;
; so its theorem is about the remaining input when it does not fail.

(defruled lex-underscore-when-not-underscore
  (implies (not (and (consp input)
                     (equal (car input) #x5f)))
           (reserrp (mv-nth 0 (lex-underscore input))))
  :enable (lex-underscore
           parse-ichars-when-caseless-chars
           prefixp
           nfix)
  :expand (nat-list-fix input))

(defruled lex-hex-digit-when-not-hex-digit
  (implies (and (consp input)
                (natp (car input))
                (not (and (<= #x30 (car input)) (<= (car input) #x39)))
                (not (and (<= #x41 (car input)) (<= (car input) #x46)))
                (not (and (<= #x61 (car input)) (<= (car input) #x66))))
           (reserrp (mv-nth 0 (lex-hex-digit input))))
  :enable (lex-hex-digit
           lex-dec-digit-when-not-dec-digit
           abnf::parse-next
           nfix))

(def-first-of-tree->string "hex-digit"
  (and (natp first) (not (equal first #x5f)))
  :enable (first-of-tree->string-when-dec-digit))

(def-lex-when-tree-match lex-underscore "\"_\"" :exact)

(def-lex-repetition-when-tree-list-match lex-*-underscore
  lex-underscore "\"_\"")

(def-lex-when-tree-match lex-hex-digit-underscores "( hex-digit *\"_\" )"
  :exact
  :hyp (reserrp (mv-nth 0 (lex-underscore rest)))
  :enable (lex-hex-digit-when-tree-match
           lex-*-underscore-when-tree-list-match))

(def-first-of-tree->string "( hex-digit *\"_\" )"
  (and (natp first) (not (equal first #x5f)))
  :name first-of-tree->string-when-hex-digit-underscores
  :enable (first-of-tree->string-when-hex-digit))

(defruled lex-hex-digit-underscores-when-lex-hex-digit-fails
  (implies (reserrp (mv-nth 0 (lex-hex-digit input)))
           (reserrp (mv-nth 0 (lex-hex-digit-underscores input))))
  :enable lex-hex-digit-underscores)

; No underscore starts a list of groups followed by an input
; that does not start with an underscore.

(defruled lex-underscore-of-groups-when-lex-underscore-fails
  (implies (and (cst-list-elem-matchp trees "( hex-digit *\"_\" )")
                (reserrp (mv-nth 0 (lex-underscore rest))))
           (reserrp (mv-nth 0 (lex-underscore
                               (append (abnf::tree-list->string trees)
                                       rest)))))
  :cases ((consp trees))
  :enable (tree-matching
           lex-underscore-when-not-underscore
           first-of-tree->string-when-hex-digit-underscores)
  :disable tree-matching-openers)

(local
 (defun lex-unicode-escape-groups-induction (trees n)
   (if (or (atom trees) (zp n))
       (list trees n)
     (lex-unicode-escape-groups-induction (cdr trees) (1- n)))))

(defruled lex-unicode-escape-groups-when-tree-list-match
  (implies (and (cst-list-elem-matchp trees "( hex-digit *\"_\" )")
                (<= (len trees) (nfix n))
                (nat-listp rest)
                (reserrp (mv-nth 0 (lex-hex-digit rest)))
                (reserrp (mv-nth 0 (lex-underscore rest))))
           (equal (mv-nth 1 (lex-unicode-escape-groups
                             n (append (abnf::tree-list->string trees) rest)))
                  rest))
  :induct (lex-unicode-escape-groups-induction trees n)
  :enable (tree-matching
           lex-unicode-escape-groups
           lex-hex-digit-underscores-when-tree-match
           lex-hex-digit-underscores-when-lex-hex-digit-fails
           lex-underscore-of-groups-when-lex-underscore-fails
           nfix)
  :disable (tree-matching-openers
            tree-list->string-when-consp)
  :expand ((:free (input) (lex-unicode-escape-groups n input))
           (abnf::tree-list->string trees)))

; A list of trees matches a repetition of one to six elements
; exactly when it has one to six trees and each matches the element.

(defruled tree-list-match-repetition-p-of-1-to-6-repetitions
  (implies (and (syntaxp (quotep rep))
                (equal (abnf::repetition->range rep)
                       (abnf::repeat-range 1 (abnf::nati-finite 6))))
           (equal (abnf::tree-list-match-repetition-p trees rep rules)
                  (and (consp trees)
                       (<= (len trees) 6)
                       (abnf::tree-match-element-p
                        (car trees) (abnf::repetition->element rep) rules)
                       (abnf::tree-list-match-element-p
                        (cdr trees) (abnf::repetition->element rep) rules))))
  :enable (abnf::tree-list-match-repetition-p
           abnf::numrep-match-repeat-range-p
           nfix)
  :expand (abnf::tree-list-match-element-p
           trees (abnf::repetition->element rep) rules))

(def-lex-when-tree-match lex-unicode-escape "unicode-escape" :exact-if-ok
  :enable (tree-list-match-repetition-p-of-1-to-6-repetitions
           lex-hex-digit-underscores-when-tree-match
           lex-unicode-escape-groups-when-tree-list-match
           lex-underscore-of-groups-when-lex-underscore-fails
           lex-underscore-when-not-underscore
           lex-hex-digit-when-not-hex-digit
           first-of-tree->string-when-hex-digit-underscores))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; String continuations.

; The function takes the whole run of skipped whitespace after the line feed,
; so it leaves at most the remaining input,
; and exactly that if the remaining input does not start with
; a character of that kind.

(def-lex-repetition-when-tree-list-match lex-*-skipped-whitespace-char
  lex-skipped-whitespace-char "skipped-whitespace-char")

(def-lex-when-tree-match lex-string-continue "string-continue" :at-most
  :enable (lex-lf-when-tree-match
           len-of-lex-*-skipped-whitespace-char-when-tree-list-match))

(def-lex-when-tree-match lex-string-continue "string-continue" :exact
  :name lex-string-continue-when-tree-match-exact
  :hyp (reserrp (mv-nth 0 (lex-skipped-whitespace-char rest)))
  :enable (lex-lf-when-tree-match
           lex-*-skipped-whitespace-char-when-tree-list-match))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The items of character and string literals.

; An item is a single character or one of several escapes,
; and the function for an item tries them in order.
; Every escape starts with a backslash,
; which is not a character of a literal,
; and the escapes differ in their second character.
; The following rules say that:
; for the trees, what the first two characters of their strings are;
; for the functions, on which first two characters they fail.

(defmacro def-first-two-of-tree->string (rule seconds &key enable)
  (b* ((thm (acl2::packn-pos
             (list 'first-two-of-tree->string-when-
                   (acl2::string-upcase rule))
             'lex-whitespace-char))
       (string '(abnf::tree->string tree)))
    `(defruled ,thm
       (implies (cst-matchp tree ,rule)
                (and (consp ,string)
                     (consp (cdr ,string))
                     (equal (car ,string) #x5c)
                     (member-equal (car (cdr ,string)) ',seconds)))
       :rule-classes
       ((:rewrite
         :corollary (implies (cst-matchp tree ,rule)
                             (and (consp ,string)
                                  (consp (cdr ,string))
                                  (equal (car ,string) #x5c))))
        (:rewrite
         :corollary (implies (and (cst-matchp tree ,rule)
                                  (syntaxp (quotep code))
                                  (not (member-equal code ',seconds)))
                             (equal (equal (car (cdr ,string)) code)
                                    nil))))
       :enable (tree-matching
                member-equal
                ,@enable)
       :expand ((:free (element rules)
                 (abnf::tree-match-element-p tree element rules))
                (abnf::tree-terminatedp tree)))))

(def-first-two-of-tree->string "quote-escape" (#x27 #x22)
  :enable (first-of-tree->string-when-dquote))
(def-first-two-of-tree->string "ascii-escape"
  (#x78 #x6e #x72 #x74 #x5c #x30))
(def-first-two-of-tree->string "byte-escape"
  (#x78 #x6e #x72 #x74 #x5c #x30 #x27 #x22)
  :enable (first-of-tree->string-when-dquote))
(def-first-two-of-tree->string "c-byte-escape"
  (#x78 #x6e #x72 #x74 #x5c #x27 #x22)
  :enable (first-of-tree->string-when-dquote))
(def-first-two-of-tree->string "unicode-escape" (#x75))
(def-first-two-of-tree->string "string-continue" (#xa)
  :enable (first-of-tree->string-when-lf))

(defmacro def-lex-fails-when-backslash (fn)
  `(defruled ,(acl2::packn-pos (list fn '-when-backslash) fn)
     (implies (and (consp input)
                   (equal (car input) #x5c))
              (reserrp (mv-nth 0 (,fn input))))
     :enable (,fn abnf::parse-next)))

(def-lex-fails-when-backslash lex-char-literal-char)
(def-lex-fails-when-backslash lex-string-literal-char)
(def-lex-fails-when-backslash lex-c-string-literal-char)
(def-lex-fails-when-backslash lex-ascii-for-char)
(def-lex-fails-when-backslash lex-ascii-for-string)

(defmacro def-lex-fails-when-second (fn seconds &key enable)
  `(defruled ,(acl2::packn-pos (list fn '-when-second-differs) fn)
     (implies (and (nat-listp input)
                   (consp input)
                   (consp (cdr input))
                   (not (member-equal (car (cdr input)) ',seconds)))
              (reserrp (mv-nth 0 (,fn input))))
     :enable (,fn
              parse-ichars-when-caseless-chars
              parse-schars-is-prefix-match
              prefixp
              member-equal
              ,@enable)))

(def-lex-fails-when-second lex-quote-escape (#x27 #x22)
  :enable (lex-dquote abnf::parse-next nfix))
(def-lex-fails-when-second lex-ascii-escape
  (#x78 #x6e #x72 #x74 #x5c #x30))
(def-lex-fails-when-second lex-byte-escape
  (#x78 #x6e #x72 #x74 #x5c #x30 #x27 #x22)
  :enable (lex-dquote abnf::parse-next nfix))
(def-lex-fails-when-second lex-c-byte-escape
  (#x78 #x6e #x72 #x74 #x5c #x27 #x22)
  :enable (lex-dquote abnf::parse-next nfix))
(def-lex-fails-when-second lex-unicode-escape (#x75))
(def-lex-fails-when-second lex-c-unicode-escape (#x75)
  :enable (lex-unicode-escape-when-second-differs))
(def-lex-fails-when-second lex-string-continue (#xa)
  :enable (lex-lf abnf::parse-next nfix))

; The items of a character literal and of a byte literal.

(def-lex-when-tree-match lex-char-literal-item
  "( char-literal-char / quote-escape / ascii-escape / unicode-escape )"
  :exact-if-ok
  :hyp (nat-listp rest)
  :enable (lex-char-literal-char-when-tree-match
           lex-quote-escape-when-tree-match
           lex-ascii-escape-when-tree-match
           lex-unicode-escape-when-tree-match
           lex-char-literal-char-when-backslash
           lex-quote-escape-when-second-differs
           lex-ascii-escape-when-second-differs
           first-two-of-tree->string-when-quote-escape
           first-two-of-tree->string-when-ascii-escape
           first-two-of-tree->string-when-unicode-escape))

(def-lex-when-tree-match lex-byte-literal-item
  "( ascii-for-char / byte-escape )"
  :exact
  :enable (lex-ascii-for-char-when-tree-match
           lex-byte-escape-when-tree-match
           lex-ascii-for-char-when-backslash
           first-two-of-tree->string-when-byte-escape))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifiers and suffixes.

; The two theorems for the characters of identifiers
; are the only ones here that depend on which characters those are;
; the theorems for identifiers and suffixes are proved from them.

(defruled lex-ascii-letter-when-not-letter
  (implies (and (consp input)
                (natp (car input))
                (not (and (<= #x41 (car input)) (<= (car input) #x5a)))
                (not (and (<= #x61 (car input)) (<= (car input) #x7a))))
           (reserrp (mv-nth 0 (lex-ascii-letter input))))
  :enable (lex-ascii-letter
           abnf::parse-next
           nfix))

(def-lex-when-tree-match lex-identifier-start "identifier-start" :exact
  :enable (lex-ascii-letter-when-tree-match))

(defruled lex-identifier-start-when-not-letter
  (implies (and (consp input)
                (natp (car input))
                (not (and (<= #x41 (car input)) (<= (car input) #x5a)))
                (not (and (<= #x61 (car input)) (<= (car input) #x7a))))
           (reserrp (mv-nth 0 (lex-identifier-start input))))
  :enable (lex-identifier-start
           lex-ascii-letter-when-not-letter))

(def-lex-when-tree-match lex-identifier-continue "identifier-continue" :exact
  :enable (lex-ascii-letter-when-tree-match
           lex-dec-digit-when-tree-match
           lex-ascii-letter-when-not-letter
           lex-dec-digit-when-not-dec-digit
           first-of-tree->string-when-dec-digit))

(def-lex-repetition-when-tree-list-match lex-*-identifier-continue
  lex-identifier-continue "identifier-continue")

(def-lex-when-tree-match lex-identifier-or-keyword "identifier-or-keyword"
  :at-most
  :enable (lex-identifier-start-when-tree-match
           lex-identifier-start-when-not-letter
           lex-identifier-continue-when-tree-match
           len-of-lex-*-identifier-continue-when-tree-list-match))

(def-lex-when-tree-match lex-suffix "suffix" :at-most
  :enable (lex-identifier-or-keyword-when-tree-match))

(def-lex-when-tree-match lex-option-suffix "[ suffix ]" :at-most
  :enable (lex-suffix-when-tree-match))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Character literals and byte literals.

; The item and the closing quote fix where the literal ends
; except for the suffix, of which the function takes as much as it can.
; A character literal may hold a unicode escape,
; on which the function may fail [SC9].

(def-lex-when-tree-match lex-char-literal "char-literal" :at-most-if-ok
  :hyp (nat-listp rest)
  :enable (lex-char-literal-item-when-tree-match
           lex-option-suffix-when-tree-match))

(def-lex-when-tree-match lex-byte-literal "byte-literal" :at-most
  :enable (lex-byte-literal-item-when-tree-match
           lex-option-suffix-when-tree-match))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; String literals.

; The body of a string literal is a list of items, up to the closing quote.
; An item fixes where it ends, except for a string continuation,
; which the function extends over all the skipped whitespace that follows.
; In a valid lexeme, the item after a string continuation
; does not start with such whitespace [SC13],
; so the function for an item leaves exactly what follows the item.
; If the function for an item fails on an item (an invalid unicode escape),
; the function for the list of items stops there, before a backslash,
; and the closing quote is not found:
; the function for the literal fails.

(deftheory check-tree-utilities
  '(abnf::check-tree-nonleaf?
    abnf::check-tree-nonleaf
    abnf::check-tree-nonleaf-1
    abnf::check-tree-nonleaf-1-1
    abnf::check-tree-list-list-1
    abnf::check-tree-list-1
    abnf::not-reserrp-when-treep
    abnf::not-reserrp-when-tree-listp
    abnf::not-reserrp-when-tree-list-listp))

(defruled lex-dquote-when-not-dquote
  (implies (not (and (consp input)
                     (equal (car input) #x22)))
           (reserrp (mv-nth 0 (lex-dquote input))))
  :enable (lex-dquote
           abnf::parse-next
           nfix))

(defruled lex-skipped-whitespace-char-when-not-skipped-whitespace
  (implies (not (and (consp input)
                     (member-equal (car input) '(#x9 #xa #xd #x20))))
           (reserrp (mv-nth 0 (lex-skipped-whitespace-char input))))
  :enable (lex-skipped-whitespace-char
           abnf::parse-next
           member-equal
           nfix))

(def-first-of-tree->string "string-literal-char"
  (and (natp first) (not (equal first #x22))))

(defmacro cst-list-elem-matchp+ (trees &rest strings)
  `(cst-list-elem-matchp ,trees ,(acl2::string-append-lst strings)))

(def-first-of-tree->string
  ("( string-literal-char / quote-escape / ascii-escape"
   " / unicode-escape / string-continue )")
  (not (equal first #x22))
  :name first-of-tree->string-when-string-literal-item
  :enable (first-of-tree->string-when-string-literal-char
           first-two-of-tree->string-when-quote-escape
           first-two-of-tree->string-when-ascii-escape
           first-two-of-tree->string-when-unicode-escape
           first-two-of-tree->string-when-string-continue))

(defruled lex-string-literal-item-when-dquote
  (implies (and (nat-listp input)
                (consp input)
                (equal (car input) #x22))
           (reserrp (mv-nth 0 (lex-string-literal-item input))))
  :enable (lex-string-literal-item
           lex-string-literal-char
           lex-quote-escape
           lex-ascii-escape
           lex-unicode-escape
           lex-string-continue
           abnf::parse-next
           parse-ichars-when-caseless-chars
           parse-schars-is-prefix-match
           prefixp))

(def-lex-when-tree-match lex-string-literal-item
  ("( string-literal-char / quote-escape / ascii-escape"
   " / unicode-escape / string-continue )")
  :exact-if-ok
  :hyp (and (nat-listp rest)
            (or (not (string-continue-item-cst-p tree))
                (reserrp (mv-nth 0 (lex-skipped-whitespace-char rest)))))
  :enable (lex-string-literal-char-when-tree-match
           lex-quote-escape-when-tree-match
           lex-ascii-escape-when-tree-match
           lex-unicode-escape-when-tree-match
           lex-string-continue-when-tree-match-exact
           lex-string-literal-char-when-backslash
           lex-quote-escape-when-second-differs
           lex-ascii-escape-when-second-differs
           lex-unicode-escape-when-second-differs
           lex-string-continue-when-second-differs
           first-two-of-tree->string-when-quote-escape
           first-two-of-tree->string-when-ascii-escape
           first-two-of-tree->string-when-unicode-escape
           first-two-of-tree->string-when-string-continue
           string-continue-item-cst-p
           check-tree-utilities
           cst-string-continue-nonleaf
           cst-string-continue-rulename))

(defruled lex-*-string-literal-item-when-tree-list-match
  (implies
   (and (cst-list-elem-matchp+
         trees
         "( string-literal-char / quote-escape / ascii-escape"
         " / unicode-escape / string-continue )")
        (abnf::tree-listp trees)
        (string-continues-maximal-p trees)
        (nat-listp rest)
        (consp rest)
        (equal (car rest) #x22)
        (not (reserrp
              (mv-nth 0 (lex-dquote
                         (mv-nth 1 (lex-*-string-literal-item
                                    (append (abnf::tree-list->string trees)
                                            rest))))))))
   (equal (mv-nth 1 (lex-*-string-literal-item
                     (append (abnf::tree-list->string trees) rest)))
          rest))
  :induct (len trees)
  :enable (tree-matching
           lex-*-string-literal-item
           lex-string-literal-item-when-tree-match
           lex-string-literal-item-when-dquote
           lex-dquote-when-not-dquote
           lex-skipped-whitespace-char-when-not-skipped-whitespace
           first-of-tree->string-when-string-literal-item
           string-continues-maximal-p
           prefixp
           member-equal
           (:induction len))
  :disable tree-matching-openers
  :expand ((string-continues-maximal-p trees)
           (lex-*-string-literal-item rest)
           (lex-*-string-literal-item
            (append (abnf::tree->string (car trees)) rest))
           (lex-*-string-literal-item
            (append (abnf::tree->string (car trees))
                    (append (abnf::tree-list->string (cdr trees)) rest)))))

(def-lex-when-tree-match lex-string-literal "string-literal" :at-most-if-ok
  :hyp (and (nat-listp rest)
            (string-continues-maximal-p
             (cadr (abnf::tree-nonleaf->branches tree))))
  :enable (lex-dquote-when-tree-match
           first-of-tree->string-when-dquote
           lex-*-string-literal-item-when-tree-list-match
           lex-option-suffix-when-tree-match))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Byte string literals.

; These are as string literals, without unicode escapes.

(def-first-of-tree->string "ascii-for-string"
  (and (natp first) (not (equal first #x22))))

(def-first-of-tree->string
  "( ascii-for-string / byte-escape / string-continue )"
  (not (equal first #x22))
  :name first-of-tree->string-when-byte-string-literal-item
  :enable (first-of-tree->string-when-ascii-for-string
           first-two-of-tree->string-when-byte-escape
           first-two-of-tree->string-when-string-continue))

(defruled lex-byte-string-literal-item-when-dquote
  (implies (and (nat-listp input)
                (consp input)
                (equal (car input) #x22))
           (reserrp (mv-nth 0 (lex-byte-string-literal-item input))))
  :enable (lex-byte-string-literal-item
           lex-ascii-for-string
           lex-byte-escape
           lex-string-continue
           abnf::parse-next
           parse-ichars-when-caseless-chars
           parse-schars-is-prefix-match
           prefixp))

(def-lex-when-tree-match lex-byte-string-literal-item
  "( ascii-for-string / byte-escape / string-continue )"
  :exact-if-ok
  :hyp (and (nat-listp rest)
            (or (not (string-continue-item-cst-p tree))
                (reserrp (mv-nth 0 (lex-skipped-whitespace-char rest)))))
  :enable (lex-ascii-for-string-when-tree-match
           lex-byte-escape-when-tree-match
           lex-string-continue-when-tree-match-exact
           lex-ascii-for-string-when-backslash
           lex-byte-escape-when-second-differs
           lex-string-continue-when-second-differs
           first-two-of-tree->string-when-byte-escape
           first-two-of-tree->string-when-string-continue
           string-continue-item-cst-p
           check-tree-utilities
           cst-string-continue-nonleaf
           cst-string-continue-rulename))

(defruled lex-*-byte-string-literal-item-when-tree-list-match
  (implies
   (and (cst-list-elem-matchp
         trees
         "( ascii-for-string / byte-escape / string-continue )")
        (abnf::tree-listp trees)
        (string-continues-maximal-p trees)
        (nat-listp rest)
        (consp rest)
        (equal (car rest) #x22)
        (not (reserrp
              (mv-nth 0 (lex-dquote
                         (mv-nth 1 (lex-*-byte-string-literal-item
                                    (append (abnf::tree-list->string trees)
                                            rest))))))))
   (equal (mv-nth 1 (lex-*-byte-string-literal-item
                     (append (abnf::tree-list->string trees) rest)))
          rest))
  :induct (len trees)
  :enable (tree-matching
           lex-*-byte-string-literal-item
           lex-byte-string-literal-item-when-tree-match
           lex-byte-string-literal-item-when-dquote
           lex-dquote-when-not-dquote
           lex-skipped-whitespace-char-when-not-skipped-whitespace
           first-of-tree->string-when-byte-string-literal-item
           string-continues-maximal-p
           prefixp
           member-equal
           (:induction len))
  :disable tree-matching-openers
  :expand ((string-continues-maximal-p trees)
           (lex-*-byte-string-literal-item rest)
           (lex-*-byte-string-literal-item
            (append (abnf::tree->string (car trees)) rest))
           (lex-*-byte-string-literal-item
            (append (abnf::tree->string (car trees))
                    (append (abnf::tree-list->string (cdr trees)) rest)))))

(def-lex-when-tree-match lex-byte-string-literal "byte-string-literal"
  :at-most-if-ok
  :hyp (and (nat-listp rest)
            (string-continues-maximal-p
             (caddr (abnf::tree-nonleaf->branches tree))))
  :enable (lex-dquote-when-tree-match
           first-of-tree->string-when-dquote
           lex-*-byte-string-literal-item-when-tree-list-match
           lex-option-suffix-when-tree-match))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; C string literals.

; These are as string literals, with their own escapes;
; the function for a unicode escape in a C string literal
; also fails on the value zero [SC9].

(def-lex-when-tree-match lex-c-unicode-escape "unicode-escape" :exact-if-ok
  :enable (lex-unicode-escape-when-tree-match)
  :expand ((lex-c-unicode-escape (append (abnf::tree->string tree) rest)))
  :disable (lex-c-unicode-escape))

(def-first-of-tree->string "c-string-literal-char"
  (and (natp first) (not (equal first #x22))))

(def-first-of-tree->string
  ("( c-string-literal-char / c-byte-escape"
   " / unicode-escape / string-continue )")
  (not (equal first #x22))
  :name first-of-tree->string-when-c-string-literal-item
  :enable (first-of-tree->string-when-c-string-literal-char
           first-two-of-tree->string-when-c-byte-escape
           first-two-of-tree->string-when-unicode-escape
           first-two-of-tree->string-when-string-continue))

(defruled lex-c-string-literal-item-when-dquote
  (implies (and (nat-listp input)
                (consp input)
                (equal (car input) #x22))
           (reserrp (mv-nth 0 (lex-c-string-literal-item input))))
  :enable (lex-c-string-literal-item
           lex-c-string-literal-char
           lex-c-byte-escape
           lex-c-unicode-escape
           lex-unicode-escape
           lex-string-continue
           abnf::parse-next
           parse-ichars-when-caseless-chars
           parse-schars-is-prefix-match
           prefixp))

(def-lex-when-tree-match lex-c-string-literal-item
  ("( c-string-literal-char / c-byte-escape"
   " / unicode-escape / string-continue )")
  :exact-if-ok
  :hyp (and (nat-listp rest)
            (or (not (string-continue-item-cst-p tree))
                (reserrp (mv-nth 0 (lex-skipped-whitespace-char rest)))))
  :enable (lex-c-string-literal-char-when-tree-match
           lex-c-byte-escape-when-tree-match
           lex-c-unicode-escape-when-tree-match
           lex-string-continue-when-tree-match-exact
           lex-c-string-literal-char-when-backslash
           lex-c-byte-escape-when-second-differs
           lex-c-unicode-escape-when-second-differs
           lex-string-continue-when-second-differs
           first-two-of-tree->string-when-c-byte-escape
           first-two-of-tree->string-when-unicode-escape
           first-two-of-tree->string-when-string-continue
           string-continue-item-cst-p
           check-tree-utilities
           cst-string-continue-nonleaf
           cst-string-continue-rulename))

(defruled lex-*-c-string-literal-item-when-tree-list-match
  (implies
   (and (cst-list-elem-matchp+
         trees
         "( c-string-literal-char / c-byte-escape"
         " / unicode-escape / string-continue )")
        (abnf::tree-listp trees)
        (string-continues-maximal-p trees)
        (nat-listp rest)
        (consp rest)
        (equal (car rest) #x22)
        (not (reserrp
              (mv-nth 0 (lex-dquote
                         (mv-nth 1 (lex-*-c-string-literal-item
                                    (append (abnf::tree-list->string trees)
                                            rest))))))))
   (equal (mv-nth 1 (lex-*-c-string-literal-item
                     (append (abnf::tree-list->string trees) rest)))
          rest))
  :induct (len trees)
  :enable (tree-matching
           lex-*-c-string-literal-item
           lex-c-string-literal-item-when-tree-match
           lex-c-string-literal-item-when-dquote
           lex-dquote-when-not-dquote
           lex-skipped-whitespace-char-when-not-skipped-whitespace
           first-of-tree->string-when-c-string-literal-item
           string-continues-maximal-p
           prefixp
           member-equal
           (:induction len))
  :disable tree-matching-openers
  :expand ((string-continues-maximal-p trees)
           (lex-*-c-string-literal-item rest)
           (lex-*-c-string-literal-item
            (append (abnf::tree->string (car trees)) rest))
           (lex-*-c-string-literal-item
            (append (abnf::tree->string (car trees))
                    (append (abnf::tree-list->string (cdr trees)) rest)))))

(def-lex-when-tree-match lex-c-string-literal "c-string-literal"
  :at-most-if-ok
  :hyp (and (nat-listp rest)
            (string-continues-maximal-p
             (caddr (abnf::tree-nonleaf->branches tree))))
  :enable (lex-dquote-when-tree-match
           first-of-tree->string-when-dquote
           lex-*-c-string-literal-item-when-tree-list-match
           lex-option-suffix-when-tree-match))
