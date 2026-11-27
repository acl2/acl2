; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "lexer")
(include-book "extra-grammatical-restrictions")

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lexer-correctness
  :parents (lexer)
  :short "Theorems that the lexer satisfies its specification."
  :long
  (xdoc::topstring
   (xdoc::p
    "The specification of the lexer is @(tsee lexing-okp)
     (see @(see extra-grammatical-restrictions)).
     We prove, of each lexeme that @(tsee lex-lexeme) returns,
     with the input that remains after it,
     every conjunct of that specification other than maximal munch [SC1]:
     the lexeme is a valid lexeme CST
     (see @(tsee lexeme-cst-okp)),
     which covers the grammar and
     the side conditions [SC2], [SC10], and [SC13];
     it is not empty, and its text starts the input;
     and it satisfies the side conditions
     [SC3], [SC7], [SC8], [SC9], [SC11], [SC12], and [SC14].
     From these, @(tsee lexing-okp-of-lexemize-rust-when-maximal)
     says that the result of the lexer satisfies its specification,
     under the hypothesis that each lexeme is maximal
     (see @(tsee lexeme-cst-list-maximal-p)).")
   (xdoc::p
    "That the lexemes are maximal is not proved yet.
     It needs a different kind of argument:
     the theorems here are about the trees that the lexer builds,
     while maximal munch is about all the trees
     that the grammar and the side conditions allow.
     The theorems in @(see lexer-tree-completeness)
     relate the lexing functions to those trees,
     and @(see lexer-maximal-munch) builds
     the proof of maximal munch on them.
     One theorem of that kind is here, with the theorems about [SC2]:
     @('rest-input-of-lex-lexeme-when-block-comment-string-p') says that
     the lexer takes exactly a complete block comment that starts the input.")
   (xdoc::p
    "The side conditions [SC5] and [SC15] are not part of @(tsee lexing-okp):
     the tokenizer checks them
     (see @(tsee tokenization-conditions-okp)).
     [SC6] classifies lexemes and rejects none,
     and [SC4] is not specified yet."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; One lexeme and the input after it.

(defruledl len-of-tree->string-of-lex-lexeme
  (b* (((mv tree rest-input) (lex-lexeme input)))
    (implies (not (reserrp tree))
             (equal (len (abnf::tree->string tree))
                    (- (len input) (len rest-input)))))
  :use (input-decomposition-of-lex-lexeme
        (:instance acl2::len-of-append
                   (x (abnf::tree->string (mv-nth 0 (lex-lexeme input))))
                   (y (mv-nth 1 (lex-lexeme input)))))
  :disable (input-decomposition-of-lex-lexeme acl2::len-of-append))

(defret consp-of-tree->string-of-lex-lexeme
  (implies (not (reserrp tree))
           (consp (abnf::tree->string tree)))
  :fn lex-lexeme
  :hints (("Goal" :use (len-of-tree->string-of-lex-lexeme
                        len-of-lex-lexeme-<)
                  :in-theory (disable len-of-lex-lexeme-<))))

(defret prefixp-of-tree->string-of-lex-lexeme
  (implies (not (reserrp tree))
           (prefixp (abnf::tree->string tree) (nat-list-fix input)))
  :fn lex-lexeme
  :hints (("Goal" :use input-decomposition-of-lex-lexeme
                  :in-theory (disable input-decomposition-of-lex-lexeme))))

(defret nthcdr-of-len-of-tree->string-of-lex-lexeme
  (implies (not (reserrp tree))
           (equal (nthcdr (len (abnf::tree->string tree))
                          (nat-list-fix input))
                  rest-input))
  :fn lex-lexeme
  :hints (("Goal" :use input-decomposition-of-lex-lexeme
                  :in-theory (disable input-decomposition-of-lex-lexeme))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The lexeme is a lexeme CST.

(defret lexeme-cst-p-of-lex-lexeme
  (implies (not (reserrp tree))
           (lexeme-cst-p tree))
  :fn lex-lexeme
  :hints (("Goal" :use cst-matchp-of-lex-lexeme
                  :in-theory (e/d (lexeme-cst-p cst-matchp$)
                                  (cst-matchp-of-lex-lexeme)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The rule name of the tree that a lexing function returns.

; The specification looks at a lexeme CST through the utilities
; that check the rule name and the number of branches of a tree.
; For those utilities to compute on the trees that the lexer builds,
; we need the rule name at the root of the tree
; that each lexing function returns:
; it is the rule that the tree is proved to match.

(local
 (defmacro def-lexed-rulename (fn rule)
   (b* ((kind-thm (acl2::packn-pos (list 'tree-kind-of- fn) fn))
        (rulename-thm (acl2::packn-pos (list 'tree-nonleaf->rulename?-of- fn)
                                       fn))
        (nonleaf-rule (acl2::packn-pos
                       (list 'cst- (acl2::string-upcase rule) '-nonleaf)
                       fn))
        (rulename-rule (acl2::packn-pos
                        (list 'cst- (acl2::string-upcase rule) '-rulename)
                        fn)))
     `(progn
        (defrulel ,kind-thm
          (b* (((mv tree &) (,fn input)))
            (implies (not (reserrp tree))
                     (equal (abnf::tree-kind tree) :nonleaf)))
          :enable ,nonleaf-rule)
        (defrulel ,rulename-thm
          (b* (((mv tree &) (,fn input)))
            (implies (not (reserrp tree))
                     (equal (abnf::tree-nonleaf->rulename? tree)
                            (abnf::rulename ,rule))))
          :enable ,rulename-rule)))))

(local
 (progn
   (def-lexed-rulename lex-whitespace "whitespace")
   (def-lexed-rulename lex-comment "comment")
   (def-lexed-rulename lex-token "token")
   (def-lexed-rulename lex-line-comment "line-comment")
   (def-lexed-rulename lex-outer-line-doc "outer-line-doc")
   (def-lexed-rulename lex-inner-line-doc "inner-line-doc")
   (def-lexed-rulename lex-block-comment "block-comment")
   (def-lexed-rulename lex-outer-block-doc "outer-block-doc")
   (def-lexed-rulename lex-inner-block-doc "inner-block-doc")
   (def-lexed-rulename lex-identifier-or-keyword "identifier-or-keyword")
   (def-lexed-rulename lex-raw-identifier "raw-identifier")
   (def-lexed-rulename lex-lifetime-token "lifetime-token")
   (def-lexed-rulename lex-raw-lifetime "raw-lifetime")
   (def-lexed-rulename lex-char-literal "char-literal")
   (def-lexed-rulename lex-byte-literal "byte-literal")
   (def-lexed-rulename lex-string-literal "string-literal")
   (def-lexed-rulename lex-byte-string-literal "byte-string-literal")
   (def-lexed-rulename lex-c-string-literal "c-string-literal")
   (def-lexed-rulename lex-raw-string-literal "raw-string-literal")
   (def-lexed-rulename lex-raw-byte-string-literal "raw-byte-string-literal")
   (def-lexed-rulename lex-raw-c-string-literal "raw-c-string-literal")
   (def-lexed-rulename lex-integer-literal "integer-literal")
   (def-lexed-rulename lex-float-literal "float-literal")
   (def-lexed-rulename lex-punctuation "punctuation")
   (def-lexed-rulename lex-delimiter "delimiter")))

; The definitions of the utilities, to enable together,
; with the rules that say that the trees and lists of trees
; that the utilities return are not errors.

(local
 (deftheory check-tree-utilities
   '(abnf::check-tree-nonleaf?
     abnf::check-tree-nonleaf
     abnf::check-tree-nonleaf-1
     abnf::check-tree-nonleaf-1-1
     abnf::check-tree-list-list-1
     abnf::check-tree-list-1
     abnf::not-reserrp-when-treep
     abnf::not-reserrp-when-tree-listp
     abnf::not-reserrp-when-tree-list-listp)))

; The functions that choose, by looking ahead,
; the function that lexes the next lexeme or token,
; to enable together.
; The rules about prefixes that split into cases are disabled
; in the proofs that open these functions,
; which only need to follow the tests that the functions make.

(local
 (deftheory lexeme-dispatch
   '(lex-lexeme
     lex-token
     lex-token-identifier-or-keyword)))

(local
 (deftheory prefix-splitters
   '(acl2::prefixp-of-cons-left
     acl2::prefixp-of-cons-right
     acl2::len-of-cdr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC3] Carriage return in doc comments.

; The lexer makes this check on each doc comment that it lexes,
; with the same test as the specification:
; no carriage return in the text of the comment.

(defret lexeme-cst-doc-comment-cr-okp-of-lex-lexeme
  (implies (not (reserrp tree))
           (lexeme-cst-doc-comment-cr-okp tree))
  :fn lex-lexeme
  :hints (("Goal" :in-theory (e/d (lex-lexeme
                                   lex-comment
                                   check-tree-utilities
                                   lexeme-cst-doc-comment-cr-okp
                                   doc-comment-lexeme-cst-p
                                   doc-comment-cr-p
                                   abnf::tree->string
                                   abnf::tree-list->string
                                   abnf::tree-list-list->string)
                                  (prefix-splitters)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC11] Underscore after a character or string literal.

(defret lexeme-cst-literal-underscore-okp-of-lex-lexeme
  (implies (not (reserrp tree))
           (lexeme-cst-literal-underscore-okp tree rest-input))
  :fn lex-lexeme
  :hints (("Goal" :in-theory (e/d (lexeme-dispatch
                                   check-tree-utilities
                                   lexeme-cst-literal-underscore-okp
                                   char-or-string-literal-lexeme-cst-p)
                                  (prefix-splitters)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC12] Single quote after a lifetime.

(defret lexeme-cst-lifetime-quote-okp-of-lex-lexeme
  (implies (not (reserrp tree))
           (lexeme-cst-lifetime-quote-okp tree rest-input))
  :fn lex-lexeme
  :hints (("Goal" :in-theory (e/d (lexeme-dispatch
                                   check-tree-utilities
                                   lexeme-cst-lifetime-quote-okp
                                   lifetime-lexeme-cst-p)
                                  (prefix-splitters)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC8] Reserved prefixes.

; The text of an identifier or keyword has no "#".
; This is needed for lifetimes:
; the lexer tells a raw lifetime by its text, which starts with 'r#,
; and the specification by its tree.

(defruledl tree->string-of-tree-nonleaf
  (equal (abnf::tree->string (abnf::tree-nonleaf rulename? branches))
         (abnf::tree-list-list->string branches))
  :expand (abnf::tree->string (abnf::tree-nonleaf rulename? branches)))

(local
 (deftheory tree-strings
   '(abnf::tree->string
     abnf::tree-list->string
     abnf::tree-list-list->string
     tree->string-of-tree-nonleaf)))

(defruledl no-pound-in-lex-ascii-letter
  (b* (((mv tree &) (lex-ascii-letter input)))
    (implies (not (reserrp tree))
             (not (member-equal #x23 (abnf::tree->string tree)))))
  :enable (lex-ascii-letter abnf::parse-next tree-strings))

(defruledl no-pound-in-lex-dec-digit
  (b* (((mv tree &) (lex-dec-digit input)))
    (implies (not (reserrp tree))
             (not (member-equal #x23 (abnf::tree->string tree)))))
  :enable (lex-dec-digit abnf::parse-next tree-strings))

(defruledl no-pound-in-parse-ichars-underscore
  (b* (((mv tree &) (abnf::parse-ichars "_" input)))
    (implies (not (reserrp tree))
             (not (member-equal #x23 (abnf::tree->string tree)))))
  :enable (abnf::parse-ichars
           abnf::parse-ichars-aux
           abnf::nat-match-insensitive-char-p
           abnf::parse-next
           tree-strings))

(defruledl no-pound-in-lex-identifier-start
  (b* (((mv tree &) (lex-identifier-start input)))
    (implies (not (reserrp tree))
             (not (member-equal #x23 (abnf::tree->string tree)))))
  :enable (lex-identifier-start
           no-pound-in-lex-ascii-letter
           tree-strings))

(defruledl no-pound-in-lex-identifier-continue
  (b* (((mv tree &) (lex-identifier-continue input)))
    (implies (not (reserrp tree))
             (not (member-equal #x23 (abnf::tree->string tree)))))
  :enable (lex-identifier-continue
           no-pound-in-lex-ascii-letter
           no-pound-in-lex-dec-digit
           no-pound-in-parse-ichars-underscore
           tree-strings))

(defruledl no-pound-in-lex-*-identifier-continue
  (b* (((mv trees &) (lex-*-identifier-continue input)))
    (not (member-equal #x23 (abnf::tree-list->string trees))))
  :induct (lex-*-identifier-continue input)
  :enable (lex-*-identifier-continue
           no-pound-in-lex-identifier-continue
           abnf::tree-list->string))

(defruledl no-pound-in-lex-identifier-or-keyword
  (b* (((mv tree &) (lex-identifier-or-keyword input)))
    (implies (not (reserrp tree))
             (not (member-equal #x23 (abnf::tree->string tree)))))
  :enable (lex-identifier-or-keyword
           no-pound-in-lex-identifier-start
           no-pound-in-lex-identifier-continue
           no-pound-in-lex-*-identifier-continue
           no-pound-in-parse-ichars-underscore
           tree-strings))

; A lifetime whose text starts with 'r# is a raw lifetime.
; The other two kinds of lifetime are
; a single quote and an identifier or keyword, which has no "#",
; and the two characters '_.

(defruledl not-equal-cadr-when-not-member-equal
  (implies (and (not (member-equal a x))
                (consp (cdr x)))
           (not (equal a (cadr x))))
  :expand ((member-equal a x)
           (member-equal a (cdr x))))

(defruledl lex-lifetime-token-when-raw-lifetime
  (b* (((mv raw-tree raw-rest) (lex-raw-lifetime input)))
    (implies (not (reserrp raw-tree))
             (equal (lex-lifetime-token input)
                    (mv (abnf::tree-nonleaf (abnf::rulename "lifetime-token")
                                            (list (list raw-tree)))
                        raw-rest))))
  :enable lex-lifetime-token)

(defruledl not-prefixp-of-lex-lifetime-token-when-not-raw-lifetime
  (b* (((mv tree &) (lex-lifetime-token input))
       ((mv raw-tree &) (lex-raw-lifetime input)))
    (implies (and (not (reserrp tree))
                  (reserrp raw-tree))
             (not (prefixp (list #x27 #x72 #x23)
                           (abnf::tree->string tree)))))
  :enable (lex-lifetime-token
           abnf::parse-ichars
           abnf::parse-ichars-aux
           abnf::nat-match-insensitive-char-p
           abnf::parse-next
           tree-strings
           not-equal-cadr-when-not-member-equal)
  :use (:instance no-pound-in-lex-identifier-or-keyword
                  (input (cdr (nat-list-fix input)))))

; The three parts of the condition.
; An identifier or keyword is not followed by a # or a quote:
; the lexer checks that after it lexes one.

(defruledl reserved-prefix-of-lex-lexeme-when-identifier
  (b* (((mv tree rest-input) (lex-lexeme input)))
    (implies (and (not (reserrp tree))
                  (identifier-or-keyword-lexeme-cst-p tree))
             (and (not (prefixp (list #x23) rest-input)) ; #
                  (not (prefixp (list #x27) rest-input)) ; '
                  (not (prefixp (list #x22) rest-input))))) ; "
  :enable (lexeme-dispatch
           check-tree-utilities
           identifier-or-keyword-lexeme-cst-p)
  :disable prefix-splitters)

; A lone underscore is not followed by one either.
; If the text of the lexeme is an underscore, the input starts with one,
; and then the lexer lexes an identifier or keyword, or a lone underscore,
; and makes the check in both cases.

(defruledl car-of-input-when-lexeme-is-underscore
  (b* (((mv tree &) (lex-lexeme input)))
    (implies (and (not (reserrp tree))
                  (equal (abnf::tree->string tree) (list #x5f)))
             (equal (car (nat-list-fix input)) #x5f)))
  :use input-decomposition-of-lex-lexeme
  :disable input-decomposition-of-lex-lexeme)

(defruledl reserved-prefix-of-lex-lexeme-when-underscore-first
  (b* (((mv tree rest-input) (lex-lexeme input)))
    (implies (and (not (reserrp tree))
                  (equal (car (nat-list-fix input)) #x5f))
             (and (not (prefixp (list #x23) rest-input)) ; #
                  (not (prefixp (list #x27) rest-input)) ; '
                  (not (prefixp (list #x22) rest-input))))) ; "
  :enable (lexeme-dispatch
           lex-whitespace
           lex-whitespace-char
           abnf::parse-next))

; A lifetime that is not a raw one is not followed by a #.
; The lexer checks that of a lifetime
; whose text does not start with 'r#.

(defruledl reserved-prefix-of-lex-lexeme-when-non-raw-lifetime
  (b* (((mv tree rest-input) (lex-lexeme input)))
    (implies (and (not (reserrp tree))
                  (non-raw-lifetime-lexeme-cst-p tree))
             (not (prefixp (list #x23) rest-input)))) ; #
  :cases ((reserrp (mv-nth 0 (lex-raw-lifetime input))))
  :enable (lexeme-dispatch
           check-tree-utilities
           non-raw-lifetime-lexeme-cst-p
           lex-lifetime-token-when-raw-lifetime
           not-prefixp-of-lex-lifetime-token-when-not-raw-lifetime)
  :disable prefix-splitters)

(defret lexeme-cst-reserved-prefix-okp-of-lex-lexeme
  (implies (not (reserrp tree))
           (lexeme-cst-reserved-prefix-okp tree rest-input))
  :fn lex-lexeme
  :hints (("Goal"
           :use (reserved-prefix-of-lex-lexeme-when-identifier
                 car-of-input-when-lexeme-is-underscore
                 reserved-prefix-of-lex-lexeme-when-underscore-first
                 reserved-prefix-of-lex-lexeme-when-non-raw-lifetime)
           :in-theory (e/d (lexeme-cst-reserved-prefix-okp
                            underscore-lexeme-cst-p)
                           (prefix-splitters)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC9] Unicode escape values.

; The lexer and the specification compute
; the value of a unicode escape in the same way.

(defruledl hex-digits-value-is-hex-digits/underscores-value
  (equal (hex-digits-value nats acc)
         (hex-digits/underscores-value nats acc))
  :induct (hex-digits-value nats acc)
  :enable (hex-digits-value
           hex-digits/underscores-value
           hex-digit-code-value))

(defruledl hex-digits/underscores-value-of-append
  (equal (hex-digits/underscores-value (append x y) value)
         (hex-digits/underscores-value
          y (hex-digits/underscores-value x value)))
  :induct (hex-digits/underscores-value x value)
  :enable hex-digits/underscores-value
  :expand (hex-digits/underscores-value (append x y) value))

; The rule names of the trees for the items of literals.

(local
 (progn
   (def-lexed-rulename lex-char-literal-char "char-literal-char")
   (def-lexed-rulename lex-string-literal-char "string-literal-char")
   (def-lexed-rulename lex-c-string-literal-char "c-string-literal-char")
   (def-lexed-rulename lex-quote-escape "quote-escape")
   (def-lexed-rulename lex-ascii-escape "ascii-escape")
   (def-lexed-rulename lex-c-byte-escape "c-byte-escape")
   (def-lexed-rulename lex-unicode-escape "unicode-escape")
   (def-lexed-rulename lex-c-unicode-escape "unicode-escape")
   (def-lexed-rulename lex-string-continue "string-continue")))

; The utilities for trees with three, four, and five branches.

(local
 (deftheory check-tree-utilities-3-4-5
   '(abnf::check-tree-nonleaf-3
     abnf::check-tree-nonleaf-4
     abnf::check-tree-nonleaf-5
     abnf::check-tree-list-list-3
     abnf::check-tree-list-list-4
     abnf::check-tree-list-list-5
     abnf::not-reserrp-when-tree-list-tuple3p
     abnf::not-reserrp-when-tree-list-tuple4p
     abnf::not-reserrp-when-tree-list-tuple5p)))

; The value of a unicode escape that the lexer returns,
; as the specification computes it from an item that holds the escape,
; is a Unicode scalar value.

(defruledl unicode-escape-item-value-of-lex-unicode-escape
  (b* (((mv tree &) (lex-unicode-escape input)))
    (implies (not (reserrp tree))
             (uni-scalar-value-p
              (unicode-escape-item-value
               (abnf::tree-nonleaf nil (list (list tree)))))))
  :enable (lex-unicode-escape
           unicode-escape-item-value
           uni-scalar-value-p
           check-tree-utilities
           check-tree-utilities-3-4-5
           hex-digits-value-is-hex-digits/underscores-value
           tree-terminatedp-of-lex-hex-digit-underscores
           abnf::tree-list-terminatedp))

; In a C string, the lexer also checks that the value is not zero.
; It computes the value from the whole text of the escape,
; and the specification from the digits and underscores between the braces:
; the two values are the same,
; since no character around the digits is a hexadecimal digit.

(defruledl unicode-escape-item-value-is-value-of-tree->string
  (b* (((mv tree &) (lex-unicode-escape input)))
    (implies (not (reserrp tree))
             (equal (unicode-escape-item-value
                     (abnf::tree-nonleaf nil (list (list tree))))
                    (hex-digits/underscores-value (abnf::tree->string tree)
                                                  0))))
  :enable (lex-unicode-escape
           unicode-escape-item-value
           check-tree-utilities
           check-tree-utilities-3-4-5
           tree-terminatedp-of-lex-hex-digit-underscores
           abnf::tree-list-terminatedp
           tree-strings
           hex-digits/underscores-value-of-append
           hex-digits/underscores-value
           hex-digit-code-value
           abnf::parse-schars
           abnf::parse-schars-aux
           abnf::nat-match-sensitive-char-p
           abnf::parse-ichars
           abnf::parse-ichars-aux
           abnf::nat-match-insensitive-char-p
           abnf::parse-next
           nfix))

(defruledl unicode-escape-item-value-of-lex-c-unicode-escape
  (b* (((mv tree &) (lex-c-unicode-escape input))
       (value (unicode-escape-item-value
               (abnf::tree-nonleaf nil (list (list tree))))))
    (implies (not (reserrp tree))
             (and (uni-scalar-value-p value)
                  (not (equal value 0)))))
  :enable (lex-c-unicode-escape
           unicode-escape-item-value-is-value-of-tree->string
           hex-digits-value-is-hex-digits/underscores-value)
  :use unicode-escape-item-value-of-lex-unicode-escape)

; An item that holds something else than a unicode escape has no value.

(defruledl unicode-escape-item-value-when-not-unicode-escape
  (implies (and (equal (abnf::tree-kind sub) :nonleaf)
                (not (equal (abnf::tree-nonleaf->rulename? sub)
                            (abnf::rulename "unicode-escape"))))
           (equal (unicode-escape-item-value
                   (abnf::tree-nonleaf nil (list (list sub))))
                  nil))
  :enable (unicode-escape-item-value
           check-tree-utilities
           check-tree-utilities-3-4-5))

; So the condition holds of each item that the lexer returns,
; for the three kinds of literals that have unicode escapes.

(defrulel unicode-escape-items-okp-of-lex-char-literal-item
  (b* (((mv tree &) (lex-char-literal-item input)))
    (implies (not (reserrp tree))
             (unicode-escape-items-okp (list tree) nil)))
  :enable (lex-char-literal-item
           unicode-escape-items-okp
           unicode-escape-item-value-of-lex-unicode-escape
           unicode-escape-item-value-when-not-unicode-escape))

(defruledl unicode-escape-items-okp-of-lex-string-literal-item
  (b* (((mv tree &) (lex-string-literal-item input)))
    (implies (not (reserrp tree))
             (unicode-escape-items-okp (list tree) nil)))
  :enable (lex-string-literal-item
           unicode-escape-items-okp
           unicode-escape-item-value-of-lex-unicode-escape
           unicode-escape-item-value-when-not-unicode-escape))

(defruledl unicode-escape-items-okp-of-lex-c-string-literal-item
  (b* (((mv tree &) (lex-c-string-literal-item input)))
    (implies (not (reserrp tree))
             (unicode-escape-items-okp (list tree) t)))
  :enable (lex-c-string-literal-item
           unicode-escape-items-okp
           unicode-escape-item-value-of-lex-c-unicode-escape
           unicode-escape-item-value-when-not-unicode-escape))

; And of the items of the body of a string or C string literal.

(defruledl unicode-escape-items-okp-of-cons
  (implies (syntaxp (not (equal items ''nil)))
           (equal (unicode-escape-items-okp (cons item items) nonzerop)
                  (and (unicode-escape-items-okp (list item) nonzerop)
                       (unicode-escape-items-okp items nonzerop))))
  :expand ((unicode-escape-items-okp (cons item items) nonzerop)
           (unicode-escape-items-okp (list item) nonzerop)
           (unicode-escape-items-okp nil nonzerop)))

(defrulel unicode-escape-items-okp-of-lex-*-string-literal-item
  (b* (((mv trees &) (lex-*-string-literal-item input)))
    (unicode-escape-items-okp trees nil))
  :induct (lex-*-string-literal-item input)
  :enable (lex-*-string-literal-item
           unicode-escape-items-okp-of-cons
           unicode-escape-items-okp-of-lex-string-literal-item)
  :expand (unicode-escape-items-okp nil nil))

(defrulel unicode-escape-items-okp-of-lex-*-c-string-literal-item
  (b* (((mv trees &) (lex-*-c-string-literal-item input)))
    (unicode-escape-items-okp trees t))
  :induct (lex-*-c-string-literal-item input)
  :enable (lex-*-c-string-literal-item
           unicode-escape-items-okp-of-cons
           unicode-escape-items-okp-of-lex-c-string-literal-item)
  :expand (unicode-escape-items-okp nil t))

; The condition, for every lexeme.

(defret lexeme-cst-unicode-escapes-okp-of-lex-lexeme
  (implies (not (reserrp tree))
           (lexeme-cst-unicode-escapes-okp tree))
  :fn lex-lexeme
  :hints (("Goal" :in-theory (e/d (lexeme-dispatch
                                   lex-char-literal
                                   lex-string-literal
                                   lex-c-string-literal
                                   check-tree-utilities
                                   check-tree-utilities-3-4-5
                                   lexeme-cst-unicode-escapes-okp)
                                  (prefix-splitters)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC13] String continuations.

; The lexer lexes the whitespace of a string continuation
; with a repetition, which takes all it can:
; when the repetition ends, lexing one more of its elements fails.
; So what follows a string continuation
; does not start with a tab, a line feed, a carriage return, or a space.

(defruledl lex-skipped-whitespace-char-fails-after-repetition
  (b* (((mv & rest-input) (lex-*-skipped-whitespace-char input)))
    (reserrp (mv-nth 0 (lex-skipped-whitespace-char rest-input))))
  :induct (lex-*-skipped-whitespace-char input)
  :enable lex-*-skipped-whitespace-char)

(defruledl not-skipped-whitespace-when-lex-skipped-whitespace-char-fails
  (implies (and (nat-listp input)
                (reserrp (mv-nth 0 (lex-skipped-whitespace-char input))))
           (and (not (prefixp (list #x9) input)) ; tab
                (not (prefixp (list #xa) input)) ; line feed
                (not (prefixp (list #xd) input)) ; carriage return
                (not (prefixp (list #x20) input)))) ; space
  :enable (lex-skipped-whitespace-char abnf::parse-next))

(defruledl no-skipped-whitespace-after-lex-string-continue
  (b* (((mv tree rest-input) (lex-string-continue input)))
    (implies (not (reserrp tree))
             (and (not (prefixp (list #x9) rest-input))
                  (not (prefixp (list #xa) rest-input))
                  (not (prefixp (list #xd) rest-input))
                  (not (prefixp (list #x20) rest-input)))))
  :enable (lex-string-continue
           lex-skipped-whitespace-char-fails-after-repetition
           not-skipped-whitespace-when-lex-skipped-whitespace-char-fails)
  :disable prefix-splitters)

(local
 (progn
   (def-lexed-rulename lex-ascii-for-string "ascii-for-string")
   (def-lexed-rulename lex-byte-escape "byte-escape")))

; For each of the three kinds of literals with string continuations:
; what follows an item that is a string continuation
; does not start with one of those characters;
; the text of the next item, which starts what follows, does not either;
; so the items of the body satisfy the condition.

(local
 (defmacro def-string-continues-maximal (item-fn rep-fn)
   (b* ((after-thm (acl2::packn-pos
                    (list 'no-skipped-whitespace-after-continue-of- item-fn)
                    item-fn))
        (prefix-thm (acl2::packn-pos
                     (list 'not-prefixp-of-tree->string-of- item-fn)
                     item-fn))
        (decomp-thm (acl2::packn-pos
                     (list 'input-decomposition-of- item-fn)
                     item-fn))
        (rep-thm (acl2::packn-pos
                  (list 'string-continues-maximal-p-of- rep-fn)
                  rep-fn)))
     `(progn
        (defruledl ,after-thm
          (b* (((mv tree rest-input) (,item-fn input)))
            (implies (and (not (reserrp tree))
                          (string-continue-item-cst-p tree))
                     (and (not (prefixp (list #x9) rest-input))
                          (not (prefixp (list #xa) rest-input))
                          (not (prefixp (list #xd) rest-input))
                          (not (prefixp (list #x20) rest-input)))))
          :enable (,item-fn
                   string-continue-item-cst-p
                   check-tree-utilities
                   no-skipped-whitespace-after-lex-string-continue)
          :disable prefix-splitters)
        (defruledl ,prefix-thm
          (b* (((mv tree &) (,item-fn input)))
            (implies (and (not (reserrp tree))
                          (not (prefixp x (nat-list-fix input))))
                     (not (prefixp x (abnf::tree->string tree)))))
          :use (,decomp-thm
                (:instance acl2::prefixp-transitive
                           (x x)
                           (y (abnf::tree->string (mv-nth 0 (,item-fn input))))
                           (z (nat-list-fix input))))
          :disable (,decomp-thm acl2::prefixp-transitive prefix-splitters))
        (defrulel ,rep-thm
          (b* (((mv trees &) (,rep-fn input)))
            (string-continues-maximal-p trees))
          :induct (,rep-fn input)
          :enable (,rep-fn ,after-thm ,prefix-thm)
          :expand ((,rep-fn (mv-nth 1 (,item-fn input)))
                   (:free (item items)
                    (string-continues-maximal-p (cons item items)))
                   (string-continues-maximal-p nil))
          :disable prefix-splitters)))))

(local
 (progn
   (def-string-continues-maximal lex-string-literal-item
     lex-*-string-literal-item)
   (def-string-continues-maximal lex-byte-string-literal-item
     lex-*-byte-string-literal-item)
   (def-string-continues-maximal lex-c-string-literal-item
     lex-*-c-string-literal-item)))

; The condition, for every lexeme.

(defret lexeme-cst-string-continues-okp-of-lex-lexeme
  (implies (not (reserrp tree))
           (lexeme-cst-string-continues-okp tree))
  :fn lex-lexeme
  :hints (("Goal" :in-theory (e/d (lexeme-dispatch
                                   lex-string-literal
                                   lex-byte-string-literal
                                   lex-c-string-literal
                                   check-tree-utilities
                                   check-tree-utilities-3-4-5
                                   lexeme-cst-string-continues-okp)
                                  (prefix-splitters)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC10] Raw string termination.

; Facts about a run of "#", for the specification's functions.

(defruledl leading-pound-count-of-repeat-and-double-quote
  (equal (leading-pound-count (append (acl2::repeat k #x23)
                                      (cons #x22 x)))
         (nfix k))
  :induct (acl2::repeat k #x23)
  :enable (acl2::repeat nfix)
  :expand ((:free (a y) (leading-pound-count (cons a y)))))

(defruledl leading-pound-count-of-repeat
  (equal (leading-pound-count (acl2::repeat k #x23))
         (nfix k))
  :induct (acl2::repeat k #x23)
  :enable (acl2::repeat nfix fix)
  :expand ((:free (a y) (leading-pound-count (cons a y)))
           (leading-pound-count nil)))

(defruledl prefixp-of-repeat-when-leading-pound-count
  (implies (and (nat-listp x)
                (<= (nfix n) (leading-pound-count x)))
           (prefixp (acl2::repeat n #x23) x))
  :induct (nthcdr n x)
  :enable (acl2::repeat nthcdr nfix zp)
  :expand (leading-pound-count x))

(defruledl nthcdr-of-repeat-and-append
  (implies (natp k)
           (equal (nthcdr k (append (acl2::repeat k a) x))
                  x))
  :induct (acl2::repeat k a)
  :enable (acl2::repeat nthcdr))

(defruledl prefixp-of-append-and-append-of-terminator
  (implies (and (consp rest)
                (equal (car rest) #x22)
                (prefixp pounds (cdr rest)))
           (prefixp (append body (cons #x22 pounds))
                    (append body rest)))
  :induct (nat-list-fix body)
  :enable (append nat-list-fix)
  :disable (acl2::prefixp-of-append-arg1
            acl2::prefixp-of-append-arg2))

(defruledl prefixp-of-append-and-terminator
  (implies (and (equal (append body rest) input)
                (consp rest)
                (equal (car rest) #x22)
                (prefixp pounds (cdr rest)))
           (prefixp (append body (cons #x22 pounds)) input))
  :use prefixp-of-append-and-append-of-terminator
  :disable (acl2::prefixp-of-append-arg1
            acl2::prefixp-of-append-arg2))

(defruledl raw-terminator-p-of-nat-list-fix
  (equal (raw-terminator-p n (nat-list-fix input))
         (raw-terminator-p n input))
  :enable raw-terminator-p)

; The body of a raw literal, for each of the three kinds.
; The lexer takes characters until the input starts with the terminator:
; a double quote followed by n "#".
; So the terminator follows the body,
; and it does not start at any character of the body.
; This is what the specification's scan requires:
; the text of the body followed by the terminator closes the literal.

(local
 (defmacro def-raw-body-closes (body-fn char-fn)
   (b* ((char-thm (acl2::packn-pos (list char-fn '-string-and-rest) body-fn))
        (term-thm (acl2::packn-pos
                   (list 'raw-terminator-p-after- body-fn) body-fn))
        (prefix-thm (acl2::packn-pos
                     (list 'prefixp-of-terminated-body-of- body-fn) body-fn))
        (step-thm (acl2::packn-pos
                   (list 'raw-terminator-p-before- body-fn) body-fn))
        (closes-thm (acl2::packn-pos
                     (list 'raw-rest-closes-p-of- body-fn) body-fn))
        (decomp-thm (acl2::packn-pos
                     (list 'input-decomposition-of- body-fn) body-fn))
        (terminated-thm (acl2::packn-pos
                         (list 'tree-list-terminatedp-of- body-fn) body-fn)))
     `(progn
        (defruledl ,char-thm
          (b* (((mv tree rest-input) (,char-fn input)))
            (implies (not (reserrp tree))
                     (and (equal (abnf::tree->string tree)
                                 (list (car (nat-list-fix input))))
                          (equal rest-input
                                 (cdr (nat-list-fix input))))))
          :enable (,char-fn abnf::parse-next tree-strings))
        (defruledl ,term-thm
          (b* (((mv trees rest-input) (,body-fn n input)))
            (implies (not (reserrp trees))
                     (raw-terminator-p n rest-input)))
          :induct (,body-fn n input)
          :enable ,body-fn)
        (defruledl ,prefix-thm
          (b* (((mv trees &) (,body-fn n input)))
            (implies (not (reserrp trees))
                     (prefixp (append (abnf::tree-list->string trees)
                                      (cons #x22 (acl2::repeat n #x23)))
                              (nat-list-fix input))))
          :use (,decomp-thm
                ,term-thm
                (:instance prefixp-of-append-and-terminator
                           (body (abnf::tree-list->string
                                  (mv-nth 0 (,body-fn n input))))
                           (rest (mv-nth 1 (,body-fn n input)))
                           (input (nat-list-fix input))
                           (pounds (acl2::repeat n #x23))))
          :enable raw-terminator-p
          :disable ,decomp-thm)
        (defruledl ,step-thm
          (b* (((mv tree input1) (,char-fn input))
               ((mv trees &) (,body-fn n input1)))
            (implies (and (not (reserrp tree))
                          (not (reserrp trees))
                          (natp n)
                          (equal (nfix (car input)) #x22)
                          (<= n (leading-pound-count
                                 (append (abnf::tree-list->string trees)
                                         (cons #x22
                                               (acl2::repeat n #x23))))))
                     (raw-terminator-p n input)))
          :cases ((consp input))
          :expand (nat-list-fix input)
          :enable (raw-terminator-p
                   ,char-thm
                   ,terminated-thm
                   nfix)
          :use ((:instance prefixp-of-repeat-when-leading-pound-count
                           (x (append (abnf::tree-list->string
                                       (mv-nth 0 (,body-fn
                                                  n
                                                  (mv-nth 1 (,char-fn input)))))
                                      (cons #x22 (acl2::repeat n #x23)))))
                (:instance ,prefix-thm
                           (input (mv-nth 1 (,char-fn input))))
                (:instance acl2::prefixp-transitive
                           (x (acl2::repeat n #x23))
                           (y (append (abnf::tree-list->string
                                       (mv-nth 0 (,body-fn
                                                  n
                                                  (mv-nth 1 (,char-fn input)))))
                                      (cons #x22 (acl2::repeat n #x23))))
                           (z (cdr (nat-list-fix input)))))
          :disable (acl2::prefixp-transitive
                    acl2::prefixp-of-append-arg1
                    acl2::prefixp-of-append-arg2
                    prefix-splitters))
        (defruledl ,closes-thm
          (b* (((mv trees &) (,body-fn n input)))
            (implies (and (not (reserrp trees))
                          (natp n))
                     (raw-rest-closes-p
                      (append (abnf::tree-list->string trees)
                              (cons #x22 (acl2::repeat n #x23)))
                      n)))
          :induct (,body-fn n input)
          :enable (,body-fn
                   ,char-thm
                   abnf::tree-list->string
                   leading-pound-count-of-repeat
                   raw-terminator-p-of-nat-list-fix
                   nfix)
          :expand ((:free (c x) (raw-rest-closes-p (cons c x) n)))
          :hints ('(:use ,step-thm)))))))

(local
 (progn
   (def-raw-body-closes lex-raw-string-body lex-raw-string-char)
   (def-raw-body-closes lex-raw-byte-string-body lex-ascii-for-raw)
   (def-raw-body-closes lex-raw-c-string-body lex-raw-c-string-char)))

; The content of a raw literal: the body between double quotes,
; within k "#" on each side.
; The lexing function takes the "#" off one pair at a time,
; so we prove the specification's condition of its text
; with m more "#" on each side, where m + k is n,
; the number of "#" of the terminator: by induction on k, as m grows.

(defruledl tree->string-of-lex-dquote
  (b* (((mv tree &) (lex-dquote input)))
    (implies (not (reserrp tree))
             (equal (abnf::tree->string tree)
                    (list #x22))))
  :enable (lex-dquote abnf::parse-next tree-strings))

(defruledl tree->string-of-parse-ichars-pound
  (b* (((mv tree &) (abnf::parse-ichars "#" input)))
    (implies (not (reserrp tree))
             (equal (abnf::tree->string tree)
                    (list #x23))))
  :enable (abnf::parse-ichars
           abnf::parse-ichars-aux
           abnf::nat-match-insensitive-char-p
           abnf::parse-next
           tree-strings))

(defruledl append-of-repeat-and-cons
  (equal (append (acl2::repeat m a) (cons a x))
         (cons a (append (acl2::repeat m a) x)))
  :induct (acl2::repeat m a)
  :enable acl2::repeat)

(defruledl repeat-of-1+
  (implies (natp m)
           (equal (acl2::repeat (+ 1 m) a)
                  (cons a (acl2::repeat m a))))
  :expand (acl2::repeat (+ 1 m) a)
  :enable fix)

(defruledl append-of-repeat-and-enclosed
  (implies (natp m)
           (equal (append (acl2::repeat m a)
                          (cons a (append s (cons a (acl2::repeat m a)))))
                  (append (acl2::repeat (+ 1 m) a)
                          (append s (acl2::repeat (+ 1 m) a)))))
  :enable (append-of-repeat-and-cons repeat-of-1+))

(local
 (defun raw-content-induction (k m input)
   (declare (xargs :measure (nfix k)
                   :hints (("Goal" :in-theory (enable nfix zp)))))
   (if (zp k)
       (list m input)
     (mv-let (tree input1)
         (abnf::parse-ichars "#" input)
       (declare (ignore tree))
       (raw-content-induction (1- k) (1+ m) input1)))))

(local
 (defmacro def-raw-content-closes (content-fn body-fn)
   (b* ((closes-thm (acl2::packn-pos
                     (list 'raw-rest-closes-p-of- body-fn) body-fn))
        (terminated-thm (acl2::packn-pos
                         (list 'tree-list-terminatedp-of- body-fn) body-fn))
        (base-thm (acl2::packn-pos
                   (list 'raw-content-string-p-of- content-fn '-base)
                   content-fn))
        (step-thm (acl2::packn-pos
                   (list 'tree->string-of- content-fn '-within)
                   content-fn))
        (within-thm (acl2::packn-pos
                     (list 'raw-content-string-p-of- content-fn '-within)
                     content-fn))
        (content-thm (acl2::packn-pos
                      (list 'raw-content-string-p-of- content-fn)
                      content-fn)))
     `(progn
        (defruledl ,base-thm
          (b* (((mv tree &) (,content-fn k n input)))
            (implies (and (zp k)
                          (not (reserrp tree))
                          (natp n)
                          (<= n 255))
                     (raw-content-string-p
                      (append (acl2::repeat n #x23)
                              (append (abnf::tree->string tree)
                                      (acl2::repeat n #x23))))))
          :expand (,content-fn k n input)
          :enable (tree-strings
                   tree->string-of-lex-dquote
                   raw-content-string-p
                   leading-pound-count-of-repeat-and-double-quote
                   nthcdr-of-repeat-and-append
                   ,closes-thm
                   ,terminated-thm
                   nfix))
        (defruledl ,step-thm
          (b* (((mv tree &) (,content-fn k n input))
               ((mv & input1) (abnf::parse-ichars "#" input))
               ((mv tree1 &) (,content-fn (+ -1 k) n input1)))
            (implies (and (not (zp k))
                          (not (reserrp tree))
                          (natp m))
                     (and (not (reserrp tree1))
                          (equal (append (acl2::repeat m #x23)
                                         (append (abnf::tree->string tree)
                                                 (acl2::repeat m #x23)))
                                 (append (acl2::repeat (+ 1 m) #x23)
                                         (append (abnf::tree->string tree1)
                                                 (acl2::repeat (+ 1 m)
                                                               #x23)))))))
          :expand (,content-fn k n input)
          :enable (tree-strings
                   tree->string-of-parse-ichars-pound
                   append-of-repeat-and-enclosed))
        (defruledl ,within-thm
          (b* (((mv tree &) (,content-fn k n input)))
            (implies (and (not (reserrp tree))
                          (natp m)
                          (natp n)
                          (equal (+ m (nfix k)) n)
                          (<= n 255))
                     (raw-content-string-p
                      (append (acl2::repeat m #x23)
                              (append (abnf::tree->string tree)
                                      (acl2::repeat m #x23))))))
          :induct (raw-content-induction k m input)
          :enable (,base-thm
                   ,step-thm
                   nfix
                   zp
                   fix))
        (defrulel ,content-thm
          (b* (((mv tree &) (,content-fn n n input)))
            (implies (and (not (reserrp tree))
                          (natp n)
                          (<= n 255))
                     (raw-content-string-p (abnf::tree->string tree))))
          :use (:instance ,within-thm (k n) (m 0))
          :enable (nfix fix))))))

(local
 (progn
   (def-raw-content-closes lex-raw-string-content lex-raw-string-body)
   (def-raw-content-closes lex-raw-byte-string-content
     lex-raw-byte-string-body)
   (def-raw-content-closes lex-raw-c-string-content lex-raw-c-string-body)))

; The condition, for every lexeme.
; The lexer counts the "#" before the opening double quote,
; fails if there are more than 255,
; and lexes the content with that number on each side
; and as the number of the terminator.

(defret lexeme-cst-raw-termination-okp-of-lex-lexeme
  (implies (not (reserrp tree))
           (lexeme-cst-raw-termination-okp tree))
  :fn lex-lexeme
  :hints (("Goal" :in-theory (e/d (lexeme-dispatch
                                   lex-raw-string-literal
                                   lex-raw-byte-string-literal
                                   lex-raw-c-string-literal
                                   check-tree-utilities
                                   check-tree-utilities-3-4-5
                                   lexeme-cst-raw-termination-okp
                                   raw-content-branch-okp
                                   abnf::tree-list->string)
                                  (prefix-splitters)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Matching a fixed string without letters.

; The lexer matches fixed strings with abnf::parse-ichars,
; which ignores case.
; When the string has no letters, such as "/*",
; the match succeeds exactly when the codes of its characters
; start the input, and it leaves the input after them.
; These rules state that in terms of prefixp and nthcdr,
; so that proofs need not open the matcher character by character,
; which splits into many cases for strings of four or five characters.
; They are not local: the proofs of maximal munch use them too.

(define caseless-chars-p ((chars character-listp))
  :returns (yes/no booleanp)
  :short "Check that no character in a list is a letter,
          i.e. that changing case leaves each of them unchanged."
  (or (atom chars)
      (and (equal (str::upcase-char (car chars)) (car chars))
           (equal (str::downcase-char (car chars)) (car chars))
           (caseless-chars-p (cdr chars))))
  :guard-hints (("Goal" :in-theory (enable character-listp)))
  :hooks nil)

(defruled not-reserrp-of-cons-when-natp
  (implies (natp n)
           (not (reserrp (cons n x))))
  :enable fty::reserrp)

(defruled parse-ichars-aux-when-caseless-chars
  (implies (and (character-listp chars)
                (caseless-chars-p chars))
           (b* (((mv nats rest-input) (abnf::parse-ichars-aux chars input))
                (codes (acl2::chars=>nats chars)))
             (and (equal (reserrp nats)
                         (not (prefixp codes (nat-list-fix input))))
                  (implies (prefixp codes (nat-list-fix input))
                           (and (equal nats codes)
                                (equal rest-input
                                       (nthcdr (len chars)
                                               (nat-list-fix input))))))))
  :induct (abnf::parse-ichars-aux chars input)
  :enable (abnf::parse-ichars-aux
           abnf::nat-match-insensitive-char-p
           abnf::parse-next
           acl2::chars=>nats
           caseless-chars-p
           character-listp
           not-reserrp-of-cons-when-natp
           nthcdr
           nfix
           zp))

(defruled parse-ichars-when-caseless-chars
  (implies (and (syntaxp (quotep chars))
                (stringp chars)
                (caseless-chars-p (str::explode chars)))
           (b* (((mv tree rest-input) (abnf::parse-ichars chars input))
                (codes (acl2::chars=>nats (str::explode chars))))
             (and (equal (reserrp tree)
                         (not (prefixp codes (nat-list-fix input))))
                  (implies (prefixp codes (nat-list-fix input))
                           (equal rest-input
                                  (nthcdr (len codes)
                                          (nat-list-fix input)))))))
  :enable (abnf::parse-ichars
           parse-ichars-aux-when-caseless-chars
           abnf::not-reserrp-when-treep))

; The text of the tree for a successful match
; consists of the codes of the string's characters.

(defruled not-reserrp-when-nat-listp
  (implies (nat-listp x)
           (not (reserrp x)))
  :enable (fty::reserrp nat-listp))

(defruled tree->string-of-parse-ichars-when-caseless-chars
  (implies (and (syntaxp (quotep chars))
                (stringp chars)
                (caseless-chars-p (str::explode chars))
                (not (reserrp (mv-nth 0 (abnf::parse-ichars chars input)))))
           (equal (abnf::tree->string
                   (mv-nth 0 (abnf::parse-ichars chars input)))
                  (acl2::chars=>nats (str::explode chars))))
  :enable (abnf::parse-ichars
           parse-ichars-aux-when-caseless-chars
           not-reserrp-when-nat-listp
           abnf::tree->string))

; The same for abnf::parse-schars, which does not ignore case,
; so that it applies to every string.
; The lexer uses it for the radix prefixes and for the exponent letters.

(defruled parse-schars-aux-is-prefix-match
  (implies (character-listp chars)
           (b* (((mv nats rest-input) (abnf::parse-schars-aux chars input))
                (codes (acl2::chars=>nats chars)))
             (and (equal (reserrp nats)
                         (not (prefixp codes (nat-list-fix input))))
                  (implies (prefixp codes (nat-list-fix input))
                           (and (equal nats codes)
                                (equal rest-input
                                       (nthcdr (len chars)
                                               (nat-list-fix input))))))))
  :induct (abnf::parse-schars-aux chars input)
  :enable (abnf::parse-schars-aux
           abnf::nat-match-sensitive-char-p
           abnf::parse-next
           acl2::chars=>nats
           character-listp
           not-reserrp-of-cons-when-natp
           nthcdr
           nfix
           zp))

(defruled parse-schars-is-prefix-match
  (implies (and (syntaxp (quotep chars))
                (stringp chars))
           (b* (((mv tree rest-input) (abnf::parse-schars chars input))
                (codes (acl2::chars=>nats (str::explode chars))))
             (and (equal (reserrp tree)
                         (not (prefixp codes (nat-list-fix input))))
                  (implies (prefixp codes (nat-list-fix input))
                           (and (equal rest-input
                                       (nthcdr (len codes)
                                               (nat-list-fix input)))
                                (equal (abnf::tree->string tree)
                                       codes))))))
  :enable (abnf::parse-schars
           parse-schars-aux-is-prefix-match
           not-reserrp-when-nat-listp
           abnf::not-reserrp-when-treep
           abnf::tree->string))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC2] Block comment closing.

; The specification scans the text of a block comment:
; it tracks the nesting depth, and requires that
; the depth reach zero exactly at the end of the text.
; To relate the lexer to it, we use the same scan on the input,
; which goes on after the comment:
; this function returns what is left of the input
; when the depth reaches zero, or :fail if it does not.

(local
 (defun bc-scan (nats depth)
   (declare (xargs :measure (len nats)))
   (cond ((zp depth) nats)
         ((atom nats) :fail)
         ((prefixp (list #x2a #x2f) nats) ; starts with */
          (bc-scan (cddr nats) (1- depth)))
         ((prefixp (list #x2f #x2a) nats) ; starts with /*
          (bc-scan (cddr nats) (1+ depth)))
         (t (bc-scan (cdr nats) depth)))))

(defruledl len-of-bc-scan-<=
  (implies (not (equal (bc-scan nats depth) :fail))
           (<= (len (bc-scan nats depth)) (len nats)))
  :rule-classes :linear
  :induct (bc-scan nats depth)
  :enable bc-scan)

(defruledl len-of-bc-scan-<
  (implies (and (posp depth)
                (not (equal (bc-scan nats depth) :fail)))
           (< (len (bc-scan nats depth)) (len nats)))
  :rule-classes :linear
  :induct (bc-scan nats depth)
  :enable (bc-scan posp zp)
  :hints ('(:use (:instance len-of-bc-scan-<=
                            (nats (cddr nats))
                            (depth (1- depth))))))

(defruledl bc-scan-of-2
  (equal (bc-scan nats 2)
         (bc-scan (bc-scan nats 1) 1))
  :prep-lemmas
  ((defrule lemma
     (implies (and (natp d) (natp e))
              (equal (bc-scan nats (+ d e))
                     (bc-scan (bc-scan nats d) e)))
     :induct (bc-scan nats d)
     :enable (bc-scan zp fix)))
  :use (:instance lemma (d 1) (e 1)))

; If the scan of a text followed by more input
; stops exactly at the end of the text,
; then the text satisfies the specification's condition:
; the scan of the text alone makes the same steps,
; since the step that reaches the end of the text
; is the one that takes a closing */ within the text.

(defruledl bc-rest-closes-p-when-bc-scan-of-append
  (implies (and (posp depth)
                (nat-listp text)
                (nat-listp rest)
                (equal (bc-scan (append text rest) depth) rest))
           (bc-rest-closes-p text depth))
  :induct (bc-rest-closes-p text depth)
  :enable (bc-rest-closes-p bc-scan posp zp nfix)
  :hints ('(:use ((:instance len-of-bc-scan-<
                             (nats rest)
                             (depth depth))
                  (:instance len-of-bc-scan-<=
                             (nats (cdr rest))
                             (depth (1- depth)))
                  (:instance len-of-bc-scan-<=
                             (nats (cdr rest))
                             (depth (1+ depth)))))))

; The lexing functions for nested block comments follow the scan.
; After the opening /* of a nested comment,
; the scan at depth 1 stops where the comment ends.
; An item, and a sequence of items, leaves the scan at depth 1:
; an item is a nested comment, which the scan enters and leaves,
; or a character that is not part of a /* or of a */,
; since the lexer looks for those first.

(defruledl cdr-of-nat-list-fix-is-nat-list-fix-of-cdr
  (equal (cdr (nat-list-fix x))
         (nat-list-fix (cdr x)))
  :expand (nat-list-fix x))

; When the scan is known to stop at the tail of a list of naturals,
; what it returns is a list of naturals.
; (The hypothesis is matched against an equality in the goal,
; which the prover uses to replace the tail by the scan.)

(defruledl nat-list-fix-of-bc-scan-when-equal-cddr
  (implies (and (equal (bc-scan nats depth) (cddr list))
                (nat-listp list))
           (equal (nat-list-fix (bc-scan nats depth))
                  (bc-scan nats depth))))

; One step of the scan at depth 1:
; at a closing */ it ends, and
; at a character that does not start a */ or a /* it advances by one.

(defruledl bc-scan-1-when-star-slash
  (implies (prefixp '(#x2a #x2f) x)
           (equal (bc-scan x 1) (cddr x)))
  :expand ((bc-scan x 1) (bc-scan (cddr x) 0)))

(defruledl bc-scan-1-when-not-delimiter
  (implies (and (consp x)
                (not (prefixp '(#x2a #x2f) x))
                (not (prefixp '(#x2f #x2a) x)))
           (equal (bc-scan x 1) (bc-scan (cdr x) 1)))
  :expand (bc-scan x 1))

; What the proofs below need of the two character classes
; used in block comments: each takes one character,
; and which characters it excludes.
; With these, the classes can stay closed in those proofs.

(defruledl rest-input-of-lex-not-star-slash
  (b* (((mv tree rest-input) (lex-not-star-slash input)))
    (implies (not (reserrp tree))
             (and (consp input)
                  (equal rest-input (cdr (nat-list-fix input))))))
  :enable (lex-not-star-slash abnf::parse-next))

(defrulel car-of-input-when-lex-not-star-slash
  (implies (not (reserrp (mv-nth 0 (lex-not-star-slash input))))
           (and (not (equal (car (nat-list-fix input)) #x2a))
                (not (equal (car (nat-list-fix input)) #x2f))))
  :rule-classes nil
  :enable (lex-not-star-slash abnf::parse-next))

(defruledl rest-input-of-lex-not-star-bang
  (b* (((mv tree rest-input) (lex-not-star-bang input)))
    (implies (not (reserrp tree))
             (and (consp input)
                  (equal rest-input (cdr (nat-list-fix input))))))
  :enable (lex-not-star-bang abnf::parse-next))

(defrulel car-of-input-when-lex-not-star-bang
  (implies (not (reserrp (mv-nth 0 (lex-not-star-bang input))))
           (not (equal (car (nat-list-fix input)) #x2a)))
  :rule-classes nil
  :enable (lex-not-star-bang abnf::parse-next))

; The proof is by the induction of the three functions.
; The flag function of the lexer is local to its book,
; so we introduce it again here.

(local
 (flag::make-flag lex-block-comment-or-doc-fns-flag
                  lex-block-comment-or-doc
                  :defthm-macro-name defthm-lex-block-comment-or-doc-fns-flag
                  :hints (("Goal" :in-theory (enable abnf::parse-ichars
                                                     abnf::parse-ichars-aux
                                                     abnf::parse-next
                                                     nfix)))))

(local
 (std::defret-mutual bc-scan-of-lex-block-comment-or-doc-fns
   (defret bc-scan-of-lex-block-comment-or-doc
     (implies (not (reserrp tree))
              (equal (bc-scan (cddr (nat-list-fix input)) 1)
                     rest-input))
     :rule-classes nil
     :fn lex-block-comment-or-doc)
   (defret bc-scan-of-lex-block-item
     (implies (and (not (reserrp tree))
                   (not (prefixp (list #x2a #x2f) (nat-list-fix input))))
              (equal (bc-scan (nat-list-fix input) 1)
                     (bc-scan rest-input 1)))
     :rule-classes nil
     :fn lex-block-item)
   (defret bc-scan-of-lex-*-block-item
     (equal (bc-scan (nat-list-fix input) 1)
            (bc-scan rest-input 1))
     :rule-classes nil
     :fn lex-*-block-item)
   ;; In each case, only the function of that case is opened,
   ;; and only the scan terms that the case needs.
   :hints (("Goal"
            :in-theory (e/d (rest-input-of-lex-not-star-slash
                             parse-ichars-when-caseless-chars
                             nthcdr
                             bc-scan-of-2
                             cdr-of-nat-list-fix-is-nat-list-fix-of-cdr
                             nat-list-fix-of-bc-scan-when-equal-cddr)
                            (lex-block-comment-or-doc
                             lex-block-item
                             lex-*-block-item
                             acl2::prefixp-when-prefixp)))
           (and (acl2::occur-lst '(acl2::flag-is 'lex-block-comment-or-doc)
                                 clause)
                '(:expand ((lex-block-comment-or-doc input)
                           (bc-scan
                            (mv-nth 1 (lex-*-block-item
                                       (nat-list-fix (cddr input))))
                            1)
                           (:free (x) (bc-scan x 0)))))
           (and (acl2::occur-lst '(acl2::flag-is 'lex-block-item) clause)
                '(:expand ((lex-block-item input)
                           (bc-scan (nat-list-fix input) 1))))
           (and (acl2::occur-lst '(acl2::flag-is 'lex-*-block-item) clause)
                '(:expand ((lex-*-block-item input)))))))

; The first item of a plain block comment also leaves the scan at depth 1,
; when the comment is not /**/ or /***/,
; which the lexer lexes as wholes before it looks for a first item.

(defrulel bc-scan-of-lex-block-first-item
  (b* (((mv tree rest-input) (lex-block-first-item input)))
    (implies (and (not (reserrp tree))
                  (not (prefixp (list #x2a #x2f) (nat-list-fix input)))
                  (not (prefixp (list #x2a #x2a #x2f) (nat-list-fix input))))
             (equal (bc-scan (nat-list-fix input) 1)
                    (bc-scan rest-input 1))))
  :rule-classes nil
  :use ((:instance bc-scan-of-lex-block-comment-or-doc
                   (input (nat-list-fix input)))
        car-of-input-when-lex-not-star-bang)
  :expand ((bc-scan (nat-list-fix input) 1)
           (bc-scan (nat-list-fix (cdr input)) 1))
  :enable (lex-block-first-item
           rest-input-of-lex-not-star-bang
           parse-ichars-when-caseless-chars
           nthcdr
           bc-scan-of-2
           cdr-of-nat-list-fix-is-nat-list-fix-of-cdr))

; So, after the opening /* of a block comment or block doc comment,
; the scan at depth 1 stops where the comment ends.

(defrulel bc-scan-of-lex-inner-block-doc
  (b* (((mv tree rest-input) (lex-inner-block-doc input)))
    (implies (not (reserrp tree))
             (equal (bc-scan (cddr (nat-list-fix input)) 1)
                    rest-input)))
  :rule-classes nil
  :use (:instance bc-scan-of-lex-*-block-item
                  (input (nat-list-fix (cdddr input))))
  :enable (lex-inner-block-doc
           parse-ichars-when-caseless-chars
           nthcdr
           bc-scan-1-when-star-slash
           bc-scan-1-when-not-delimiter
           cdr-of-nat-list-fix-is-nat-list-fix-of-cdr
           nat-list-fix-of-bc-scan-when-equal-cddr))

(defrulel bc-scan-of-lex-outer-block-doc
  (b* (((mv tree rest-input) (lex-outer-block-doc input)))
    (implies (not (reserrp tree))
             (equal (bc-scan (cddr (nat-list-fix input)) 1)
                    rest-input)))
  :rule-classes nil
  :use ((:instance bc-scan-of-lex-*-block-item
                   (input (nat-list-fix (cddddr input))))
        (:instance car-of-input-when-lex-not-star-slash
                   (input (nat-list-fix (cdddr input)))))
  :enable (lex-outer-block-doc
           rest-input-of-lex-not-star-slash
           parse-ichars-when-caseless-chars
           nthcdr
           bc-scan-1-when-star-slash
           bc-scan-1-when-not-delimiter
           cdr-of-nat-list-fix-is-nat-list-fix-of-cdr
           nat-list-fix-of-bc-scan-when-equal-cddr))

(defrulel bc-scan-of-lex-block-comment
  (b* (((mv tree rest-input) (lex-block-comment input)))
    (implies (not (reserrp tree))
             (equal (bc-scan (cddr (nat-list-fix input)) 1)
                    rest-input)))
  :rule-classes nil
  :use ((:instance bc-scan-of-lex-block-first-item
                   (input (nat-list-fix (cddr input))))
        (:instance bc-scan-of-lex-*-block-item
                   (input (mv-nth 1 (lex-block-first-item
                                     (nat-list-fix (cddr input)))))))
  :enable (lex-block-comment
           parse-ichars-when-caseless-chars
           nthcdr
           bc-scan-1-when-star-slash
           bc-scan-1-when-not-delimiter
           cdr-of-nat-list-fix-is-nat-list-fix-of-cdr
           nat-list-fix-of-bc-scan-when-equal-cddr))

; From the scan on the input to the condition on the text of the comment.

(defruledl block-comment-string-p-when-bc-scan-of-cddr
  (implies (and (nat-listp string)
                (nat-listp rest)
                (prefixp (list #x2f #x2a) (append string rest))
                (equal (bc-scan (cddr (append string rest)) 1)
                       rest))
           (block-comment-string-p string))
  :enable (block-comment-string-p fix)
  :use ((:instance len-of-bc-scan-<
                   (nats (cddr (append string rest)))
                   (depth 1))
        (:instance bc-rest-closes-p-when-bc-scan-of-append
                   (text (cddr string))
                   (depth 1))))

(local
 (defmacro def-block-comment-string-p (fn)
   (b* ((string-thm (acl2::packn-pos
                     (list 'block-comment-string-p-of- fn) fn))
        (scan-thm (acl2::packn-pos (list 'bc-scan-of- fn) fn))
        (decomp-thm (acl2::packn-pos
                     (list 'input-decomposition-of- fn) fn))
        (terminated-thm (acl2::packn-pos
                         (list 'tree-terminatedp-of- fn) fn)))
     `(defruledl ,string-thm
        (b* (((mv tree &) (,fn input)))
          (implies (and (not (reserrp tree))
                        (prefixp (list #x2f #x2a) (nat-list-fix input)))
                   (block-comment-string-p (abnf::tree->string tree))))
        :use (,scan-thm
              ,decomp-thm
              (:instance block-comment-string-p-when-bc-scan-of-cddr
                         (string (abnf::tree->string (mv-nth 0 (,fn input))))
                         (rest (mv-nth 1 (,fn input)))))
        :enable ,terminated-thm
        :disable (,decomp-thm prefix-splitters)))))

(local
 (progn
   (def-block-comment-string-p lex-block-comment)
   (def-block-comment-string-p lex-outer-block-doc)
   (def-block-comment-string-p lex-inner-block-doc)))

; The condition, for every lexeme:
; if its text starts with /*, the text is one complete block comment.
; The text of a lexeme starts the input.
; If the input starts with /*, the lexer lexes a block comment,
; plain or doc, with one of the three functions above:
; whitespace does not start with a "/", and the lexer looks for
; a comment before it lexes a token.

(defruledl prefixp-of-input-when-prefixp-of-lexeme
  (b* (((mv tree &) (lex-lexeme input)))
    (implies (and (not (reserrp tree))
                  (prefixp x (abnf::tree->string tree)))
             (prefixp x (nat-list-fix input))))
  :use (prefixp-of-tree->string-of-lex-lexeme
        (:instance acl2::prefixp-transitive
                   (x x)
                   (y (abnf::tree->string (mv-nth 0 (lex-lexeme input))))
                   (z (nat-list-fix input))))
  :disable (prefixp-of-tree->string-of-lex-lexeme
            acl2::prefixp-transitive
            prefix-splitters))

(defruledl block-comment-string-p-of-lex-lexeme-when-input-starts
  (b* (((mv tree &) (lex-lexeme input)))
    (implies (and (not (reserrp tree))
                  (prefixp (list #x2f #x2a) (nat-list-fix input)))
             (block-comment-string-p (abnf::tree->string tree))))
  :enable (lex-lexeme
           lex-comment
           lex-whitespace
           lex-whitespace-char
           abnf::parse-next
           tree-strings
           block-comment-string-p-of-lex-block-comment
           block-comment-string-p-of-lex-outer-block-doc
           block-comment-string-p-of-lex-inner-block-doc))

(defruledl block-comment-string-p-of-lex-lexeme
  (b* (((mv tree &) (lex-lexeme input)))
    (implies (and (not (reserrp tree))
                  (prefixp (list #x2f #x2a) (abnf::tree->string tree)))
             (block-comment-string-p (abnf::tree->string tree))))
  :use ((:instance prefixp-of-input-when-prefixp-of-lexeme
                   (x (list #x2f #x2a)))
        block-comment-string-p-of-lex-lexeme-when-input-starts)
  :disable prefix-splitters)

; Conversely, if the input starts with a complete block comment,
; the lexer takes exactly that comment, if it does not fail.
; The scan of a text that satisfies the specification's condition,
; followed by more input, stops exactly at the end of the text;
; and the lexer stops where the scan does.

(defruledl bc-scan-of-append-when-bc-rest-closes-p
  (implies (and (natp depth)
                (nat-listp text)
                (bc-rest-closes-p text depth))
           (equal (bc-scan (append text rest) depth)
                  rest))
  :induct (bc-rest-closes-p text depth)
  :enable (bc-rest-closes-p bc-scan zp nfix)
  :expand (bc-rest-closes-p (cdr text) depth))

(defruledl bc-scan-of-cddr-of-append-when-block-comment-string-p
  (implies (and (nat-listp string)
                (block-comment-string-p string))
           (equal (bc-scan (cddr (append string rest)) 1)
                  rest))
  :enable (block-comment-string-p
           bc-scan-of-append-when-bc-rest-closes-p))

(local
 (defmacro def-rest-input-is-bc-scan (fn)
   `(defruledl ,(acl2::packn-pos (list 'rest-input-of- fn '-is-bc-scan) fn)
      (b* (((mv tree rest-input) (,fn input)))
        (implies (not (reserrp tree))
                 (equal rest-input
                        (bc-scan (cddr (nat-list-fix input)) 1))))
      :use ,(acl2::packn-pos (list 'bc-scan-of- fn) fn))))

(local (def-rest-input-is-bc-scan lex-block-comment))
(local (def-rest-input-is-bc-scan lex-outer-block-doc))
(local (def-rest-input-is-bc-scan lex-inner-block-doc))

(defruledl rest-input-of-lex-lexeme-is-bc-scan
  (b* (((mv tree rest-input) (lex-lexeme input)))
    (implies (and (not (reserrp tree))
                  (prefixp (list #x2f #x2a) (nat-list-fix input)))
             (equal rest-input
                    (bc-scan (cddr (nat-list-fix input)) 1))))
  :enable (lex-lexeme
           lex-comment
           lex-whitespace
           lex-whitespace-char
           abnf::parse-next
           rest-input-of-lex-block-comment-is-bc-scan
           rest-input-of-lex-outer-block-doc-is-bc-scan
           rest-input-of-lex-inner-block-doc-is-bc-scan))

(defruled rest-input-of-lex-lexeme-when-block-comment-string-p
  (implies (and (nat-listp string)
                (block-comment-string-p string)
                (not (reserrp (mv-nth 0 (lex-lexeme (append string rest))))))
           (equal (mv-nth 1 (lex-lexeme (append string rest)))
                  (nat-list-fix rest)))
  :use ((:instance rest-input-of-lex-lexeme-is-bc-scan
                   (input (append string rest)))
        (:instance bc-scan-of-cddr-of-append-when-block-comment-string-p
                   (rest (nat-list-fix rest))))
  :enable block-comment-string-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The lexeme is a valid lexeme CST:
; a lexeme CST that satisfies [SC2], [SC10], and [SC13].

(defret lexeme-cst-okp-of-lex-lexeme
  (implies (not (reserrp tree))
           (lexeme-cst-okp tree))
  :fn lex-lexeme
  :hints (("Goal" :in-theory (e/d (lexeme-cst-okp
                                   block-comment-string-p-of-lex-lexeme)
                                  (prefix-splitters)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC14] Float literals ending with a period.

; The lexer's test for a period that belongs to the number before it
; is the specification's:
; a period, followed by input that leaves the period to the number.

(defruledl number-period-ahead-p-is-period-and-follower-okp
  (equal (number-period-ahead-p input)
         (and (prefixp (list #x2e) (nat-list-fix input))
              (number-period-follower-okp (cdr (nat-list-fix input)))))
  :enable (number-period-ahead-p
           number-period-follower-okp
           identifier-start-code-p
           lex-identifier-start
           lex-ascii-letter
           abnf::parse-next
           abnf::not-reserrp-when-treep
           nfix))

; The text of a decimal literal, of an exponent, and of a suffix
; consists of letters, digits, underscores, and signs.
; In particular, it has no period.

(local
 (defun word-code-p (code)
   (and (natp code)
        (or (and (<= #x30 code) (<= code #x39)) ; 0-9
            (and (<= #x41 code) (<= code #x5a)) ; A-Z
            (and (<= #x61 code) (<= code #x7a)) ; a-z
            (equal code #x5f) ; _
            (equal code #x2b) ; +
            (equal code #x2d))))) ; -

(local
 (defun word-codes-p (codes)
   (or (atom codes)
       (and (word-code-p (car codes))
            (word-codes-p (cdr codes))))))

(defruledl word-codes-p-of-append
  (equal (word-codes-p (append x y))
         (and (word-codes-p x)
              (word-codes-p y)))
  :induct (word-codes-p x)
  :enable (word-codes-p append))

; For a function that lexes one tree
; (the keyword says if the tree is an option, which is never an error),
; and for a function that lexes a repetition, given the one for its element.

(local
 (defmacro def-word-codes (fn &key enable option)
   (b* ((thm (acl2::packn-pos (list 'word-codes-p-of- fn) fn))
        (concl '(word-codes-p (abnf::tree->string tree))))
     `(defruledl ,thm
        (b* (((mv tree &) (,fn input)))
          ,(if option concl `(implies (not (reserrp tree)) ,concl)))
        :enable (,fn
                 tree-strings
                 word-codes-p-of-append
                 tree->string-of-parse-ichars-when-caseless-chars
                 ,@enable)))))

(local
 (defmacro def-word-codes-rep (rep-fn elem-fn)
   (b* ((thm (acl2::packn-pos (list 'word-codes-p-of- rep-fn) rep-fn))
        (elem-thm (acl2::packn-pos (list 'word-codes-p-of- elem-fn) rep-fn)))
     `(defruledl ,thm
        (b* (((mv trees &) (,rep-fn input)))
          (word-codes-p (abnf::tree-list->string trees)))
        :induct (,rep-fn input)
        :enable (,rep-fn
                 ,elem-thm
                 abnf::tree-list->string
                 word-codes-p-of-append)))))

(local
 (progn
   (def-word-codes lex-ascii-letter :enable (abnf::parse-next))
   (def-word-codes lex-ascii-letter-no-e :enable (abnf::parse-next))
   (def-word-codes lex-ascii-letter-no-hex-digit :enable (abnf::parse-next))
   (def-word-codes lex-dec-digit :enable (abnf::parse-next))
   (def-word-codes lex-identifier-start
     :enable (word-codes-p-of-lex-ascii-letter))
   (def-word-codes lex-identifier-continue
     :enable (word-codes-p-of-lex-ascii-letter
              word-codes-p-of-lex-dec-digit))
   (def-word-codes-rep lex-*-identifier-continue lex-identifier-continue)
   (def-word-codes lex-suffix-no-e
     :enable (word-codes-p-of-lex-ascii-letter-no-e
              word-codes-p-of-lex-*-identifier-continue))
   (def-word-codes lex-suffix-no-hex-digit
     :enable (word-codes-p-of-lex-ascii-letter-no-hex-digit
              word-codes-p-of-lex-*-identifier-continue))
   (def-word-codes lex-suffix-no-underscore
     :enable (word-codes-p-of-lex-identifier-start
              word-codes-p-of-lex-*-identifier-continue))
   (def-word-codes lex-option-suffix-no-e
     :option t
     :enable (word-codes-p-of-lex-suffix-no-e))
   (def-word-codes lex-option-suffix-no-hex-digit
     :option t
     :enable (word-codes-p-of-lex-suffix-no-hex-digit))
   (def-word-codes lex-option-suffix-no-underscore
     :option t
     :enable (word-codes-p-of-lex-suffix-no-underscore))
   (def-word-codes lex-dec-digit/underscore
     :enable (word-codes-p-of-lex-dec-digit))
   (def-word-codes-rep lex-*-dec-digit/underscore lex-dec-digit/underscore)
   (def-word-codes lex-dec-literal
     :enable (word-codes-p-of-lex-dec-digit
              word-codes-p-of-lex-*-dec-digit/underscore))
   (def-word-codes lex-underscore-as-dec-item)
   (def-word-codes-rep lex-*-underscore-as-dec-item
     lex-underscore-as-dec-item)
   (def-word-codes lex-exponent-letter
     :enable (abnf::parse-schars
              abnf::parse-schars-aux
              abnf::nat-match-sensitive-char-p
              abnf::parse-next))
   (def-word-codes lex-option-sign :option t)
   (def-word-codes lex-float-exponent
     :enable (word-codes-p-of-lex-exponent-letter
              word-codes-p-of-lex-option-sign
              word-codes-p-of-lex-*-underscore-as-dec-item
              word-codes-p-of-lex-dec-digit
              word-codes-p-of-lex-*-dec-digit/underscore))))

; The last character of such text is not a period.

(defruledl car-of-last-of-cons
  (equal (car (last (cons a x)))
         (if (consp x)
             (car (last x))
           a))
  :enable last)

(defruledl not-period-car-of-last-when-word-codes-p
  (implies (and (word-codes-p x)
                (consp x))
           (not (equal (car (last x)) #x2e)))
  :induct (word-codes-p x)
  :enable (word-codes-p last))

(defruledl consp-of-tree->string-of-lex-dec-literal
  (b* (((mv tree &) (lex-dec-literal input)))
    (implies (not (reserrp tree))
             (consp (abnf::tree->string tree))))
  :use (input-decomposition-of-lex-dec-literal
        len-of-lex-dec-literal-<
        (:instance acl2::len-of-append
                   (x (abnf::tree->string (mv-nth 0 (lex-dec-literal input))))
                   (y (mv-nth 1 (lex-dec-literal input)))))
  :disable (input-decomposition-of-lex-dec-literal
            len-of-lex-dec-literal-<
            acl2::len-of-append))

; A float literal ends with a period only if it has no fraction:
; with a fraction, it ends with the fraction, an exponent, or a suffix.
; The lexer lexes a float literal without a fraction
; only after its test on what follows the period.

(defruledl float-period-of-lex-float-literal
  (b* (((mv tree rest-input) (lex-float-literal input)))
    (implies (and (not (reserrp tree))
                  (equal (car (last (abnf::tree->string tree))) #x2e))
             (number-period-follower-okp rest-input)))
  :enable (lex-float-literal
           tree-strings
           car-of-last-of-cons
           not-period-car-of-last-when-word-codes-p
           number-period-ahead-p-is-period-and-follower-okp
           parse-ichars-when-caseless-chars
           tree->string-of-parse-ichars-when-caseless-chars
           word-codes-p-of-lex-float-exponent
           word-codes-p-of-lex-dec-literal
           word-codes-p-of-lex-option-suffix-no-e
           word-codes-p-of-lex-option-suffix-no-underscore
           consp-of-tree->string-of-lex-dec-literal))

(defret lexeme-cst-float-period-okp-of-lex-lexeme
  (implies (not (reserrp tree))
           (lexeme-cst-float-period-okp tree rest-input))
  :fn lex-lexeme
  :hints (("Goal" :in-theory (e/d (lexeme-dispatch
                                   check-tree-utilities
                                   lexeme-cst-float-period-okp
                                   float-period-lexeme-cst-p
                                   tree-strings
                                   float-period-of-lex-float-literal)
                                  (prefix-splitters)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC7] Reserved numeric forms.

; The condition has three parts, proved in turn below,
; for a lexeme that holds an integer or float literal:
; what follows it does not start with "e" or "E";
; if its text is a radix prefix followed only by digits and underscores,
; what follows it is not a period that would belong to it;
; and if its text starts with a radix prefix,
; its tree is not that of a decimal literal.

; First part.
; A suffix ends with a repetition of identifier characters,
; which takes all it can:
; when the repetition ends, lexing one more of its elements fails,
; so that what follows does not start with a letter.
; Without a suffix, what follows the digits is what follows the literal,
; and the lexer has checked it,
; except after an exponent, where a letter would start a suffix.

(defruledl lex-identifier-continue-fails-after-repetition
  (b* (((mv & rest-input) (lex-*-identifier-continue input)))
    (reserrp (mv-nth 0 (lex-identifier-continue rest-input))))
  :induct (lex-*-identifier-continue input)
  :enable lex-*-identifier-continue)

(defruledl not-exponent-letter-ahead-p-when-lex-identifier-continue-fails
  (implies (reserrp (mv-nth 0 (lex-identifier-continue input)))
           (not (exponent-letter-ahead-p input)))
  :enable (lex-identifier-continue
           lex-ascii-letter
           abnf::parse-next
           exponent-letter-ahead-p
           abnf::not-reserrp-when-treep))

(defruledl not-exponent-letter-ahead-p-when-lex-identifier-start-fails
  (implies (reserrp (mv-nth 0 (lex-identifier-start input)))
           (not (exponent-letter-ahead-p input)))
  :enable (lex-identifier-start
           lex-ascii-letter
           abnf::parse-next
           exponent-letter-ahead-p
           abnf::not-reserrp-when-treep))

(defruledl not-exponent-letter-ahead-p-after-lex-option-suffix-no-e
  (b* (((mv & rest-input) (lex-option-suffix-no-e input)))
    (implies (not (exponent-letter-ahead-p input))
             (not (exponent-letter-ahead-p rest-input))))
  :enable (lex-option-suffix-no-e
           lex-suffix-no-e
           lex-identifier-continue-fails-after-repetition
           not-exponent-letter-ahead-p-when-lex-identifier-continue-fails))

(defruledl not-exponent-letter-ahead-p-after-lex-option-suffix-no-hex-digit
  (b* (((mv & rest-input) (lex-option-suffix-no-hex-digit input)))
    (implies (not (exponent-letter-ahead-p input))
             (not (exponent-letter-ahead-p rest-input))))
  :enable (lex-option-suffix-no-hex-digit
           lex-suffix-no-hex-digit
           lex-identifier-continue-fails-after-repetition
           not-exponent-letter-ahead-p-when-lex-identifier-continue-fails))

(defruledl not-exponent-letter-ahead-p-after-lex-option-suffix-no-underscore
  (b* (((mv & rest-input) (lex-option-suffix-no-underscore input)))
    (not (exponent-letter-ahead-p rest-input)))
  :enable (lex-option-suffix-no-underscore
           lex-suffix-no-underscore
           lex-identifier-continue-fails-after-repetition
           not-exponent-letter-ahead-p-when-lex-identifier-continue-fails
           not-exponent-letter-ahead-p-when-lex-identifier-start-fails
           abnf::not-reserrp-when-treep))

(defruledl not-exponent-letter-ahead-p-when-number-period-follower-okp
  (implies (number-period-follower-okp input)
           (not (exponent-letter-ahead-p input)))
  :enable (number-period-follower-okp
           identifier-start-code-p
           exponent-letter-ahead-p))

(defruledl not-exponent-letter-ahead-p-after-lex-float-literal
  (b* (((mv tree rest-input) (lex-float-literal input)))
    (implies (not (reserrp tree))
             (not (exponent-letter-ahead-p rest-input))))
  :enable (lex-float-literal
           parse-ichars-when-caseless-chars
           number-period-ahead-p-is-period-and-follower-okp
           not-exponent-letter-ahead-p-when-number-period-follower-okp
           not-exponent-letter-ahead-p-after-lex-option-suffix-no-e
           not-exponent-letter-ahead-p-after-lex-option-suffix-no-underscore
           nthcdr))

(defruledl not-exponent-letter-ahead-p-after-lex-integer-literal
  (b* (((mv tree rest-input) (lex-integer-literal input)))
    (implies (not (reserrp tree))
             (not (exponent-letter-ahead-p rest-input))))
  :enable (lex-integer-literal
           not-exponent-letter-ahead-p-after-lex-option-suffix-no-e
           not-exponent-letter-ahead-p-after-lex-option-suffix-no-hex-digit)
  :disable prefix-splitters)

(defruledl no-exponent-letter-after-lex-lexeme-when-number-literal
  (b* (((mv tree rest-input) (lex-lexeme input)))
    (implies (and (not (reserrp tree))
                  (number-literal-lexeme-cst-p tree))
             (not (exponent-letter-ahead-p rest-input))))
  :enable (lexeme-dispatch
           check-tree-utilities
           number-literal-lexeme-cst-p
           not-exponent-letter-ahead-p-after-lex-float-literal
           not-exponent-letter-ahead-p-after-lex-integer-literal)
  :disable prefix-splitters)

; Second part.
; The text of an integer literal is that of its digits, with the prefix,
; followed by that of its suffix.
; If all of it after the prefix is digits and underscores,
; so is the suffix; but a suffix starts with a letter
; (after a hexadecimal literal, one that is not a hexadecimal digit),
; so there is no suffix.
; Then what follows the literal is what follows its digits,
; where the lexer has checked that there is no period
; that would belong to the literal.

(defruledl digits/underscores-p-of-append
  (equal (digits/underscores-p (append x y) hexp)
         (and (digits/underscores-p x hexp)
              (digits/underscores-p y hexp)))
  :induct (len x)
  :enable (append (:induction len))
  :expand ((digits/underscores-p x hexp)
           (:free (a b) (digits/underscores-p (cons a b) hexp))))

(defruledl lex-option-suffix-no-hex-digit-when-digits/underscores
  (b* (((mv tree rest-input) (lex-option-suffix-no-hex-digit input)))
    (implies (digits/underscores-p (abnf::tree->string tree) hexp)
             (equal rest-input (nat-list-fix input))))
  :enable (lex-option-suffix-no-hex-digit
           lex-suffix-no-hex-digit
           lex-ascii-letter-no-hex-digit
           abnf::parse-next
           tree-strings
           digits/underscores-p))

(defruledl lex-option-suffix-no-e-when-digits/underscores
  (b* (((mv tree rest-input) (lex-option-suffix-no-e input)))
    (implies (digits/underscores-p (abnf::tree->string tree) nil)
             (equal rest-input (nat-list-fix input))))
  :enable (lex-option-suffix-no-e
           lex-suffix-no-e
           lex-ascii-letter-no-e
           abnf::parse-next
           tree-strings
           digits/underscores-p))

(defruledl prefix-of-tree->string-of-lex-hex-literal
  (b* (((mv tree &) (lex-hex-literal input)))
    (implies (not (reserrp tree))
             (prefixp (list #x30 #x78) (abnf::tree->string tree))))
  :enable (lex-hex-literal parse-schars-is-prefix-match tree-strings))

(defruledl prefix-of-tree->string-of-lex-bin-literal
  (b* (((mv tree &) (lex-bin-literal input)))
    (implies (not (reserrp tree))
             (prefixp (list #x30 #x62) (abnf::tree->string tree))))
  :enable (lex-bin-literal parse-schars-is-prefix-match tree-strings))

(defruledl prefix-of-tree->string-of-lex-oct-literal
  (b* (((mv tree &) (lex-oct-literal input)))
    (implies (not (reserrp tree))
             (prefixp (list #x30 #x6f) (abnf::tree->string tree))))
  :enable (lex-oct-literal parse-schars-is-prefix-match tree-strings))

(defruledl digits/underscores-p-of-suffix-when-hex-literal-string
  (implies (and (nat-listp lit)
                (nat-listp suffix)
                (prefixp (list #x30 #x78) lit)
                (radix-literal-string-p (append lit suffix)))
           (digits/underscores-p suffix t))
  :enable (radix-literal-string-p
           digits/underscores-p-of-append))

(defruledl digits/underscores-p-of-suffix-when-bin/oct-literal-string
  (implies (and (nat-listp lit)
                (nat-listp suffix)
                (or (prefixp (list #x30 #x62) lit)
                    (prefixp (list #x30 #x6f) lit))
                (radix-literal-string-p (append lit suffix)))
           (digits/underscores-p suffix nil))
  :enable (radix-literal-string-p
           digits/underscores-p-of-append))

; One lemma for each radix, each with one instance of the lemmas above,
; then the three together.
; (All three instances in one proof are too much for the prover.)

(defruledl no-number-period-after-lex-integer-literal-when-hex
  (b* (((mv tree rest-input) (lex-integer-literal input)))
    (implies (and (not (reserrp tree))
                  (prefixp (list #x30 #x78) (nat-list-fix input))
                  (radix-literal-string-p (abnf::tree->string tree)))
             (not (number-period-ahead-p rest-input))))
  :use (:instance digits/underscores-p-of-suffix-when-hex-literal-string
                  (lit (abnf::tree->string
                        (mv-nth 0 (lex-hex-literal input))))
                  (suffix (abnf::tree->string
                           (mv-nth 0 (lex-option-suffix-no-hex-digit
                                      (mv-nth 1 (lex-hex-literal input)))))))
  :enable (lex-integer-literal
           tree-strings
           prefix-of-tree->string-of-lex-hex-literal
           lex-option-suffix-no-hex-digit-when-digits/underscores)
  :disable prefix-splitters)

(defruledl no-number-period-after-lex-integer-literal-when-bin
  (b* (((mv tree rest-input) (lex-integer-literal input)))
    (implies (and (not (reserrp tree))
                  (not (prefixp (list #x30 #x78) (nat-list-fix input)))
                  (prefixp (list #x30 #x62) (nat-list-fix input))
                  (radix-literal-string-p (abnf::tree->string tree)))
             (not (number-period-ahead-p rest-input))))
  :use (:instance digits/underscores-p-of-suffix-when-bin/oct-literal-string
                  (lit (abnf::tree->string
                        (mv-nth 0 (lex-bin-literal input))))
                  (suffix (abnf::tree->string
                           (mv-nth 0 (lex-option-suffix-no-e
                                      (mv-nth 1 (lex-bin-literal input)))))))
  :enable (lex-integer-literal
           tree-strings
           prefix-of-tree->string-of-lex-bin-literal
           lex-option-suffix-no-e-when-digits/underscores)
  :disable prefix-splitters)

(defruledl no-number-period-after-lex-integer-literal-when-oct
  (b* (((mv tree rest-input) (lex-integer-literal input)))
    (implies (and (not (reserrp tree))
                  (not (prefixp (list #x30 #x78) (nat-list-fix input)))
                  (not (prefixp (list #x30 #x62) (nat-list-fix input)))
                  (prefixp (list #x30 #x6f) (nat-list-fix input))
                  (radix-literal-string-p (abnf::tree->string tree)))
             (not (number-period-ahead-p rest-input))))
  :use (:instance digits/underscores-p-of-suffix-when-bin/oct-literal-string
                  (lit (abnf::tree->string
                        (mv-nth 0 (lex-oct-literal input))))
                  (suffix (abnf::tree->string
                           (mv-nth 0 (lex-option-suffix-no-e
                                      (mv-nth 1 (lex-oct-literal input)))))))
  :enable (lex-integer-literal
           tree-strings
           prefix-of-tree->string-of-lex-oct-literal
           lex-option-suffix-no-e-when-digits/underscores)
  :disable prefix-splitters)

(defruledl no-number-period-after-lex-integer-literal-when-radix-literal
  (b* (((mv tree rest-input) (lex-integer-literal input)))
    (implies (and (not (reserrp tree))
                  (radix-prefix-p input)
                  (radix-literal-string-p (abnf::tree->string tree)))
             (not (number-period-ahead-p rest-input))))
  :enable (radix-prefix-p
           no-number-period-after-lex-integer-literal-when-hex
           no-number-period-after-lex-integer-literal-when-bin
           no-number-period-after-lex-integer-literal-when-oct))

; No float literal starts with a radix prefix:
; the decimal literal that starts the input is then the digit 0,
; and what follows it is "b", "o", or "x",
; not an exponent or a period.

(defruledl lex-*-dec-digit/underscore-when-item-fails
  (implies (reserrp (mv-nth 0 (lex-dec-digit/underscore input)))
           (equal (lex-*-dec-digit/underscore input)
                  (mv nil (nat-list-fix input))))
  :enable lex-*-dec-digit/underscore)

(defruledl rest-of-lex-dec-literal-when-radix-prefix-p
  (implies (radix-prefix-p input)
           (equal (mv-nth 1 (lex-dec-literal input))
                  (cdr (nat-list-fix input))))
  :prep-lemmas
  ((defrule lemma
     (implies (and (nat-listp input)
                   (radix-prefix-p input))
              (equal (mv-nth 1 (lex-dec-literal input))
                     (cdr input)))
     :enable (radix-prefix-p
              lex-dec-literal
              lex-dec-digit
              lex-dec-digit/underscore
              abnf::parse-next
              abnf::not-reserrp-when-treep
              parse-ichars-when-caseless-chars
              lex-*-dec-digit/underscore-when-item-fails
              nfix)))
  :use (:instance lemma (input (nat-list-fix input))))

(defruledl lex-float-literal-fails-when-radix-prefix-p
  (implies (radix-prefix-p input)
           (reserrp (mv-nth 0 (lex-float-literal input))))
  :prep-lemmas
  ((defrule lemma
     (implies (and (nat-listp input)
                   (radix-prefix-p input))
              (reserrp (mv-nth 0 (lex-float-literal input))))
     :use rest-of-lex-dec-literal-when-radix-prefix-p
     :enable (radix-prefix-p
              lex-float-literal
              exponent-letter-ahead-p
              number-period-ahead-p)))
  :use (:instance lemma (input (nat-list-fix input))))

(defruledl no-number-period-after-lex-lexeme-when-radix-literal
  (b* (((mv tree rest-input) (lex-lexeme input)))
    (implies (and (not (reserrp tree))
                  (number-literal-lexeme-cst-p tree)
                  (radix-prefix-p input)
                  (radix-literal-string-p (abnf::tree->string tree)))
             (not (number-period-ahead-p rest-input))))
  :enable (lexeme-dispatch
           check-tree-utilities
           number-literal-lexeme-cst-p
           tree-strings
           lex-float-literal-fails-when-radix-prefix-p
           no-number-period-after-lex-integer-literal-when-radix-literal)
  :disable prefix-splitters)

; Third part.
; When the input starts with a radix prefix,
; the lexer lexes the literal in that radix,
; so the tree holds a literal in that radix, not a decimal one.

(local
 (progn
   (def-lexed-rulename lex-bin-literal "bin-literal")
   (def-lexed-rulename lex-oct-literal "oct-literal")
   (def-lexed-rulename lex-hex-literal "hex-literal")))

(defruledl not-dec-integer-literal-of-lex-lexeme-when-radix-prefix-p
  (b* (((mv tree &) (lex-lexeme input)))
    (implies (and (not (reserrp tree))
                  (radix-prefix-p input))
             (not (dec-integer-literal-lexeme-cst-p tree))))
  :enable (lexeme-dispatch
           lex-integer-literal
           check-tree-utilities
           abnf::check-tree-nonleaf-2
           abnf::check-tree-list-list-2
           abnf::not-reserrp-when-tree-list-tuple2p
           dec-integer-literal-lexeme-cst-p
           radix-prefix-p)
  :disable prefix-splitters)

; The condition, from its three parts.
; The text of the lexeme starts the input,
; so a radix prefix of the text is one of the input.

(defruledl radix-prefix-p-when-radix-literal-string-p
  (implies (radix-literal-string-p nats)
           (radix-prefix-p nats))
  :enable (radix-literal-string-p radix-prefix-p)
  :disable prefix-splitters)

(defruledl radix-prefix-p-of-input-when-radix-prefix-p-of-lexeme
  (b* (((mv tree &) (lex-lexeme input)))
    (implies (and (not (reserrp tree))
                  (radix-prefix-p (abnf::tree->string tree)))
             (radix-prefix-p input)))
  :use ((:instance prefixp-of-input-when-prefixp-of-lexeme
                   (x (list #x30 #x62)))
        (:instance prefixp-of-input-when-prefixp-of-lexeme
                   (x (list #x30 #x6f)))
        (:instance prefixp-of-input-when-prefixp-of-lexeme
                   (x (list #x30 #x78))))
  :enable (radix-prefix-p tree-terminatedp-of-lex-lexeme)
  :disable prefix-splitters)

(defret lexeme-cst-reserved-number-okp-of-lex-lexeme
  (implies (not (reserrp tree))
           (lexeme-cst-reserved-number-okp tree rest-input))
  :fn lex-lexeme
  :hints (("Goal"
           :in-theory
           (e/d (lexeme-cst-reserved-number-okp
                 exponent-letter-ahead-p
                 radix-prefix-p-when-radix-literal-string-p
                 radix-prefix-p-of-input-when-radix-prefix-p-of-lexeme
                 not-dec-integer-literal-of-lex-lexeme-when-radix-prefix-p)
                (prefix-splitters))
           :use (no-number-period-after-lex-lexeme-when-radix-literal
                 no-exponent-letter-after-lex-lexeme-when-number-literal
                 (:instance number-period-ahead-p-is-period-and-follower-okp
                            (input (mv-nth 1 (lex-lexeme input))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The lexer and the specification.

(define lexeme-cst-list-maximal-p ((trees abnf::tree-listp)
                                   (input nat-listp))
  :returns (yes/no booleanp)
  :short "Check that each lexeme CST in a list
          is maximal against the input that follows it [SC1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the maximal munch part of @(tsee lexing-okp), by itself:
     each tree in the list satisfies @(tsee lexeme-cst-maximal-p)
     with the input that remains after it and the trees before it.")
   (xdoc::p
    "It is the hypothesis of
     @(tsee lexing-okp-of-lexemize-rust-when-maximal),
     which proves the other parts of @(tsee lexing-okp) for the lexer.
     That the lexer's lexemes are maximal is not proved yet."))
  :measure (len trees)
  (b* ((trees (abnf::tree-list-fix trees))
       (input (nat-list-fix input))
       ((when (endp trees)) t)
       (tree (car trees))
       (rest-input (nthcdr (len (abnf::tree->string tree)) input)))
    (and (lexeme-cst-maximal-p tree rest-input)
         (lexeme-cst-list-maximal-p (cdr trees) rest-input))))

; The lexer lexes one lexeme after another, as many as it can.
; Each of them satisfies the conditions proved above,
; with the input that the lexer goes on from,
; which is the input after the text of the lexeme.

(defruledl lexing-okp-of-lex-*-lexeme-when-maximal
  (b* (((mv trees rest-input) (lex-*-lexeme input)))
    (implies (and (not (consp rest-input))
                  (lexeme-cst-list-maximal-p trees input))
             (lexing-okp trees input)))
  :induct (lex-*-lexeme input)
  :enable (lex-*-lexeme
           lexing-okp
           lexeme-cst-list-maximal-p))

(defrule lexing-okp-of-lexemize-rust-when-maximal
  :short "The lexemes that the lexer returns satisfy the specification,
          if each of them is maximal."
  :long
  (xdoc::topstring
   (xdoc::p
    "When @(tsee lexemize-rust) succeeds,
     its result satisfies @(tsee lexing-okp),
     under the hypothesis that each lexeme is maximal
     (see @(tsee lexeme-cst-list-maximal-p)):
     every other part of the specification is proved here.
     That is, each lexeme is a valid lexeme CST
     (it matches the grammar, and satisfies [SC2], [SC10], and [SC13]);
     it is not empty, and its text starts the remaining input;
     it satisfies [SC3], [SC7], [SC8], [SC9], [SC11], [SC12], and [SC14];
     and the lexemes cover the input exactly."))
  (b* ((trees (lexemize-rust input)))
    (implies (and (not (reserrp trees))
                  (lexeme-cst-list-maximal-p trees input))
             (lexing-okp trees input)))
  :enable (lexemize-rust
           lexing-okp-of-lex-*-lexeme-when-maximal))
