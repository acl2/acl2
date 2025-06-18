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

(include-book "keywords")
(include-book "symbols")
(include-book "grammar")

(include-book "projects/abnf/parsing-tools/defdefparse" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser
  :parents (lexing-and-parsing)
  :short "An executable parser of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "If you are looking for API functions for calling the Leo parser,
     please see @(see parser-interface).  The following section describes
     the process of parsing a list of tokens into a CST.")
   (xdoc::p
    "This is a fairly simple parser for the Leo syntactic grammar.
     Efficiency is not the primary focus for now;
     correctness and simplicity are.
     In the future, we may optimize this parser,
     or we may use "
    (xdoc::seetopic "apt::apt" "APT")
    " to do so.")
   (xdoc::p
    "The parser consists of a collection of parsing functions
     that operate on a sequence of tokens.
     Most parsing functions take a lookahead token (an optional
     ABNF tree) and a sequence of the remaining tokens (list of
     ABNF trees).")
   (xdoc::p
    "Each ABNF tree in the sequence of tokens
     (and the lookahead token) should have a rulename
     from the right hand side of the ABNF rule for @('token')
     indicating the kind of token it is:")
   (xdoc::codeblock
    "token = keyword"
    "      / identifier"
    "      / atomic-literal"
    "      / numeral"
    "      / annotation"
    "      / symbol")
   (xdoc::p
    "All the parsing functions return, as first result,
     an ABNF tree or list of trees
     that represents the parsed input.
     This is called a CST (Concrete Syntax Tree).")
   (xdoc::p
    "Almost all the parsing functions also return
     the next unparsed token and the tokens that follow it.
     That is, they prefetch the token, so it is ready for the next function.
     If the end of the input is reached, the next token is @('nil')
     (and so is the list of tokens after it)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-b*-binder pok
  :parents (parser)  ; This :parents option should be the default but currently
                     ; def-b*-binder xdoc ignores the defxdoc+ :default-parent.
  :short "@(tsee b*) binder for checking and propagating
          error results of parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is related to @(tsee fty::patbind-ok),
     but it is used for most of the parsing functions,
     in many places."))
  :decls
  ((declare (xargs :guard (acl2::destructure-guard ok args acl2::forms 1))))
  :body
  `(b* (((mv patbinder-ok-fresh-variable-for-result token input)
         ,(car acl2::forms))
        ((when (reserrp patbinder-ok-fresh-variable-for-result))
         (mv (reserrf-push patbinder-ok-fresh-variable-for-result)
             token input))
        (,(car args) patbinder-ok-fresh-variable-for-result))
     ,acl2::rest-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-b*-binder pok<
  :parents (parser)
  :short "@(tsee b*) binder for checking and propagating
          error results of parsing functions and ensuring termination."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee patbind-pok),
     but it also checks that
     the @(tsee parsize) of the output token and remaining tokens
     is strictly below the one of the input token and remaining tokens.
     The test is put in an @(tsee mbt),
     because it is always true,
     but we need to test for it explicitly in order to ensure termination
     of certain recursive functions;
     after the functions have been admitted,
     guard verification ensures that those tests are indeed true."))
  :decls
  ((declare (xargs :guard (acl2::destructure-guard ok args acl2::forms 1))))
  :body
  `(b* (((mv patbinder-ok-fresh-variable-for-result token1 input1)
         ,(car acl2::forms))
        ((when (reserrp patbinder-ok-fresh-variable-for-result))
         (mv (reserrf-push patbinder-ok-fresh-variable-for-result)
             token1 input1))
        ((unless (mbt (< (parsize token1 input1)
                         (parsize token input))))
         (mv (reserrf :impossible) token1 input1))
        (token token1)
        (input input1)
        (,(car args) patbinder-ok-fresh-variable-for-result))
     ,acl2::rest-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ perr (arg)
  :short "Returning a parsing error."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used only in certain lower-level parsing functions."))
  `(mv (reserrf ,arg) nil (abnf::tree-list-fix input)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-token ((input abnf::tree-listp))
  :returns (mv (tree? abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('token')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to obtain the next token in the input, if any."))
  (b* (((when (atom input)) (mv nil nil))
       (input (abnf::tree-list-fix input)))
    (mv (car input) (cdr input)))
  :hooks (:fix)
  ///

  (defret len-of-parse-token-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-token-<
    (implies tree?
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parsize ((token? abnf::tree-optionp) (input abnf::tree-listp))
  :returns (size natp)
  :short "Size of the parser input."
  :long
  (xdoc::topstring
   (xdoc::p
    "As discussed in @(see parser),
     most parsing functions take the input with
     the next token (if present) prefetched.
     Thus, when considering the size of the input,
     and how it decreases during parsing,
     we need to take into account the next token.
     We count it as 1 if present, as 0 if absent."))
  (+ (abnf::tree-option-case token? :some 1 :none 0)
     (len input))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-rootp ((rulename stringp) (token abnf::tree-optionp))
  :returns (yes/no booleanp)
  :short "Check if the given token has the given rule name as root."
  (abnf-tree-with-root-p (abnf::tree-option-fix token) rulename)
  :hooks (:fix)
  ///

  (defruled token-nonnil-when-rootp
    (implies (token-rootp string token)
             token)
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-stringp ((string stringp) (token abnf::tree-optionp))
  :returns (yes/no booleanp)
  :short "Check if the given token has the given string as fringe."
  (abnf::tree-option-case
   token
   :some (equal (abnf::tree->string token.val)
                (string=>nats (str-fix string)))
   :none nil)
  :hooks (:fix)
  ///

  (defruled token-nonnil-when-stringp
    (implies (token-stringp string token)
             token)
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-token-root ((rulename stringp) (token abnf::tree-optionp))
  :returns (tree abnf::tree-resultp)
  :short "Check if the given token is present
          and has the given rule name as root."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check is successful, return the token.
     Using this function ensures that we get a CST tree or @(see reserr)."))
  (abnf::tree-option-case
   token
   :some (if (token-rootp rulename token.val)
             token.val
           (reserrf (list :required (str-fix rulename) :found token.val)))
   :none (reserrf (list :required (str-fix rulename) :found nil)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-token-string ((string stringp) (token abnf::tree-optionp))
  :returns (tree abnf::tree-resultp)
  :short "Check if the given token is present
          and has the given string as fringe."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check is successful, return the token.
     Using this function ensures that we get a CST tree or @(see reserr)."))
  (abnf::tree-option-case
   token
   :some (if (token-stringp string token.val)
             token.val
           (reserrf (list :required (str-fix string) :found token.val)))
   :none (reserrf (list :required (str-fix string) :found nil)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-keyword ((keyword stringp)
                       (token abnf::tree-optionp)
                       (input abnf::tree-listp))
  :guard (member-equal keyword *keywords*)
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a specified @('keyword')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to check the presence of an expected keyword.
     We return it as a leaf tree as the first result,
     because this is how a keyword occurs
     in the CSTs of the syntactic grammar.
     In other words, the @('keyword') rulename does not appear
     in any CST returned by the parser.")
   (xdoc::p
    "This is consistent with the fact that
     the rule for @('keyword') does not appear on the right
     hand side of any rule other than the rule @('token').")
   (xdoc::p
    "This function is used to parse a keyword that appears
     in the list of tokens.  There are other keywords that
     can appear within @('atomic-literal') tokens, but those
     have already been assembled into the token by the lexer
     and will not be seen by this function."))
  (b* ((tree (check-token-root "keyword" token))
       ((when (reserrp tree)) (perr (reserrf-push tree)))
       ((unless (equal (abnf::tree->string tree)
                       (string=>nats (str-fix keyword))))
        (perr (list :required (str-fix keyword)
                    :found (abnf::tree-option-fix token))))
       (tree (abnf::tree-leafterm (string=>nats (str-fix keyword))))
       ((mv token input) (parse-token input)))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-keyword-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret parsize-of-parse-keyword-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret len-of-parse-keyword-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-keyword-<
    (implies (and (not (reserrp tree))
                  next-token)
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-symbol-among ((symbols string-listp)
                            (token abnf::tree-optionp)
                            (input abnf::tree-listp))
  :guard (subsetp-equal symbols *symbols*)
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('symbol') among the ones in a specified list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to check the presence of an expected symbol.
     We return it as a leaf tree as the first result,
     because this is how a symbol occurs
     in the CSTs of the syntactic grammar.
     In other words, the @('symbol') rulename does not appear
     in any CST returned by the parser.")
   (xdoc::p
    "As with keywords, this is consistent with the fact that
     the rule @('symbol') does not appear on the right
     hand side of any rule other than the rule @('token').")
   (xdoc::p
    "This function is used to parse a symbol that appears
     in the list of tokens.  There is a small number of other symbols that
     can appear within @('identifier') or @('atomic-literal') tokens, but those
     have already been assembled into the token by the lexer
     and will not be seen by this function."))
  (b* ((tree (check-token-root "symbol" token))
       ((when (reserrp tree)) (perr (reserrf-push tree)))
       (fringe (abnf::tree->string tree))
       ((unless (nat-listp fringe)) (perr :impossible))
       ((unless (parse-symbol-among-aux fringe symbols))
        (perr (list :required :one-of (str::string-list-fix symbols)
                    :found tree)))
       (tree (abnf::tree-leafterm fringe))
       ((mv token input) (parse-token input)))
    (mv tree token input))
  :hooks (:fix)

  :prepwork
  ((define parse-symbol-among-aux ((nats nat-listp) (strings string-listp))
     :returns (yes/no booleanp)
     :parents nil
     (and (consp strings)
          (or (equal (string=>nats (str-fix (car strings)))
                     (nat-list-fix nats))
              (parse-symbol-among-aux nats (cdr strings))))
     :hooks (:fix)))

  ///

  (defret parsize-of-parse-symbol-among-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret parsize-of-parse-symbol-among-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret len-of-parse-symbol-among-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-symbol-among-<
    (implies (and (not (reserrp tree))
                  next-token)
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-symbol ((symbol stringp)
                      (token abnf::tree-optionp)
                      (input abnf::tree-listp))
  :guard (member-equal symbol *symbols*)
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a specified @('symbol')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to check the presence of an expected symbol.")
   (xdoc::p
    "For more details see @(see parse-symbol-among)."))
  (parse-symbol-among (list symbol) token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-symbol-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-symbol-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear)

  (defret len-of-parse-symbol-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-symbol-<
    (implies (and (not (reserrp tree))
                  next-token)
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-identifier ((token abnf::tree-optionp)
                          (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('identifier')."
  (b* ((tree (check-token-root "identifier" token))
       ((when (reserrp tree)) (perr (reserrf-push tree)))
       ((mv token input) (parse-token input)))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-identifier-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret parsize-of-parse-identifier-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret len-of-parse-identifier-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-identifier-<
    (implies (and (not (reserrp tree))
                  next-token)
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-program-id ((token abnf::tree-optionp)
                          (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('program-id')."
  (b* (((pok tree1) (parse-identifier token input))
       ((pok tree2) (parse-symbol "." token input))
       ((pok tree3) (parse-identifier token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "program-id")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-program-id-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-program-id-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-locator ((token abnf::tree-optionp)
                       (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('locator')."
  (b* (((pok tree1) (parse-program-id token input))
       ((pok tree2) (parse-symbol "/" token input))
       ((pok tree3) (parse-identifier token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "locator")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-locator-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-locator-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-annotation ((token abnf::tree-optionp)
                          (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('annotation')."
  (b* ((tree (check-token-root "annotation" token))
       ((when (reserrp tree)) (perr (reserrf-push tree)))
       ((mv token input) (parse-token input)))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-annotation-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret parsize-of-parse-annotation-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret len-of-parse-annotation-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-annotation-<
    (implies (and (not (reserrp tree))
                  next-token)
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-*-annotation ((token abnf::tree-optionp)
                             (input abnf::tree-listp))
  :returns (mv (trees
                abnf::tree-list-resultp
                :hints
                (("Goal"
                  :in-theory
                  (enable
                   abnf::treep-when-tree-resultp-and-not-reserrp
                   abnf::tree-listp-when-tree-list-resultp-and-not-reserrp))))
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('*annotation')."
  (b* (((unless (token-rootp "annotation" token))
        (mv nil
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input)))
       ((pok< tree1) (parse-annotation token input))
       ((pok rest-trees) (parse-*-annotation token input)))
    (mv (cons tree1 rest-trees) token input))
  :measure (parsize token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-*-annotation-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-atomic-literal ((token abnf::tree-optionp)
                              (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('atomic-literal')."
  (b* ((tree (check-token-root "atomic-literal" token))
       ((when (reserrp tree)) (perr (reserrf-push tree)))
       ((mv token input) (parse-token input)))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-atomic-literal-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret parsize-of-parse-atomic-literal-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-numeral ((token abnf::tree-optionp)
                       (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('numeral') token."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when parsing group coordinates and
     could be used for other untyped natural numbers,
     but currently most uses of @('numeral') are handled
     by the lexer when constructing numeric literals."))
  (b* ((tree (check-token-root "numeral" token))
       ((when (reserrp tree)) (perr (reserrf-push tree)))
       ((mv token input) (parse-token input)))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-numeral-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret parsize-of-numeral-literal-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-?-comma ((token abnf::tree-optionp)
                       (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('[ \",\" ]')."
  (if (token-stringp "," token)
      (b* (((pok tree) (parse-symbol "," token input)))
        (mv (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree)))
            token
            input))
    (mv (abnf::make-tree-nonleaf :rulename? nil :branches nil)
        (abnf::tree-option-fix token)
        (abnf::tree-list-fix input)))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-?-comma
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-named-primitive-type ((token abnf::tree-optionp)
                              (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('named-primitive-type')."
  (cond ((token-stringp "u8" token)
         (b* (((pok tree) (parse-keyword "u8" token input)))
           (mv (abnf-tree-wrap tree
                               "unsigned-type"
                               "integer-type"
                               "arithmetic-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "u16" token)
         (b* (((pok tree) (parse-keyword "u16" token input)))
           (mv (abnf-tree-wrap tree
                               "unsigned-type"
                               "integer-type"
                               "arithmetic-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "u32" token)
         (b* (((pok tree) (parse-keyword "u32" token input)))
           (mv (abnf-tree-wrap tree
                               "unsigned-type"
                               "integer-type"
                               "arithmetic-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "u64" token)
         (b* (((pok tree) (parse-keyword "u64" token input)))
           (mv (abnf-tree-wrap tree
                               "unsigned-type"
                               "integer-type"
                               "arithmetic-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "u128" token)
         (b* (((pok tree) (parse-keyword "u128" token input)))
           (mv (abnf-tree-wrap tree
                               "unsigned-type"
                               "integer-type"
                               "arithmetic-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "i8" token)
         (b* (((pok tree) (parse-keyword "i8" token input)))
           (mv (abnf-tree-wrap tree
                               "signed-type"
                               "integer-type"
                               "arithmetic-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "i16" token)
         (b* (((pok tree) (parse-keyword "i16" token input)))
           (mv (abnf-tree-wrap tree
                               "signed-type"
                               "integer-type"
                               "arithmetic-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "i32" token)
         (b* (((pok tree) (parse-keyword "i32" token input)))
           (mv (abnf-tree-wrap tree
                               "signed-type"
                               "integer-type"
                               "arithmetic-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "i64" token)
         (b* (((pok tree) (parse-keyword "i64" token input)))
           (mv (abnf-tree-wrap tree
                               "signed-type"
                               "integer-type"
                               "arithmetic-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "i128" token)
         (b* (((pok tree) (parse-keyword "i128" token input)))
           (mv (abnf-tree-wrap tree
                               "signed-type"
                               "integer-type"
                               "arithmetic-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "field" token)
         (b* (((pok tree) (parse-keyword "field" token input)))
           (mv (abnf-tree-wrap tree
                               "field-type"
                               "arithmetic-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "group" token)
         (b* (((pok tree) (parse-keyword "group" token input)))
           (mv (abnf-tree-wrap tree
                               "group-type"
                               "arithmetic-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "scalar" token)
         (b* (((pok tree) (parse-keyword "scalar" token input)))
           (mv (abnf-tree-wrap tree
                               "scalar-type"
                               "arithmetic-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "bool" token)
         (b* (((pok tree) (parse-keyword "bool" token input)))
           (mv (abnf-tree-wrap tree
                               "boolean-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "address" token)
         (b* (((pok tree) (parse-keyword "address" token input)))
           (mv (abnf-tree-wrap tree
                               "address-type"
                               "named-primitive-type")
               token input)))
        ((token-stringp "string" token)
         (b* (((pok tree) (parse-keyword "string" token input)))
           (mv (abnf-tree-wrap tree
                               "string-type"
                               "named-primitive-type")
               token input)))
        (t (mv (reserrf (list :found (abnf::tree-option-fix token)))
               (abnf::tree-option-fix token)
               (abnf::tree-list-fix input))))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-named-primitive-type-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-named-primitive-type-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note, there is no parsing function for rule "primitive-type"
;; because it is not used by anything.  We can easily add it
;; if and when it becomes necessary or desired.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-unit-type ((token abnf::tree-optionp)
                         (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('unit-type')."
  (b* (((pok tree1) (parse-symbol "(" token input))
       ((pok tree2) (parse-symbol ")" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "unit-type")
         :branches (list (list tree1)
                         (list tree2)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-unit-type-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-unit-type-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-named-type-as-locator-?-dot-record ((token abnf::tree-optionp)
                                                  (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse the @('named-type') alternative @('locator [ \".\" %s\"record\" ]')."
  (b* (((pok tree1) (parse-locator token input))
       (token-after-loc token)
       (input-after-loc input)
       ((mv opt-tree token input)
        (b* (((pok tree2) (parse-symbol "." token-after-loc input-after-loc))
             ((pok tree3) (parse-keyword "record" token input)))
          (mv (abnf::make-tree-nonleaf :rulename? nil
                                       :branches (list (list tree2)
                                                       (list tree3)))
              token input))))
    (if (reserrp opt-tree)
        (mv (abnf::make-tree-nonleaf
             :rulename? (abnf::rulename "named-type")
             :branches (list (list tree1)
                             (list (abnf::make-tree-nonleaf :rulename? nil
                                                            :branches nil))))
            token-after-loc input-after-loc)
      (mv (abnf::make-tree-nonleaf
             :rulename? (abnf::rulename "named-type")
             :branches (list (list tree1)
                             (list opt-tree)))
            token input)))
  :hooks (:fix)
  ///

  (defret parsize-of-named-type-locator-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-named-type-locator-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-named-type-as-identifier-?-dot-record ((token abnf::tree-optionp)
                                                     (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse the @('named-type') alternative @('identifier [ \".\" %s\"record\" ]')."
  (b* (((pok tree1) (parse-identifier token input))
       (token-after-id token)
       (input-after-id input)
       ((mv opt-tree token input)
        (b* (((pok tree2) (parse-symbol "." token-after-id input-after-id))
             ((pok tree3) (parse-keyword "record" token input)))
          (mv (abnf::make-tree-nonleaf :rulename? nil
                                       :branches (list (list tree2)
                                                       (list tree3)))
              token input))))
    (if (reserrp opt-tree)
        (mv (abnf::make-tree-nonleaf
             :rulename? (abnf::rulename "named-type")
             :branches (list (list tree1)
                             (list (abnf::make-tree-nonleaf :rulename? nil
                                                            :branches nil))))
            token-after-id input-after-id)
      (mv (abnf::make-tree-nonleaf
             :rulename? (abnf::rulename "named-type")
             :branches (list (list tree1)
                             (list opt-tree)))
            token input)))
  :hooks (:fix)
  ///

  (defret parsize-of-named-type-identifier-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-named-type-identifier-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-named-type ((token abnf::tree-optionp)
                          (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('named-type')."
  (b* (((mv tree token1 input1) (parse-named-primitive-type token input))
       ((when (not (reserrp tree)))
        (mv (abnf-tree-wrap tree "named-type")
            token1 input1))
       ((mv tree token2 input2)
        (parse-named-type-as-locator-?-dot-record token input))
       ((when (not (reserrp tree)))
        (mv tree token2 input2))
       ((mv tree token3 input3)
        (parse-named-type-as-identifier-?-dot-record token input))
       ((when (not (reserrp tree)))
        (mv tree token3 input3)))
    (mv tree ; the last err result
        (abnf::tree-option-fix token)
        (abnf::tree-list-fix input)))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-named-type-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-named-type-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines parse-types

  (define parse-type ((token abnf::tree-optionp)
                      (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('type')."
    (b* (((mv tree token0 input0) (parse-unit-type token input))
         ((when (not (reserrp tree)))
          (mv (abnf-tree-wrap tree "type")
              token0 input0))
         ((mv tree token1 input1) (parse-named-type token input))
         ((when (not (reserrp tree)))
          (mv (abnf-tree-wrap tree "type")
              token1 input1))
         ((pok tree) (parse-tuple-type token input)))
      (mv (abnf-tree-wrap tree "type")
          token input))
    :measure (two-nats-measure (parsize token input) 1))

  ;; tuple-type = "(" type 1*( "," type ) [ "," ] ")"
  (define parse-tuple-type ((token abnf::tree-optionp)
                            (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('tuple-type')."
    (b* (((pok tree1) (parse-symbol "(" token input))
         ((pok< treeA) (parse-type token input))
         ((pok treesB) (parse-*-comma-type token input))
         ((unless (consp treesB))
          (mv (reserrf (list :singleton-tuple-type treeA))
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((mv tree-opt-comma token input)
          (if (token-stringp "," token) ; optional trailing comma
             (b* (((pok ctree) (parse-symbol "," token input)))
               (mv (abnf::make-tree-nonleaf
                    :rulename? nil
                    :branches (list (list ctree)))
                   token input))
           (mv (abnf::make-tree-nonleaf
                :rulename? nil
                :branches nil)
               token input)))
         ((when (reserrp tree-opt-comma))
          (mv (reserrf (list :not-possible tree-opt-comma))
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok tree-close) (parse-symbol ")" token input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "tuple-type")
           :branches (list (list tree1)
                           (list treeA)
                           treesB
                           (list tree-opt-comma)
                           (list tree-close)))
          token input))
    :measure (two-nats-measure (parsize token input) 0))

  (define parse-*-comma-type ((token abnf::tree-optionp)
                              (input abnf::tree-listp))
    :returns (mv (trees abnf::tree-list-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('*( \",\" type )')."
    (b* (((unless (token-stringp "," token))
          (mv nil
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         (start-token token)
         (start-input input)
         ((pok< tree1) (parse-symbol "," token input))
         (token1 token)
         (input1 input)
         ((mv tree2 token input) (parse-type token input)))
      (if (reserrp tree2)
          ;; if there is no type after the comma,
          ;; then this call to parse-*-comma-type should not eat the comma,
          ;; it should return just the empty list of trees.
          (mv nil
              (abnf::tree-option-fix start-token)
              (abnf::tree-list-fix start-input))
        (b* ((tree (abnf::make-tree-nonleaf :rulename? nil
                                            :branches (list (list tree1)
                                                            (list tree2))))
             ;; tree is now the part of *( "," type ) within the parentheses
             ((unless (mbt (< (parsize token input)
                              (parsize token1 input1))))
              (mv (reserrf :impossible) token1 input1))
             ((pok rest-trees) (parse-*-comma-type token input)))
          (mv (cons tree rest-trees) token input))))
    :measure (two-nats-measure (parsize token input) 0))

  :ruler-extenders :all

  :returns-hints
  (("Goal"
    :in-theory
    (e/d
     (abnf::treep-when-tree-resultp-and-not-reserrp
      abnf::tree-listp-when-tree-list-resultp-and-not-reserrp)
     (parse-type
      parse-tuple-type
      parse-*-comma-type)))
   (and
    (acl2::occur-lst '(acl2::flag-is 'parse-type) clause)
    '(:expand (parse-type token input)))
   (and
    (acl2::occur-lst '(acl2::flag-is 'parse-tuple-type) clause)
    '(:expand (parse-tuple-type token input)))
   (and
    (acl2::occur-lst '(acl2::flag-is 'parse-*-comma-type) clause)
    '(:expand (parse-*-comma-type token input))))

  :verify-guards nil ; done below

  ///

  (defret-mutual parsizeof-parse-types-<=
    (defret parsizeof-parse-type-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-type)
    (defret parsizeof-parse-tuple-type-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-tuple-type)
    (defret parsizeof-parse-*-comma-type-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-*-comma-type)
    :hints
    (("Goal" :in-theory (disable parse-type
                                 parse-tuple-type
                                 parse-*-comma-type))
     (and
      (acl2::occur-lst '(acl2::flag-is 'parse-type) clause)
      '(:expand (parse-type token input)))
     (and
      (acl2::occur-lst '(acl2::flag-is 'parse-tuple-type) clause)
      '(:expand (parse-tuple-type token input)))
     (and
      (acl2::occur-lst '(acl2::flag-is 'parse-*-comma-type) clause)
      '(:expand (parse-*-comma-type token input)))))

  (defret-mutual parsizeof-parse-types-<
    (defret parsizeof-parse-type-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-type)
    (defret parsizeof-parse-tuple-type-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-tuple-type)
    (defret parsizeof-parse-*-comma-type-<
      t
      :rule-classes nil
      :fn parse-*-comma-type)
    :hints
    (("Goal" :in-theory (disable parse-type
                                 parse-tuple-type
                                 parse-*-comma-type))
     (and
      (acl2::occur-lst '(acl2::flag-is 'parse-type) clause)
      '(:expand (parse-type token input)))
     (and
      (acl2::occur-lst '(acl2::flag-is 'parse-tuple-type) clause)
      '(:expand (parse-tuple-type token input)))
     (and
      (acl2::occur-lst '(acl2::flag-is 'parse-*-comma-type) clause)
      '(:expand (parse-*-comma-type token input)))))

  (verify-guards parse-type)

  (fty::deffixequiv-mutual parse-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-group-coordinate ((token abnf::tree-optionp)
                                (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('group-coordinate')."
  (cond ((token-stringp "+" token)
         (b* (((pok tree) (parse-symbol "+" token input)))
           (mv (abnf-tree-wrap tree "group-coordinate") token input)))
        ((token-stringp "-" token)
         (b* (((pok< tree) (parse-symbol "-" token input))
              ((when (null token)) ; the next token
               ;; Just the "-" is good enough for here (although this
               ;; condition would be an error in a full program,
               ;; it can come up when parsing just a group-coordinate).
               (mv (abnf-tree-wrap tree "group-coordinate") token input))
              ;; Try to parse a following numeral, because if the "-"
              ;; and a following token are there, there could also be a numeral.
              ;; Note that group-coordinate must be followed by
              ;; either "," or ")group", so there is no ambiguity.
              ((mv tree1 next1 input1)
               (parse-numeral token input))
              ((unless (reserrp tree1))
               (mv (abnf::make-tree-nonleaf
                    :rulename? (abnf::rulename "group-coordinate")
                    :branches  ; because of the parens in '( [ "-" ] numeral )'
                               ; we need another nonleaf for the group
                    (list (list (abnf::make-tree-nonleaf
                                 :rulename? nil
                                 :branches
                                 (list  ; The option starts another tree,
                                        ; which has the "-" in it here.
                                  (list (abnf::make-tree-nonleaf
                                         :rulename? nil
                                         :branches (list (list tree))))
                                  (list tree1))))))
                   next1 input1)))
           ;; The next token is not a numeral, so just accept the "-"
           (mv (abnf-tree-wrap tree "group-coordinate") token input)))
        ((token-stringp "_" token)
         (b* (((pok tree) (parse-symbol "_" token input)))
           (mv (abnf-tree-wrap tree "group-coordinate") token input)))
        (t (b* (((pok tree) (parse-numeral token input)))
             (mv (abnf::make-tree-nonleaf
                  :rulename? (abnf::rulename "group-coordinate")
                  :branches
                  (list (list (abnf::make-tree-nonleaf
                               :rulename? nil
                               :branches
                               (list    ; The option starts another tree,
                                        ; but it has nothing in it here.
                                (list (abnf::make-tree-nonleaf
                                       :rulename? nil
                                       :branches (list)))
                                (list tree))))))
                 token input))))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-group-coordinate-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-group-coordinate-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-affine-group-literal ((token abnf::tree-optionp)
                                    (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('affine-group-literal')."
  (b* (((pok tree1) (parse-symbol "(" token input))
       ((pok tree2) (parse-group-coordinate token input))
       ((pok tree3) (parse-symbol "," token input))
       ((pok tree4) (parse-group-coordinate token input))
       ((pok tree5) (parse-symbol ")group" token input))
       (tree (abnf::make-tree-nonleaf
              :rulename? (abnf::rulename "affine-group-literal")
              :branches (list (list tree1)
                              (list tree2)
                              (list tree3)
                              (list tree4)
                              (list tree5)))))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-affine-group-literal-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-affine-group-literal-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-literal ((token abnf::tree-optionp)
                       (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('literal')."
  (b* (((pok tree) (if (token-stringp "(" token)
                       (parse-affine-group-literal token input)
                     (parse-atomic-literal token input))))
    (mv (abnf-tree-wrap tree "literal") token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-literal-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-literal-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-variable-or-free-constant ((token abnf::tree-optionp)
                                         (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('variable-or-free-constant')."
  (b* (((pok tree) (parse-identifier token input)))
    (mv (abnf-tree-wrap tree "variable-or-free-constant")
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-variable-or-free-constant-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-variable-or-free-constant-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-associated-constant ((token abnf::tree-optionp)
                                   (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('associated-constant')."
  (b* (((pok tree1) (parse-named-type token input))
       ((pok tree2) (parse-symbol "::" token input))
       ((pok tree3) (parse-identifier token input))
       (tree (abnf::make-tree-nonleaf
                  :rulename? (abnf::rulename "associated-constant")
                  :branches (list (list tree1)
                                  (list tree2)
                                  (list tree3)))))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-associated-constant-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-associated-constant-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Currently unused, but save for later.
;; Note that this does not support an optional trailing comma.
(define parse-*-comma-natural ((token abnf::tree-optionp)
                               (input abnf::tree-listp))
  :returns (mv
            (trees
             abnf::tree-list-resultp
             :hints
             (("Goal"
               :in-theory
               (enable
                abnf::treep-when-tree-resultp-and-not-reserrp
                abnf::tree-listp-when-tree-list-resultp-and-not-reserrp))))
            (next-token abnf::tree-optionp)
            (rest-input abnf::tree-listp))
  :short "Parse a @('*( \",\" natural )')."
  (b* (((unless (token-stringp "," token))
        (mv nil
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input)))
       ((pok tree1) (parse-symbol "," token input))
       ((pok tree2) (parse-numeral token input))
       (tree (abnf::make-tree-nonleaf :rulename? nil
                                      :branches (list (list tree1)
                                                      (list tree2))))
       ((pok trees) (parse-*-comma-natural token input)))
    (mv (cons tree trees) token input))
  :measure (parsize token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-*-comma-natural-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See also parse-postfix-expression
(define parse-rest-of-struct-component-expression ((token abnf::tree-optionp)
                                                    (input abnf::tree-listp)
                                                    (current abnf::treep))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse the rest of a @('struct-component-expression')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The argument @('current') is the parsed postfix expression
       that starts the struct component expression."))
  (b* (((pok tree2) (parse-symbol "." token input))
       ((pok tree3) (parse-identifier token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "struct-component-expression")
         :branches (list (list current)
                         (list tree2)
                         (list tree3)))
        token
        input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-rest-of-struct-component-expression-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-rest-of-struct-component-expression-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See also parse-postfix-expression
(define parse-rest-of-tuple-component-expression ((token abnf::tree-optionp)
                                                  (input abnf::tree-listp)
                                                  (current abnf::treep))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse the rest of a @('tuple-component-expression')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The argument @('current') is the parsed postfix expression
       that starts the tuple component expression."))
  (b* (((pok tree2) (parse-symbol "." token input))
       ((pok tree3) (parse-numeral token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "tuple-component-expression")
         :branches (list (list current)
                         (list tree2)
                         (list tree3)))
        token
        input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-rest-of-tuple-component-expression-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-rest-of-tuple-component-expression-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-unit-expression ((token abnf::tree-optionp)
                               (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('unit-expression')."
  (b* (((pok tree1) (parse-symbol "(" token input))
       ((pok tree2) (parse-symbol ")" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "unit-expression")
         :branches (list (list tree1)
                         (list tree2)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-unit-expression-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-unit-expression-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines parse-expressions

  (define parse-expression ((token abnf::tree-optionp)
                            (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse an @('expression')."
    (b* (((pok tree) (parse-conditional-ternary-expression token input)))
      (mv (abnf-tree-wrap tree "expression") token input))
    :measure (two-nats-measure (parsize token input) 20))

  (define parse-conditional-ternary-expression ((token abnf::tree-optionp)
                                        (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('conditional-ternary-expression')."
    (b* (((pok< tree) (parse-binary-expression token input))
         ((unless (token-stringp "?" token))
          (mv (abnf-tree-wrap tree "conditional-ternary-expression")
              token
              input))
         ((pok tree2) (parse-symbol "?" token input))
         ((pok< tree3) (parse-expression token input))
         ((pok tree4) (parse-symbol ":" token input))
         ((pok tree5) (parse-expression token input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "conditional-ternary-expression")
           :branches (list (list tree)
                           (list tree2)
                           (list tree3)
                           (list tree4)
                           (list tree5)))
          token
          input))
    :measure (two-nats-measure (parsize token input) 19))

  (define parse-binary-expression  ((token abnf::tree-optionp)
                                    (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('binary-expression')."
    (b* (((pok tree) (parse-conditional-disjunctive-expression token input)))
      (mv (abnf-tree-wrap tree "binary-expression")
          token input))
    :measure (two-nats-measure (parsize token input) 18))

  (define parse-conditional-disjunctive-expression ((token abnf::tree-optionp)
                                        (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('conditional-disjunctive-expression')."
    (b* (((pok< tree) (parse-conditional-conjunctive-expression token input))
         (current (abnf-tree-wrap tree "conditional-disjunctive-expression"))
         ((pok tree) (parse-conditional-disjunctive-expression-rest token
                                                        input
                                                        current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 17))

  (define parse-conditional-disjunctive-expression-rest ((token abnf::tree-optionp)
                                             (input abnf::tree-listp)
                                             (current abnf::treep))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse the rest of a @('conditional-disjunctive-expression')."
    (b* (((when (not (token-stringp "||" token)))
          (mv (abnf::tree-fix current)
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok tree2) (parse-symbol "||" token input))
         ((pok< tree3) (parse-conditional-conjunctive-expression token input))
         (current (abnf::make-tree-nonleaf
                   :rulename? (abnf::rulename "conditional-disjunctive-expression")
                   :branches (list (list current)
                                   (list tree2)
                                   (list tree3))))
         ((pok tree) (parse-conditional-disjunctive-expression-rest token
                                                        input
                                                        current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 17))

  (define parse-conditional-conjunctive-expression ((token abnf::tree-optionp)
                                        (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('conditional-conjunctive-expression')."
    (b* (((pok< tree) (parse-equality-expression token input))
         (current (abnf-tree-wrap tree "conditional-conjunctive-expression"))
         ((pok tree) (parse-conditional-conjunctive-expression-rest token
                                                        input
                                                        current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 16))

  (define parse-conditional-conjunctive-expression-rest ((token abnf::tree-optionp)
                                             (input abnf::tree-listp)
                                             (current abnf::treep))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse the rest of a @('conditional-conjunctive-expression')."
    (b* (((when (not (token-stringp "&&" token)))
          (mv (abnf::tree-fix current)
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok tree2) (parse-symbol "&&" token input))
         ((pok< tree3) (parse-equality-expression token input))
         (current (abnf::make-tree-nonleaf
                   :rulename? (abnf::rulename "conditional-conjunctive-expression")
                   :branches (list (list current)
                                   (list tree2)
                                   (list tree3))))
         ((pok tree) (parse-conditional-conjunctive-expression-rest token
                                                        input
                                                        current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 16))

  (define parse-equality-expression ((token abnf::tree-optionp)
                                     (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse an @('equality-expression')."
    (b* (((pok< tree) (parse-ordering-expression token input)))
      (if (or (token-stringp "==" token)
              (token-stringp "!=" token))
          (b* (((pok tree2) (parse-symbol-among (list "==" "!=")
                                                token input))
               ((pok< tree3) (parse-ordering-expression token input)))
            (mv (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "equality-expression")
                 :branches (list (list tree)
                                 (list tree2)
                                 (list tree3)))
                token
                input))
        (mv (abnf-tree-wrap tree "equality-expression")
            token
            input)))
    :measure (two-nats-measure (parsize token input) 15))

  (define parse-ordering-expression ((token abnf::tree-optionp)
                                     (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse an @('ordering-expression')."
    (b* (((pok< tree) (parse-exclusive-disjunctive-expression token input)))
      (if (or (token-stringp "<" token)
              (token-stringp ">" token)
              (token-stringp "<=" token)
              (token-stringp ">=" token))
          (b* (((pok tree2) (parse-symbol-among (list "<" ">" "<=" ">=")
                                                token input))
               ((pok tree3) (parse-exclusive-disjunctive-expression token input)))
            (mv (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "ordering-expression")
                 :branches (list (list tree)
                                 (list tree2)
                                 (list tree3)))
                token
                input))
        (mv (abnf-tree-wrap tree "ordering-expression")
            token
            input)))
    :measure (two-nats-measure (parsize token input) 14))

  (define parse-exclusive-disjunctive-expression ((token abnf::tree-optionp)
                                                 (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('exclusive-disjunctive-expression')."
    (b* (((pok< tree) (parse-disjunctive-expression token input))
         (current (abnf-tree-wrap tree "exclusive-disjunctive-expression"))
         ((pok tree) (parse-exclusive-disjunctive-expression-rest token
                                                                 input
                                                                 current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 13))

  (define parse-exclusive-disjunctive-expression-rest ((token abnf::tree-optionp)
                                                      (input abnf::tree-listp)
                                                      (current abnf::treep))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse the rest of a @('exclusive-disjunctive-expression')."
    (b* (((when (not (token-stringp "^" token)))
          (mv (abnf::tree-fix current)
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok tree2) (parse-symbol "^" token input))
         ((pok< tree3) (parse-disjunctive-expression token input))
         (current (abnf::make-tree-nonleaf
                   :rulename? (abnf::rulename "exclusive-disjunctive-expression")
                   :branches (list (list current)
                                   (list tree2)
                                   (list tree3))))
         ((pok tree) (parse-exclusive-disjunctive-expression-rest token
                                                                 input
                                                                 current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 13))

  (define parse-disjunctive-expression ((token abnf::tree-optionp)
                                                 (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('disjunctive-expression')."
    (b* (((pok< tree) (parse-conjunctive-expression token input))
         (current (abnf-tree-wrap tree "disjunctive-expression"))
         ((pok tree) (parse-disjunctive-expression-rest token
                                                                 input
                                                                 current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 12))

  (define parse-disjunctive-expression-rest ((token abnf::tree-optionp)
                                                      (input abnf::tree-listp)
                                                      (current abnf::treep))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse the rest of a @('disjunctive-expression')."
    (b* (((when (not (token-stringp "|" token)))
          (mv (abnf::tree-fix current)
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok tree2) (parse-symbol "|" token input))
         ((pok< tree3) (parse-conjunctive-expression token input))
         (current (abnf::make-tree-nonleaf
                   :rulename? (abnf::rulename "disjunctive-expression")
                   :branches (list (list current)
                                   (list tree2)
                                   (list tree3))))
         ((pok tree) (parse-disjunctive-expression-rest token
                                                                 input
                                                                 current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 12))

  (define parse-conjunctive-expression ((token abnf::tree-optionp)
                                        (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('conjunctive-expression')."
    (b* (((pok< tree) (parse-shift-expression token input))
         (current (abnf-tree-wrap tree "conjunctive-expression"))
         ((pok tree) (parse-conjunctive-expression-rest token
                                                        input
                                                        current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 11))

  (define parse-conjunctive-expression-rest ((token abnf::tree-optionp)
                                             (input abnf::tree-listp)
                                             (current abnf::treep))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse the rest of a @('conjunctive-expression')."
    (b* (((when (not (token-stringp "&" token)))
          (mv (abnf::tree-fix current)
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok tree2) (parse-symbol "&" token input))
         ((pok< tree3) (parse-shift-expression token input))
         (current (abnf::make-tree-nonleaf
                   :rulename? (abnf::rulename "conjunctive-expression")
                   :branches (list (list current)
                                   (list tree2)
                                   (list tree3))))
         ((pok tree) (parse-conjunctive-expression-rest token
                                                        input
                                                        current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 11))

  (define parse-shift-expression ((token abnf::tree-optionp)
                                  (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('shift-expression')."
    (b* (((pok< tree) (parse-additive-expression token input))
         (current (abnf-tree-wrap tree "shift-expression"))
         ((pok tree) (parse-shift-expression-rest token
                                                  input
                                                  current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 10))

  (define parse-shift-expression-rest ((token abnf::tree-optionp)
                                       (input abnf::tree-listp)
                                       (current abnf::treep))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse the rest of a @('shift-expression')."
    (b* (((when (and (not (token-stringp "<<" token))
                     (not (token-stringp ">>" token))))
          (mv (abnf::tree-fix current)
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok tree2) (parse-symbol-among (list "<<" ">>") token input))
         ((pok< tree3) (parse-additive-expression token input))
         (current (abnf::make-tree-nonleaf
                   :rulename? (abnf::rulename "shift-expression")
                   :branches (list (list current)
                                   (list tree2)
                                   (list tree3))))
         ((pok tree) (parse-shift-expression-rest token
                                                  input
                                                  current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 10))

  (define parse-additive-expression ((token abnf::tree-optionp)
                                     (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse an @('additive-expression')."
    (b* (((pok< tree) (parse-multiplicative-expression token input))
         (current (abnf-tree-wrap tree "additive-expression"))
         ((pok tree) (parse-additive-expression-rest token
                                                     input
                                                     current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 9))

  (define parse-additive-expression-rest ((token abnf::tree-optionp)
                                          (input abnf::tree-listp)
                                          (current abnf::treep))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse the rest of an @('additive-expression')."
    (b* (((when (and (not (token-stringp "+" token))
                     (not (token-stringp "-" token))))
          (mv (abnf::tree-fix current)
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok tree2) (parse-symbol-among (list "+" "-") token input))
         ((pok< tree3) (parse-multiplicative-expression token input))
         (current (abnf::make-tree-nonleaf
                   :rulename? (abnf::rulename "additive-expression")
                   :branches (list (list current)
                                   (list tree2)
                                   (list tree3))))
         ((pok tree) (parse-additive-expression-rest token
                                                     input
                                                     current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 9))

  (define parse-multiplicative-expression ((token abnf::tree-optionp)
                                           (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('multiplicative-expression')."
    (b* (((pok< tree) (parse-exponential-expression token input))
         (current (abnf-tree-wrap tree "multiplicative-expression"))
         ((pok tree) (parse-multiplicative-expression-rest token
                                                           input
                                                           current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 8))

  (define parse-multiplicative-expression-rest ((token abnf::tree-optionp)
                                                (input abnf::tree-listp)
                                                (current abnf::treep))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse the rest of a @('multiplicative-expression')."
    (b* (((when (and (not (token-stringp "*" token))
                     (not (token-stringp "/" token))
                     (not (token-stringp "%" token))))
          (mv (abnf::tree-fix current)
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok tree2) (parse-symbol-among (list "*" "/" "%") token input))
         ((pok< tree3) (parse-exponential-expression token input))
         (current (abnf::make-tree-nonleaf
                   :rulename? (abnf::rulename "multiplicative-expression")
                   :branches (list (list current)
                                   (list tree2)
                                   (list tree3))))
         ((pok tree) (parse-multiplicative-expression-rest token
                                                           input
                                                           current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 8))

  (define parse-exponential-expression ((token abnf::tree-optionp)
                                        (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parsen an @('exponential-expression')."
    (b* (((pok< tree) (parse-unary-expression token input)))
      (if (token-stringp "**" token)
          (b* (((pok tree2) (parse-symbol "**" token input))
               ((pok tree3) (parse-exponential-expression token
                                                          input)))
            (mv (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "exponential-expression")
                 :branches (list (list tree)
                                 (list tree2)
                                 (list tree3)))
                token
                input))
        (mv (abnf-tree-wrap tree "exponential-expression")
            token
            input)))
    :measure (two-nats-measure (parsize token input) 7))

  (define parse-unary-expression ((token abnf::tree-optionp)
                                  (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('unary-expression')."
    (if (or (token-stringp "!" token)
            (token-stringp "-" token))
        (b* (((pok tree1) (parse-symbol-among (list "!" "-")
                                              token input))
             ((pok tree2) (parse-unary-expression token input)))
          (mv (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "unary-expression")
               :branches (list (list tree1)
                               (list tree2)))
              token
              input))
      (b* (((pok tree) (parse-postfix-expression token input)))
        (mv (abnf-tree-wrap tree "unary-expression")
            token
            input)))
    :measure (two-nats-measure (parsize token input) 6))

  (define parse-postfix-expression ((token abnf::tree-optionp)
                                    (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('postfix-expression')."
    :long
    (xdoc::topstring
     (xdoc::p
      "A postfix expression is either a primary expression
       or something (@('struct-component-expression') or @('operator-call'))
       that has a postfix expression followed by a dot (@('.')) and an
       identifier and in the case of @('operator-call'), a parenthesized list
       of arguments.")
     (xdoc::p
      "We first try to parse a primary expression.  If there is no
       primary expression here, there cannot be a postfix expression,
       since every postfix expression bottoms out in a primary expression
       on the left.")
     (xdoc::p
      "After finding a primary expression, we wrap it with
       a postfix expression layer and pass it to
       @(see parse-postfix-expression-rest), which looks for
       dot and indentifier recursively."))
    (b* (((pok< tree) (parse-primary-expression token input))
         (current (abnf-tree-wrap tree "postfix-expression"))
         ((pok tree) (parse-postfix-expression-rest token
                                                    input
                                                    current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 5))

  (define parse-postfix-expression-rest ((token abnf::tree-optionp)
                                         (input abnf::tree-listp)
                                         (current abnf::treep))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse the rest of a @('postfix-expression')."
    :long
    (xdoc::topstring
     (xdoc::p
      "The argument @('current') is the postfix expression
       that starts this postfix expression.
       If this function is called from @('parse-postfix-expression'),
       @('current') is a prefix expression wrapped with a postfix expression;
       if this function was called from itself,
       @('current') is an @('operator-call') or a @('tuple-component-expression')
       or a @('struct-component-expression'),
       wrapped with a postfix expression.")
     (xdoc::p
      "We then attempt to parse the rest of an
       @('operator-call') or @('tuple-component-expression')
       or @('struct-component-expression') here.
       If successful, we wrap it and call this function recursively.
       Otherwise we just return @('current')."))
    (b* (((mv opcall token1 input1) (parse-rest-of-operator-call token
                                                                 input
                                                                 current))
         ((when (not (reserrp opcall)))
          (b* (((unless (mbt (< (parsize token1 input1)
                                (parsize token input))))
                (mv (reserrf :impossible) token1 input1)))
            (parse-postfix-expression-rest token1
                                           input1
                                           (abnf-tree-wrap opcall
                                                           "postfix-expression"))))
         ((mv tc-expr token1 input1) (parse-rest-of-tuple-component-expression
                                      token
                                      input
                                      current))
         ((when (not (reserrp tc-expr)))
          (b* (((unless (mbt (< (parsize token1 input1)
                                (parsize token input))))
                (mv (reserrf :impossible) token1 input1)))
            (parse-postfix-expression-rest token1
                                           input1
                                           (abnf-tree-wrap tc-expr
                                                           "postfix-expression"))))
         ((mv cc-expr token1 input1) (parse-rest-of-struct-component-expression
                                      token
                                      input
                                      current))
         ((when (not (reserrp cc-expr)))
          (parse-postfix-expression-rest token1
                                         input1
                                         (abnf-tree-wrap cc-expr
                                                         "postfix-expression"))))
      (mv (abnf::tree-fix current)
          (abnf::tree-option-fix token)
          (abnf::tree-list-fix input)))
    :measure (two-nats-measure (parsize token input) 4))

  (define parse-rest-of-operator-call ((token abnf::tree-optionp)
                                       (input abnf::tree-listp)
                                       (current abnf::treep))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse the rest of an @('operator-call')."
    :long
    (xdoc::topstring
     (xdoc::p
      "The argument @('current') is the parsed postfix expression
       that starts the operator call.
       If there is no operator call here, returns a reserrp."))
    (b* (((pok tree2) (parse-symbol "." token input))
         ((pok tree3) (parse-identifier token input))
         ((pok tree4) (parse-symbol "(" token input)))
      (if (token-stringp ")" token)
          ;; a unary-operator-call
          (b* (((pok tree5) (parse-symbol ")" token input))
               (opcall-tree (abnf::make-tree-nonleaf
                             :rulename? (abnf::rulename "unary-operator-call")
                             :branches (list (list current)
                                             (list tree2)
                                             (list tree3)
                                             (list tree4)
                                             (list tree5)))))
            (mv (abnf-tree-wrap opcall-tree
                                "operator-call")
                token
                input))
        ;; a binary-operator-call
        (b* (((pok tree5) (parse-expression token input))
             ;; Now there could be an optional comma
             ((mv ctree-or-err ctoken cinput) (parse-symbol "," token input))
             ;; An omitted optional thing still requires a nonleaf tree
             ;; Set ctree, token, and input accordingly.
             (ctree (if (reserrp ctree-or-err)
                        ;; omitted optional comma:
                        (abnf::make-tree-nonleaf :rulename? nil :branches nil)
                      ;; present optional comma:
                      (abnf::make-tree-nonleaf
                       :rulename? nil
                       :branches (list (list ctree-or-err)))))
             (token (if (reserrp ctree-or-err)
                        token
                      ctoken))
             (input (if (reserrp ctree-or-err)
                        input
                      cinput))
             ((pok tree6) (parse-symbol ")" token input))
             (opcall-tree (abnf::make-tree-nonleaf
                           :rulename? (abnf::rulename "binary-operator-call")
                           :branches (list (list current)
                                           (list tree2)   ; "."
                                           (list tree3)   ; identifier
                                           (list tree4)   ; "("
                                           (list tree5)   ; expression
                                           (list ctree)   ; [","]
                                           (list tree6))))) ; ")"
          (mv (abnf-tree-wrap opcall-tree
                              "operator-call")
              token
              input))))
    :measure (two-nats-measure (parsize token input) 3))

  (define parse-primary-expression ((token abnf::tree-optionp)
                                    (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('primary-expression')."
    :long
    (xdoc::topstring
     (xdoc::p
      "A primary expression can start with the keyword @('\"(\"'),
      in which case it can be either a unit expression,
      a parenthesized expression or an affine group literal.
      Since the unit expression is most restricted, it is tried first.
      The group literal is more restricted than a parenthesized expression,
      and ends with @('\")group\"'), so we try to parse literals before
      trying parenthesized expressions.")
     (xdoc::p
      "There are quite a few kinds of primary expressions that can start with
       an identifier.  A variable reference is just a plain identifier.
       Free function calls start with an identifier but are followed by
       @('function-arguments'), so they must be tried before variable
       references.
       Associated constants and static function calls start with a
       named type, which can be a primitive type or an identifier, which is
       then followed by @('\"::\"').
       Static function calls start with the same syntax as associated constants
       but are followed by function arguments, so they must be tried before
       assocated constants."))
    (cond
     ((token-stringp "(" token)
      (b* (((mv tree token1 input1) (parse-unit-expression token input))
           ((when (not (reserrp tree)))
            (mv (abnf-tree-wrap tree
                                "primary-expression")
                token1 input1))
           ((mv tree token1 input1) (parse-literal token input))
           ((when (not (reserrp tree)))
            ;; The only literal that can start with "(" here should be
            ;; an affine group literal.
            ;; Wrap the literal/affine-group-literal with a primary-expression
            (mv (abnf-tree-wrap tree
                                "primary-expression")
                token1 input1))
           ;; 2nd thing that can start with "(" is tuple expression,
           ;; which has zero or two or more components.
           ((mv tree token1 input1) (parse-tuple-expression token input))
           ((when (not (reserrp tree)))
            (mv (abnf-tree-wrap tree
                                "primary-expression")
                token1 input1))
           ;; The 3rd and last thing that can start with "(" is a parenthesized
           ;; expression.
           ((pok tree1) (parse-symbol "(" token input))
           ((pok tree2) (parse-expression token input))
           ((pok tree3) (parse-symbol ")" token input))
           (tree (abnf::make-tree-nonleaf
                  :rulename? (abnf::rulename "primary-expression")
                  :branches (list (list tree1)
                                  (list tree2)
                                  (list tree3)))))
        (mv tree token input)))
     ((token-rootp "atomic-literal" token)
      (b* (((pok tree) (parse-atomic-literal token input)))
        (mv (abnf-tree-wrap tree
                            "literal"
                            "primary-expression")
            token input)))
     (t
      (b* (((mv tree token1 input1) (parse-struct-expression token input))
           ((when (not (reserrp tree)))
            (mv (abnf-tree-wrap tree
                                "primary-expression")
                token1 input1))
           ((mv tree token1 input1) (parse-static-function-call token input))
           ((when (not (reserrp tree)))
            (mv (abnf-tree-wrap tree
                                "primary-expression")
                token1 input1))
           ((mv tree token1 input1) (parse-associated-constant token input))
           ((when (not (reserrp tree)))
            (mv (abnf-tree-wrap tree
                                "primary-expression")
                token1 input1))
           ((mv tree token1 input1) (parse-free-function-call token input))
           ((when (not (reserrp tree)))
            (mv (abnf-tree-wrap tree
                                "primary-expression")
                token1 input1))
           ((pok tree) (parse-variable-or-free-constant token input)))
        (mv (abnf-tree-wrap tree
                            "primary-expression")
            token input))))
    :measure (two-nats-measure (parsize token input) 2))

  ;; tuple-expression = "(" expression 1*( "," expression ) [ "," ] ")"
  (define parse-tuple-expression ((token abnf::tree-optionp)
                                  (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('tuple-expression')."
    (b* (((pok tree1) (parse-symbol "(" token input))
         ((pok< treeA) (parse-expression token input))
         ((pok treesB) (parse-*-comma-expression token input))
         ((unless (consp treesB))
          (mv (reserrf (list :singleton-tuple-expression treeA))
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((mv tree-opt-comma token input)
          (if (token-stringp "," token) ; optional trailing comma
              (b* (((pok ctree) (parse-symbol "," token input)))
                (mv (abnf::make-tree-nonleaf
                     :rulename? nil
                     :branches (list (list ctree)))
                    token input))
            (mv (abnf::make-tree-nonleaf
                 :rulename? nil
                 :branches nil)
                token input)))
         ((when (reserrp tree-opt-comma))
          (mv (reserrf (list :not-possible tree-opt-comma))
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok tree-close) (parse-symbol ")" token input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "tuple-expression")
           :branches (list (list tree1)
                           (list treeA)
                           treesB
                           (list tree-opt-comma)
                           (list tree-close)))
          token input))
    :measure (two-nats-measure (parsize token input) 1))

    (define parse-struct-expression ((token abnf::tree-optionp)
                                    (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('struct-expression')."
    (b* (((pok tree1) (parse-identifier token input))
         ((pok< tree2) (parse-symbol "{" token input))
         ((pok< tree3) (parse-struct-component-initializer token input))
         ((pok trees4) (parse-*-comma-struct-component-initializer token input))
         ((pok tree5) (parse-?-comma token input))
         ((pok< tree6) (parse-symbol "}" token input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "struct-expression")
           :branches (list (list tree1)
                           (list tree2)
                           (list tree3)
                           trees4
                           (list tree5)
                           (list tree6)))
          token input))
    :measure (two-nats-measure (parsize token input) 1))

  (define parse-struct-component-initializer ((token abnf::tree-optionp)
                                               (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('struct-component-initializer')."
    (b* (((pok< tree1) (parse-identifier token input)))
      (if (token-stringp ":" token)
          (b* (((pok tree2) (parse-symbol ":" token input))
               ((pok tree3) (parse-expression token input)))
            (mv (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "struct-component-initializer")
                 :branches (list (list tree1)
                                 (list tree2)
                                 (list tree3)))
                token input))
        (mv (abnf::make-tree-nonleaf
             :rulename? (abnf::rulename "struct-component-initializer")
             :branches (list (list tree1)))
            token input)))
    :measure (two-nats-measure (parsize token input) 0))

  (define parse-*-comma-struct-component-initializer  ((token abnf::tree-optionp)
                                                        (input abnf::tree-listp))
    :returns (mv (trees abnf::tree-list-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('*( \",\" struct-component-initializer )')."
    (b* (((unless (token-stringp "," token))
          (mv nil
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         (start-token token)
         (start-input input)
         ((pok< tree1) (parse-symbol "," token input))
         (token1 token)
         (input1 input)
         ((mv tree2 token input)
          (parse-struct-component-initializer token input)))
      (if (reserrp tree2)
          ;; if there is no struct-component-initializer after the comma,
          ;; then this call to parse-*-comma-type should not eat the comma,
          ;; it should return just the empty list of trees.
          (mv nil
              (abnf::tree-option-fix start-token)
              (abnf::tree-list-fix start-input))
        (b* ((tree (abnf::make-tree-nonleaf :rulename? nil
                                            :branches (list (list tree1)
                                                            (list tree2))))
             ;; tree is now the part of *( "," struct-component-initializer )
             ;; within the parentheses.
             ((unless (mbt (< (parsize token input)
                              (parsize token1 input1))))
              (mv (reserrf :impossible) token1 input1))
             ((pok rest-trees) (parse-*-comma-struct-component-initializer
                                token
                                input)))
          (mv (cons tree rest-trees)
              token
              input))))
    :measure (two-nats-measure (parsize token input) 0))

  (define parse-static-function-call ((token abnf::tree-optionp)
                                      (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('static-function-call')."
    (b* (((pok tree1) (parse-named-type token input))
         ((pok tree2) (parse-symbol "::" token input))
         ((pok tree3) (parse-identifier token input))
         ((pok tree4) (parse-function-arguments token input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "static-function-call")
           :branches (list (list tree1)
                           (list tree2)
                           (list tree3)
                           (list tree4)))
          token input))
    :measure (two-nats-measure (parsize token input) 1))

  (define parse-free-function-call ((token abnf::tree-optionp)
                                    (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('free-function-call')."
    (b* (((mv tree1 token-after-tree1 input-after-tree1)
          (b* (((mv tree-locator token-after-locator input-after-locator)
                (parse-locator token input))
               ((when (not (reserrp tree-locator)))
                (mv tree-locator token-after-locator input-after-locator)))
            (parse-identifier token input)))
         ((when (reserrp tree1))
          (mv tree1
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok tree2) (parse-function-arguments token-after-tree1 input-after-tree1)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "free-function-call")
           :branches (list (list tree1)
                           (list tree2)))
          token input))
    :measure (two-nats-measure (parsize token input) 1))

  (define parse-function-arguments ((token abnf::tree-optionp)
                                    (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('function-arguments')."
    (b* (((pok tree1) (parse-symbol "(" token input))
         ((pok tree2)
          (if (token-stringp ")" token)
              (mv (abnf::make-tree-nonleaf
                   :rulename? nil
                   :branches nil)
                  token input)
            (b* (((pok< tree) (parse-expression token input))
                 ((pok trees) (parse-*-comma-expression token input)))
              (if (token-stringp "," token) ; optional trailing comma
                  (b* (((pok ctree) (parse-symbol "," token input)))
                    (mv (abnf::make-tree-nonleaf
                         :rulename? nil
                         :branches (list (list tree)
                                         trees
                                         (list (abnf::make-tree-nonleaf
                                                :rulename? nil
                                                :branches (list (list ctree))))))
                        token input))
                (mv (abnf::make-tree-nonleaf
                     :rulename? nil
                     :branches (list (list tree)
                                     trees
                                     ;; omitted optional comma:
                                     (list (abnf::make-tree-nonleaf
                                            :rulename? nil
                                            :branches nil))))
                    token input)))))
         ((pok tree3) (parse-symbol ")" token input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "function-arguments")
           :branches (list (list tree1)
                           (list tree2)
                           (list tree3)))
          token input))
    :measure (two-nats-measure (parsize token input) 0))

  (define parse-*-comma-expression ((token abnf::tree-optionp)
                                    (input abnf::tree-listp))
    :returns (mv (trees abnf::tree-list-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('*( \",\" expression )')."
    (b* (((unless (token-stringp "," token))
          (mv nil
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         (start-token token)
         (start-input input)
         ((pok< tree1) (parse-symbol "," token input))
         (token1 token)
         (input1 input)
         ((mv tree2 token input) (parse-expression token input)))
      (if (reserrp tree2)
          ;; if there is no expression after the comma,
          ;; then this call should not eat the comma,
          ;; and it should return the empty list of trees.
          (mv nil
              (abnf::tree-option-fix start-token)
              (abnf::tree-list-fix start-input))
        (b* ((tree (abnf::make-tree-nonleaf :rulename? nil
                                            :branches (list (list tree1)
                                                            (list tree2))))
             ;; similar to pok< for the tree2 above
             ((unless (mbt (< (parsize token input)
                              (parsize token1 input1))))
              (mv (reserrf :impossible) token1 input1))
             ((pok trees) (parse-*-comma-expression token input)))
          (mv (cons tree trees) token input))))
    :measure (two-nats-measure (parsize token input) 0))

  :prepwork
  ((defun parse-expressions-expand-hints (id clause world)
     (declare (ignore id world))
     (cond
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-expression) clause)
       '(:expand
         (parse-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-conditional-ternary-expression) clause)
       '(:expand
         (parse-conditional-ternary-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-binary-expression) clause)
       '(:expand (parse-binary-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-conditional-disjunctive-expression) clause)
       '(:expand (parse-conditional-disjunctive-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-conditional-disjunctive-expression-rest) clause)
       '(:expand
         (parse-conditional-disjunctive-expression-rest token input current)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-conditional-conjunctive-expression) clause)
       '(:expand
         (parse-conditional-conjunctive-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-conditional-conjunctive-expression-rest) clause)
       '(:expand
         (parse-conditional-conjunctive-expression-rest token input current)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-equality-expression) clause)
       '(:expand
         (parse-equality-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-ordering-expression) clause)
       '(:expand
         (parse-ordering-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-exclusive-disjunctive-expression) clause)
       '(:expand
         (parse-exclusive-disjunctive-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-exclusive-disjunctive-expression-rest) clause)
       '(:expand
         (parse-exclusive-disjunctive-expression-rest token input current)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-disjunctive-expression) clause)
       '(:expand
         (parse-disjunctive-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-disjunctive-expression-rest) clause)
       '(:expand
         (parse-disjunctive-expression-rest token input current)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-conjunctive-expression) clause)
       '(:expand
         (parse-conjunctive-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-conjunctive-expression-rest) clause)
       '(:expand
         (parse-conjunctive-expression-rest token input current)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-shift-expression) clause)
       '(:expand
         (parse-shift-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-shift-expression-rest) clause)
       '(:expand
         (parse-shift-expression-rest token input current)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-additive-expression) clause)
       '(:expand
         (parse-additive-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-additive-expression-rest) clause)
       '(:expand
         (parse-additive-expression-rest token input current)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-multiplicative-expression) clause)
       '(:expand
         (parse-multiplicative-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-multiplicative-expression-rest) clause)
       '(:expand
         (parse-multiplicative-expression-rest token input current)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-exponential-expression) clause)
       '(:expand
         (parse-exponential-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-unary-expression) clause)
       '(:expand
         (parse-unary-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-postfix-expression) clause)
       '(:expand
         (parse-postfix-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-postfix-expression-rest) clause)
       '(:expand
         (parse-postfix-expression-rest token input current)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-rest-of-operator-call) clause)
       '(:expand
         (parse-rest-of-operator-call token input current)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-primary-expression) clause)
       '(:expand
         (parse-primary-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-tuple-expression) clause)
       '(:expand
         (parse-tuple-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-struct-expression) clause)
       '(:expand
         (parse-struct-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-struct-component-initializer) clause)
       '(:expand
         (parse-struct-component-initializer token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-*-comma-struct-component-initializer) clause)
       '(:expand
         (parse-*-comma-struct-component-initializer token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-static-function-call) clause)
       '(:expand
         (parse-static-function-call token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-free-function-call) clause)
       '(:expand
         (parse-free-function-call token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-function-arguments) clause)
       '(:expand
         (parse-function-arguments token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-*-comma-expression) clause)
       '(:expand
         (parse-*-comma-expression token input))))))

  :ruler-extenders :all

  :verify-guards nil ; done below

  :returns-hints
  (("Goal"
    :in-theory
    (e/d (abnf::treep-when-tree-resultp-and-not-reserrp
          abnf::tree-listp-when-tree-list-resultp-and-not-reserrp)
         (parse-expression
          parse-conditional-ternary-expression
          parse-binary-expression
          parse-conditional-disjunctive-expression
          parse-conditional-disjunctive-expression-rest
          parse-conditional-conjunctive-expression
          parse-conditional-conjunctive-expression-rest
          parse-equality-expression
          parse-ordering-expression
          parse-exclusive-disjunctive-expression
          parse-exclusive-disjunctive-expression-rest
          parse-disjunctive-expression
          parse-disjunctive-expression-rest
          parse-conjunctive-expression
          parse-conjunctive-expression-rest
          parse-shift-expression
          parse-shift-expression-rest
          parse-additive-expression
          parse-additive-expression-rest
          parse-multiplicative-expression
          parse-multiplicative-expression-rest
          parse-exponential-expression
          parse-unary-expression
          parse-postfix-expression
          parse-postfix-expression-rest
          parse-rest-of-operator-call
          parse-primary-expression
          parse-tuple-expression
          parse-struct-expression
          parse-struct-component-initializer
          parse-*-comma-struct-component-initializer
          parse-static-function-call
          parse-free-function-call
          parse-function-arguments
          parse-*-comma-expression)))
   parse-expressions-expand-hints)

  ///

  (defret-mutual parsize-of-parse-expressions-<=
    (defret parsize-of-parse-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-expression)
    (defret parsize-of-parse-conditional-ternary-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-conditional-ternary-expression)
    (defret parsize-of-parse-binary-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-binary-expression)
    (defret parsize-of-parse-conditional-disjunctive-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-conditional-disjunctive-expression)
    (defret parsize-of-parse-conditional-disjunctive-expression-rest-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-conditional-disjunctive-expression-rest)
    (defret parsize-of-parse-conditional-conjunctive-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-conditional-conjunctive-expression)
    (defret parsize-of-parse-conditional-conjunctive-expression-rest-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-conditional-conjunctive-expression-rest)
    (defret parsize-of-parse-equality-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-equality-expression)
    (defret parsize-of-parse-ordering-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-ordering-expression)
    (defret parsize-of-parse-exclusive-disjunctive-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-exclusive-disjunctive-expression)
    (defret parsize-of-parse-exclusive-disjunctive-expression-rest-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-exclusive-disjunctive-expression-rest)
    (defret parsize-of-parse-disjunctive-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-disjunctive-expression)
    (defret parsize-of-parse-disjunctive-expression-rest-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-disjunctive-expression-rest)
    (defret parsize-of-parse-conjunctive-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-conjunctive-expression)
    (defret parsize-of-parse-conjunctive-expression-rest-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-conjunctive-expression-rest)
    (defret parsize-of-parse-shift-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-shift-expression)
    (defret parsize-of-parse-shift-expression-rest-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-shift-expression-rest)
    (defret parsize-of-parse-additive-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-additive-expression)
    (defret parsize-of-parse-additive-expression-rest-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-additive-expression-rest)
    (defret parsize-of-parse-multiplicative-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-multiplicative-expression)
    (defret parsize-of-parse-multiplicative-expression-rest-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-multiplicative-expression-rest)
    (defret parsize-of-parse-exponential-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-exponential-expression)
    (defret parsize-of-parse-unary-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-unary-expression)
    (defret parsize-of-parse-postfix-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-postfix-expression)
    (defret parsize-of-parse-postfix-expression-rest-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-postfix-expression-rest)
    (defret parsize-of-parse-rest-of-operator-call-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-rest-of-operator-call)
    (defret parsize-of-parse-primary-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-primary-expression)
    (defret parsize-of-parse-tuple-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-tuple-expression)
    (defret parsize-of-parse-struct-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-struct-expression)
    (defret parsize-of-parse-struct-component-initializer-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-struct-component-initializer)
    (defret parsize-of-parse-*-comma-struct-component-initializer-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-*-comma-struct-component-initializer)
    (defret parsize-of-parse-static-function-call-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-static-function-call)
    (defret parsize-of-parse-free-function-call-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-free-function-call)
    (defret parsize-of-parse-function-arguments-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-function-arguments)
    (defret parsize-of-parse-*-comma-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-*-comma-expression)
    :hints
    (("Goal" :in-theory (disable parse-expression
                                 parse-conditional-ternary-expression
                                 parse-binary-expression
                                 parse-conditional-disjunctive-expression
                                 parse-conditional-disjunctive-expression-rest
                                 parse-conditional-conjunctive-expression
                                 parse-conditional-conjunctive-expression-rest
                                 parse-equality-expression
                                 parse-ordering-expression
                                 parse-exclusive-disjunctive-expression
                                 parse-exclusive-disjunctive-expression-rest
                                 parse-disjunctive-expression
                                 parse-disjunctive-expression-rest
                                 parse-conjunctive-expression
                                 parse-conjunctive-expression-rest
                                 parse-shift-expression
                                 parse-shift-expression-rest
                                 parse-additive-expression
                                 parse-additive-expression-rest
                                 parse-multiplicative-expression
                                 parse-multiplicative-expression-rest
                                 parse-exponential-expression
                                 parse-unary-expression
                                 parse-postfix-expression
                                 parse-postfix-expression-rest
                                 parse-rest-of-operator-call
                                 parse-primary-expression
                                 parse-tuple-expression
                                 parse-struct-expression
                                 parse-struct-component-initializer
                                 parse-*-comma-struct-component-initializer
                                 parse-static-function-call
                                 parse-free-function-call
                                 parse-function-arguments
                                 parse-*-comma-expression))
     parse-expressions-expand-hints))

  (defret-mutual parsize-of-parse-expressions-<
    (defret parsize-of-parse-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-expression)
    (defret parsize-of-parse-conditional-ternary-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-conditional-ternary-expression)
    (defret parsize-of-parse-binary-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-binary-expression)
    (defret parsize-of-parse-conditional-disjunctive-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-conditional-disjunctive-expression)
    (defret parsize-of-parse-conditional-disjunctive-expression-rest-<
      t
      :rule-classes nil
      :fn parse-conditional-disjunctive-expression-rest)
    (defret parsize-of-parse-conditional-conjunctive-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-conditional-conjunctive-expression)
    (defret parsize-of-parse-conditional-conjunctive-expression-rest-<
      t
      :rule-classes nil
      :fn parse-conditional-conjunctive-expression-rest)
    (defret parsize-of-parse-equality-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-equality-expression)
    (defret parsize-of-parse-ordering-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-ordering-expression)
    (defret parsize-of-parse-exclusive-disjunctive-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-exclusive-disjunctive-expression)
    (defret parsize-of-parse-exclusive-disjunctive-expression-rest-<
      t
      :rule-classes nil
      :fn parse-exclusive-disjunctive-expression-rest)
    (defret parsize-of-parse-disjunctive-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-disjunctive-expression)
    (defret parsize-of-parse-disjunctive-expression-rest-<
      t
      :rule-classes nil
      :fn parse-disjunctive-expression-rest)
    (defret parsize-of-parse-conjunctive-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-conjunctive-expression)
    (defret parsize-of-parse-conjunctive-expression-rest-<
      t
      :rule-classes nil
      :fn parse-conjunctive-expression-rest)
    (defret parsize-of-parse-shift-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-shift-expression)
    (defret parsize-of-parse-shift-expression-rest-<
      t
      :rule-classes nil
      :fn parse-shift-expression-rest)
    (defret parsize-of-parse-additive-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-additive-expression)
    (defret parsize-of-parse-additive-expression-rest-<
      t
      :rule-classes nil
      :fn parse-additive-expression-rest)
    (defret parsize-of-parse-multiplicative-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-multiplicative-expression)
    (defret parsize-of-parse-multiplicative-expression-rest-<
      t
      :rule-classes nil
      :fn parse-multiplicative-expression-rest)
    (defret parsize-of-parse-exponential-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-exponential-expression)
    (defret parsize-of-parse-unary-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-unary-expression)
    (defret parsize-of-parse-postfix-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-postfix-expression)
    (defret parsize-of-parse-postfix-expression-rest-<
      t
      :rule-classes nil
      :fn parse-postfix-expression-rest)
    (defret parsize-of-parse-rest-of-operator-call-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-rest-of-operator-call)
    (defret parsize-of-parse-primary-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-primary-expression)
    (defret parsize-of-parse-tuple-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-tuple-expression)
    (defret parsize-of-parse-struct-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-struct-expression)
    (defret parsize-of-parse-struct-component-initializer-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-struct-component-initializer)
    (defret parsize-of-parse-*-comma-struct-component-initializer-<
      t
      :rule-classes nil
      :fn parse-*-comma-struct-component-initializer)
    (defret parsize-of-parse-static-function-call-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-static-function-call)
    (defret parsize-of-parse-free-function-call-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-free-function-call)
    (defret parsize-of-parse-function-arguments-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-function-arguments)
    (defret parsize-of-parse-*-comma-expression-<
      t
      :rule-classes nil
      :fn parse-*-comma-expression)
    :hints
    (("Goal" :in-theory (disable parse-expression
                                 parse-conditional-ternary-expression
                                 parse-binary-expression
                                 parse-conditional-disjunctive-expression
                                 parse-conditional-disjunctive-expression-rest
                                 parse-conditional-conjunctive-expression
                                 parse-conditional-conjunctive-expression-rest
                                 parse-equality-expression
                                 parse-ordering-expression
                                 parse-exclusive-disjunctive-expression
                                 parse-exclusive-disjunctive-expression-rest
                                 parse-disjunctive-expression
                                 parse-disjunctive-expression-rest
                                 parse-conjunctive-expression
                                 parse-conjunctive-expression-rest
                                 parse-shift-expression
                                 parse-shift-expression-rest
                                 parse-additive-expression
                                 parse-additive-expression-rest
                                 parse-multiplicative-expression
                                 parse-multiplicative-expression-rest
                                 parse-exponential-expression
                                 parse-unary-expression
                                 parse-postfix-expression
                                 parse-postfix-expression-rest
                                 parse-rest-of-operator-call
                                 parse-primary-expression
                                 parse-tuple-expression
                                 parse-struct-expression
                                 parse-struct-component-initializer
                                 parse-*-comma-struct-component-initializer
                                 parse-static-function-call
                                 parse-free-function-call
                                 parse-function-arguments
                                 parse-*-comma-expression))
     parse-expressions-expand-hints))

  (verify-guards parse-expression
    :hints
    (("Goal" :in-theory (disable parse-expression
                                 parse-conditional-ternary-expression
                                 parse-binary-expression
                                 parse-conditional-disjunctive-expression
                                 parse-conditional-disjunctive-expression-rest
                                 parse-conditional-conjunctive-expression
                                 parse-conditional-conjunctive-expression-rest
                                 parse-equality-expression
                                 parse-ordering-expression
                                 parse-exclusive-disjunctive-expression
                                 parse-exclusive-disjunctive-expression-rest
                                 parse-disjunctive-expression
                                 parse-disjunctive-expression-rest
                                 parse-conjunctive-expression
                                 parse-conjunctive-expression-rest
                                 parse-shift-expression
                                 parse-shift-expression-rest
                                 parse-additive-expression
                                 parse-additive-expression-rest
                                 parse-multiplicative-expression
                                 parse-multiplicative-expression-rest
                                 parse-exponential-expression
                                 parse-unary-expression
                                 parse-postfix-expression
                                 parse-postfix-expression-rest
                                 parse-rest-of-operator-call
                                 parse-primary-expression
                                 parse-tuple-expression
                                 parse-struct-expression
                                 parse-struct-component-initializer
                                 parse-*-comma-struct-component-initializer
                                 parse-static-function-call
                                 parse-free-function-call
                                 parse-function-arguments
                                 parse-*-comma-expression))))
  (fty::deffixequiv-mutual parse-expressions)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-constant-declaration ((token abnf::tree-optionp)
                                    (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('constant-declaration')."
  (b* (((pok tree1) (parse-keyword "const" token input))
       ((pok tree2) (parse-identifier token input))
       ((pok tree3) (parse-symbol ":" token input))
       ((pok tree4) (parse-type token input))
       ((pok tree5) (parse-symbol "=" token input))
       ((pok tree6) (parse-expression token input))
       ((pok tree7) (parse-symbol ";" token input))
       (tree (abnf::make-tree-nonleaf
              :rulename? (abnf::rulename "constant-declaration")
              :branches (list (list tree1)
                              (list tree2)
                              (list tree3)
                              (list tree4)
                              (list tree5)
                              (list tree6)
                              (list tree7)))))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-constant-declaration-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-constant-declaration-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-variable-declaration ((token abnf::tree-optionp)
                                    (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('variable-declaration')."
  (b* (((pok tree1) (parse-keyword "let" token input))
       ((pok tree2) (parse-identifier token input))
       ((pok tree3) (parse-symbol ":" token input))
       ((pok tree4) (parse-type token input))
       ((pok tree5) (parse-symbol "=" token input))
       ((pok tree6) (parse-expression token input))
       ((pok tree7) (parse-symbol ";" token input))
       (tree (abnf::make-tree-nonleaf
              :rulename? (abnf::rulename "variable-declaration")
              :branches (list (list tree1)
                              (list tree2)
                              (list tree3)
                              (list tree4)
                              (list tree5)
                              (list tree6)
                              (list tree7)))))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-variable-declaration-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-variable-declaration-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-return-statement ((token abnf::tree-optionp)
                                (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('return-statement')."
  (b* (((pok tree1) (parse-keyword "return" token input))
       ((pok tree2) (parse-expression token input))
       ((pok tree3) (parse-symbol ";" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "return-statement")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-return-statement-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-return-statement-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-string-literal ((token abnf::tree-optionp)
                              (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('string-literal')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when parsing console statements.
     We check if the next token is an @('atomic-literal')
     that wraps a @('string-literal'),
     and in that case we return the underlying @('string-literal')."))
  (b* (((unless (abnf::tree-option-case token :some))
        (perr (list :found :no-token)))
       (tree (abnf::tree-option-some->val token))
       ((unless (and (abnf::tree-case tree :nonleaf)
                     (equal (abnf::tree-nonleaf->rulename? tree)
                            (abnf::rulename "atomic-literal"))))
        (perr (list :found tree)))
       (treess (abnf::tree-nonleaf->branches tree))
       ((unless (and (consp treess)
                     (not (consp (cdr treess)))))
        (perr :impossible))
       (trees (car treess))
       ((unless (and (consp trees)
                     (not (consp (cdr trees)))))
        (perr :impossible))
       (tree (car trees))
       ((mv token input) (parse-token input)))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-string-literal-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret parsize-of-parse-string-literal-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-assert-call ((token abnf::tree-optionp)
                           (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('assert-call')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since currently the name @('assert') is not a keyword,
     we need to consider it an identifier.")
   (xdoc::p
    "We call this ACL2 function when the next token is @('assert').
     Thus, we do not re-check that here."))
  (b* (((pok &) (parse-identifier token input))
       (tree1 (abnf::tree-leafterm (string=>nats "assert")))
       ((pok tree2) (parse-symbol "(" token input))
       ((pok tree3) (parse-expression token input))
       ((pok tree4) (parse-symbol ")" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "assert-call")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-assert-call-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-assert-call-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-assert-equal-call ((token abnf::tree-optionp)
                           (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('assert-equal-call')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since currently the name @('assert_eq') is not a keyword,
     we need to consider it an identifier.")
   (xdoc::p
    "We call this ACL2 function when the next token is @('assert_eq').
     Thus, we do not re-check that here."))
  (b* (((pok &) (parse-identifier token input))
       (tree1 (abnf::tree-leafterm (string=>nats "assert_eq")))
       ((pok tree2) (parse-symbol "(" token input))
       ((pok tree3) (parse-expression token input))
       ((pok tree4) (parse-symbol "," token input))
       ((pok tree5) (parse-expression token input))
       ((pok tree6) (parse-?-comma token input))
       ((pok< tree7) (parse-symbol ")" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "assert-equal-call")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)
                         (list tree5)
                         (list tree6)
                         (list tree7)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-assert-equal-call-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-assert-equal-call-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-assert-not-equal-call ((token abnf::tree-optionp)
                           (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('assert-not-equal-call')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since currently the name @('assert_neq') is not a keyword,
     we need to consider it an identifier.")
   (xdoc::p
    "We call this ACL2 function when the next token is @('assert_neq').
     Thus, we do not re-check that here."))
  (b* (((pok &) (parse-identifier token input))
       (tree1 (abnf::tree-leafterm (string=>nats "assert_neq")))
       ((pok tree2) (parse-symbol "(" token input))
       ((pok tree3) (parse-expression token input))
       ((pok tree4) (parse-symbol "," token input))
       ((pok tree5) (parse-expression token input))
       ((pok tree6) (parse-?-comma token input))
       ((pok< tree7) (parse-symbol ")" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "assert-not-equal-call")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)
                         (list tree5)
                         (list tree6)
                         (list tree7)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-assert-not-equal-call-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-assert-not-equal-call-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-console-call ((token abnf::tree-optionp)
                            (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('console-call')."
  (b* (((pok tree)
        (if (token-stringp "assert" token)
            (parse-assert-call token input)
          (if (token-stringp "assert_eq" token)
              (parse-assert-equal-call token input)
          (if (token-stringp "assert_neq" token)
              (parse-assert-not-equal-call token input)
            (mv (reserrf :invalid-console-call-type)
                (abnf::tree-option-fix token)
                (abnf::tree-list-fix input)))))))
    (mv (abnf-tree-wrap tree "console-call") token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-console-call-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-console-call-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-console-statement ((token abnf::tree-optionp)
                                 (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('console-statement')."
  (b* (((pok tree1) (parse-keyword "console" token input))
       ((pok tree2) (parse-symbol "." token input))
       ((pok tree3) (parse-console-call token input))
       ((pok tree4) (parse-symbol ";" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "console-statement")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-console-statement-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-console-statement-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-finalize-statement ((token abnf::tree-optionp)
                                 (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('finalize-statement')."
  :guard-debug t
  (b* (((pok tree1) (parse-keyword "async" token input))
       ((pok tree2) (parse-keyword "finalize" token input))
       ((pok tree3) (parse-function-arguments token input))
       ((pok tree4) (parse-symbol ";" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "finalize-statement")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-finalize-statement-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-finalize-statement-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-increment-statement ((token abnf::tree-optionp)
                                 (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('increment-statement')."
  (b* (((pok tree1) (parse-keyword "increment" token input))
       ((pok tree2) (parse-symbol "(" token input))
       ((pok tree3) (parse-identifier token input))
       ((pok tree4) (parse-symbol "," token input))
       ((pok tree5) (parse-expression token input))
       ((pok tree6) (parse-symbol "," token input))
       ((pok tree7) (parse-expression token input))
       ((pok tree8) (parse-?-comma token input))
       ((pok tree9) (parse-symbol ")" token input))
       ((pok tree10) (parse-symbol ";" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "increment-statement")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)
                         (list tree5)
                         (list tree6)
                         (list tree7)
                         (list tree8)
                         (list tree9)
                         (list tree10)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-increment-statement-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-increment-statement-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-decrement-statement ((token abnf::tree-optionp)
                                 (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('decrement-statement')."
  (b* (((pok tree1) (parse-keyword "decrement" token input))
       ((pok tree2) (parse-symbol "(" token input))
       ((pok tree3) (parse-identifier token input))
       ((pok tree4) (parse-symbol "," token input))
       ((pok tree5) (parse-expression token input))
       ((pok tree6) (parse-symbol "," token input))
       ((pok tree7) (parse-expression token input))
       ((pok tree8) (parse-?-comma token input))
       ((pok tree9) (parse-symbol ")" token input))
       ((pok tree10) (parse-symbol ";" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "decrement-statement")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)
                         (list tree5)
                         (list tree6)
                         (list tree7)
                         (list tree8)
                         (list tree9)
                         (list tree10)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-decrement-statement-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-decrement-statement-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-assignment-operator ((token abnf::tree-optionp)
                                   (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('assignment-operator')."
  (b* (((pok tree) (parse-symbol-among ;; None of these is a prefix of any other,
                                       ;; so just leave them in the order they
                                       ;; are in rule assignment-operator.
                                       (list "="
                                             "+=" "-=" "*=" "/=" "%=" "**="
                                             "<<=" ">>="
                                             "&=" "|=" "^="
                                             "&&=" "||=")
                                       token input)))
    (mv (abnf-tree-wrap tree "assignment-operator")
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-assignment-operator-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-assignment-operator-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines parse-statements

  (define parse-statement ((token abnf::tree-optionp)
                           (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('statement')."
    (cond
     ((token-stringp "let" token)
      (b* (((pok tree) (parse-variable-declaration token input)))
        (mv (abnf-tree-wrap tree "statement") token input)))
     ((token-stringp "const" token)
      (b* (((pok tree) (parse-constant-declaration token input)))
        (mv (abnf-tree-wrap tree "statement") token input)))
     ((token-stringp "return" token)
      (b* (((pok tree) (parse-return-statement token input)))
        (mv (abnf-tree-wrap tree "statement") token input)))
     ((token-stringp "console" token)
      (b* (((pok tree) (parse-console-statement token input)))
        (mv (abnf-tree-wrap tree "statement") token input)))
     ((token-stringp "if" token)
      (b* (((pok tree) (parse-conditional-statement token input)))
        (mv (abnf-tree-wrap tree "statement") token input)))
     ((token-stringp "for" token)
      (b* (((pok tree) (parse-loop-statement token input)))
        (mv (abnf-tree-wrap tree "statement") token input)))
     ((token-stringp "async" token)
      (b* (((pok tree) (parse-finalize-statement token input)))
        (mv (abnf-tree-wrap tree "statement") token input)))
     ((token-stringp "increment" token)
      (b* (((pok tree) (parse-increment-statement token input)))
        (mv (abnf-tree-wrap tree "statement") token input)))
        ((token-stringp "decrement" token)
      (b* (((pok tree) (parse-decrement-statement token input)))
        (mv (abnf-tree-wrap tree "statement") token input)))
     ((token-stringp "{" token)
      (b* (((pok tree) (parse-block token input)))
        (mv (abnf-tree-wrap tree "statement") token input)))
     (t (b* (((pok tree1) (parse-expression token input))
             ((pok tree2) (parse-assignment-operator token input))
             ((pok tree3) (parse-expression token input))
             ((pok tree4) (parse-symbol ";" token input))
             (tree (abnf::make-tree-nonleaf
                    :rulename? (abnf::rulename "assignment-statement")
                    :branches (list (list tree1)
                                    (list tree2)
                                    (list tree3)
                                    (list tree4)))))
              (mv (abnf-tree-wrap tree "statement") token input))))
    :measure (two-nats-measure (parsize token input) 2))

  (define parse-*-statement ((token abnf::tree-optionp)
                             (input abnf::tree-listp))
    :returns (mv (trees abnf::tree-list-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('*statement')."
    (b* (((when (token-stringp "}" token))
          (mv nil
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok< tree) (parse-statement token input))
         ((pok trees) (parse-*-statement token input)))
      (mv (cons tree trees) token input))
    :measure (two-nats-measure (parsize token input) 3))

  (define parse-block ((token abnf::tree-optionp)
                       (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('block')."
    (b* (((pok tree1) (parse-symbol "{" token input))
         ((pok trees2) (parse-*-statement token input))
         ((pok tree3) (parse-symbol "}" token input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "block")
           :branches (list (list tree1)
                           trees2
                           (list tree3)))
          token input))
    :measure (two-nats-measure (parsize token input) 0))

  (define parse-branch ((token abnf::tree-optionp)
                        (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('branch')."
    (b* (((pok tree1) (parse-keyword "if" token input))
         ((pok tree2) (parse-expression token input))
         ((pok tree3) (parse-block token input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "branch")
           :branches (list (list tree1)
                           (list tree2)
                           (list tree3)))
          token input))
    :measure (two-nats-measure (parsize token input) 0))

  (define parse-loop-statement ((token abnf::tree-optionp)
                                (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('loop-statement')."
    (b* (((pok tree1) (parse-keyword "for" token input))
         ((pok tree2) (parse-identifier token input))
         ((pok tree3) (parse-symbol ":" token input))
         ((pok tree4) (parse-type token input))
         ((pok tree5) (parse-keyword "in" token input))
         ((pok tree6) (parse-expression token input))
         ((pok tree7) (parse-symbol ".." token input))
         ((mv etree-r etoken einput) (parse-symbol "=" token input))
         (tree8 (if (reserrp etree-r)
                    ;; omitted optional equal sign:
                    (abnf::make-tree-nonleaf :rulename? nil :branches nil)
                  ;; present optional equal sign:
                  (abnf::make-tree-nonleaf
                   :rulename? nil
                   :branches (list (list etree-r)))))
         (token (if (reserrp etree-r) token etoken))
         (input (if (reserrp etree-r) input einput))
         ((pok tree9) (parse-expression token input))
         ((pok tree10) (parse-block token input))
         (tree (abnf::make-tree-nonleaf
                :rulename? (abnf::rulename "loop-statement")
                :branches (list (list tree1)
                                (list tree2)
                                (list tree3)
                                (list tree4)
                                (list tree5)
                                (list tree6)
                                (list tree7)
                                (list tree8)
                                (list tree9)
                                (list tree10)))))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 0))

  (define parse-conditional-statement ((token abnf::tree-optionp)
                                       (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('conditional-statement')."
    (b* (((pok< tree) (parse-branch token input))
         ((when (not (token-stringp "else" token)))
          (mv (abnf-tree-wrap tree "conditional-statement")
              token input))
         ((pok tree2) (parse-keyword "else" token input))
         ((pok tree3)
          (if (token-stringp "{" token)
              (parse-block token input)
            (parse-conditional-statement token input))))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "conditional-statement")
           :branches (list (list tree)
                           (list tree2)
                           (list tree3)))
          token input))
    :measure (two-nats-measure (parsize token input) 1))

  :prepwork
  ((defun parse-statements-expand-hints (id clause world)
     (declare (ignore id world))
     (cond
      ((acl2::occur-lst '(acl2::flag-is 'parse-statement) clause)
       '(:expand (parse-statement token input)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-*-statement) clause)
       '(:expand (parse-*-statement token input)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-block) clause)
       '(:expand (parse-block token input)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-branch) clause)
       '(:expand (parse-branch token input)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-loop-statement) clause)
       '(:expand (parse-loop-statement token input)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-conditional-statement) clause)
       '(:expand (parse-conditional-statement token input))))))

  :verify-guards nil ; done below

  :returns-hints
  (("Goal"
    :in-theory
    (e/d (abnf::treep-when-tree-resultp-and-not-reserrp
          abnf::tree-listp-when-tree-list-resultp-and-not-reserrp)
         (parse-statement
          parse-*-statement
          parse-block
          parse-branch
          parse-loop-statement
          parse-conditional-statement)))
   parse-statements-expand-hints)

  ///

  (defret-mutual parsize-of-parse-statements-<=
    (defret parsize-of-parse-statement-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-statement)
    (defret parsize-of-parse-*-statement-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-*-statement)
    (defret parsize-of-parse-block-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-block)
    (defret parsize-of-parse-branch-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-branch)
    (defret parsize-of-parse-loop-statement-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-loop-statement)
    (defret parsize-of-parse-conditional-statement-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-conditional-statement)
    :hints
    (("Goal" :in-theory (disable parse-statement
                                 parse-*-statement
                                 parse-block
                                 parse-branch
                                 parse-loop-statement
                                 parse-conditional-statement))
     parse-statements-expand-hints))

  (defret-mutual parsize-of-parse-statements-<
    (defret parsize-of-parse-statement-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-statement)
    (defret parsize-of-parse-*-statement-<
      t
      :rule-classes nil
      :fn parse-*-statement)
    (defret parsize-of-parse-block-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-block)
    (defret parsize-of-parse-branch-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-branch)
    (defret parsize-of-parse-loop-statement-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-loop-statement)
    (defret parsize-of-parse-conditional-statement-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-conditional-statement)
    :hints
    (("Goal" :in-theory (disable parse-statement
                                 parse-*-statement
                                 parse-block
                                 parse-branch
                                 parse-loop-statement
                                 parse-conditional-statement))
     parse-statements-expand-hints))

  (verify-guards parse-statement
    :hints (("Goal" :in-theory (disable parse-statement
                                        parse-*-statement
                                        parse-block
                                        parse-branch
                                        parse-loop-statement
                                        parse-conditional-statement))))

  (fty::deffixequiv-mutual parse-statements)
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-function-parameter ((token abnf::tree-optionp)
                                  (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('function-parameter')."
  (b* (((pok tree1)
        (cond ((token-stringp "const" token)
               (b* (((pok tree) (parse-keyword "const" token input)))
                 (mv (abnf::make-tree-nonleaf
                      :rulename? nil
                      :branches (list (list tree)))
                     token input)))
              ((token-stringp "constant" token)
               (b* (((pok tree) (parse-keyword "constant" token input)))
                 (mv (abnf::make-tree-nonleaf
                      :rulename? nil
                      :branches (list (list tree)))
                     token input)))
              ((token-stringp "public" token)
               (b* (((pok tree) (parse-keyword "public" token input)))
                 (mv (abnf::make-tree-nonleaf
                      :rulename? nil
                      :branches (list (list tree)))
                     token input)))
              (t
               (mv (abnf::make-tree-nonleaf
                    :rulename? nil
                    :branches nil)
                   token input))))
       ((pok tree2) (parse-identifier token input))
       ((pok tree3) (parse-symbol ":" token input))
       ((pok tree4) (parse-type token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "function-parameter")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-function-parameter-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-function-parameter-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-*-comma-function-parameter ((token abnf::tree-optionp)
                                          (input abnf::tree-listp))
  :returns (mv
            (trees
             abnf::tree-list-resultp
             :hints
             (("Goal"
               :in-theory
               (enable
                abnf::treep-when-tree-resultp-and-not-reserrp
                abnf::tree-listp-when-tree-list-resultp-and-not-reserrp))))
            (next-token abnf::tree-optionp)
            (rest-input abnf::tree-listp))
  :short "Parse a @('*( \",\" function-parameter )')."
  (b* (((unless (token-stringp "," token))
        (mv nil
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input)))
       (start-token token)
       (start-input input)
       ((pok tree1) (parse-symbol "," token input))
       ((mv tree2 token input) (parse-function-parameter token input)))
    (if (reserrp tree2)
        ;; If there is no function parameter after the comma,
        ;; then this call should not eat the comma,
        ;; and it should return the empty list of trees.
        (mv nil
            (abnf::tree-option-fix start-token)
            (abnf::tree-list-fix start-input))
      (b* ((tree (abnf::make-tree-nonleaf :rulename? nil
                                          :branches (list (list tree1)
                                                          (list tree2))))
           ((pok trees) (parse-*-comma-function-parameter token input)))
        (mv (cons tree trees) token input))))
  :measure (parsize token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-*-comma-function-parameter-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-function-parameters ((token abnf::tree-optionp)
                                   (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('function-parameters')."
  (b* (((pok< tree) (parse-function-parameter token input))
       ((pok trees) (parse-*-comma-function-parameter token input)))
    (if (token-stringp "," token) ; optional trailing comma
        (b* (((pok ctree) (parse-symbol "," token input)))
          (mv (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "function-parameters")
               :branches (list (list tree)
                               trees
                               (list (abnf::make-tree-nonleaf
                                      :rulename? nil
                                      :branches (list (list ctree))))))
              token input))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "function-parameters")
           :branches (list (list tree)
                           trees
                           ;; omitted optional comma:
                           (list (abnf::make-tree-nonleaf
                                  :rulename? nil
                                  :branches nil))))
          token input)))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-function-parameters-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-function-parameters-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-?-output-type ((token abnf::tree-optionp)
                             (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse @('[ \"->\" type ]')."
  (b* (((mv treeA tokenA inputA)
        (b* (((pok tree1) (parse-symbol "->" token input))
             ((pok tree2) (parse-type token input)))
          (mv (abnf::make-tree-nonleaf
               :rulename? nil
               :branches (list (list tree1)
                               (list tree2)))
              token input))))
    (if (reserrp treeA)
        (mv (abnf::make-tree-nonleaf :rulename? nil
                                     :branches nil)
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input))
      (mv treeA tokenA inputA)))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-?-output-type
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-finalizer ((token abnf::tree-optionp)
                         (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('finalize') block."
  :long
  (xdoc::topstring
   (xdoc::p
    "A finalizer block has similar syntax to a function/transition declaration,
     but does not support annotations, has an optional return type,
     and can only appear at the end of a transition declaration."))
  (b* (((pok tree1) (parse-keyword "finalize" token input))
       ((pok tree2) (parse-identifier token input))
       ((pok tree3) (parse-symbol "(" token input))
       ((pok tree4) (if (token-stringp ")" token)
                        (mv (abnf::make-tree-nonleaf :rulename? nil
                                                     :branches nil)
                            token input)
                      (b* (((pok tree)
                            (parse-function-parameters token input)))
                        (mv (abnf::make-tree-nonleaf
                             :rulename? nil
                             :branches (list (list tree)))
                            token input))))
       ((pok tree5) (parse-symbol ")" token input))
       ((pok tree6) (parse-?-output-type token input))
       ((pok tree7) (parse-block token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "finalizer")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)
                         (list tree5)
                         (list tree6)
                         (list tree7)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-finalizer-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-finalizer-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-?-finalizer ((token abnf::tree-optionp)
                           (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('[ finalizer ]')."
  (b* (((mv tree token1 input1) (parse-finalizer token input))
       ((when (not (reserrp tree)))
        (mv (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree)))
            token1
            input1)))
    (mv (abnf::make-tree-nonleaf :rulename? nil :branches nil)
        (abnf::tree-option-fix token)
        (abnf::tree-list-fix input)))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-?-finalizer
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-struct-component-declaration ((token abnf::tree-optionp)
                                            (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('struct-component-declaration')."
  (b* (((pok tree1) (parse-identifier token input))
       ((pok tree2) (parse-symbol ":" token input))
       ((pok tree3) (parse-type token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "struct-component-declaration")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-struct-component-declaration-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-struct-component-declaration-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-*-comma-struct-component-declaration ((token abnf::tree-optionp)
                                                     (input abnf::tree-listp))
  :returns (mv
            (trees
             abnf::tree-list-resultp
             :hints
             (("Goal"
               :in-theory
               (enable
                abnf::treep-when-tree-resultp-and-not-reserrp
                abnf::tree-listp-when-tree-list-resultp-and-not-reserrp))))
            (next-token abnf::tree-optionp)
            (rest-input abnf::tree-listp))
  :short "Parse a @('*( \",\" struct-component-declaration )')."
  (b* (((unless (token-stringp "," token))
        (mv nil
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input)))
       (start-token token)
       (start-input input)
       ((pok tree1) (parse-symbol "," token input))
       ((mv tree2 token input) (parse-struct-component-declaration token input)))
    (if (reserrp tree2)
        ;; If there is no struct-component-declaration after the comma,
        ;; then this call should not eat the comma,
        ;; and it should return the empty list of trees.
        (mv nil
            (abnf::tree-option-fix start-token)
            (abnf::tree-list-fix start-input))
      (b* ((tree (abnf::make-tree-nonleaf :rulename? nil
                                          :branches (list (list tree1)
                                                          (list tree2))))
           ((pok trees) (parse-*-comma-struct-component-declaration token input)))
        (mv (cons tree trees) token input))))
  :measure (parsize token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-*-comma-struct-component-declaration-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-struct-component-declarations ((token abnf::tree-optionp)
                                   (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('struct-component-declarations')."
  (b* (((pok< tree) (parse-struct-component-declaration token input))
       ((pok trees) (parse-*-comma-struct-component-declaration token input)))
    (if (token-stringp "," token) ; optional trailing comma
        (b* (((pok ctree) (parse-symbol "," token input)))
          (mv (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "struct-component-declarations")
               :branches (list (list tree)
                               trees
                               (list (abnf::make-tree-nonleaf
                                      :rulename? nil
                                      :branches (list (list ctree))))))
              token input))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "struct-component-declarations")
           :branches (list (list tree)
                           trees
                           ;; omitted optional comma:
                           (list (abnf::make-tree-nonleaf
                                  :rulename? nil
                                  :branches nil))))
          token input)))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-struct-component-declarations-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-struct-component-declarations-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-struct-declaration ((token abnf::tree-optionp)
                                   (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('struct-declaration')."
  (b* (((pok tree1) (parse-keyword "struct" token input))
       ((pok tree2) (parse-identifier token input))
       ((pok tree3) (parse-symbol "{" token input))
       ((pok tree4) (parse-struct-component-declarations token input))
       ((pok tree5) (parse-symbol "}" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "struct-declaration")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)
                         (list tree5)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-struct-declaration-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-struct-declaration-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-record-declaration ((token abnf::tree-optionp)
                                  (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('record-declaration')."
  (b* (((pok tree1) (parse-keyword "record" token input))
       ((pok tree2) (parse-identifier token input))
       ((pok tree3) (parse-symbol "{" token input))
       ((pok tree4) (parse-struct-component-declarations token input))
       ((pok tree5) (parse-symbol "}" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "record-declaration")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)
                         (list tree5)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-record-declaration-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-record-declaration-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-mapping-declaration ((token abnf::tree-optionp)
                                   (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('mapping-declaration')."
  (b* (((pok tree1) (parse-keyword "mapping" token input))
       ((pok tree2) (parse-identifier token input))
       ((pok tree3) (parse-symbol ":" token input))
       ((pok tree4) (parse-type token input))
       ((pok tree5) (parse-symbol "=>" token input))
       ((pok tree6) (parse-type token input))
       ((pok tree7) (parse-symbol ";" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "mapping-declaration")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)
                         (list tree5)
                         (list tree6)
                         (list tree7)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-mapping-declaration-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-mapping-declaration-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-function-declaration ((token abnf::tree-optionp)
                                    (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('function-declaration')."
  (b* (((pok trees-anns) (parse-*-annotation token input))
       ((pok tree1) (parse-keyword "function" token input))
       ((pok tree2) (parse-identifier token input))
       ((pok tree3) (parse-symbol "(" token input))
       ((pok tree4) (if (token-stringp ")" token)
                        (mv (abnf::make-tree-nonleaf :rulename? nil
                                                     :branches nil)
                            token input)
                      (b* (((pok tree)
                            (parse-function-parameters token input)))
                        (mv (abnf::make-tree-nonleaf
                             :rulename? nil
                             :branches (list (list tree)))
                            token input))))
       ((pok tree5) (parse-symbol ")" token input))
       ((pok tree6) (parse-symbol "->" token input))
       ((pok tree7) (parse-type token input))
       ((pok tree8) (parse-block token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "function-declaration")
         :branches (list trees-anns
                         (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)
                         (list tree5)
                         (list tree6)
                         (list tree7)
                         (list tree8)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-function-declaration-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-function-declaration-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-transition-declaration ((token abnf::tree-optionp)
                                      (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('transition-declaration')."
  :long
  (xdoc::topstring
   (xdoc::p
    "A transition is a special kind of function.
     Its syntax differs in two ways: the keyword used
     and the optional @('finalizer') at the end."))
  (b* (((pok trees-anns) (parse-*-annotation token input))
       ((pok tree1) (parse-keyword "transition" token input))
       ((pok tree2) (parse-identifier token input))
       ((pok tree3) (parse-symbol "(" token input))
       ((pok tree4) (if (token-stringp ")" token)
                        (mv (abnf::make-tree-nonleaf :rulename? nil
                                                     :branches nil)
                            token input)
                      (b* (((pok tree)
                            (parse-function-parameters token input)))
                        (mv (abnf::make-tree-nonleaf
                             :rulename? nil
                             :branches (list (list tree)))
                            token input))))
       ((pok tree5) (parse-symbol ")" token input))
       ((pok tree6) (parse-symbol "->" token input))
       ((pok tree7) (parse-type token input))
       ((pok tree8) (parse-block token input))
       ((pok tree9) (parse-?-finalizer token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "transition-declaration")
         :branches (list trees-anns
                         (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)
                         (list tree5)
                         (list tree6)
                         (list tree7)
                         (list tree8)
                         (list tree9)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-transition-declaration-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-transition-declaration-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-transition-or-function-declaration ((token abnf::tree-optionp)
                                                  (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse either a @('transition-declaration') or a @('function-declaration')."
  (b* (((mv tree1 token1 input1)
        (parse-transition-declaration token input))
       ((when (not (reserrp tree1)))
        (mv tree1 token1 input1)))
    (parse-function-declaration token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-transition-or-function-declaration-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-transition-or-function-declaration-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-program-item ((token abnf::tree-optionp)
                           (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('program-item')."
  (b* (((pok tree)
        (if (token-rootp "annotation" token)
            (parse-transition-or-function-declaration token input)
          (if (token-stringp "transition" token)
              (parse-transition-declaration token input)
              (if (token-stringp "function" token)
                  (parse-function-declaration token input)
                (if (token-stringp "struct" token)
                    (parse-struct-declaration token input)
                  (if (token-stringp "record" token)
                      (parse-record-declaration token input)
                    (parse-mapping-declaration token input))))))))
    (mv (abnf-tree-wrap tree "program-item") token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-program-item-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-program-item-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-*-program-item ((token abnf::tree-optionp)
                              (input abnf::tree-listp))
  :returns (mv
            (trees
             abnf::tree-list-resultp
             :hints
             (("Goal"
               :in-theory
               (enable
                abnf::treep-when-tree-resultp-and-not-reserrp
                abnf::tree-listp-when-tree-list-resultp-and-not-reserrp))))
            (next-token abnf::tree-optionp)
            (rest-input abnf::tree-listp))
  :short "Parse a @('*program-item')."
  (b* (((when (token-stringp "}" token))
        (mv nil
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input)))
       ((pok< tree) (parse-program-item token input))
       ((pok trees) (parse-*-program-item token input)))
    (mv (cons tree trees) token input))
  :measure (parsize token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-*-program-item-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-program-declaration ((token abnf::tree-optionp)
                                   (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('program-declaration')."
  (b* (((pok tree1) (parse-keyword "program" token input))
       ((pok tree2) (parse-program-id token input))
       ((pok tree3) (parse-symbol "{" token input))
       ((pok trees4) (parse-*-program-item token input))
       ((pok tree5) (parse-symbol "}" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "program-declaration")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         trees4
                         (list tree5)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-program-declaration-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-program-declaration-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-import-declaration ((token abnf::tree-optionp)
                                  (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('import-declaration')."
  (b* (((pok tree1) (parse-keyword "import" token input))
       ((pok tree2) (parse-program-id token input))
       ((pok tree3) (parse-symbol ";" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "import-declaration")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-import-declaration-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-import-declaration-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-*-import-declaration ((token abnf::tree-optionp)
                                    (input abnf::tree-listp))
  :returns (mv
            (trees
             abnf::tree-list-resultp
             :hints
             (("Goal"
               :in-theory
               (enable
                abnf::treep-when-tree-resultp-and-not-reserrp
                abnf::tree-listp-when-tree-list-resultp-and-not-reserrp))))
            (next-token abnf::tree-optionp)
            (rest-input abnf::tree-listp))
  :short "Parse a @('*import-declaration')."
  (abnf::tree-option-case
   token
   ;; This pattern is designed to return a list of import declarations
   ;; when the token is empty, which is needed if an import decl can
   ;; appear at the end of a file.  Currently there is a required
   ;; element after the imports, but we leave the pattern here for reference.
   :none (mv nil
             nil
             (abnf::tree-list-fix input))
   :some (b* (((mv tree1 token1 input1)
               (parse-import-declaration token input))
              ((when (reserrp tree1))
               (mv nil
                   (abnf::tree-option-fix token)
                   (abnf::tree-list-fix input)))
              ((pok trees) (parse-*-import-declaration token1 input1)))
           (mv (cons tree1 trees) token input)))
  :measure (parsize token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-*-import-declaration-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-file ((input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('file')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level function that organizes a list of tokens
     into a CST.
     We get the first token (if any),
     and then we parse zero or more import declarations,
     and then we parse the program declaration,
     and return a @('file') CST.
     If there is no error, there is no next token and no remaining input."))
  (b* (((mv token input) (parse-token input))
       ((pok import-trees) (parse-*-import-declaration token input))
       ((pok tree1) (parse-program-declaration token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "file")
         :branches (list import-trees
                         (list tree1)))
        nil nil))
  :hooks (:fix))
