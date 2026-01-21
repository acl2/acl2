; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "grammar")

(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/utilities/user-interface" :dir :system)
(include-book "projects/abnf/constructor-utilities" :dir :system)
(include-book "projects/abnf/parsing-tools/defdefparse" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "unicode/read-utf8" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser
  :parents (concrete-syntax)
  :short "An executable parser of PFCS."
  :long
  (xdoc::topstring
   (xdoc::p
    "If you are looking for API functions for calling the PFCS parser,
     please see @(see parser-interface).")
   (xdoc::p
    "This is a fairly simple parser for the PFCS syntactic grammar.
     The parser consists of a collection of parsing functions that
     operate on a sequence of tokens.
     Most parsing functions take a lookahead token (an optional ABNF
     tree) and a sequence of the remaining tokens (list of ABNF trees).")
   (xdoc::p
    "Each ABNF tree in the sequence of tokens
     (and the lookahead token) should have a rulename
     from the right hand side of the ABNF rule for @('token')
     indicating the kind of token it is:")
   (xdoc::codeblock
    "token = identifier / integer / operator / separator")
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
    "This is related to @(tsee fty::patbind-ok).
     It is used for many of the parsing functions."))
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

(define parse-operator ((operator stringp)
                       (token abnf::tree-optionp)
                       (input abnf::tree-listp))
  :guard (member-equal operator *operators*)
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a specified @('operator')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to check the presence of an expected operator.
     We return it as a leaf tree as the first result,
     because this is how an operator occurs
     in the CSTs of the syntactic grammar.
     In other words, the @('operator') rulename does not appear
     in any CST returned by the parser.")
   (xdoc::p
    "This is consistent with the fact that
     the rule for @('operator') does not appear on the right
     hand side of any rule other than the rule @('token')."))
  (b* ((tree (check-token-root "operator" token))
       ((when (reserrp tree)) (perr (reserrf-push tree)))
       ((unless (equal (abnf::tree->string tree)
                       (string=>nats (str-fix operator))))
        (perr (list :required (str-fix operator)
                    :found (abnf::tree-option-fix token))))
       (tree (abnf::tree-leafterm (string=>nats (str-fix operator))))
       ((mv token input) (parse-token input)))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-operator-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret parsize-of-parse-operator-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret len-of-parse-operator-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-operator-<
    (implies (and (not (reserrp tree))
                  next-token)
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-operator-among ((operators string-listp)
                              (token abnf::tree-optionp)
                              (input abnf::tree-listp))
  :guard (subsetp-equal operators *operators*)
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('operator') among the ones in a specified list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to check the presence of an expected operator.
     We return it as a leaf tree as the first result,
     because this is how an operator occurs
     in the CSTs of the syntactic grammar.
     In other words, the @('operator') rulename does not appear
     in any CST returned by the parser.")
   (xdoc::p
    "This is consistent with the fact that
     the rule @('operator') does not appear on the right
     hand side of any rule other than the rule @('token')."))
  (b* ((tree (check-token-root "operator" token))
       ((when (reserrp tree)) (perr (reserrf-push tree)))
       (fringe (abnf::tree->string tree))
       ((unless (nat-listp fringe)) (perr :impossible))
       ((unless (parse-operator-among-aux fringe operators))
        (perr (list :required :one-of (str::string-list-fix operators)
                    :found tree)))
       (tree (abnf::tree-leafterm fringe))
       ((mv token input) (parse-token input)))
    (mv tree token input))
  :hooks (:fix)

  :prepwork
  ((define parse-operator-among-aux ((nats nat-listp) (strings string-listp))
     :returns (yes/no booleanp)
     :parents nil
     (and (consp strings)
          (or (equal (string=>nats (str-fix (car strings)))
                     (nat-list-fix nats))
              (parse-operator-among-aux nats (cdr strings))))
     :hooks (:fix)))

  ///

  (defret parsize-of-parse-operator-among-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret parsize-of-parse-operator-among-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret len-of-parse-operator-among-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-operator-among-<
    (implies (and (not (reserrp tree))
                  next-token)
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-separator ((separator stringp)
                         (token abnf::tree-optionp)
                         (input abnf::tree-listp))
  :guard (member-equal separator *separators*)
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a specified @('separator')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to check the presence of an expected separator.
     We return it as a leaf tree as the first result,
     because this is how an separator occurs
     in the CSTs of the syntactic grammar.
     In other words, the @('separator') rulename does not appear
     in any CST returned by the parser.")
   (xdoc::p
    "This is consistent with the fact that
     the rule for @('separator') does not appear on the right
     hand side of any rule other than the rule @('token')."))
  (b* ((tree (check-token-root "separator" token))
       ((when (reserrp tree)) (perr (reserrf-push tree)))
       ((unless (equal (abnf::tree->string tree)
                       (string=>nats (str-fix separator))))
        (perr (list :required (str-fix separator)
                    :found (abnf::tree-option-fix token))))
       (tree (abnf::tree-leafterm (string=>nats (str-fix separator))))
       ((mv token input) (parse-token input)))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-separator-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret parsize-of-parse-separator-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret len-of-parse-separator-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-separator-<
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
  :short "Parse an @('identifier') token."
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

(define parse-numeral ((token abnf::tree-optionp)
                       (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('numeral') token."
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

  (defret parsize-of-parse-numeral-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize))))

  (defret len-of-parse-numeral-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-numeral-<
    (implies (and (not (reserrp tree))
                  next-token)
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Large mutual recursion to parse expressions
(defines parse-expressions

  ;; expression = additive-expression

  (define parse-expression ((token abnf::tree-optionp)
                            (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse an @('expression')."
    (b* (((pok tree) (parse-additive-expression token input)))
      (mv (abnf-tree-wrap tree "expression")
          token
          input))
    :measure (two-nats-measure (parsize token input) 5))

  ;; additive-expression = multiplication-expression
  ;;                     / additive-expression "+" multiplication-expression
  ;;                     / additive-expression "-" multiplication-expression

  (define parse-additive-expression ((token abnf::tree-optionp)
                                     (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('additive-expression')."
    (b* (((pok< tree) (parse-multiplication-expression token input))
         (current (abnf-tree-wrap tree "additive-expression"))
         ((pok tree) (parse-additive-expression-rest token
                                                     input
                                                     current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 4))

  (define parse-additive-expression-rest ((token abnf::tree-optionp)
                                          (input abnf::tree-listp)
                                          (current abnf::treep))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse the rest of a @('additive-expression')."
    (b* (((when (not (or (token-stringp "+" token) (token-stringp "-" token))))
          (mv (abnf::tree-fix current)
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok tree2) (parse-operator-among (list "+" "-") token input))
         ((pok< tree3) (parse-multiplication-expression token input))
         ;; About the previous clause:
         ;; Although in general we could return the argument `current`
         ;; when we see "+" but no following multiplication-expression,
         ;; but since there is nothing else that could start with "+"
         ;; we simplify and return an error if there is "+" without a
         ;; following multiplication-expression.
         (current (abnf::make-tree-nonleaf
                   :rulename? (abnf::rulename "additive-expression")
                   :branches (list (list current)
                                   (list tree2)
                                   (list tree3))))
         ((pok tree) (parse-additive-expression-rest token
                                                     input
                                                     current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 4))

  ;; multiplication-expression = unary-minus-expression
  ;;                           / multiplication-expression "*" unary-minus-expression

  (define parse-multiplication-expression ((token abnf::tree-optionp)
                                           (input abnf::tree-listp))
      :returns (mv (tree abnf::tree-resultp)
                   (next-token abnf::tree-optionp)
                   (rest-input abnf::tree-listp))
      :short "Parse a @('multiplication-expression')."
      (b* (((pok< tree) (parse-unary-minus-expression token input))
           (current (abnf-tree-wrap tree "multiplication-expression"))
           ((pok tree) (parse-multiplication-expression-rest token
                                                             input
                                                             current)))
        (mv tree token input))
      :measure (two-nats-measure (parsize token input) 3))

  (define parse-multiplication-expression-rest ((token abnf::tree-optionp)
                                                (input abnf::tree-listp)
                                                (current abnf::treep))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse the rest of a @('multiplication-expression')."
    (b* (((when (not (token-stringp "*" token)))
          (mv (abnf::tree-fix current)
              (abnf::tree-option-fix token)
              (abnf::tree-list-fix input)))
         ((pok tree2) (parse-operator "*" token input))
         ((pok< tree3) (parse-unary-minus-expression token input))
         ;; About the previous clause:
         ;; Although in general we could return the argument `current`
         ;; when we see "*" but no following unary-minus-expression,
         ;; but since there is nothing else that could start with "*"
         ;; we simplify and return an error if there is "*" without a
         ;; following unary-minus-expression.
         (current (abnf::make-tree-nonleaf
                   :rulename? (abnf::rulename "multiplication-expression")
                   :branches (list (list current)
                                   (list tree2)
                                   (list tree3))))
         ((pok tree) (parse-multiplication-expression-rest token
                                                           input
                                                           current)))
      (mv tree token input))
    :measure (two-nats-measure (parsize token input) 3))

  ;; unary-minus-expression = [ "-" ] primary-expression

  (define parse-unary-minus-expression ((token abnf::tree-optionp)
                                        (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('unary-minus-expression')."
    :long "If the \"-\" is not present, the @('unary-minus-expression')
           in the CST is a simple wrapper around the @('primary-expression');
           this is analogous to how the @('multiplication-expression') and
           @('additive-expression') work."
    (if (token-stringp "-" token)
        (b* (((pok dash-tree) (parse-operator "-" token input))
             ((pok expr-tree) (parse-primary-expression token input)))
          (mv (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "unary-minus-expression")
               :branches (list
                          ;; optional dash
                          (list (abnf::make-tree-nonleaf
                                 :rulename? nil
                                 :branches (list (list dash-tree))))
                          (list expr-tree)))
              token input))
        (b* (((pok expr-tree) (parse-primary-expression token input)))
          (mv (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "unary-minus-expression")
               :branches (list
                          ;; omitted optional dash
                          (list (abnf::make-tree-nonleaf
                                 :rulename? nil
                                 :branches nil))
                          (list expr-tree)))
              token input)))
    :measure (two-nats-measure (parsize token input) 2))

  ;; primary-expression = identifier / numeral / "(" expression ")"

  (define parse-primary-expression ((token abnf::tree-optionp)
                                    (input abnf::tree-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (next-token abnf::tree-optionp)
                 (rest-input abnf::tree-listp))
    :short "Parse a @('primary-expression')."
    (b* (((mv tree token0 input0) (parse-identifier token input))
         ((when (not (reserrp tree)))
          (mv (abnf-tree-wrap tree "primary-expression")
              token0 input0))
         ((mv tree token1 input1) (parse-numeral token input))
         ((when (not (reserrp tree)))
          (mv (abnf-tree-wrap tree "primary-expression")
              token1 input1))
         ((pok tree1) (parse-separator "(" token input))
         ((pok tree2) (parse-expression token input)) ; maybe pok< ?
         ((pok tree3) (parse-separator ")" token input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "primary-expression")
           :branches (list (list tree1)
                           (list tree2)
                           (list tree3)))
          token input))
    :measure (two-nats-measure (parsize token input) 1))

  :prepwork
  ((defun parse-expressions-expand-hints (id clause world)
     (declare (ignore id world))
     (cond
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-expression) clause)
       '(:expand
         (parse-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-additive-expression) clause)
       '(:expand (parse-additive-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-additive-expression-rest) clause)
       '(:expand
         (parse-additive-expression-rest token input current)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-multiplication-expression) clause)
       '(:expand (parse-multiplication-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-multiplication-expression-rest) clause)
       '(:expand
         (parse-multiplication-expression-rest token input current)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-primary-expression) clause)
       '(:expand
         (parse-primary-expression token input)))
      ((acl2::occur-lst
        '(acl2::flag-is 'parse-unary-minus-expression) clause)
       '(:expand
         (parse-unary-minus-expression token input))))))

  :ruler-extenders :all

  :verify-guards nil ; done below

  :returns-hints
  (("Goal"
    :in-theory
    (e/d (abnf::treep-when-tree-resultp-and-not-reserrp
          abnf::tree-listp-when-tree-list-resultp-and-not-reserrp)
         (parse-expression
          parse-additive-expression
          parse-additive-expression-rest
          parse-multiplication-expression
          parse-multiplication-expression-rest
          parse-unary-minus-expression
          parse-primary-expression)))
   parse-expressions-expand-hints)

  ///

  (defret-mutual parsize-of-parse-expressions-<=
    (defret parsize-of-parse-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-expression)
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
    (defret parsize-of-parse-multiplication-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-multiplication-expression)
    (defret parsize-of-parse-multiplication-expression-rest-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-multiplication-expression-rest)
    (defret parsize-of-parse-unary-minus-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-unary-minus-expression)
    (defret parsize-of-parse-primary-expression-<=
      (<= (parsize next-token rest-input)
          (parsize token input))
      :rule-classes :linear
      :fn parse-primary-expression)
    :hints
    (("Goal" :in-theory (disable parse-expression
                                 parse-additive-expression
                                 parse-additive-expression-rest
                                 parse-multiplication-expression
                                 parse-multiplication-expression-rest
                                 parse-unary-minus-expression
                                 parse-primary-expression))
     parse-expressions-expand-hints))

  (defret-mutual parsize-of-parse-expressions-<
    (defret parsize-of-parse-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-expression)

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
    (defret parsize-of-parse-multiplication-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-multiplication-expression)
    (defret parsize-of-parse-multiplication-expression-rest-<
      t
      :rule-classes nil
      :fn parse-multiplication-expression-rest)
    (defret parsize-of-parse-unary-minus-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-unary-minus-expression)
    (defret parsize-of-parse-primary-expression-<
      (implies (not (reserrp tree))
               (< (parsize next-token rest-input)
                  (parsize token input)))
      :rule-classes :linear
      :fn parse-primary-expression)
    :hints
    (("Goal" :in-theory (disable parse-expression
                                 parse-additive-expression
                                 parse-additive-expression-rest
                                 parse-multiplication-expression
                                 parse-multiplication-expression-rest
                                 parse-unary-minus-expression
                                 parse-primary-expression))
     parse-expressions-expand-hints))

  (verify-guards parse-expression
    :hints
    (("Goal" :in-theory (disable parse-expression
                                 parse-multiplication-expression
                                 parse-multiplication-expression-rest
                                 parse-multiplication-expression
                                 parse-multiplication-expression-rest
                                 parse-unary-minus-expression
                                 parse-primary-expression))))

  (fty::deffixequiv-mutual parse-expressions)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; equality-constraint = expression "==" expression

(define parse-equality-constraint ((token abnf::tree-optionp)
                                   (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('equality-constraint')."
  (b* (((pok tree1) (parse-expression token input))
       ((pok tree2) (parse-operator "==" token input))
       ((pok tree3) (parse-expression token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "equality-constraint")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)))
        token
        input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-equality-expression-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-equality-expression-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; relation-constraint = identifier "(" [ expression *( "," expression ) ] ")"

(define parse-*-comma-expression ((token abnf::tree-optionp)
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
  :short "Parse a @('*( \",\" expression )')."
  (b* (((unless (token-stringp "," token))
        (mv nil
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input)))
       (start-token token)
       (start-input input)
       ((pok< tree1) (parse-separator "," token input))
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
  :measure (parsize token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-*-comma-expression-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

(define parse-relation-constraint ((token abnf::tree-optionp)
                                   (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('relation-constraint')."
  (b* (((pok tree1) (parse-identifier token input))
       ((pok tree2) (parse-separator "(" token input))
       ((pok tree3) (if (token-stringp ")" token)
                        (mv (abnf::make-tree-nonleaf :rulename? nil
                                                     :branches nil)
                            token input)
                      (b* (((pok< tree) (parse-expression token input))
                           ((pok trees) (parse-*-comma-expression token input)))
                        ;; we do not support trailing comma currently
                        (mv (abnf::make-tree-nonleaf
                             :rulename? nil
                             :branches (list (list tree)
                                             trees))
                            token input))))
       ((pok tree4) (parse-separator ")" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "relation-constraint")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)
                         (list tree4)))
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-relation-constraint-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-relation-constraint-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; constraint = equality-constraint / relation-constraint

(define parse-constraint ((token abnf::tree-optionp)
                          (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('constraint')."
  (b* (((mv tree token0 input0) (parse-equality-constraint token input))
       ((when (not (reserrp tree)))
        (mv (abnf-tree-wrap tree "constraint")
            token0 input0))
       ((pok tree) (parse-relation-constraint token input)))
    (mv (abnf-tree-wrap tree "constraint")
        token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-constraint-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-constraint-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; definition = identifier "(" [ identifier *( "," identifier ) ] ")"
;;              ":=" "{" [ constraint *( "," constraint ) ] "}"

(define parse-*-comma-identifier ((token abnf::tree-optionp)
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
  :short "Parse a @('*( \",\" identifier )')."
  (b* (((unless (token-stringp "," token))
        (mv nil
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input)))
       (start-token token)
       (start-input input)
       ((pok< tree1) (parse-separator "," token input))
       (token1 token)
       (input1 input)
       ((mv tree2 token input) (parse-identifier token input)))
    (if (reserrp tree2)
        ;; if there is no identifier after the comma,
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
           ((pok trees) (parse-*-comma-identifier token input)))
        (mv (cons tree trees) token input))))
  :measure (parsize token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-*-comma-identifier-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

(define parse-*-comma-constraint ((token abnf::tree-optionp)
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
  :short "Parse a @('*( \",\" constraint )')."
  (b* (((unless (token-stringp "," token))
        (mv nil
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input)))
       (start-token token)
       (start-input input)
       ((pok< tree1) (parse-separator "," token input))
       (token1 token)
       (input1 input)
       ((mv tree2 token input) (parse-constraint token input)))
    (if (reserrp tree2)
        ;; if there is no constraint after the comma,
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
           ((pok trees) (parse-*-comma-constraint token input)))
        (mv (cons tree trees) token input))))
  :measure (parsize token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-*-comma-constraint-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

(define parse-definition ((token abnf::tree-optionp)
                          (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('definition')."
  (b* (((pok tree1) (parse-identifier token input))
       ((pok tree2) (parse-separator "(" token input))
       ((pok tree3) (if (token-stringp ")" token)
                        (mv (abnf::make-tree-nonleaf :rulename? nil
                                                     :branches nil)
                            token input)
                      (b* (((pok< tree) (parse-identifier token input))
                           ((pok trees) (parse-*-comma-identifier token input)))
                        (mv (abnf::make-tree-nonleaf
                             :rulename? nil
                             :branches (list (list tree)
                                             trees))
                            token input))))
       ((pok tree4) (parse-separator ")" token input))
       ((pok tree5) (parse-operator ":=" token input))
       ((pok tree6) (parse-separator "{" token input))
       ((pok tree7) (if (token-stringp "}" token)
                        ;; placeholder for the optional constraints
                        (mv (abnf::make-tree-nonleaf :rulename? nil
                                                     :branches nil)
                            token input)
                        (b* (((pok< tree) (parse-constraint token input))
                             ((pok trees) (parse-*-comma-constraint token input)))
                          (mv (abnf::make-tree-nonleaf
                               :rulename? nil
                               :branches (list (list tree)
                                               trees))
                              token input))))
       ((pok tree8) (parse-separator "}" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "definition")
         :branches (list (list tree1)
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

  (defret parsize-of-parse-definition-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-definition-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; system = *definition *constraint

(define parse-*-definition  ((token abnf::tree-optionp)
                             (input abnf::tree-listp))
  :returns (mv (trees abnf::tree-list-resultp
                      :hints
                      (("Goal"
                        :in-theory
                        (enable
                         abnf::treep-when-tree-resultp-and-not-reserrp
                         abnf::tree-listp-when-tree-list-resultp-and-not-reserrp))))
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('*definition')."
  (b* (((mv tree token-after-definition input-after-definition)
        (parse-definition token input))
       ((when (reserrp tree))
        ;; no definitions found in this call
        (mv nil
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input)))
       ((pok trees) (parse-*-definition token-after-definition
                                        input-after-definition)))
    (mv (cons tree trees) token input))
  :measure (parsize token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-*-definition-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

(define parse-*-constraint  ((token abnf::tree-optionp)
                             (input abnf::tree-listp))
  :returns (mv (trees abnf::tree-list-resultp
                      :hints
                      (("Goal"
                        :in-theory
                        (enable
                         abnf::treep-when-tree-resultp-and-not-reserrp
                         abnf::tree-listp-when-tree-list-resultp-and-not-reserrp))))
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a @('*constraint')."
  (b* (((mv tree token-after-constraint input-after-constraint)
        (parse-constraint token input))
       ((when (reserrp tree))
        ;; no constraints found in this call
        (mv nil
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input)))
       ((pok trees) (parse-*-constraint token-after-constraint
                                        input-after-constraint)))
    (mv (cons tree trees) token input))
  :measure (parsize token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-*-constraint-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

(define parse-system ((input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a PFCS @('system')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level function that organizes a list of tokens
     into a PFCS @('system') CST.
     We get the first token (if any), then
     we parse zero or more definitions followed by zero or more constraints
     that may use those definitions,
     and return a CST.
     If there is no error, there should be no next token and no remaining
     input, and that should be checked by the caller.")
   (xdoc::p
    "Since @('definition') is the only construct using the operator
     @(':=') and is the only construct using the the separator @('}')
     with which it terminates the definition, it is safe and
     unambiguous to first try to parse as many definitions as possible
     and then to parse the constraints."))
  (b* (((mv token input) (parse-token input))
       ((pok trees1) (parse-*-definition token input))
       ((pok trees2) (parse-*-constraint token input)))
       ;; Anything left over is an error; we check that from parse-pfcs.

    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "system")
         :branches (list trees1
                         trees2))
        token input))
  :hooks (:fix))
