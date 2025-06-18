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

(include-book "lexing")

(include-book "../definition/parser-interface")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tools to test the ACL2 parser of Leo.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that parsing the next token in (append input1 input2)
; consumes input1 (which may include some preceding non-tokens),
; returns a token CST,
; returns a list of lexeme CSTs whose fringe is input1
; and whose rightmost lexeme is the token (we just equate the fringes),
; and returns input2 as remaining input.

(defmacro test-parse-token (input1 input2 &optional token-type)
  `(assert-event
    (b* ((input1 (input-to-unicode-points ,input1))
         (input2 (input-to-unicode-points ,input2))
         (input12 (append input1 input2))
         (lexed1 (lexemize-leo input1))
         (lexed12 (lexemize-leo input12))
         ;; Both the first string and the appended strings must lex OK.
         ((when (reserrp lexed1)) nil)
         ((when (reserrp lexed12)) nil)
         (tokenized1 (filter-and-lower-tokens lexed1))
         (tokenized12 (filter-and-lower-tokens lexed12))
         ;; Both the first string and the appended strings must have at least
         ;; one token and then we check they are the same token.
         ((when (or (reserrp tokenized1) (null tokenized1))) nil)
         ((when (or (reserrp tokenized12) (null tokenized12))) nil)
         ((mv token1 rest1) (parse-token tokenized1))
         ((mv token12 rest12) (parse-token tokenized12)))
      (and (equal token1 token12)
           (null rest1)
           (if (stringp ,token-type)
               (abnf-tree-with-root-p token1 ,token-type)
             (or (abnf-tree-with-root-p token1 "keyword")
                 (abnf-tree-with-root-p token1 "identifier")
                 (abnf-tree-with-root-p token1 "atomic-literal")
                 (abnf-tree-with-root-p token1 "numeral")
                 (abnf-tree-with-root-p token1 "annotation")
                 (abnf-tree-with-root-p token1 "symbol")))
           (abnf-tree-list-with-root-p lexed1 "lexeme")
           (abnf-tree-list-with-root-p lexed12 "lexeme")
           (prefixp lexed1 lexed12)
           (prefixp tokenized1 tokenized12)
           (prefixp rest1 rest12)

           (equal (abnf::tree-list->string (nthcdr (len lexed1) lexed12))
                  input2)

           (equal (abnf::tree->string token1)
                  (abnf::tree->string (car (last lexed1))))
           (equal (abnf::tree-list->string lexed1) input1)
           (equal (abnf::tree-list->string lexed12) input12)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse a keyword in full,
; i.e. ensuring that all the input is consumed.
; The keyword may be preceded and followed by non-tokens,
; which are also consumed.
; Return the keyword CST and the lexeme CSTs if successful.

(define parse-full-keyword ((keyword stringp) (input nat-listp))
  :guard (member-equal keyword *keywords*)
  :returns (mv (tree abnf::tree-resultp)
               (ret-lexemes abnf::tree-listp))
  (b* ((lexemes (lexemize-leo input))
       ((when (or (reserrp lexemes) (null lexemes)))
        (mv (reserrf (list :lexing-failed-or-yielded-no-lexemes lexemes)) nil))
       (tokens (filter-and-lower-tokens lexemes))
       ((when (or (reserrp tokens) (null tokens)))
        (mv (reserrf (list :tokenizing-failed-or-yielded-no-tokens tokens)) nil))
       (first-token (first tokens))
       ((unless (abnf::treep first-token))
        (mv (reserrf (list :bad-first-token first-token)) nil))
       (rest-tokens (rest tokens))
       ((unless (abnf::tree-listp rest-tokens))
        (mv (reserrf (list :bad-rest-tokens rest-tokens)) nil))
       ((mv tree next rest)
        (parse-keyword keyword first-token rest-tokens))
       ((when (reserrp tree))
        (mv (reserrf (list :keyword-parse-failed tree)) lexemes))
       ((when next)
        (mv (reserrf (list :extra-token next)) lexemes))
       ((when rest)
        (mv (reserrf (list :extra-input rest)) lexemes)))
    (mv tree (abnf::tree-list-fix lexemes))))

;;;;;;;;;;;;;;;;;;;;

; Check that parsing a keyword succeeds.
; We check that the CST is a leaf one,
; that the lexemes are lexeme CSTs with the input as fringe.

(defmacro test-parse-keyword (keyword input)
  `(assert-event
    (b* ((input (input-to-unicode-points ,input))
         ((mv tree lexemes) (parse-full-keyword ,keyword input)))
      (and (abnf::tree-case tree :leafterm)
           (abnf-tree-list-with-root-p lexemes "lexeme")
           (equal (abnf::tree-list->string lexemes) input)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse a symbol in full,
; i.e. ensuring that all the input is consumed.
; The symbol may be preceded and followed by non-tokens,
; which are also consumed.
; Return the symbol CST and the lexeme CSTs if successful.

(define parse-full-symbol ((symbol stringp) (input nat-listp))
  :guard (member-equal symbol *symbols*)
  :returns (mv (tree abnf::tree-resultp)
               (ret-lexemes abnf::tree-listp))
  (b* ((lexemes (lexemize-leo input))
       ((when (or (reserrp lexemes) (null lexemes)))
        (mv (reserrf (list :lexing-failed-or-yielded-no-lexemes lexemes)) nil))
       (tokens (filter-and-lower-tokens lexemes))
       ((when (or (reserrp tokens) (null tokens)))
        (mv (reserrf (list :tokenizing-failed-or-yielded-no-tokens tokens)) nil))
       (first-token (first tokens))
       ((unless (abnf::treep first-token))
        (mv (reserrf (list :bad-first-token first-token)) nil))
       (rest-tokens (rest tokens))
       ((unless (abnf::tree-listp rest-tokens))
        (mv (reserrf (list :bad-rest-tokens rest-tokens)) nil))
       ((mv tree next rest)
        (parse-symbol symbol first-token rest-tokens))
       ((when (reserrp tree))
        (mv (reserrf (list :symbol-parse-failed tree)) lexemes))
       ((when next)
        (mv (reserrf (list :extra-token next)) lexemes))
       ((when rest)
        (mv (reserrf (list :extra-input rest)) lexemes)))
    (mv tree (abnf::tree-list-fix lexemes))))

;;;;;;;;;;;;;;;;;;;;

; Check that parsing a symbol succeeds.
; We check that the CST is a leaf one,
; that the lexemes are lexeme CSTs with the input as fringe.

(defmacro test-parse-symbol (symbol input)
  `(assert-event
    (b* ((input (input-to-unicode-points ,input))
         ((mv tree lexemes) (parse-full-symbol ,symbol input)))
      (and (abnf::tree-case tree :leafterm)
           (abnf-tree-list-with-root-p lexemes "lexeme")
           (equal (abnf::tree-list->string lexemes) input)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse a construct in full,
; i.e. ensuring that all the input is consumed.
; There may be non-tokens preceding and following the construct,
; and non-tokens between the tokens that form the construct
; if the construct consists of multiple tokens;
; all these non-tokens are consumed as well,
; in particular any leading and trailing ones.
; The construct to parse is determined by the argument parsing function.
; Return the construct CST and the lexeme CSTs if successful.
;
; NOTE: the parse-fn may now be something that can consume zero tokens,
; as long as the input has zero tokens.  For example, parse-*-comma-expression.

(defmacro parse-full (parse-fn input)
  `(b* ((__function__ 'parse-full)
        (lexemes (lexemize-leo ,input))
        ((when (reserrp lexemes)) ; allow a construct that has no lexemes
         (mv (reserrf (list :lexing-failed lexemes)) nil))
        (tokens (filter-and-lower-tokens lexemes))
        ((when (reserrp tokens)) ; allow a construct that has no tokens
         (mv (reserrf (list :tokenizing-failed tokens)) nil))

        (first-token (if (null tokens) nil
                       (first tokens)))
        ((when (and (not (null tokens))
                    (not (abnf::treep first-token))))
         (mv (reserrf (list :bad-first-token first-token)) nil))
        (rest-tokens (if (null tokens) nil
                       (rest tokens)))
        ((unless (abnf::tree-listp rest-tokens))
         (mv (reserrf (list :bad-rest-tokens rest-tokens)) nil))

        ((mv tree next rest) (,parse-fn first-token rest-tokens))
        ((when (reserrp tree))
         (mv (reserrf (list :symbol-parse-failed tree)) nil))
        ((when next)
         (mv (reserrf (list :extra-token next)) nil))
        ((when rest)
         (mv (reserrf (list :extra-input rest)) nil)))
     (mv tree lexemes)))

;;;;;;;;;;;;;;;;;;;;

; Check that parsing a construct defined by rulename in the grammar,
; with the corresponding parsing function passed as argument,
; succeeds.

(defmacro test-parse (parse-fn rulename input)
  `(assert-event
    (b* ((input (input-to-unicode-points ,input))
         ((mv tree lexemes) (parse-full ,parse-fn input)))
      (and (abnf-tree-with-root-p tree ,rulename)
           (abnf-tree-list-with-root-p lexemes "lexeme")
           (equal (abnf::tree-list->string lexemes) input)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that parsing a file succeeds consuming all the input.

(defmacro test-parse-file (input)
  `(assert-event
    (file-parses-same-fringe? ,input)
   ))

(defmacro test-parse-file-fail (input)
  `(assert-event
    (not (file-parses? ,input))))

;; Use a similar method for testing of parsing statements and expressions.
;; Note, this is not so much testing the parser as testing the parser-interface.
;; The -FAIL macros check fewer things, so that if the primary parse succeeds
;; but one of the extra checks fails we won't get a false negative.

(defmacro test-parse-statement (input)
  `(assert-event
    (statement-parses-same-fringe? ,input)
   ))

(defmacro test-parse-statement-fail (input)
  `(assert-event
    (not (statement-parses? ,input))))

(defmacro test-parse-expression (input)
  `(assert-event
    (expression-parses-same-fringe? ,input)
   ))

(defmacro test-parse-expression-fail (input)
  `(assert-event
    (not (expression-parses? ,input))))

;; The following allow any token type, which is not very discriminating.
;; The test-parse-token above allows specifying the token type,
;; makes sure the parsing stops when the token stops by supplying
;; a following string that should not be parsed,
;; and contains many checks on the results.  The definition here is a
;; more basic definition.

(defmacro test-parse-token-basic (input)
  `(assert-event
    (token-parses-same-fringe? ,input)
   ))

(defmacro test-parse-token-fail (input)
  `(assert-event
    (not (token-parses? ,input))))
