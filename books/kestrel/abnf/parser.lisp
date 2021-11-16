; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "concrete-syntax")
(include-book "parsing-primitives-seq")

(include-book "std/io/read-file-characters" :dir :system)

(local (include-book "kestrel/utilities/typed-lists/nat-list-fix-theorems" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-parser
  :parents (abnf)
  :short "A verified executable parser of ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "It may be possible to derive this parser from @(tsee parse-grammar*)
     (or a variant of it that resolves the ambiguity discussed there)
     via transformational refinements,
     but here we write an implementation directly
     and we prove its correctness.")
   (xdoc::p
    "The implementation and verification techniques employed for this parser
     seem more general than the parser.
     They should be applicable to parsers of other languages specified in ABNF,
     e.g. to HTTP parsers.
     It may also be possible to build a parser generator
     that turns ABNF grammars
     (satisfying certain restrictions, as with typical parser generators)
     into verified executable parsers,
     i.e. executable parsers accompanied by proofs of correctness."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-parser-implementation

  :parents (grammar-parser)

  :short "Implementation of the parser of ABNF grammars."

  :long

  (xdoc::topstring

   (xdoc::p
    "This is a recursive-descent, backtracking parser.
     There is a parsing function for every rule,
     and parsing functions for certain groups, options, and repetitions.
     There are also parameterized parsing functions for
     terminals (natural numbers) matching
     exact values, ranges, and (case-insensitively) characters.")

   (xdoc::h3 "Inputs and Outputs")

   (xdoc::p
    "Each of these parsing functions
     takes as input a list of natural numbers (i.e. terminals),
     and returns as outputs
     (i) an indication of success or failure,
     (ii) the tree or list of trees
     obtained from parsing a prefix of the input
     (or @('nil') if parsing fails),
     and (iii) the remaining suffix of the input that must still be parsed.
     The indication of success or failure is
     either @('nil') to indicate success,
     or a "
    (xdoc::seetopic "msg" "message")
    " to describe the failure.
     This is consistent with the <i>@(see Seq)</i> macros,
     with which these parsing functions are implemented.")

   (xdoc::p
    "The @(tsee parse-grammar) top-level function
     takes as input a list of natural numbers
     and returns as output just a tree, or @('nil') to indicate failure;
     this function consumes all the input, failing if there is unparsed input.
     The @(tsee parse-grammar-from-file) function
     takes as input a file name and calls @(tsee parse-grammar) on its content,
     returning a tree or @('nil').")

   (xdoc::p
    "Each parsing function definition is accompanied by a theorem stating that
     the function fixes its input list of natural numbers.
     The proof of each such theorem uses, as rewrite rules,
     the theorems for the parsing functions called by
     the parsing function whose theorem is being proved.")

   (xdoc::h3 "Disambiguation and Look-Ahead")

   (xdoc::p
    "As explained in the documentation of @(tsee parse-grammar*),
     the grammar of the ABNF concrete syntax [RFC:4] is ambiguous.
     The rule @('rulelist') allows strings `@('c-nl WSP')'
     either to be split into an ending @('c-nl') under a @('rule')
     and a starting @('WSP') under an immediately following @('(*c-wsp c-nl)'),
     or to be made into a @('c-wsp')
     in the ending part of @('elements') under the @('rule').
     The same kind of choice applies when,
     instead of a @('rule') immediately followed by a @('(*c-wsp c-nl)'),
     there are two subsequent @('(*c-wsp c-nl)')s:
     the string `@('c-nl WSP')' can be
     either split between the two @('(*c-wsp c-nl)')s
     or put all under the first one.
     Indeed, expanding @('elements') in the definiens of @('rule')
     gives @('... *c-wsp c-nl'),
     which ends in the same way as the group @('(*c-wsp c-nl)'):
     this is why the ambiguity applies equally to
     a @('rule') immediately followed by a @('(*c-wsp c-nl)')
     and to a @('(*c-wsp c-nl)')
     immediately followed by a @('(*c-wsp c-nl)').")

   (xdoc::p
    "Aside from the @('rulelist') rule,
     the rest of the grammar is LL(*):")

   (xdoc::ul

    (xdoc::li
     "In the @('repeat') rule,
      a look-ahead of an unbounded number of @('DIGIT')s
      is needed to determine the alternative
      (the second alternative if @('\"*\"') is found after the @('DIGIT')s,
      otherwise the first alternative).")

    (xdoc::li
     "In the @('concatenation') rule,
      a look-ahead of an unbounded number of @('c-wsp')s
      is needed to determine where a @('concatenation') ends
      (it does if no @('repetition') is found after the @('c-wsp')s,
      otherwise the @('concatenation')
      continues with the found @('repetition'))."))

   (xdoc::p
    "Aside from the @('rulelist'), @('repeat'), and @('concatenation') rules,
     the rest of the grammar is LL(2):")

   (xdoc::ul

    (xdoc::li
     "In the @('defined-as') rule,
      a look-ahead of two symbols
      is needed to distinguish @('\"=\"') and @('\"=/\"').")

    (xdoc::li
     "In the @('element') rule,
      a look-ahead of two symbols
      is needed to distinguish @('num-val') and @('char-val')
      (the two symbols are @('\"%\"') and the one after).")

    (xdoc::li
     "In the @('char-val') rule,
      a look-ahead of two symbols is needed
      to distinguish @('case-insensitive-string') and @('case-sensitive-string')
      (the two symbols are @('\"%\"') and the one after)."))

   (xdoc::p
    "In each of the three rules listed above,
     the two choices have the first character in common.
     Thus, it may seem that these rules are actually LL(1),
     by first parsing the first character in common
     and then deciding how to proceed based on the next character.
     However, each character pair like @('\"=/\"') and @('\"%s\"')
     is parsed in one shot via one call to @(tsee parse-ichars)
     which produces a single leaf tree
     with the list of those two character codes,
     not via two calls to @(tsee parse-ichar)
     which would produce two leaf trees
     each with a singleton list of one character code.
     If the rules were formulated as concatenations of single-character strings
     (e.g. @('\"=\" \"/\"') and @('\"%\" \"s\"')) instead,
     these rules would be LL(1).")

   (xdoc::p
    "Aside from the
     @('rulelist'),
     @('repeat'),
     @('concatenation'),
     @('defined-as'),
     @('element'), and
     @('char-val') rules,
     the rest of the grammar is LL(1).")

   (xdoc::p
    "The parser resolves the @('rulelist') ambiguity
     by keeping strings `@('c-nl WSP')' as @('c-wsp')s
     under @('rule') or
     under the first @('(*c-wsp c-nl)') of two subsequent @('(*c-wsp c-nl)')s,
     instead of splitting them into a @('c-nl')
     to end the @('rule') or
     to end the first @('(*c-wsp c-nl)') of two subsequent @('(*c-wsp c-nl)')s,
     and a @('WSP') to start the subsequent @('(*c-wsp c-nl)').
     The decision point is when a @('c-nl') is encountered
     while parsing the ending @('*c-wsp') of @('elements')
     or while parsing the @('*c-wsp') of a @('(*c-wsp c-nl)'):
     should the @('*c-wsp') be considered finished
     and the @('c-nl') used to end the @('rule') or @('(*c-wsp c-nl)'),
     or should the parser attempt to extend the @('*c-wsp')
     with an extra @('c-wsp'), if the @('c-nl') is followed by a @('WSP')?
     By having @(tsee parse-*cwsp) always try the extra @('c-wsp'),
     we never split strings `@('c-nl WSP')'.
     Thus, @(tsee parse-*cwsp) tries to parse as many @('c-wsp')s as possible,
     like all the other @('parse-*...') parsing functions.
     If the @('c-nl') is not followed by a @('WSP'),
     the parsing of the extra @('c-wsp') fails
     and the only possibility left is to finish the @('*c-wsp')
     and use the @('c-nl') to end the @('rule') or the @('(*c-wsp c-nl)');
     there is no ambiguity in this case.")

   (xdoc::p
    "The look-ahead for the LL(*), LL(2), and LL(1) rules
     is handled via backtracking.
     The amount of backtracking
     is expected to be small in reasonable grammars.")

   (xdoc::h3 "Termination")

   (xdoc::p
    "The termination of the singly recursive parsing functions
     (e.g. @(tsee parse-*bit))
     is proved by showing that the size of the input decreases.")

   (xdoc::p
    "The termination of the mutually recursive parsing functions
     (i.e. @(tsee parse-alternation), @(tsee parse-concatenation), etc.)
     is proved via a lexicographic measure consisting of
     the size of the input and an ordering of the parsing functions.
     This is explained in the following paragraphs.")

   (xdoc::p
    "Since @(tsee parse-alternation) calls @(tsee parse-concatenation)
     on the same input,
     the size of the input alone is not sufficient
     to show that the mutually recursive parsing functions terminate.
     But @(tsee parse-concatenation) never
     (indirectly) calls @(tsee parse-alternation) on the same input:
     it has to go through @(tsee parse-group) or @(tsee parse-option),
     which consume a @('\"(\"') or a @('\"[\"')
     before calling @(tsee parse-alternation) on, therefore, a smaller input.
     So if we order the parsing functions, by assigning numbers to them,
     so that @(tsee parse-alternation) has
     a larger order number than @(tsee parse-concatenation),
     either the size of the input goes down,
     or it stays the same but the parsing function order number goes down.
     In other words, the lexicographic measure goes down.")

   (xdoc::p
    "To establish the relative ordering of the parsing functions,
     we look at which ones (may) call which other ones on the same input:
     the former must be (assigned) larger (order numbers) than the latter.
     Thus, we have the following ordering constraints:")

   (xdoc::ul

    (xdoc::li
     "@(tsee parse-alternation) must be
      larger than @(tsee parse-concatenation).")

    (xdoc::li
     "@(tsee parse-concatenation) must be
      larger than @(tsee parse-repetition).")

    (xdoc::li
     "@(tsee parse-repetition) must be larger than @(tsee parse-element).
      (The former calls the latter on the same input
      if @(tsee parse-?repeat) does not consume any input.)")

    (xdoc::li
     "@(tsee parse-element) must be larger than @(tsee parse-group).")

    (xdoc::li
     "@(tsee parse-element) must be larger than @(tsee parse-option).")

    (xdoc::li
     "@(tsee parse-alt-rest) must be larger than
      @(tsee parse-alt-rest-comp).")

    (xdoc::li
     "@(tsee parse-conc-rest) must be larger than
      @(tsee parse-conc-rest-comp)."))

   (xdoc::p
    "These constraints provide a partial order on the parsing function,
     which we can totalize as follows (from smallest to largest):")

   (xdoc::ol
    (xdoc::li "@(tsee parse-conc-rest-comp)")
    (xdoc::li "@(tsee parse-conc-rest)")
    (xdoc::li "@(tsee parse-alt-rest-comp)")
    (xdoc::li "@(tsee parse-alt-rest)")
    (xdoc::li "@(tsee parse-option)")
    (xdoc::li "@(tsee parse-group)")
    (xdoc::li "@(tsee parse-element)")
    (xdoc::li "@(tsee parse-repetition)")
    (xdoc::li "@(tsee parse-concatenation)")
    (xdoc::li "@(tsee parse-alternation)"))

   (xdoc::p
    "Note that when a smaller function calls a larger or equal function,
     it does so on a smaller input.
     In particular:
     @(tsee parse-group) and @(tsee parse-option) call @(tsee parse-alternation)
     only after consuming a @('\"(\"') or a @('\"[\"');
     @(tsee parse-alt-rest-comp) calls @(tsee parse-concatenation)
     only after consuming at least a @('\"\/\"'); and
     @(tsee parse-conc-rest-comp) calls @(tsee parse-repetition)
     only after consuming at least one @('c-wsp'), which is never empty.")

   (xdoc::p
    "The theorems about input lengths
     that accompany the parsing function definitions
     are used in the termination proofs,
     both of the singly recursive functions
     and of the mutually recursive functions."))

  :order-subtopics t)

(defval *grammar-parser-error-msg*
  :parents (grammar-parser-implementation)
  :short "Message for grammar parsing errors."
  :long
  (xdoc::topstring-p
   "This message does not carry a lot of information,
    but it keeps the grammar parser simpler for now.")
  (msg "ABNF Grammar Parser Error.~%")
  ///

  (defruled msgp-of-*grammar-parser-error-msg*
    (msgp *grammar-parser-error-msg*)))

(define parse-in-either-range ((min1 natp) (max1 natp)
                               (min2 natp) (max2 natp)
                               (input nat-listp))
  :guard (and (<= min1 max1)
              (< max1 min2)
              (<= min2 max2))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a natural number in one of two given ranges
          into a tree that matches
          a group consisting of
          an alternation of
          the corresponding range numeric value notations."
  (seq-backtrack input
                 ((tree := (parse-in-range min1 max1 input))
                  (return (make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree)))))
                 ((tree := (parse-in-range min2 max2 input))
                  (return (make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree))))))
  :no-function t
  ///

  (fty::deffixequiv parse-in-either-range
    :args ((input nat-listp)))

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-in-either-range-linear
               :rule-classes :linear)))

(define parse-*-in-either-range ((min1 natp) (max1 natp)
                                 (min2 natp) (max2 natp)
                                 (input nat-listp))
  :guard (and (<= min1 max1)
              (< max1 min2)
              (<= min2 max2))
  :returns (mv (error? not)
               (trees tree-listp)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse zero or more natural numbers,
          each of which in one of two given ranges,
          into a list of trees that matches
          the repetition of zero or more alternations
          of the corresponding range numeric value notations."
  (seq-backtrack
   input
   ((tree := (parse-in-either-range min1 max1 min2 max2 input))
    (trees := (parse-*-in-either-range min1 max1 min2 max2 input))
    (return (cons tree trees)))
   ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  ///

  (fty::deffixequiv parse-*-in-either-range
    :args ((input nat-listp)))

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*-in-either-range-linear
               :rule-classes :linear)))

(define parse-ichar ((char characterp) (input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a natural number
          that encodes, case-insensitively, a given character,
          into a tree that matches
          a case-insensitive character value notation
          that consists of that character."
  (b* (((mv error? nat input) (parse-any input))
       ((when error?) (mv error? nil input))
       ((unless (nat-match-insensitive-char-p nat char))
        (mv *grammar-parser-error-msg* nil (cons nat input))))
    (mv nil (tree-leafterm (list nat)) input))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-ichar-linear
               :rule-classes :linear)))

(define parse-ichars ((char1 characterp) (char2 characterp) (input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse two natural numbers
          that encode, case-insensitively, two given characters,
          into a tree that matches
          a case-insensitive character value notation
          that consists of those two characters."
  (b* (((mv error? nat1 input) (parse-any input))
       ((when error?) (mv error? nil input))
       ((unless (nat-match-insensitive-char-p nat1 char1))
        (mv *grammar-parser-error-msg* nil (cons nat1 input)))
       ((mv error? nat2 input) (parse-any input))
       ((when error?) (mv error? nil input))
       ((unless (nat-match-insensitive-char-p nat2 char2))
        (mv *grammar-parser-error-msg* nil (cons nat2 input))))
    (mv nil (tree-leafterm (list nat1 nat2)) input))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-ichars-linear
               :rule-classes :linear)))

(define parse-alpha ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a letter."
  (seq-backtrack input
                 ((tree := (parse-in-range #x41 #x5a input))
                  (return (make-tree-nonleaf :rulename? *alpha*
                                             :branches (list (list tree)))))
                 ((tree := (parse-in-range #x61 #x7a input))
                  (return (make-tree-nonleaf :rulename? *alpha*
                                             :branches (list (list tree))))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-alpha-linear
               :rule-classes :linear)))

(define parse-bit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a bit."
  (seq-backtrack input
                 ((tree := (parse-ichar #\0 input))
                  (return (make-tree-nonleaf :rulename? *bit*
                                             :branches (list (list tree)))))
                 ((tree := (parse-ichar #\1 input))
                  (return (make-tree-nonleaf :rulename? *bit*
                                             :branches (list (list tree))))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-bit-linear
               :rule-classes :linear)))

(define parse-cr ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a carriage return."
  (seq input
       (tree := (parse-exact #x0d input))
       (return (make-tree-nonleaf :rulename? *cr*
                                  :branches (list (list tree)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-cr-linear
               :rule-classes :linear)))

(define parse-digit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a decimal digit."
  (seq input
       (tree := (parse-in-range #x30 #x39 input))
       (return (make-tree-nonleaf :rulename? *digit*
                                  :branches (list (list tree)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-digit-linear
               :rule-classes :linear)))

(define parse-dquote ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a double quote."
  (seq input
       (tree := (parse-exact #x22 input))
       (return
        (make-tree-nonleaf :rulename? *dquote* :branches (list (list tree)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dquote-linear
               :rule-classes :linear)))

(define parse-htab ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a horizontal tab."
  (seq input
       (tree := (parse-exact #x09 input))
       (return (make-tree-nonleaf :rulename? *htab*
                                  :branches (list (list tree)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-htab-linear
               :rule-classes :linear)))

(define parse-lf ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a line feed."
  (seq input
       (tree := (parse-exact #x0a input))
       (return (make-tree-nonleaf :rulename? *lf*
                                  :branches (list (list tree)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-lf-linear
               :rule-classes :linear)))

(define parse-sp ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a space."
  (seq input
       (tree := (parse-exact #x20 input))
       (return (make-tree-nonleaf :rulename? *sp*
                                  :branches (list (list tree)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-sp-linear
               :rule-classes :linear)))

(define parse-vchar ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a visible character."
  (seq input
       (tree := (parse-in-range #x21 #x7e input))
       (return
        (make-tree-nonleaf :rulename? *vchar* :branches (list (list tree)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-vchar-linear
               :rule-classes :linear)))

(define parse-crlf ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a carriage return followed by a line feed."
  (seq input
       (tree-cr := (parse-cr input))
       (tree-lf := (parse-lf input))
       (return
        (make-tree-nonleaf :rulename? *crlf* :branches (list (list tree-cr)
                                                             (list tree-lf)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-crlf-linear
               :rule-classes :linear)))

(define parse-hexdig ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a hexadecimal digit."
  (seq-backtrack
   input
   ((tree := (parse-digit input))
    (return (make-tree-nonleaf :rulename? *hexdig*
                               :branches (list (list tree)))))
   ((tree := (parse-ichar #\A input))
    (return (make-tree-nonleaf :rulename? *hexdig*
                               :branches (list (list tree)))))
   ((tree := (parse-ichar #\B input))
    (return (make-tree-nonleaf :rulename? *hexdig*
                               :branches (list (list tree)))))
   ((tree := (parse-ichar #\C input))
    (return (make-tree-nonleaf :rulename? *hexdig*
                               :branches (list (list tree)))))
   ((tree := (parse-ichar #\D input))
    (return (make-tree-nonleaf :rulename? *hexdig*
                               :branches (list (list tree)))))
   ((tree := (parse-ichar #\E input))
    (return (make-tree-nonleaf :rulename? *hexdig*
                               :branches (list (list tree)))))
   ((tree := (parse-ichar #\F input))
    (return (make-tree-nonleaf :rulename? *hexdig*
                               :branches (list (list tree))))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-hexdig-linear
               :rule-classes :linear)))

(define parse-wsp ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a space or horizontal tab."
  (seq-backtrack
   input
   ((tree := (parse-sp input))
    (return (make-tree-nonleaf :rulename? *wsp* :branches (list (list tree)))))
   ((tree := (parse-htab input))
    (return (make-tree-nonleaf :rulename? *wsp* :branches (list (list tree))))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-wsp-linear
               :rule-classes :linear)))

(define parse-prose-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a prose value notation."
  (seq input
       (tree-open-angle := (parse-ichar #\< input))
       (trees-text := (parse-*-in-either-range #x20 #x3d #x3f #x7e input))
       (tree-close-angle := (parse-ichar #\> input))
       (return
        (make-tree-nonleaf :rulename? *prose-val*
                           :branches (list (list tree-open-angle)
                                           trees-text
                                           (list tree-close-angle)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-prose-val-linear
               :rule-classes :linear)))

(define parse-*bit ((input nat-listp))
  :returns (mv (error? not)
               (trees tree-listp)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition of zero or more bits."
  (seq-backtrack input
                 ((tree := (parse-bit input))
                  (trees := (parse-*bit input))
                  (return (cons tree trees)))
                 ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*bit-linear
               :rule-classes :linear)))

(define parse-*digit ((input nat-listp))
  :returns (mv (error? not)
               (trees tree-listp)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition of zero or more decimal digits."
  (seq-backtrack input
                 ((tree := (parse-digit input))
                  (trees := (parse-*digit input))
                  (return (cons tree trees)))
                 ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*digit-linear
               :rule-classes :linear)))

(define parse-*hexdig ((input nat-listp))
  :returns (mv (error? not)
               (trees tree-listp)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition of zero or more hexadecimal digits."
  (seq-backtrack input
                 ((tree := (parse-hexdig input))
                  (trees := (parse-*hexdig input))
                  (return (cons tree trees)))
                 ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*hexdig-linear
               :rule-classes :linear)))

(define parse-1*bit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (tree-listp trees)
                           (implies error? (not trees))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition of one or more bits."
  (seq input
       (tree := (parse-bit input))
       (trees := (parse-*bit input))
       (return (cons tree trees)))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*bit-linear
               :rule-classes :linear)))

(define parse-1*digit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (tree-listp trees)
                           (implies error? (not trees))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition of one or more decimal digits."
  (seq input
       (tree := (parse-digit input))
       (trees := (parse-*digit input))
       (return (cons tree trees)))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*digit-linear
               :rule-classes :linear)))

(define parse-1*hexdig ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (tree-listp trees)
                           (implies error? (not trees))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition of one or more hexadecimal digits."
  (seq input
       (tree := (parse-hexdig input))
       (trees := (parse-*hexdig input))
       (return (cons tree trees)))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*hexdig-linear
               :rule-classes :linear)))

(define parse-dot-1*bit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a group @('(\".\" 1*BIT)')."
  (seq input
       (tree := (parse-ichar #\. input))
       (trees := (parse-1*bit input))
       (return
        (make-tree-nonleaf :rulename? nil :branches (list (list tree) trees))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dot-*1bit-linear
               :rule-classes :linear)))

(define parse-dot-1*digit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a group @('(\".\" 1*DIGIT)')."
  (seq input
       (tree := (parse-ichar #\. input))
       (trees := (parse-1*digit input))
       (return
        (make-tree-nonleaf :rulename? nil :branches (list (list tree) trees))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dot-*1digit-linear
               :rule-classes :linear)))

(define parse-dot-1*hexdig ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a group @('(\".\" 1*HEXDIG)')."
  (seq input
       (tree := (parse-ichar #\. input))
       (trees := (parse-1*hexdig input))
       (return
        (make-tree-nonleaf :rulename? nil :branches (list (list tree) trees))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dot-*1hexdig-linear
               :rule-classes :linear)))

(define parse-dash-1*bit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a group @('(\"-\" 1*BIT)')."
  (seq input
       (tree := (parse-ichar #\- input))
       (trees := (parse-1*bit input))
       (return
        (make-tree-nonleaf :rulename? nil :branches (list (list tree) trees))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dash-*1bit-linear
               :rule-classes :linear)))

(define parse-dash-1*digit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a group @('(\"-\" 1*DIGIT)')."
  (seq input
       (tree := (parse-ichar #\- input))
       (trees := (parse-1*digit input))
       (return
        (make-tree-nonleaf :rulename? nil :branches (list (list tree) trees))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dash-*1digit-linear
               :rule-classes :linear)))

(define parse-dash-1*hexdig ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a group @('(\"-\" 1*HEXDIG)')."
  (seq input
       (tree := (parse-ichar #\- input))
       (trees := (parse-1*hexdig input))
       (return
        (make-tree-nonleaf :rulename? nil :branches (list (list tree) trees))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dash-*1hexdig-linear
               :rule-classes :linear)))

(define parse-*-dot-1*bit ((input nat-listp))
  :returns (mv (error? not)
               (trees tree-listp)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition @('*(\".\" 1*BIT)')."
  (seq-backtrack
   input
   ((tree := (parse-dot-1*bit input))
    (trees := (parse-*-dot-1*bit input))
    (return (cons tree trees)))
   ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*-dot-*1bit-linear
               :rule-classes :linear)))

(define parse-*-dot-1*digit ((input nat-listp))
  :returns (mv (error? not)
               (trees tree-listp)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition @('*(\".\" 1*DIGIT)')."
  (seq-backtrack
   input
   ((tree := (parse-dot-1*digit input))
    (trees := (parse-*-dot-1*digit input))
    (return (cons tree trees)))
   ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*-dot-*1digit-linear
               :rule-classes :linear)))

(define parse-*-dot-1*hexdig ((input nat-listp))
  :returns (mv (error? not)
               (trees tree-listp)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition @('*(\".\" 1*HEXDIG)')."
  (seq-backtrack
   input
   ((tree := (parse-dot-1*hexdig input))
    (trees := (parse-*-dot-1*hexdig input))
    (return (cons tree trees)))
   ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*-dot-*1hexdig-linear
               :rule-classes :linear)))

(define parse-1*-dot-1*bit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (tree-listp trees)
                           (implies error? (not trees))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition @('1*(\".\" 1*BIT)')."
  (seq input
       (tree := (parse-dot-1*bit input))
       (trees := (parse-*-dot-1*bit input))
       (return (cons tree trees)))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*-dot-1*bit-linear
               :rule-classes :linear)))

(define parse-1*-dot-1*digit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (tree-listp trees)
                           (implies error? (not trees))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition @('1*(\".\" 1*DIGIT)')."
  (seq input
       (tree := (parse-dot-1*digit input))
       (trees := (parse-*-dot-1*digit input))
       (return (cons tree trees)))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*-dot-1*digit-linear
               :rule-classes :linear)))

(define parse-1*-dot-1*hexdig ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (tree-listp trees)
                           (implies error? (not trees))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition @('1*(\".\" 1*HEXDIG)')."
  (seq input
       (tree := (parse-dot-1*hexdig input))
       (trees := (parse-*-dot-1*hexdig input))
       (return (cons tree trees)))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*-dot-1*hexdig-linear
               :rule-classes :linear)))

(define parse-bin-val-rest ((input nat-listp))
  :returns (mv (error? not)
               (tree treep)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse an option @('[ 1*(\".\" 1*BIT) / (\"-\" 1*BIT) ]'),
          which is the rest of the definiens of @('bin-val')."
  (seq-backtrack
   input
   ((trees := (parse-1*-dot-1*bit input))
    (return (make-tree-nonleaf :rulename? nil :branches (list trees))))
   ((tree := (parse-dash-1*bit input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree)))))
   ((return-raw (mv nil
                    (make-tree-nonleaf :rulename? nil :branches nil)
                    (nat-list-fix input)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-bin-val-rest-linear
               :rule-classes :linear)))

(define parse-dec-val-rest ((input nat-listp))
  :returns (mv (error? not)
               (tree treep)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse an option @('[ 1*(\".\" 1*DIGIT) / (\"-\" 1*DIGIT) ]'),
          which is the rest of the definiens of @('dec-val')."
  (seq-backtrack
   input
   ((trees := (parse-1*-dot-1*digit input))
    (return (make-tree-nonleaf :rulename? nil :branches (list trees))))
   ((tree := (parse-dash-1*digit input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree)))))
   ((return-raw (mv nil
                    (make-tree-nonleaf :rulename? nil :branches nil)
                    (nat-list-fix input)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-dec-val-rest-linear
               :rule-classes :linear)))

(define parse-hex-val-rest ((input nat-listp))
  :returns (mv (error? not)
               (tree treep)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse an option @('[ 1*(\".\" 1*HEXDIG) / (\"-\" 1*HEXDIG) ]'),
          which is the rest of the definiens of @('hex-val')."
  (seq-backtrack
   input
   ((trees := (parse-1*-dot-1*hexdig input))
    (return (make-tree-nonleaf :rulename? nil :branches (list trees))))
   ((tree := (parse-dash-1*hexdig input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree)))))
   ((return-raw (mv nil
                    (make-tree-nonleaf :rulename? nil :branches nil)
                    (nat-list-fix input)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-hex-val-rest-linear
               :rule-classes :linear)))

(define parse-bin-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a binary numeric value notation."
  (seq input
       (tree := (parse-ichar #\b input))
       (trees := (parse-1*bit input))
       (tree-rest := (parse-bin-val-rest input))
       (return
        (make-tree-nonleaf :rulename? *bin-val*
                           :branches (list (list tree)
                                           trees
                                           (list tree-rest)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name parse-bin-val-linear
               :rule-classes :linear)))

(define parse-dec-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a decimal numeric value notation."
  (seq input
       (tree := (parse-ichar #\d input))
       (trees := (parse-1*digit input))
       (tree-rest := (parse-dec-val-rest input))
       (return
        (make-tree-nonleaf :rulename? *dec-val*
                           :branches (list (list tree)
                                           trees
                                           (list tree-rest)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dec-val-linear
               :rule-classes :linear)))

(define parse-hex-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a hexadecimal numeric value notation."
  (seq input
       (tree := (parse-ichar #\x input))
       (trees := (parse-1*hexdig input))
       (tree-rest := (parse-hex-val-rest input))
       (return
        (make-tree-nonleaf :rulename? *hex-val*
                           :branches (list (list tree)
                                           trees
                                           (list tree-rest)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-hex-val-linear
               :rule-classes :linear)))

(define parse-bin/dec/hex-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a group @('(bin-val / dec-val / hex-val)')."
  (seq-backtrack
   input
   ((tree := (parse-bin-val input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree)))))
   ((tree := (parse-dec-val input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree)))))
   ((tree := (parse-hex-val input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree))))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-bin/dec/hex-val-linear
               :rule-classes :linear)))

(define parse-num-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a numeric value notation."
  (seq input
       (tree-% := (parse-ichar #\% input))
       (tree-val := (parse-bin/dec/hex-val input))
       (return
        (make-tree-nonleaf :rulename? *num-val*
                           :branches (list (list tree-%) (list tree-val)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-num-val-linear
               :rule-classes :linear)))

(define parse-quoted-string ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a quoted string."
  (seq input
       (tree-open-quote := (parse-dquote input))
       (trees := (parse-*-in-either-range #x20 #x21 #x23 #x7e input))
       (tree-close-quote := (parse-dquote input))
       (return (make-tree-nonleaf :rulename? *quoted-string*
                                  :branches (list (list tree-open-quote)
                                                  trees
                                                  (list tree-close-quote)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-quoted-string-linear
               :rule-classes :linear)))

(define parse-?%i ((input nat-listp))
  :returns (mv (error? not)
               (tree treep)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse an option @('[ \"%i\" ]')."
  (seq-backtrack
   input
   ((tree := (parse-ichars #\% #\i input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree)))))
   ((return-raw (mv nil
                    (make-tree-nonleaf :rulename? nil :branches nil)
                    (nat-list-fix input)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-?%i-rest-linear
               :rule-classes :linear)))

(define parse-case-insensitive-string ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a case-insensitive character value notation."
  (seq input
       (tree-%i := (parse-?%i input))
       (tree-qstring := (parse-quoted-string input))
       (return (make-tree-nonleaf :rulename? *case-insensitive-string*
                                  :branches (list (list tree-%i)
                                                  (list tree-qstring)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-case-insensitive-string-linear
               :rule-classes :linear)))

(define parse-case-sensitive-string ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a case-sensitive character value notation."
  (seq input
       (tree-%s := (parse-ichars #\% #\s input))
       (tree-qstring := (parse-quoted-string input))
       (return (make-tree-nonleaf :rulename? *case-sensitive-string*
                                  :branches (list (list tree-%s)
                                                  (list tree-qstring)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-case-sensitive-string-linear
               :rule-classes :linear)))

(define parse-char-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a character value notation."
  (seq-backtrack
   input
   ((tree := (parse-case-insensitive-string input))
    (return (make-tree-nonleaf :rulename? *char-val*
                               :branches (list (list tree)))))
   ((tree := (parse-case-sensitive-string input))
    (return (make-tree-nonleaf :rulename? *char-val*
                               :branches (list (list tree))))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-char-val-linear
               :rule-classes :linear)))

(define parse-wsp/vchar ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a group @('(WSP / VCHAR)')."
  (seq-backtrack
   input
   ((tree := (parse-wsp input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree)))))
   ((tree := (parse-vchar input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree))))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-wsp/vchar-linear
               :rule-classes :linear)))

(define parse-*wsp/vchar ((input nat-listp))
  :returns (mv (error? not)
               (trees tree-listp)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition @('*(WSP / VCHAR)')."
  (seq-backtrack input
                 ((tree := (parse-wsp/vchar input))
                  (trees := (parse-*wsp/vchar input))
                  (return (cons tree trees)))
                 ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*wsp/vchar-linear
               :rule-classes :linear)))

(define parse-comment ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a comment."
  (seq input
       (tree-semicolon := (parse-ichar #\; input))
       (trees-text := (parse-*wsp/vchar input))
       (tree-crlf := (parse-crlf input))
       (return (make-tree-nonleaf :rulename? *comment*
                                  :branches (list (list tree-semicolon)
                                                  trees-text
                                                  (list tree-crlf)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-comment-linear
               :rule-classes :linear)))

(define parse-cnl ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a comment or new line."
  (seq-backtrack
   input
   ((tree := (parse-comment input))
    (return (make-tree-nonleaf :rulename? *c-nl*
                               :branches (list (list tree)))))
   ((tree := (parse-crlf input))
    (return (make-tree-nonleaf :rulename? *c-nl*
                               :branches (list (list tree))))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-cnl-linear
               :rule-classes :linear)))

(define parse-cnl-wsp ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a group @('(c-nl WSP)')."
  (seq input
       (tree-cnl := (parse-cnl input))
       (tree-wsp := (parse-wsp input))
       (return (make-tree-nonleaf :rulename? nil
                                  :branches (list (list tree-cnl)
                                                  (list tree-wsp)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-cnl-wsp-linear
               :rule-classes :linear)))

(define parse-cwsp ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse either white space,
          or a comment and new line followed by white space."
  (seq-backtrack
   input
   ((tree := (parse-wsp input))
    (return (make-tree-nonleaf :rulename? *c-wsp*
                               :branches (list (list tree)))))
   ((tree := (parse-cnl-wsp input))
    (return (make-tree-nonleaf :rulename? *c-wsp*
                               :branches (list (list tree))))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-cwsp-linear
               :rule-classes :linear)))

(define parse-*cwsp ((input nat-listp))
  :returns (mv (error? not)
               (trees tree-listp)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition of zero or more @('c-wsp')s."
  (seq-backtrack input
                 ((tree := (parse-cwsp input))
                  (trees := (parse-*cwsp input))
                  (return (cons tree trees)))
                 ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*cwsp-linear
               :rule-classes :linear)))

(define parse-1*cwsp ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (tree-listp trees)
                           (implies error? (not trees))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition of one or more @('c-wsp')s."
  (seq input
       (tree := (parse-cwsp input))
       (trees := (parse-*cwsp input))
       (return (cons tree trees)))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*cwsp-linear
               :rule-classes :linear)))

(define parse-*digit-star-*digit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a group @('(*DIGIT \"*\" *DIGIT)')."
  (seq input
       (trees1 := (parse-*digit input))
       (tree := (parse-ichar #\* input))
       (trees2 := (parse-*digit input))
       (return (make-tree-nonleaf :rulename? nil :branches (list trees1
                                                                 (list tree)
                                                                 trees2))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-*digit-star-*digit-linear
               :rule-classes :linear)))

(define parse-repeat ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition range."
  :long
  (xdoc::topstring-p
   "Since a non-empty sequence of digits matches
    both @('1*DIGIT')
    and the start of @('(*DIGIT \"*\" *DIGIT)'),
    the latter is tried before the former.")
  (seq-backtrack
   input
   ((tree := (parse-*digit-star-*digit input))
    (return (make-tree-nonleaf :rulename? *repeat*
                               :branches (list (list tree)))))
   ((trees := (parse-1*digit input))
    (return (make-tree-nonleaf :rulename? *repeat* :branches (list trees)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-repeat-linear
               :rule-classes :linear)))

(define parse-?repeat ((input nat-listp))
  :returns (mv (error? not)
               (tree treep)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse an optional repetition range."
  (seq-backtrack
   input
   ((tree := (parse-repeat input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree)))))
   ((return-raw (mv nil
                    (make-tree-nonleaf :rulename? nil :branches nil)
                    (nat-list-fix input)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-?repeat-linear
               :rule-classes :linear)))

(define parse-alpha/digit/dash ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a group @('(ALPHA / DIGIT / \"-\")')."
  (seq-backtrack
   input
   ((tree := (parse-alpha input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree)))))
   ((tree := (parse-digit input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree)))))
   ((tree := (parse-ichar #\- input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree))))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-alpha/digit/dash-linear
               :rule-classes :linear)))

(define parse-*-alpha/digit/dash ((input nat-listp))
  :returns (mv (error? not)
               (trees tree-listp)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition @('*(ALPHA / DIGIT / \"-\")')."
  (seq-backtrack input
                 ((tree := (parse-alpha/digit/dash input))
                  (trees := (parse-*-alpha/digit/dash input))
                  (return (cons tree trees)))
                 ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*-alpha/digit/dash-linear
               :rule-classes :linear)))

(define parse-rulename ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a rule name."
  (seq input
       (tree := (parse-alpha input))
       (trees := (parse-*-alpha/digit/dash input))
       (return (make-tree-nonleaf :rulename? *rulename*
                                  :branches (list (list tree) trees))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-rulename-linear
               :rule-classes :linear)))

(defines parse-alt/conc/rep/elem/group/option
  :verify-guards nil ; done below
  :flag-local nil

  (define parse-alternation ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (tree-optionp tree?)
                             (implies (not error?) (treep tree?))
                             (implies error? (not tree?))))
                 (rest-input nat-listp))
    :parents (grammar-parser-implementation)
    :short "Parse an alternation."
    :long
    (xdoc::topstring
     (xdoc::p
      "Ideally the body of this function would be:")
     (xdoc::codeblock
      "(seq input"
      "     (tree := (parse-concatenation input))"
      "     (trees := (parse-alt-rest input))"
      "     (return (make-tree-nonleaf :rulename? *alternation*"
      "                                :branches (list (list tree) trees))))")
     (xdoc::p
      "But that would defeat the termination proof,
       which would include a failed subgoal saying that,
       when @(tsee parse-concatenation) succeeds,
       the length of its remaining input
       is less than or equal to
       the length of its initial input.
       This is the case for @(tsee parse-concatenation),
       but it can only be proved after the function has been admitted.
       In the termination proof, it is like an uninterpreted function.")
     (xdoc::p
      "So we add the condition on the lengths mentioned above
       as a redundant check.
       To do that, we cannot use @('seq'),
       which prevents us from referring to different versions of the input.")
     (xdoc::p
      "The linear rules below are used in the guard verification proof.")
     (xdoc::@def "parse-alternation")
     (xdoc::@def "len-of-parse-alternation-linear-1")
     (xdoc::@def "len-of-parse-alternation-linear-2"))
    (b* (((mv error? tree input1) (parse-concatenation input))
         ((when error?) (mv error? nil input1))
         ((unless (mbt (< (len input1) (len input)))) (mv "" nil nil))
         ((mv error? trees input2) (parse-alt-rest input1))
         ((when error?) (mv error? nil input2)))
      (mv nil
          (make-tree-nonleaf :rulename? *alternation*
                             :branches (list (list tree) trees))
          input2))
    :measure (two-nats-measure (len input) 9)
    :no-function t)

  (define parse-concatenation ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (tree-optionp tree?)
                             (implies (not error?) (treep tree?))
                             (implies error? (not tree?))))
                 (rest-input nat-listp))
    :parents (grammar-parser-implementation)
    :short "Parse a concatenation."
    :long
    (xdoc::topstring
     (xdoc::p
      "Ideally the body of this function would be:")
     (xdoc::codeblock
      "(seq input"
      "     (tree := (parse-repetition input))"
      "     (trees := (parse-conc-rest input))"
      "     (return (make-tree-nonleaf :rulename? *concatenation*"
      "                                :branches (list (list tree) trees))))")
     (xdoc::p
      "But that would defeat the termination proof,
       which would include a failed subgoal saying that,
       when @(tsee parse-repetition) succeeds,
       the length of its remaining input
       is less than or equal to
       the length of its initial input.
       This is the case for @(tsee parse-repetition),
       but it can only be proved after the function has been admitted.
       In the termination proof, it is like an uninterpreted function.")
     (xdoc::p
      "So we add the condition on the lengths mentioned above
       as a redundant check.
       To do that, we cannot use @('seq'),
       which prevents us from referring to different versions of the input.")
     (xdoc::p
      "The linear rules below are used in the guard verification proof.")
     (xdoc::@def "parse-concatenation")
     (xdoc::@def "len-of-parse-concatenation-linear-1")
     (xdoc::@def "len-of-parse-concatenation-linear-2"))
    (b* (((mv error? tree input1) (parse-repetition input))
         ((when error?) (mv error? nil input1))
         ((unless (mbt (< (len input1) (len input)))) (mv "" nil nil))
         ((mv error? trees input2) (parse-conc-rest input1))
         ((when error?) (mv error? nil input2)))
      (mv nil
          (make-tree-nonleaf :rulename? *concatenation*
                             :branches (list (list tree) trees))
          input2))
    :measure (two-nats-measure (len input) 8)
    :no-function t)

  (define parse-repetition ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (tree-optionp tree?)
                             (implies (not error?) (treep tree?))
                             (implies error? (not tree?))))
                 (rest-input nat-listp))
    :parents (grammar-parser-implementation)
    :short "Parse a repetition."
    :long
    (xdoc::topstring
     (xdoc::p
      "The linear rules below are used in the guard verification proof.")
     (xdoc::@def "parse-repetition")
     (xdoc::@def "len-of-parse-repetition-linear-1")
     (xdoc::@def "len-of-parse-repetition-linear-2"))
    (seq input
         (tree-repeat := (parse-?repeat input))
         (tree-element := (parse-element input))
         (return (make-tree-nonleaf :rulename? *repetition*
                                    :branches (list (list tree-repeat)
                                                    (list tree-element)))))
    :measure (two-nats-measure (len input) 7)
    :no-function t)

  (define parse-element ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (tree-optionp tree?)
                             (implies (not error?) (treep tree?))
                             (implies error? (not tree?))))
                 (rest-input nat-listp))
    :parents (grammar-parser-implementation)
    :short "Parse an element."
    :long
    (xdoc::topstring
     (xdoc::p
      "The linear rules below are used in the guard verification proof.")
     (xdoc::@def "parse-element")
     (xdoc::@def "len-of-parse-element-linear-1")
     (xdoc::@def "len-of-parse-element-linear-2"))
    (seq-backtrack input
                   ((tree := (parse-rulename input))
                    (return (make-tree-nonleaf :rulename? *element*
                                               :branches (list (list tree)))))
                   ((tree := (parse-group input))
                    (return (make-tree-nonleaf :rulename? *element*
                                               :branches (list (list tree)))))
                   ((tree := (parse-option input))
                    (return (make-tree-nonleaf :rulename? *element*
                                               :branches (list (list tree)))))
                   ((tree := (parse-char-val input))
                    (return (make-tree-nonleaf :rulename? *element*
                                               :branches (list (list tree)))))
                   ((tree := (parse-num-val input))
                    (return (make-tree-nonleaf :rulename? *element*
                                               :branches (list (list tree)))))
                   ((tree := (parse-prose-val input))
                    (return (make-tree-nonleaf :rulename? *element*
                                               :branches (list (list tree))))))
    :measure (two-nats-measure (len input) 6)
    :no-function t)

  (define parse-group ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (tree-optionp tree?)
                             (implies (not error?) (treep tree?))
                             (implies error? (not tree?))))
                 (rest-input nat-listp))
    :parents (grammar-parser-implementation)
    :short "Parse a group."
    :long
    (xdoc::topstring
     (xdoc::p
      "The linear rules below are used in the guard verification proof.")
     (xdoc::@def "parse-group")
     (xdoc::@def "len-of-parse-group-linear-1")
     (xdoc::@def "len-of-parse-group-linear-2"))
    (seq input
         (tree-open-round := (parse-ichar #\( input))
         (trees-open-pad := (parse-*cwsp input))
         (tree-alt := (parse-alternation input))
         (trees-close-pad := (parse-*cwsp input))
         (tree-close-round := (parse-ichar #\) input))
         (return (make-tree-nonleaf :rulename? *group*
                                    :branches (list (list tree-open-round)
                                                    trees-open-pad
                                                    (list tree-alt)
                                                    trees-close-pad
                                                    (list tree-close-round)))))
    :measure (two-nats-measure (len input) 5)
    :no-function t)

  (define parse-option ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (tree-optionp tree?)
                             (implies (not error?) (treep tree?))
                             (implies error? (not tree?))))
                 (rest-input nat-listp))
    :parents (grammar-parser-implementation)
    :short "Parse an option."
    :long
    (xdoc::topstring
     (xdoc::p
      "The linear rules below are used in the guard verification proof.")
     (xdoc::@def "parse-option")
     (xdoc::@def "len-of-parse-option-linear-1")
     (xdoc::@def "len-of-parse-option-linear-2"))
    (seq input
         (tree-open-square := (parse-ichar #\[ input))
         (trees-open-pad := (parse-*cwsp input))
         (tree-alt := (parse-alternation input))
         (trees-close-pad := (parse-*cwsp input))
         (tree-close-square := (parse-ichar #\] input))
         (return (make-tree-nonleaf :rulename? *option*
                                    :branches (list (list tree-open-square)
                                                    trees-open-pad
                                                    (list tree-alt)
                                                    trees-close-pad
                                                    (list tree-close-square)))))
    :measure (two-nats-measure (len input) 4)
    :no-function t)

  (define parse-alt-rest ((input nat-listp))
    :returns (mv (error? not)
                 (trees tree-listp)
                 (rest-input nat-listp))
    :parents (grammar-parser-implementation)
    :short "Parse a repetition @('*(*c-wsp \"/\" *c-wsp concatenation)'),
            which is the rest of the definiens of @('alternation')."
    :long
    (xdoc::topstring
     (xdoc::p
      "Ideally the body of this function would be:")
     (xdoc::codeblock
      "(seq-backtrack"
      "  input"
      "  ((tree := (parse-alt-rest-comp input))"
      "   (trees := (parse-alt-rest input))"
      "   (return (cons tree trees)))"
      "  ((return-raw (mv nil nil (nat-list-fix input)))))")
     (xdoc::p
      "But that would defeat the termination proof,
       which would include a failed subgoal saying that,
       when @(tsee parse-alt-rest-comp) succeeds,
       the length of its remaining input
       is strictly less than
       the length of its initial input.
       This is the case for @(tsee parse-alt-rest-comp),
       but it can only be proved after the function has been admitted.
       In the termination proof, it is like an uninterpreted function.")
     (xdoc::p
      "So we add the condition on the lengths mentioned above
       as a redundant check.
       To do that, we cannot use @('seq-backtrack'),
       which prevents us from referring to different versions of the input.
       In order to maintain the invariant that
       @(tsee parse-alt-rest) never fails,
       we return no error if the condition is not satisfied
       (which never happens).")
     (xdoc::p
      "The linear rule below is used in the guard verification proof.")
     (xdoc::@def "parse-alt-rest")
     (xdoc::@def "len-of-parse-alt-rest-linear-1"))
    (b* (((mv error? tree input1)
          (parse-alt-rest-comp input))
         ((when error?) (mv nil nil (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input)))) (mv nil nil nil))
         ((mv & trees input2) (parse-alt-rest input1)))
      (mv nil (cons tree trees) input2))
    :measure (two-nats-measure (len input) 3)
    :no-function t)

  (define parse-alt-rest-comp ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (tree-optionp tree?)
                             (implies (not error?) (treep tree?))
                             (implies error? (not tree?))))
                 (rest-input nat-listp))
    :parents (grammar-parser-implementation)
    :short "Parse a group @('(*c-wsp \"/\" *c-wsp concatenation)'),
            which is a component of
            the rest of the definiens of @('alternation')."
    :long
    (xdoc::topstring
     (xdoc::p
      "The linear rules below are used in the guard verification proof.")
     (xdoc::@def "parse-alt-rest-comp")
     (xdoc::@def "len-of-parse-alt-rest-comp-linear-1")
     (xdoc::@def "len-of-parse-alt-rest-comp-linear-2"))
    (seq input
         (trees1 := (parse-*cwsp input))
         (tree-slash := (parse-ichar #\/ input))
         (trees2 := (parse-*cwsp input))
         (tree-conc := (parse-concatenation input))
         (return (make-tree-nonleaf :rulename? nil
                                    :branches (list trees1
                                                    (list tree-slash)
                                                    trees2
                                                    (list tree-conc)))))
    :measure (two-nats-measure (len input) 2)
    :no-function t)

  (define parse-conc-rest ((input nat-listp))
    :returns (mv (error? not)
                 (trees tree-listp)
                 (rest-input nat-listp))
    :parents (grammar-parser-implementation)
    :short "Parse a repetition @('*(1*c-wsp repetition)'),
            which is the rest of the definiens of @('concatenation')."
    :long
    (xdoc::topstring
     (xdoc::p
      "Ideally the body of this function would be:")
     (xdoc::codeblock
      "(seq-backtrack"
      "  input"
      "  ((tree := (parse-conc-rest-comp input))"
      "   (trees := (parse-conc-rest input))"
      "   (return (cons tree trees)))"
      "  ((return-raw (mv nil nil (nat-list-fix input)))))")
     (xdoc::p
      "But that would defeat the termination proof,
       which would include a failed subgoal saying that,
       when @(tsee parse-conc-rest-comp) succeeds,
       the length of its remaining input
       is strictly less than
       the length of its initial input.
       This is the case for @(tsee parse-conc-rest-comp),
       but it can only be proved after the function has been admitted.
       In the termination proof, it is like an uninterpreted function.")
     (xdoc::p
      "So we add the condition on the lengths mentioned above
       as a redundant check.
       To do that, we cannot use @('seq-backtrack'),
       which prevents us from referring to different versions of the input.
       In order to maintain the invariant that
       @(tsee parse-conc-rest) never fails,
       we return no error if the condition is not satisfied
       (which never happens).")
     (xdoc::p
      "The linear rule below is used in the guard verification proof.")
     (xdoc::@def "parse-conc-rest")
     (xdoc::@def "len-of-parse-conc-rest-linear-1"))
    (b* (((mv error? tree input1)
          (parse-conc-rest-comp input))
         ((when error?) (mv nil nil (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input)))) (mv nil nil nil))
         ((mv & trees input2) (parse-conc-rest input1)))
      (mv nil (cons tree trees) input2))
    :measure (two-nats-measure (len input) 1)
    :no-function t)

  (define parse-conc-rest-comp ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (tree-optionp tree?)
                             (implies (not error?) (treep tree?))
                             (implies error? (not tree?))))
                 (rest-input nat-listp))
    :parents (grammar-parser-implementation)
    :short "Parse a group @('(1*c-wsp repetition)'),
            which is a component of
            the rest of the definiens of @('concatenation')."
    :long
    (xdoc::topstring
     (xdoc::p
      "The linear rules below are used in the guard verification proof.")
     (xdoc::@def "parse-conc-rest-comp")
     (xdoc::@def "len-of-parse-conc-rest-comp-linear-1")
     (xdoc::@def "len-of-parse-conc-rest-comp-linear-2"))
    (seq input
         (trees := (parse-1*cwsp input))
         (tree := (parse-repetition input))
         (return (make-tree-nonleaf :rulename? nil
                                    :branches (list trees (list tree)))))
    :measure (two-nats-measure (len input) 0)
    :no-function t)

  ///

  (defthm-parse-alt/conc/rep/elem/group/option-flag

    (defthm len-of-parse-alternation-linear-1
      (<= (len (mv-nth 2 (parse-alternation input)))
          (len input))
      :rule-classes :linear
      :flag parse-alternation)

    (defthm len-of-parse-concatenation-linear-1
      (<= (len (mv-nth 2 (parse-concatenation input)))
          (len input))
      :rule-classes :linear
      :flag parse-concatenation)

    (defthm len-of-parse-repetition-linear-1
      (<= (len (mv-nth 2 (parse-repetition input)))
          (len input))
      :rule-classes :linear
      :flag parse-repetition)

    (defthm len-of-parse-element-linear-1
      (<= (len (mv-nth 2 (parse-element input)))
          (len input))
      :rule-classes :linear
      :flag parse-element)

    (defthm len-of-parse-group-linear-1
      (<= (len (mv-nth 2 (parse-group input)))
          (len input))
      :rule-classes :linear
      :flag parse-group)

    (defthm len-of-parse-option-linear-1
      (<= (len (mv-nth 2 (parse-option input)))
          (len input))
      :rule-classes :linear
      :flag parse-option)

    (defthm len-of-parse-alt-rest-linear-1
      (<= (len (mv-nth 2 (parse-alt-rest input)))
          (len input))
      :rule-classes :linear
      :flag parse-alt-rest)

    (defthm len-of-parse-alt-rest-comp-linear-1
      (<= (len (mv-nth 2 (parse-alt-rest-comp input)))
          (len input))
      :rule-classes :linear
      :flag parse-alt-rest-comp)

    (defthm len-of-parse-conc-rest-linear-1
      (<= (len (mv-nth 2 (parse-conc-rest input)))
          (len input))
      :rule-classes :linear
      :flag parse-conc-rest)

    (defthm len-of-parse-conc-rest-comp-linear-1
      (<= (len (mv-nth 2 (parse-conc-rest-comp input)))
          (len input))
      :rule-classes :linear
      :flag parse-conc-rest-comp))

  (defrule len-of-parse-conc-rest-comp-linear-2
    (implies (not (mv-nth 0 (parse-conc-rest-comp input)))
             (< (len
                 (mv-nth 2 (parse-conc-rest-comp input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-conc-rest-comp input)))

  (defrule len-of-parse-alt-rest-comp-linear-2
    (implies (not (mv-nth 0 (parse-alt-rest-comp input)))
             (< (len
                 (mv-nth 2 (parse-alt-rest-comp input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-alt-rest-comp input)))

  (defrule len-of-parse-option-linear-2
    (implies (not (mv-nth 0 (parse-option input)))
             (< (len (mv-nth 2 (parse-option input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-option input)))

  (defrule len-of-parse-group-linear-2
    (implies (not (mv-nth 0 (parse-group input)))
             (< (len (mv-nth 2 (parse-group input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-group input)))

  (defrule len-of-parse-element-linear-2
    (implies (not (mv-nth 0 (parse-element input)))
             (< (len (mv-nth 2 (parse-element input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-element input)))

  (defrule len-of-parse-repetition-linear-2
    (implies (not (mv-nth 0 (parse-repetition input)))
             (< (len (mv-nth 2 (parse-repetition input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-repetition input)))

  (defrule len-of-parse-concatenation-linear-2
    (implies (not (mv-nth 0 (parse-concatenation input)))
             (< (len (mv-nth 2 (parse-concatenation input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-concatenation input)))

  (defrule len-of-parse-alternation-linear-2
    (implies (not (mv-nth 0 (parse-alternation input)))
             (< (len (mv-nth 2 (parse-alternation input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-alternation input)))

  (verify-guards parse-alternation)

  (fty::deffixequiv-mutual parse-alt/conc/rep/elem/group/option :args (input)))

(define parse-elements ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse the definiens of a rule."
  (seq input
       (tree := (parse-alternation input))
       (trees := (parse-*cwsp input))
       (return (make-tree-nonleaf :rulename? *elements*
                                  :branches (list (list tree) trees))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-elements-linear
               :rule-classes :linear)))

(define parse-equal-/-equal-slash ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse the group @('(\"=\" / \"=/\")')."
  :long
  (xdoc::topstring-p
   "Since @('\"=\"') is a prefix of @('\"=/\"'),
    the latter is tried before the former.")
  (seq-backtrack
   input
   ((tree := (parse-ichars #\= #\/ input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree)))))
   ((tree := (parse-ichar #\= input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree))))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-equal-/-equal-slash-linear
               :rule-classes :linear)))

(define parse-defined-as ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse the text between a rule name and its definiens."
  (seq input
       (trees1 := (parse-*cwsp input))
       (tree := (parse-equal-/-equal-slash input))
       (trees2 := (parse-*cwsp input))
       (return (make-tree-nonleaf :rulename? *defined-as*
                                  :branches (list trees1
                                                  (list tree)
                                                  trees2))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-defined-as-linear
               :rule-classes :linear)))

(define parse-rule ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a rule."
  (seq input
       (tree1 := (parse-rulename input))
       (tree2 := (parse-defined-as input))
       (tree3 := (parse-elements input))
       (tree4 := (parse-cnl input))
       (return (make-tree-nonleaf :rulename? *rule*
                                  :branches (list (list tree1)
                                                  (list tree2)
                                                  (list tree3)
                                                  (list tree4)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-rule-linear
               :rule-classes :linear)))

(define parse-*cwsp-cnl ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a group @('(*c-wsp c-nl)')."
  (seq input
       (trees := (parse-*cwsp input))
       (tree := (parse-cnl input))
       (return (make-tree-nonleaf :rulename? nil
                                  :branches (list trees (list tree)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-*cwsp-cnl-linear
               :rule-classes :linear)))

(define parse-rule-/-*cwsp-cnl ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a group @('( rule / (*c-wsp c-nl) )')."
  (seq-backtrack
   input
   ((tree := (parse-rule input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree)))))
   ((tree := (parse-*cwsp-cnl input))
    (return (make-tree-nonleaf :rulename? nil :branches (list (list tree))))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-rule-/-*cwsp-cnl-linear
               :rule-classes :linear)))

(define parse-*-rule-/-*cwsp-cnl ((input nat-listp))
  :returns (mv (error? not)
               (trees tree-listp)
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a repetition @('*( rule / (*c-wsp c-nl) )')."
  (seq-backtrack
   input
   ((tree := (parse-rule-/-*cwsp-cnl input))
    (trees := (parse-*-rule-/-*cwsp-cnl input))
    (return (cons tree trees)))
   ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*-rule-/-*cwsp-cnl-linear
               :rule-classes :linear)))

(define parse-rulelist ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :parents (grammar-parser-implementation)
  :short "Parse a rule list."
  (seq input
       (tree := (parse-rule-/-*cwsp-cnl input))
       (trees := (parse-*-rule-/-*cwsp-cnl input))
       (return (make-tree-nonleaf :rulename? *rulelist*
                                  :branches (list (cons tree trees)))))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-rulelist-linear
               :rule-classes :linear)))

(define parse-grammar ((nats nat-listp))
  :returns (tree? tree-optionp)
  :parents (grammar-parser-implementation)
  :short "Parse a sequence of natural numbers into an ABNF grammar."
  :long
  (xdoc::topstring-p
   "This function parses the natural numbers into a list of rules,
    returning the corresponding parse tree,
    or @('nil') if parsing fails.
    This function also checks that
    there are no leftover natural numbers when parsing ends,
    returning @('nil') if this check fails.")
  (b* (((mv error? tree? rest) (parse-rulelist nats))
       ((when error?) nil)
       ((when rest) nil))
    tree?)
  :no-function t
  :hooks (:fix))

(define parse-grammar-from-file ((filename acl2::stringp) state)
  :returns (mv (tree? tree-optionp)
               state)
  :parents (grammar-parser-implementation)
  :short "Parse a file into an ABNF grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ABNF language consists of sequences of ASCII codes,
     as shown by theorem "
    (xdoc::seetopic "*all-concrete-syntax-rules*"
                    "@('ascii-only-*all-concrete-syntax-rules*')")
    ". ASCII codes are octets (i.e. 8-bit bytes).
     Thus, instead of parsing sequences of natural numbers,
     we can parse sequences of characters (which are isomorphic to octets),
     by converting the characters to the corresponding octets.
     The characters can be read from a file.")
   (xdoc::p
    "This function parses the characters from a file into a grammar.
     If parsing fails, @('nil') is returned.
     If reading the characters from the file fails, @('nil') is returned.")
   (xdoc::p
    "Thus, a language definition in ABNF can be put into a file
     (e.g. copied and pasted from an RFC)
     and parsed with this function.
     Note that in ABNF lines are terminated by a carriage return and line feed,
     so the file must follow that convention.
     On Unix systems (e.g. Linux and macOS),
     this can be accomplished by writing the file in Emacs,
     setting the buffer's end-of-line to carriage return and line feed
     by calling @('set-buffer-file-coding-system') with @('dos'),
     and saving the file.
     If the file is put under a version control system,
     it should be forced to be treated as a binary file,
     to avoid turning carriage returns and line feeds into just line feeds
     across Windows and Unix platforms.")
   (xdoc::p
    "If parsing succeeds, it returns a correct parse tree
     for the contents of the file as a list of ABNF rules,
     according to the concrete syntax rules."))
  (b* (((mv chars state) (read-file-characters filename state))
       ((unless (character-listp chars))
        (mv (hard-error 'abnf "ABNF Grammar File Reading Error." nil)
            state))
       (nats (chars=>nats chars))
       (tree? (parse-grammar nats))
       ((unless tree?)
        (mv (hard-error 'abnf "ABNF Grammar File Parsing Error." nil)
            state)))
    (mv tree? state))
  :no-function t)
