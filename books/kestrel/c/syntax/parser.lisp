; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "files")
(include-book "abstract-syntax-operations")

(include-book "kestrel/fty/nat-option" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "kestrel/utilities/strings/char-code-theorems" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Library extensions.

(defruledl natp-when-bytep
  (implies (bytep x)
           (natp x)))

(defruledl rationalp-when-bytep
  (implies (bytep x)
           (rationalp x)))

(defruledl acl2-numberp-when-bytep
  (implies (bytep x)
           (acl2-numberp x)))

(defruledl integerp-when-natp
  (implies (natp x)
           (integerp x)))

(defruledl rationalp-when-natp
  (implies (natp x)
           (rationalp x)))

(defruledl acl2-numberp-when-natp
  (implies (natp x)
           (acl2-numberp x)))

(defruledl natp-of-plus
  (implies (and (natp x)
                (natp y))
           (natp (+ x y))))

(defruledl natp-of-logand
  (implies (and (natp x)
                (natp y))
           (natp (logand x y)))
  :enable natp
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruledl natp-of-ash
  (implies (natp x)
           (natp (ash x y)))
  :prep-books ((include-book "kestrel/arithmetic-light/ash" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser
  :parents (syntax-for-tools)
  :short "A parser of C into our abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide a parser to turn C code into
     the abstract syntax defined in @(see abstract-syntax).
     The parser is based on our C concrete syntax formulation
     in @(see concrete-syntax).
     In line with the rationale for our abstract syntax,
     the parser preserves much of the information from the concrete syntax.")
   (xdoc::p
    "Currently the parser handles all C code constructs after preprocessing;
     our parser does not do any preprocessing.
     We plan to extend our abstract syntax with some preprocessing constructs,
     and accordingly extend our parser to recognize and preserve those.
     We may also develop our own C preprocessor in the future.")
   (xdoc::p
    "Parsing C, even after preprocessing, is notoriously complicated.
     There are syntactic ambiguities stemming from the fact that
     an identifier may be an expression or a type name.
     This is often addressed by performing
     some static semantic analysis during parsing,
     in order to tell apart identifier expressions and identifier type names.
     Our parser instead parses the ambiguous constructs
     into explicit representations of ambiguous constructs:
     see @(tsee abstract-syntax).
     Our approach avoids the static semantic analysis during parsing,
     at the cost of more complicated parsing logic,
     but we prefer the cleaner separation of concerns.")
   (xdoc::p
    "The current implementation of our parser
     does not capture all ambiguous constructs yet.
     It is possible that our parser may reject some valid C code.
     However, we plan to cover all ambiguous constructs soon.")
   (xdoc::p
    "Our parser uses recursive descent,
     both for lexing and for parsing proper.
     The parser is closely based on the ABNF grammar in @(see grammar),
     which should be consulted alongside the parser code.
     Since that grammar is left-recursive,
     we perform the usual left recursion elimination.")
   (xdoc::p
    "Although currently lexing should be context-independent
     (i.e. it should be possible to lex the code and then parse it),
     our parser is written so that lexing is called on the fly.
     This makes it possible to accommodate context-dependent lexing,
     which may be needed as we add support for some preprocessing constructs.")
   (xdoc::p
    "Our parser uses "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuples")
    " to handle errors; see that documentation page.
     The current parser is amenable to
     returning more informative error messages,
     but we have already put some effort into doing that.")
   (xdoc::p
    "This parser is currently not verified, for expediency.
     We plan to go back and work on verifying, or synthesizing,
     components of this parser, and ideally eventually the whole parser.
     This work will be based on our "
    (xdoc::seetopic "abnf::abnf" "ABNF library and tools")
    ". Even better, we may investigate generating the parser automatically
     from the grammar with suitable additional information;
     The aforementioned ABNF library already has some parsing generation tools,
     but they are fairly simple and preliminary,
     so they would need significant extensions.")
   (xdoc::p
    "The parser is amenable to some optimizations.
     For now we have favored simplicity and regularity,
     but if performance turns out to be important,
     we can optimize the implementation in some respects.
     Even better, we could investigate applying optimizing transformations
     to the current parser implementation,
     or perhaps to a simpler and higher-level implementation;
     this could be part of the idea of generating the parser automatically,
     mentioned above."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum token
  :short "Fixtype of tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>token</i> in the grammar in [C:A.1.1] [C:6.4].")
   (xdoc::p
    "This is used by the parser.
     It is not part of the abstract syntax in @(see abstract-syntax),
     even though the ABNF grammar has a rule for @('token').
     Our parser is structured in two levels, which is common:
     (i) lexing/tokenization; and (ii) parsing proper.
     Thus, it is useful to have an abstract-syntax-like type for tokens,
     which is what this fixtype is.")
   (xdoc::p
    "We represent a C keyword or puncutator as an ACL2 string,
     which suffices to represent all C keywords and punctuators,
     which are all ASCII.
     We could consider defining enumeration fixtypes
     for keywords and puncutators instead,
     and use them here instead of strings.")
   (xdoc::p
    "We use the identifiers, constants, and string literals
     from the abstract syntax
     to represent the corresponding tokens.
     However, note that the parser never generates enumeration constants,
     which overlap with identifiers,
     but need type checking to be distinguished from identifiers;
     the parser always classifies those as identifiers."))
  (:keyword ((unwrap string)))
  (:ident ((unwrap ident)))
  (:const ((unwrap const)))
  (:string ((unwrap stringlit)))
  (:punctuator ((unwrap stringp)))
  :pred tokenp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-token
  :short "An irrelevant token."
  :type tokenp
  :body (token-ident (ident :irrelevant)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist token-list
  :short "Fixtype of lists of tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "Tokens are defined in @(tsee token)."))
  :elt-type token
  :true-listp t
  :elementp-of-nil nil
  :pred token-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption token-option
  token
  :short "Fixtype of optional tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "Tokens are defined in @(tsee token)."))
  :pred token-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-msg ((token token-optionp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp character-alistp))))
  :short "Represent a token as a message."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in parser error messages,
     so it does not have to provide a complete description of the token
     for all possible tokens.
     We only give a complete description of keyword and punctuator tokens,
     because those are the kinds that may be a mismatch
     (e.g. expecing a @(':'), found a @(';') instead).
     For the other kinds, we give a more generic description.")
   (xdoc::p
    "It is convenient to treat uniformly tokens and @('nil'),
     which happens when the end of the file is reached.
     This is why this function takes an optional token as input."))
  (if token
      (token-case
       token
       :keyword (msg "the keyword ~x0" token.unwrap)
       :ident "an identifier"
       :const "a constant"
       :string "a string literal"
       :punctuator (msg "the punctuator ~x0" token.unwrap))
    "end of file"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-keywordp ((token token-optionp) (keyword stringp))
  :returns (yes/no booleanp)
  :short "Check if a token is a given keyword."
  :long
  (xdoc::topstring
   (xdoc::p
    "This operates on an optional token,
     since we normally call this function on an optional token."))
  (and token
       (token-case token :keyword)
       (equal (token-keyword->unwrap token)
              keyword))

  ///

  (defrule non-nil-when-token-keywordp
    (implies (token-keywordp token keyword)
             token)
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-punctuatorp ((token token-optionp) (punctuator stringp))
  :returns (yes/no booleanp)
  :short "Check if a token is a given punctuator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This operates on an optional token,
     since we normally call this function on an optional token."))
  (and token
       (token-case token :punctuator)
       (equal (token-punctuator->unwrap token)
              punctuator))

  ///

  (defrule non-nil-when-token-punctuatorp
    (implies (token-punctuatorp token punctuator)
             token)
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum lexeme
  :short "Fixtype of lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>lexeme</i> in our ABNF grammar,
     but since for now we just skip over comments and whitespace,
     we have no additional information about them here.")
   (xdoc::p
    "Like @(tsee token), this is abstract-syntax-like,
     but it is not part of the abstract syntax,
     because it is not needed there."))
  (:token ((unwrap token)))
  (:comment ())
  (:whitespace ())
  :pred lexemep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-lexeme
  :short "An irrelevant lexeme."
  :type lexemep
  :body (lexeme-token (irr-token)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption lexeme-option
  lexeme
  :short "Fixtype of optional lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lexemes are defined in @(tsee lexeme)."))
  :pred lexeme-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod position
  :short "Fixtype of positions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A position within a file is normally specified by
     a combination of a line number and column number.
     We number lines from 1,
     which is consistent with [C:6.10.4/2]:
     since the characters in the first line
     have 0 preceding new-line characters,
     the number of the first line is 1 plus 0, i.e. 1.
     We number columns from 0,
     but we could change that to 1.
     Numbering lines from 1 and columns from 0
     is also consistent with Emacs."))
  ((line pos)
   (column nat))
  :pred positionp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-position
  :short "An irrelevant position."
  :type positionp
  :body (make-position :line 1 :column 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-init ()
  :returns (pos positionp)
  :short "Initial position in a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is at line 1 and column 0."))
  (make-position :line 1 :column 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-inc-column ((columns natp) (pos positionp))
  :returns (new-pos positionp)
  :short "Increment a position by a number of columns."
  :long
  (xdoc::topstring
   (xdoc::p
    "The line number is unchanged."))
  (change-position pos :column (+ (position->column pos) columns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-inc-line ((lines posp) (pos positionp))
  :returns (new-pos positionp)
  :short "Increment a position by a number of lines."
  :long
  (xdoc::topstring
   (xdoc::p
    "The column is reset to 0."))
  (make-position :line (+ (position->line pos) lines) :column 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-to-msg ((pos positionp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp character-alistp))))
  :short "Represent a position as a message."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in user-oriented error messages."))
  (msg "(line ~x0, column ~x1)" (position->line pos) (position->column pos)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod char+position
  :short "Fixtype of pairs each consisting of a character and a position."
  ((char nat)
   (position position))
  :pred char+position-p
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist char+position-list
  :short "Fixtype of lists of
          pairs each consisting of a character and a position."
  :elt-type char+position
  :true-listp t
  :elementp-of-nil nil
  :pred char+position-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod span
  :short "Fixtype of spans."
  :long
  (xdoc::topstring
   (xdoc::p
    "A span consists of two positions,
     which characterize a contiguous portion of a file.
     Each parsed construct has a span.
     The ending position of a span is inclusive."))
  ((start position)
   (end position))
  :pred spanp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-span
  :short "An irrelevant span."
  :type spanp
  :body (make-span :start (irr-position) :end (irr-position)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define span-join ((span1 spanp) (span2 spanp))
  :returns (span spanp)
  :short "Join two spans."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first span must come before the second one.
     We return a new span that goes
     from the start of the first span to the end of the second span."))
  (make-span :start (span->start span1)
             :end (span->end span2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define span-to-msg ((span spanp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp character-alistp))))
  :short "Represent a span as a message."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in user-oriented messages."))
  (msg "[~@0 to ~@1]"
       (position-to-msg (span->start span))
       (position-to-msg (span->end span))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod token+span
  :short "Fixtype of pairs each consisting of a token and a span."
  ((token token)
   (span span))
  :pred token+span-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist token+span-list
  :short "Fixtype of lists of pairs each consisting of a token and a span."
  :elt-type token+span
  :true-listp t
  :elementp-of-nil nil
  :pred token+span-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection parstate
  :short "Fixtype of parser states."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our parsing functions take and return parser states.")
   (xdoc::p
    "The parser state is a stobj, which we turn into a fixtype
     by adding a fixer along with readers and writers
     that fix their inputs and unconditionally return typed outputs.
     The use of a stobj is an optimization for speed:
     conceptually, the parser state could be defined as a @(tsee fty::defprod),
     and in fact it was defined like that in previous versions of the parser.
     The description below of the parser state treats the parser state
     as if it were defined via @(tsee fty::defprod), not as a stobj;
     at the end, we explain how the stobj represents that parser state.")
   (xdoc::p
    "The primary component of a parser state
     is the input sequence @('bytes') of bytes remaining,
     which initially comes from a file (see @(see files)).
     Bytes are read and removed from this component,
     and turned into characters.")
   (xdoc::p
    "Given the need for look-ahead during lexing,
     we use the common technique of ``unreading'' characters sometimes,
     i.e. putting them back into the parser state.
     But since we have already turned bytes into characters,
     we do not want to put back the bytes:
     thus, the @('chars-unread') component of the parser state
     contains a list of characters that have been put back, in character form;
     the form is natural numbers, i.e. Unicode code points.
     The list is initially empty.
     When non-empty, it must be thought of
     as preceding the @('bytes') byte list.
     If the list is not empty,
     the next character will be read directly from that list,
     not from the byte list.")
   (xdoc::p
    "To avoid putting back the wrong character by mistake,
     i.e. a character that was not actually read,
     we use the @('chars-read') component of the parser state
     to keep track of which characters have been read and could be unread.
     Thus, every time we read a character,
     we add it to the @('chars-read') list,
     which can be visualized, reversed, to the left of
     the @('chars-unread') and @('bytes') lists:")
   (xdoc::codeblock
    "+----------+    read    +--------+-------+"
    "| chars    |   <-----   | chars  | bytes |"
    "| read     |            | unread |       |"
    "| reversed |   ----->   |        |       |"
    "+----------+   unread   +--------+-------+")
   (xdoc::p
    "The reading of a character moves the character from right to left,
     from the @('chars-unread') list to the reversed @('chars-read') list
     if @('chars-unread') is not empty,
     or from the @('bytes') list to the reversed @('chars-read') list
     where one or more bytes are UTF-8-decoded into the character.")
   (xdoc::p
    "When a character is unread, it is moved from left to right,
     i.e. from the reversed @('chars-read') list to the @('chars-unread') list.
     If @('chars-read') is empty, it is an internal error:
     if the parser code is correct, this must never happen.")
   (xdoc::p
    "The reading and unreading of characters happens at the lexing level.
     A similar look-ahead happens at the proper parsing level,
     where the elements of the read and unread lists
     are not characters but tokens.
     The parser state has lists @('tokens-read') and @('tokens-unread')
     whose handling is similar to the ones for characters.
     The lists can be visualized as follows
     (there are two different situations, explained after the diagram):")
   (xdoc::codeblock
    "+----------+----------+    read    +--------+-------+"
    "| tokens   | chars    |   <-----   | chars  | bytes |"
    "| read     | read     |            | unread |       |"
    "| reversed | reversed |   ----->   |        |       |"
    "+----------+----------+   unread   +--------+-------+"
    ""
    "+----------+    read    +--------+--------+-------+"
    "| tokens   |   <-----   | tokens | chars  | bytes |"
    "| read     |            | unread | unread |       |"
    "| reversed |   ----->   |        |        |       |"
    "+----------+   unread   +--------+--------+-------+")
   (xdoc::p
    "When a token is successfully read,
     it is moved left to the reversed @('tokens-read') list,
     and @('chars-read') is cleared.
     The reason is that, once a token is read,
     all the characters read form the token,
     and there is no need to ever unread them:
     they have already formed the token.
     But after reading that token, in order to read the next token,
     the @('chars-read') list is populated with
     the characters that are read in order to read the next token.
     So in general the reversed @('tokens-read') list
     is at the left of the reversed @('chars-read') list,
     and the latter is cleared again when another token
     is added to @('tokens-read').
     This is the first situation depicted in the diagram above.")
   (xdoc::p
    "Characters are read only as a subroutine of reading tokens.
     If a token is unread, it is unread just after having been read,
     with the @('chars-read') list still cleared.
     The unread token is moved right, added to the @('tokens-unread') list.
     As more tokens are unread, they are also moved right.
     As they are read again, they are moved left.
     This is the second situation depicted in the diagram above.
     Note that we may have some unread characters,
     which were read and then unread in the course of reading tokens,
     so the @('chars-unread') list is
     between the @('token-unread') and @('bytes') lists.")
   (xdoc::p
    "While @('chars-read') is cleared every time a token is read,
     @('tokens-read') is never cleared.
     This lets us do some backtracking when needed,
     but without saving and copying the whole parser state:
     we just need to keep track of how many tokens must be put back
     for backtracking.")
   (xdoc::p
    "For reporting errors, it is useful to keep track of
     where in a file the constructs being parsed occur.
     To this end, the @('position') component of the parser state
     is the position, in the file, of the next character to be read
     from the @('bytes') component;
     if this component is empty,
     the position is just one past the last character in the file.
     For read and unread characters,
     since we have already found their position and have moved past it,
     we store their positions in the @('chars-read') and @('chars-unread').
     This is why they contain not just characters,
     but @(tsee char+position) pairs.
     Similarly, for tokens, we also store their spans.")
   (xdoc::p
    "To support backtracking,
     we also keep track of zero or more checkpoints,
     which indicate positions in the @('tokens-read') list.
     When a checkpoint is recorded,
     the current length of @('tokens-read') is stored as a checkpoint,
     by @(tsee cons)ing it to the @('checkpoints') list.
     Later, the checkpoint can be simply cleared,
     in which case it is simply removed from the check,
     by replacing @('checkpoints') with its @(tsee cdr).
     Alternatively, we can backtrack to the checkpoint,
     which involves moving tokens from @('tokens-read') to @('tokens-unread')
     until @('tokens-read') has the length of the checkpoint in question;
     then the checkpoint is removed from @('checkpoints') as well.
     That is, we have the ability to backtrack to earlier tokens,
     without having to keep track of how many tokens we have read
     since the potential point of backtrack.
     The reason why @('checkpoints') is a list of natural numbers
     and not just an optional natural number
     is that we may need to support ``nested'' backtracking
     while parsing something that may also backtrack.")
   (xdoc::p
    "We include a boolean flag saying whether
     certain GCC extensions should be accepted or not.
     These GCC extensions are limited to the ones
     currently captured in our abstract syntax.
     This parser state component is set at the beginning and never changes,
     but it is useful to have it as part of the parser state
     to avoid passing an additional parameter.
     This parser state component could potentially evolve into
     a richer set of options for different versions and dialects of C.")
   (xdoc::p
    "For speed, we cache the value returned by
     the function @(tsee parsize) defined later.
     Some profiling revealed that significant time was spent there,
     due to the need to save the parser state size
     before certain @(tsee mbt) tests.
     Ideally we should obtain this optimization using @(tsee apt::isodata),
     but that transformation currently does not quite handle
     all of the parser's functions.")
   (xdoc::p
    "Also for speed, we cache the number of the tokens read so far.
     The checkpointing and backtracking mechanism described above
     calculates that length in order to record it as a checkpoint.
     When there is a significant number of read token, that can take time,
     as revealed by some profiling.")
   (xdoc::p
    "The stobj for the parser state consists of
     the components described above,
     but in a stobj instead of a @(tsee fty::defprod).
     This is a ``shallow'' stobj, because several of the components
     are still lists that are updated in a non-destructive way.
     We plan to ``deepen'' the stobj by using arrays and indices
     to simulate those lists in a more efficient way.")
   (xdoc::p
    "The definition of the stobj itself is straightforward,
     but we use a @(tsee make-event) so we can use @(tsee position-init)
     instead of a term for its value that exposes
     the internal representation of positions.")
   (xdoc::p
    "The @(tsee defstobj) generates an enabled recognizer,
     which we disable after introducing the readers and writers.
     We define a fixer for that recognizer,
     using @(tsee mbe) to avoid the stobj restriction
     of having to return the stobj on all paths.
     Then we define a fixtype with the same name as the stobj,
     which causes no issue because fixtypes and stobjs
     are in different name spaces.
     In defining the fixtype,
     we set the equivalence relation to be non-executable,
     because otherwise we run into stobj restrictions.")
   (xdoc::p
    "The @(tsee defstobj) also generates recognizers for the fields,
     for which we have no use.
     But we rename them to less ambiguous names,
     by incorporating @('parstate') into them,
     to avoid polluting the name space.
     These recognizers are enabled, but we do not bother disabling them,
     because we are not going to use them anywhere anyhow.")
   (xdoc::p
    "The @(tsee defstobj) also generates readers and writers for the fields,
     but they neither fix their inputs
     nor return outputs with unconditional types.
     So we define our own readers and writers that do both things,
     which we define in terms of the generated ones.
     The generated ones are enabled,
     but we do not both disabling them,
     because we are not going to use them anywhere anyhow.
     We also prove some theorems about how readers and writers interact,
     as needed.")
   (xdoc::p
    "We locally enable @(tsee length) in order for
     the proofs generated by @(tsee defstobj) to go through.
     This is also useful for proofs about our readers and writers;
     for those, we also locally enable the fixer.")
   (xdoc::p
    "By making the parser state a stobj instead of a @(tsee fty::defprod),
     we cannot use the @(':require') feature of @(tsee fty::defprod)
     to enforce that the two redundant components described above
     are indeed redundant.
     But we can probably use @(tsee defabsstobj) for that,
     which may be also overall a better way to
     ``turn'' a stobj into a @(tsee fty::defprod)-like fixtype."))

  ;; needed for DEFSTOBJ and writer proofs:

  (local (in-theory (enable length)))

  ;; stobj definition:

  (make-event
   `(defstobj parstate
      (bytes :type (satisfies byte-listp)
             :initially nil)
      (position :type (satisfies positionp)
                :initially ,(position-init))
      (chars-read :type (satisfies char+position-listp)
                  :initially nil)
      (chars-unread :type (satisfies char+position-listp)
                    :initially nil)
      (tokens-read :type (satisfies token+span-listp)
                   :initially nil)
      (tokens-read-len :type (integer 0 *)
                       :initially 0)
      (tokens-unread :type (satisfies token+span-listp)
                     :initially nil)
      (checkpoints :type (satisfies nat-listp)
                   :initially nil)
      (gcc :type (satisfies booleanp)
           :initially nil)
      (size :type (integer 0 *)
            :initially 0)
      :renaming (;; field recognizers:
                 (bytesp raw-parstate->bytes-p)
                 (positionp raw-parstate->position-p)
                 (chars-readp raw-parstate->chars-read-p)
                 (chars-unreadp raw-parstate->chars-unread-p)
                 (tokens-readp raw-parstate->tokens-read-p)
                 (tokens-read-lenp raw-parstate->tokens-read-len-p)
                 (tokens-unreadp raw-parstate->tokens-unread-p)
                 (checkpointsp raw-parstate->checkpoints-p)
                 (gccp raw-parstate->gcc-p)
                 (sizep raw-parstate->size-p)
                 ;; field readers:
                 (bytes raw-parstate->bytes)
                 (position raw-parstate->position)
                 (chars-read raw-parstate->chars-read)
                 (chars-unread raw-parstate->chars-unread)
                 (tokens-read raw-parstate->tokens-read)
                 (tokens-read-len raw-parstate->tokens-read-len)
                 (tokens-unread raw-parstate->tokens-unread)
                 (checkpoints raw-parstate->checkpoints)
                 (gcc raw-parstate->gcc)
                 (size raw-parstate->size)
                 ;; field writers:
                 (update-bytes raw-update-parstate->bytes)
                 (update-position raw-update-parstate->position)
                 (update-chars-read raw-update-parstate->chars-read)
                 (update-chars-unread raw-update-parstate->chars-unread)
                 (update-tokens-read raw-update-parstate->tokens-read)
                 (update-tokens-read-len raw-update-parstate->tokens-read-len)
                 (update-tokens-unread raw-update-parstate->tokens-unread)
                 (update-checkpoints raw-update-parstate->checkpoints)
                 (update-gcc raw-update-parstate->gcc)
                 (update-size raw-update-parstate->size))))

  ;; fixer:

  (define parstate-fix (parstate)
    :returns (parstate parstatep)
    (mbe :logic (if (parstatep parstate)
                    parstate
                  (create-parstate))
         :exec parstate)
    ///
    (defrule parstate-fix-when-parstatep
      (implies (parstatep parstate)
               (equal (parstate-fix parstate)
                      parstate))))

  ;; fixtype:

  (fty::deffixtype parstate
    :pred parstatep
    :fix parstate-fix
    :equiv parstate-equiv
    :define t
    :executablep nil)

  ;; needed for readers and writers proofs:

  (local (in-theory (enable parstate-fix)))

  ;; readers:

  (define parstate->bytes (parstate)
    :returns (bytes byte-listp)
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->bytes parstate)
                  nil)
         :exec (raw-parstate->bytes parstate))
    :hooks (:fix)
    ///
    (more-returns
     (bytes true-listp :rule-classes :type-prescription)))

  (define parstate->position (parstate)
    :returns (position positionp)
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->position parstate)
                  (position-init))
         :exec (raw-parstate->position parstate))
    :hooks (:fix))

  (define parstate->chars-read (parstate)
    :returns (chars-read char+position-listp)
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->chars-read parstate)
                  nil)
         :exec (raw-parstate->chars-read parstate))
    :hooks (:fix))

  (define parstate->chars-unread (parstate)
    :returns (chars-unread char+position-listp)
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->chars-unread parstate)
                  nil)
         :exec (raw-parstate->chars-unread parstate))
    :hooks (:fix))

  (define parstate->tokens-read (parstate)
    :returns (tokens-read token+span-listp)
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->tokens-read parstate)
                  nil)
         :exec (raw-parstate->tokens-read parstate))
    :hooks (:fix))

  (define parstate->tokens-read-len (parstate)
    :returns (tokens-read-len natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->tokens-read-len parstate)
                  0)
         :exec (raw-parstate->tokens-read-len parstate))
    :hooks (:fix))

  (define parstate->tokens-unread (parstate)
    :returns (tokens-unread token+span-listp)
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->tokens-unread parstate)
                  nil)
         :exec (raw-parstate->tokens-unread parstate))
    :hooks (:fix))

  (define parstate->checkpoints (parstate)
    :returns (checkpoints nat-listp)
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->checkpoints parstate)
                  nil)
         :exec (raw-parstate->checkpoints parstate))
    :hooks (:fix))

  (define parstate->gcc (parstate)
    :returns (gcc booleanp)
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->gcc parstate)
                  nil)
         :exec (raw-parstate->gcc parstate))
    :hooks (:fix))

  (define parstate->size (parstate)
    :returns (size natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->size parstate)
                  0)
         :exec (raw-parstate->size parstate))
    :hooks (:fix))

  ;; writers:

  (define update-parstate->bytes ((bytes byte-listp) parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->bytes (byte-list-fix bytes) parstate))
    :hooks (:fix))

  (define update-parstate->position ((position positionp) parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->position (position-fix position) parstate))
    :hooks (:fix))

  (define update-parstate->chars-read ((chars-read char+position-listp)
                                       parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->chars-read (char+position-list-fix chars-read)
                                       parstate))
    :hooks (:fix))

  (define update-parstate->chars-unread ((chars-unread char+position-listp)
                                         parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->chars-unread (char+position-list-fix chars-unread)
                                         parstate))
    :hooks (:fix))

  (define update-parstate->tokens-read ((tokens-read token+span-listp)
                                        parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->tokens-read (token+span-list-fix tokens-read)
                                        parstate))
    :hooks (:fix))

  (define update-parstate->tokens-read-len ((tokens-read-len natp) parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->tokens-read-len (lnfix tokens-read-len)
                                            parstate))
    :hooks (:fix))

  (define update-parstate->tokens-unread ((tokens-unread token+span-listp)
                                          parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->tokens-unread (token+span-list-fix tokens-unread)
                                          parstate))
    :hooks (:fix))

  (define update-parstate->checkpoints ((checkpoints nat-listp) parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->checkpoints (nat-list-fix checkpoints)
                                        parstate))
    :hooks (:fix))

  (define update-parstate->gcc ((gcc booleanp) parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->gcc (bool-fix gcc) parstate))
    :hooks (:fix))

  (define update-parstate->size ((size natp) parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->size (lnfix size) parstate))
    :hooks (:fix))

  ;; readers over writers:

  (defrule parstate->size-of-update-parstate->tokens-read
    (equal (parstate->size (update-parstate->tokens-read tokens-read parstate))
           (parstate->size parstate))
    :enable (parstate->size
             update-parstate->tokens-read
             parstatep
             parstate-fix
             length))

  (defrule parstate->size-of-update-parstate->tokens-read-len
    (equal (parstate->size
            (update-parstate->tokens-read-len tokens-read-len parstate))
           (parstate->size parstate))
    :enable (parstate->size
             update-parstate->tokens-read-len
             parstatep
             parstate-fix
             length))

  (defrule parstate->size-of-update-parstate->checkpoints
    (equal (parstate->size
            (update-parstate->checkpoints checkpoints parstate))
           (parstate->size parstate))
    :enable (parstate->size
             update-parstate->checkpoints
             parstatep
             parstate-fix
             length))

  (defrule parstate->size-of-update-parstate->size
    (equal (parstate->size (update-parstate->size size parstate))
           (lnfix size))
    :enable (parstate->size
             update-parstate->size
             parstatep
             parstate-fix
             length))

  ;; keep recognizer disabled:

  (in-theory (disable parstatep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-parstate ((data byte-listp) (gcc booleanp) parstate)
  :returns (parstate parstatep)
  :short "Initialize the parser state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the state when we start parsing a file.
     Given (the data of) a file to parse,
     and a flag saying whether GCC extensions should be accepted or not,
     the initial parsing state consists of
     the data to parse,
     no unread characters or tokens,
     no read characters or tokens,
     the initial file position,
     and no checkpoints."))
  (b* ((parstate (update-parstate->bytes data parstate))
       (parstate (update-parstate->position (position-init) parstate))
       (parstate (update-parstate->chars-read nil parstate))
       (parstate (update-parstate->chars-unread nil parstate))
       (parstate (update-parstate->tokens-read nil parstate))
       (parstate (update-parstate->tokens-read-len 0 parstate))
       (parstate (update-parstate->tokens-unread nil parstate))
       (parstate (update-parstate->checkpoints nil parstate))
       (parstate (update-parstate->gcc gcc parstate))
       (parstate (update-parstate->size (len data) parstate)))
    parstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parsize ((parstate parstatep))
  :returns (size natp :rule-classes (:rewrite :type-prescription))
  :short "Size of the parsing state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a synonym of @(tsee parstate->size) at this point.
     It was slightly more elaborate when
     @(tsee parstate) was defined via @(tsee fty::defprod)."))
  (parstate->size parstate)
  :hooks (:fix)

  ///

  (defrule parsize-of-initparstate
    (equal (parsize (init-parstate nil gcc parstate))
           0)
    :enable init-parstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; fixtype version of PARSTATE stobj (useful for debugging and testing)
(fty::defprod parstate$
  ((bytes byte-list)
   (position position)
   (chars-read char+position-list)
   (chars-unread char+position-list)
   (tokens-read token+span-list)
   (tokens-read-len nat)
   (tokens-unread token+span-list)
   (checkpoints nat-list)
   (gcc bool)
   (size nat))
  :prepwork ((local (in-theory (enable nfix)))))

; convert PARSTATE stobj to fixtype value (useful for debugging and testing)
(define to-parstate$ (parstate)
  (make-parstate$
   :bytes (parstate->bytes parstate)
   :position (parstate->position parstate)
   :chars-read (parstate->chars-read parstate)
   :chars-unread (parstate->chars-unread parstate)
   :tokens-read (parstate->tokens-read parstate)
   :tokens-read-len (parstate->tokens-read-len parstate)
   :tokens-unread (parstate->tokens-unread parstate)
   :checkpoints (parstate->checkpoints parstate)
   :gcc (parstate->gcc parstate)
   :size (parstate->size parstate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-to-msg ((char nat-optionp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp
                                                   character-alistp))))
  :short "Represent an optional character as a message."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in @(tsee parstate),
     we represent characters as natural numbers,
     meant to be Unicode code points (more precisely, Unicode scalar values),
     including ASCII codes as a subset.
     When an unexpected character is encountered during lexing,
     we return user-oriented error messages
     that include a description of the unexpected character.
     This ACL2 function constructs that description.")
   (xdoc::p
    "We use @(tsee read-char) (defined later) to read characters.
     That function recognizes three new-line delimiters:
     line feed, carriage return, and carriage return followed by line feed.
     That function turns all these three into just a line feed.
     Thus, when this function is called to convert to a message
     a character coming from @(tsee read-char),
     that character has never code 13 (for carriage return),
     and if it has code 10 (line feed)
     it is not necessarily a line feed in the file,
     but it could be a carriage return possibly followed by line feed.
     For this reason, we treat the case of code 10 a bit differently,
     and our @('*ascii-control-char-names*') table
     has an internal-error-signaling entry for codes 10 and 13,
     because we do not access that table for those two codes.")
   (xdoc::p
    "We also allow the character to be absent, i.e. to be @('nil').
     This happens when we reach the end of the file:
     attempting to read a character returns @('nil'),
     instead of a natural number (see @(tsee read-char)).
     For error messages, it is convenient to treat this case
     similarly to the case of an actual character.
     So, for @('nil'), this function returns a description of `end of file'."))
  (cond ((not char) "end of file")
        ((= char 10) (msg "the new-line character (LF, CR, or CR LF)"))
        ((< char 32) (msg "the ~s0 character (ASCII code ~x1)"
                          (nth char *ascii-control-char-names*) char))
        ((= char 32) "the SP (space) character (ASCII code 32)")
        ((and (<= 33 char) (<= char 126))
         (msg "the ~s0 character (ASCII code ~x1)"
              (str::implode (list (code-char char))) char))
        ((= char 127) "the DEL (delete) character (ASCII code 127)")
        (t (msg "the non-ASCII Unicode character with code ~x0" char)))
  :guard-hints (("Goal" :in-theory (enable character-listp
                                           nat-optionp)))

  :prepwork
  ((defconst *ascii-control-char-names*
     '("NUL"
       "SOH"
       "STX"
       "ETX"
       "EOT"
       "ENQ"
       "ACK"
       "BEL"
       "BS (backspace)"
       "HT (horizontal tab)"
       "<INTERNAL ERROR IF THIS SHOWS>"
       "VT (vertical tab)"
       "FF (form feed)"
       "<INTERNAL ERROR IF THIS SHOWS>"
       "SO"
       "SI"
       "DLE"
       "DC1"
       "DC2"
       "DC3"
       "DC4"
       "NAK"
       "SYN"
       "ETB"
       "CAN"
       "EM"
       "SUB"
       "ESC"
       "FS"
       "GS"
       "RS"
       "US"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ reterr-msg (&key where expected found extra)
  :short "Return an error consisting of a message
          with information about what was expected and what was found where."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by our lexing and parsing functions
     to more concisely return more uniform error messages.")
   (xdoc::p
    "This macro assumes that a suitable local macro @('reterr') is in scope
     (see "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuples")
    "), which is the case for our lexing and parsing functions.
     This macro takes as inputs four terms,
     which must evaluate to messages (i.e. values satisfying @(tsee msgp)).
     Those are used to form a larger message,
     in the manner that should be obvious from the body of this macro.
     Note that the fourth term is optional,
     in case we want to provide additional information.")
   (xdoc::p
    "For now we also include, at the end of the message,
     an indication of the ACL2 function that caused the error.
     This is useful as we are debugging the parser,
     but we may remove it once the parser is more tested or even verified."))
  `(reterr (msg "Expected ~@0 at ~@1; found ~@2 instead.~@3~%~
                 [from function ~x4]~%"
                ,expected
                ,where
                ,found
                ,(if extra
                     `(msg " ~@0" ,extra)
                   "")
                __function__)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-char ((parstate parstatep))
  :returns (mv erp
               (char? nat-optionp)
               (pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Read a character."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the character, we also return its position.
     No character is returned if we are at the end of the file;
     in this case, the returned file position is the one of
     the non-existent character just past the end of the file
     (i.e. the position of a character if we added it to the end of the file).")
   (xdoc::p
    "If a character is read, it is added to the list of read characters.
     See @(tsee parstate).")
   (xdoc::p
    "If some character was put back earlier,
     we get the character directly from there,
     removing it from the list;
     see @(tsee parstate).
     There is no change in position in the parser state in this case,
     because the position is the one at the start of the byte list.
     Otherwise, we look at the bytes.")
   (xdoc::p
    "If there are no more bytes, we have reached the end of file.
     We return @('nil'), for no character,
     and we leave the parser state unchanged.")
   (xdoc::p
    "Otherwise, we read the first byte, which is removed from the parser state.
     Since we support Unicode, we perform UTF-8 decoding,
     which may involve reading additional bytes.")
   (xdoc::p
    "Looking at the rules in the ABNF grammar for basic and extended characters,
     we see that the codes of the three ASCII non-new-line extended characters
     (namely dollar, at sign, and backquote)
     fill gaps in the ASCII codes of the basic characters,
     so that the codes 9, 11, 12, and 32-126 are all valid ASCII characters,
     which are thus returned, incrementing the position by one column.
     If instead the byte is the ASCII code 10 for line feed,
     we increment the position by one line.
     If instead the byte is the ASCII code 13 for carriage return,
     there are two cases based on whether the immediately following byte
     exists and is the ASCII code 10 for line feed:
     if it does, we consume two bytes instead of one,
     but we return just a line feed,
     since we only really need one new-line character
     (also in line with [C:5.2.1/3]);
     if it does not, we just consume the carriage return,
     but return a line feed,
     again for normalizing the new-line character.
     In both cases, we increment the position by one line,
     which also resets the column to 0 (see @(tsee position-inc-line)).")
   (xdoc::p
    "Note that horizontal tab, vertical tab, and form feed
     just increment the column number by 1 and leave the line number unchanged,
     like most other characters.
     This may not match the visual appearance,
     but the parser has no way to know
     how many columns a horizontal tab takes,
     or how many lines a vertical tab or form feed takes.
     So, at least for now, we just treat these as most other characters.")
   (xdoc::p
    "We exclude most ASCII control characters,
     except for the basic ones and for the new-line ones,
     since there should be little need to use those in C code.
     Furthermore, some are dangerous, particularly backspace,
     since it may make the code look different from what it is,
     similarly to "
    (xdoc::ahref "https://en.wikipedia.org/wiki/Trojan_Source" "Trojan Source")
    " in Unicode.")
   (xdoc::p
    "If the first byte is 128 or more,
     it must start a non-ASCII Unicode character.
     There are three cases to consider.
     It is easy to find references to UTF-8 encoding/decoding, for instance "
    (xdoc::ahref "https://en.wikipedia.org/wiki/UTF-8" "this Wikipedia page")
    ".")
   (xdoc::p
    "<b>First case</b>:
     If the first byte has the form @('110xxxyy'),
     it must be followed by a second byte of the form @('10yyzzzz'),
     which together encode @('xxxyyyyzzzz'),
     which covers the range from 0 to 7FFh.
     We return an error if there is no second byte.
     We return an error if the encoded value is below 80h.
     If all these checks pass,
     the code covers the character range from @('U+80') to @('U+7FF').")
   (xdoc::p
    "<b>Second case</b>:
     If the first byte has the form @('1110xxxx'),
     it must be followed by a second byte of the form @('10yyyyzz')
     and by a third byte of the form @('10zzwwww'),
     which together encode @('xxxxyyyyzzzzwwww'),
     which covers the range from 0 to FFFFh.
     We return an error if there is no second or third byte.
     We return an error if the encoded value is below 800h.
     If all these checks pass,
     the code covers the character range from @('U+800') to @('U+FFFF'),
     but we return an error if the character
     is between @('U+202A') and @('U+202E')
     or between @('U+2066') and @('U+2069');
     see the @('safe-nonascii') rule in our ABNF grammar.")
   (xdoc::p
    "<b>Third case</b>:
     If the first byte has the form @('11110xyy'),
     it must be followed by a second byte of the form @('10yyzzzz')
     and by a third byte of the form @('10wwwwuu')
     and by a fourth byte of the form @('10uuvvvv'),
     which together encode @('xyyyyzzzzwwwwuuuuvvvv'),
     which covers the range from 0 to 1FFFFFh.
     We return an error if there is no second or third or fourth byte.
     We return an error if the encoded value is below 10000h or above 10FFFFh.
     If all these checks pass,
     the code covers the character range from @('U+10000') to @('U+1FFFFF').")
   (xdoc::p
    "If the first byte read has any other value,
     either it is an invalid UTF-8 encoding (e.g. @('111...'))
     or it is an ASCII character that we do not accept (e.g. @('00000000')).
     We return an error in this case.")
   (xdoc::p
    "Note that all the non-ASCII characters that we accept
     just increment the column number by 1 and leave the line number unchanged.
     This may not be appropriate for certain Unicode characters,
     but for now we treat them in this simplified way."))
  (b* (((reterr) nil (irr-position) parstate)
       (parstate.bytes (parstate->bytes parstate))
       (parstate.position (parstate->position parstate))
       (parstate.chars-read (parstate->chars-read parstate))
       (parstate.chars-unread (parstate->chars-unread parstate))
       (parstate.size (parstate->size parstate))
       ((when (and (consp parstate.chars-unread)
                   (> parstate.size 0)))
        (b* ((char+pos (car parstate.chars-unread))
             (parstate (update-parstate->chars-unread
                        (cdr parstate.chars-unread) parstate))
             (parstate (update-parstate->chars-read
                        (cons char+pos parstate.chars-read) parstate))
             (parstate (update-parstate->size (1- parstate.size) parstate)))
          (retok (char+position->char char+pos)
                 (char+position->position char+pos)
                 parstate)))
       ((unless (and (consp parstate.bytes)
                     (> parstate.size 0)))
        (retok nil parstate.position parstate))
       (byte (car parstate.bytes))
       (bytes (cdr parstate.bytes))
       ;; ASCII except line feed and carriage return:
       ((when (or (= byte 9)
                  (= byte 11)
                  (= byte 12)
                  (and (<= 32 byte) (<= byte 126))))
        (b* ((parstate (update-parstate->bytes bytes parstate))
             (parstate (update-parstate->position
                        (position-inc-column 1 parstate.position) parstate))
             (parstate (update-parstate->chars-read
                        (cons (make-char+position
                               :char byte
                               :position parstate.position)
                              parstate.chars-read)
                        parstate))
             (parstate (update-parstate->size (1- parstate.size) parstate)))
          (retok byte parstate.position parstate)))
       ;; line feed:
       ((when (= byte 10))
        (b* ((parstate (update-parstate->bytes bytes parstate))
             (parstate (update-parstate->position
                        (position-inc-line 1 parstate.position) parstate))
             (parstate (update-parstate->chars-read
                        (cons (make-char+position
                               :char 10
                               :position parstate.position)
                              parstate.chars-read)
                        parstate))
             (parstate (update-parstate->size (1- parstate.size) parstate)))
          (retok 10 parstate.position parstate)))
       ;; carriage return:
       ((when (= byte 13))
        (b* (((mv bytes count) (if (and (consp bytes)
                                        (> parstate.size 1)
                                        (= (car bytes) 10))
                                   (mv (cdr bytes) 2)
                                 (mv bytes 1)))
             (parstate (update-parstate->bytes bytes parstate))
             (parstate (update-parstate->position
                        (position-inc-line 1 parstate.position) parstate))
             (parstate (update-parstate->chars-read
                        (cons (make-char+position
                               :char 10
                               :position parstate.position)
                              parstate.chars-read)
                        parstate))
             (parstate (update-parstate->size
                        (- parstate.size count) parstate)))
          (retok 10 parstate.position parstate)))
       ;; 2-byte UTF-8:
       ((when (= (logand byte #b11100000) #b11000000)) ; 110xxxyy
        (b* (((unless (and (consp bytes)
                           (> parstate.size 1)))
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 110... ~
                                          (i.e. between 192 and 223) ~
                                          of a two-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
             (byte2 (car bytes))
             (bytes (cdr bytes))
             ((unless (= (logand byte2 #b11000000) #b10000000)) ; 10yyzzzz
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 110... ~
                                          (i.e. between 192 and 223) ~
                                          of a two-byte UTF-8 encoding"
                                         byte)
                          :found (msg "the byte ~x0" byte2)))
             (code (+ (ash (logand byte #b00011111) 6)
                      (logand byte2 #b00111111)))
             ((when (< code #x80))
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "a value between 80h and 7FFh ~
                                          UTF-8-encoded in the two bytes ~
                                          (~x0 ~x1)"
                                         byte byte2)
                          :found (msg "the value ~x0" code)))
             (parstate (update-parstate->bytes bytes parstate))
             (parstate (update-parstate->position
                        (position-inc-column 1 parstate.position) parstate))
             (parstate (update-parstate->chars-read
                        (cons (make-char+position
                               :char code
                               :position parstate.position)
                              parstate.chars-read)
                        parstate))
             (parstate (update-parstate->size (- parstate.size 2) parstate)))
          (retok code parstate.position parstate)))
       ;; 3-byte UTF-8:
       ((when (= (logand byte #b11110000) #b11100000)) ; 1110xxxx
        (b* (((unless (and (consp bytes)
                           (> parstate.size 1)))
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 1110... ~
                                          (i.e. between 224 to 239) ~
                                          of a three-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
             (byte2 (car bytes))
             (bytes (cdr bytes))
             ((unless (= (logand byte2 #b11000000) #b10000000)) ; 10yyyyzz
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 1110... ~
                                          (i.e. between 224 and 239) ~
                                          of a three-byte UTF-8 encoding"
                                         byte)
                          :found (msg "the byte ~x0" byte2)))
             ((unless (and (consp bytes)
                           (> parstate.size 2)))
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 1110... ~
                                          (i.e. between 224 to 239) ~
                                          and the second byte ~x1 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          of a three-byte UTF-8 encoding"
                                         byte byte2)
                          :found "end of file"))
             (byte3 (car bytes))
             (bytes (cdr bytes))
             ((unless (= (logand byte3 #b11000000) #b10000000)) ; 10zzwwww
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 1110... ~
                                          (i.e. between 224 and 239) ~
                                          and the second byte ~x1 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          of a three-byte UTF-8 encoding"
                                         byte byte2)
                          :found (msg "the byte ~x0" byte3)))
             (code (+ (ash (logand byte #b00001111) 12)
                      (ash (logand byte2 #b00111111) 6)
                      (logand byte3 #b00111111)))
             ((when (< code #x800))
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "a value between 800h and FFFFh ~
                                          UTF-8-encoded in the three bytes ~
                                          (~x0 ~x1 ~x2)"
                                         byte byte2 byte3)
                          :found (msg "the value ~x0" code)))
             ((when (or (and (<= #x202a code)
                             (<= code #x202e))
                        (and (<= #x2066 code)
                             (<= code #x2069))))
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected "a Unicode character with code ~
                                     in the range 9-13 or 32-126 ~
                                     or 128-8233 or 8239-8293 or ~
                                     or 8298-55295 or 57344-1114111"
                          :found (char-to-msg code)))
             (parstate (update-parstate->bytes bytes parstate))
             (parstate (update-parstate->position
                        (position-inc-column 1 parstate.position) parstate))
             (parstate (update-parstate->chars-read
                        (cons (make-char+position
                               :char code
                               :position parstate.position)
                              parstate.chars-read)
                        parstate))
             (parstate (update-parstate->size (- parstate.size 3) parstate)))
          (retok code parstate.position parstate)))
       ;; 4-byte UTF-8:
       ((when (= (logand #b11111000 byte) #b11110000)) ; 11110xyy
        (b* (((unless (and (consp bytes)
                           (> parstate.size 1)))
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 to 247) ~
                                          of a four-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
             (byte2 (car bytes))
             (bytes (cdr bytes))
             ((unless (= (logand byte2 #b11000000) #b10000000)) ; 10yyzzzz
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 and 247) ~
                                          of a four-byte UTF-8 encoding"
                                         byte)
                          :found (msg "the byte ~x0" byte2)))
             ((unless (and (consp bytes)
                           (> parstate.size 2)))
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 to 247) ~
                                          and the second byte ~x1 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          of a four-byte UTF-8 encoding"
                                         byte byte2)
                          :found "end of file"))
             (byte3 (car bytes))
             (bytes (cdr bytes))
             ((unless (= (logand byte3 #b11000000) #b10000000)) ; 10wwwwuu
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 and 247) ~
                                          and the second byte ~x1 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          of a four-byte UTF-8 encoding"
                                         byte byte2)
                          :found (msg "the byte ~x0" byte3)))
             ((unless (and (consp bytes)
                           (> parstate.size 3)))
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 to 247) ~
                                          and the second byte ~x1 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          and the third byte ~x2 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          of a four-byte UTF-8 encoding"
                                         byte byte2 byte3)
                          :found "end of file"))
             (byte4 (car bytes))
             (bytes (cdr bytes))
             ((unless (= (logand byte4 #b11000000) #b10000000)) ; 10uuvvvv
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 and 247) ~
                                          and the second byte ~x1 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          and the third byte ~x2 ~
                                          of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          of a four-byte UTF-8 encoding"
                                         byte byte2 byte3)
                          :found (msg "the byte ~x0" byte4)))
             (code (+ (ash (logand byte #b00000111) 18)
                      (ash (logand byte2 #b00111111) 12)
                      (ash (logand byte3 #b00111111) 6)
                      (logand byte4 #b00111111)))
             ((when (or (< code #x10000)
                        (> code #x10ffff)))
              (reterr-msg :where (position-to-msg parstate.position)
                          :expected (msg "a value between 10000h and 10FFFFh ~
                                          UTF-8-encoded in the four bytes ~
                                          (~x0 ~x1 ~x2 ~x3)"
                                         byte byte2 byte3 byte4)
                          :found (msg "the value ~x0" code)))
             (parstate (update-parstate->bytes bytes parstate))
             (parstate (update-parstate->position
                        (position-inc-column 1 parstate.position) parstate))
             (parstate (update-parstate->chars-read
                        (cons (make-char+position
                               :char code
                               :position parstate.position)
                              parstate.chars-read)
                        parstate))
             (parstate (update-parstate->size (- parstate.size 4) parstate)))
          (retok code parstate.position parstate))))
    (reterr-msg :where (position-to-msg parstate.position)
                :expected "a byte in the range 9-13 or 32-126 or 192-223"
                :found (msg "the byte ~x0" byte)))
  :guard-hints (("Goal" :in-theory (e/d (len fix natp)
                                        ((:e tau-system))))) ; for speed
  :prepwork ((local (in-theory (enable acl2-numberp-when-bytep
                                       acl2-numberp-when-natp
                                       rationalp-when-bytep
                                       rationalp-when-natp
                                       integerp-when-natp
                                       natp-when-bytep
                                       natp-of-plus
                                       natp-of-logand
                                       natp-of-ash)))
             (local (include-book "arithmetic/top" :dir :system)))

  ///

  (defret parsize-of-read-char-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize len nfix))))

  (defret parsize-of-read-char-cond
    (implies (and (not erp)
                  char?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize len fix nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-char ((parstate parstatep))
  :returns (new-parstate parstatep :hyp (parstatep parstate))
  :short "Unread a character."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pop the character from the @('chars-read') stack
     and we push it onto the @('chars-unread') stack.")
   (xdoc::p
    "It is an internal error if the @('chars-read') stack is empty.
     It means that the calling code is wrong.
     In this case, after raising the hard error,
     logically we return a parser state
     where we push an irrelevant character and position,
     so that the theorem about @(tsee parsize) holds unconditionally."))
  (b* ((parstate.chars-read (parstate->chars-read parstate))
       (parstate.chars-unread (parstate->chars-unread parstate))
       (parstate.size (parstate->size parstate))
       ((unless (consp parstate.chars-read))
        (raise "Internal error: no character to unread.")
        (b* ((parstate (update-parstate->chars-unread
                        (cons (make-char+position
                               :char 0
                               :position (irr-position))
                              parstate.chars-unread)
                        parstate))
             (parstate (update-parstate->size (1+ parstate.size) parstate)))
          parstate))
       (char+pos (car parstate.chars-read))
       (parstate (update-parstate->chars-unread
                  (cons char+pos parstate.chars-unread) parstate))
       (parstate (update-parstate->chars-read
                  (cdr parstate.chars-read) parstate))
       (parstate (update-parstate->size (1+ parstate.size) parstate)))
    parstate)

  ///

  (defret parsize-of-unread-char
    (equal (parsize new-parstate)
           (1+ (parsize parstate)))
    :hints (("Goal" :in-theory (enable parsize len nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-chars ((n natp) (parstate parstatep))
  :returns (new-parstate parstatep :hyp (parstatep parstate))
  :short "Unread a specified number of characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "This repeatedly calls @(tsee unread-char)
     to unread zero or more characters.
     The number of characters is specified by @('n').
     This number may be 0."))
  (b* (((when (zp n)) (parstate-fix parstate))
       (parstate (unread-char parstate)))
    (unread-chars (1- n) parstate))

  ///

  (defret parsize-of-unread-chars
    (equal (parsize new-parstate)
           (+ (parsize parstate) (nfix n)))
    :hints (("Goal"
             :induct t
             :in-theory (enable nfix fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-identifier/keyword ((first-char (unsigned-byte-p 8 first-char))
                                (first-pos positionp)
                                (parstate parstatep))
  :guard (or (and (<= (char-code #\A) first-char)
                  (<= first-char (char-code #\Z)))
             (and (<= (char-code #\a) first-char)
                  (<= first-char (char-code #\z)))
             (= first-char (char-code #\_)))
  :returns (mv erp
               (lexeme lexemep)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex an identifier or keyword."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called after the first character of the identifier or keyword
     has been already read;
     that character is passed to this function.
     The position of that character is also passed as input.")
   (xdoc::p
    "Since grammatically keywords are identifiers,
     we just lex grammatical identifiers,
     but return a keyword lexeme if the grammatical identifier
     matches a keyword.
     If GCC extensions are supported,
     we check the grammatical identifier
     against some additional keywords;
     see the ABNF grammar rule for @('gcc-keyword').")
   (xdoc::p
    "Given that the first character (a letter or underscore)
     has already been read,
     it remains to read zero or more
     letters, digits, and underscores.
     These are read in a loop,
     which stops when no letter, digit, or underscore is read.
     The stopping happens if there is no next character (i.e. end of file),
     or the next character is something else;
     in the latter case, the character is unread,
     because it could be part of the next lexeme.
     If successful, the loop returns a list of characters (natural numbers),
     which the caller combines with the first character to form a string.
     This is an ASCII string by construction,
     so the characters all satisfy @('(unsigned-byte-p 7)'),
     but we use @('(unsigned-byte-p 8)')
     in the guard of this function and in the return type of the loop,
     because @(tsee nats=>string) has that as guard
     (more precisely, lists of that).
     If the ASCII string is a keyword, we return a keyword token.
     Otherwise, we return an identifier token."))
  (b* (((reterr) (irr-lexeme) (irr-span) parstate)
       ((erp rest-chars last-pos parstate)
        (lex-identifier/keyword-loop first-pos parstate))
       (span (make-span :start first-pos :end last-pos))
       (chars (cons first-char rest-chars))
       (string (acl2::nats=>string chars)))
    (if (or (member-equal string '("auto"
                                   "break"
                                   "case"
                                   "char"
                                   "const"
                                   "continue"
                                   "default"
                                   "do"
                                   "double"
                                   "else"
                                   "enum"
                                   "extern"
                                   "float"
                                   "for"
                                   "goto"
                                   "if"
                                   "inline"
                                   "int"
                                   "long"
                                   "register"
                                   "restrict"
                                   "return"
                                   "short"
                                   "signed"
                                   "sizeof"
                                   "static"
                                   "struct"
                                   "switch"
                                   "typedef"
                                   "union"
                                   "unsigned"
                                   "void"
                                   "volatile"
                                   "while"
                                   "_Alignas"
                                   "_Alignof"
                                   "_Atomic"
                                   "_Bool"
                                   "_Complex"
                                   "_Generic"
                                   "_Imaginary"
                                   "_Noreturn"
                                   "_Static_assert"
                                   "_Thread_local"))
            (and (parstate->gcc parstate)
                 (member-equal string '("__alignof"
                                        "__alignof__"
                                        "asm"
                                        "__asm"
                                        "__asm__"
                                        "__attribute"
                                        "__attribute__"
                                        "__builtin_va_list"
                                        "__extension__"
                                        "_Float128"
                                        "__inline"
                                        "__inline__"
                                        "__int128"
                                        "__restrict"
                                        "__restrict__"
                                        "__signed"
                                        "__signed__"
                                        "typeof"
                                        "__typeof"
                                        "__typeof__"))))
        (retok (lexeme-token (token-keyword string)) span parstate)
      (retok (lexeme-token (token-ident (ident string))) span parstate)))

  :prepwork

  ((define lex-identifier/keyword-loop ((pos-so-far positionp)
                                        (parstate parstatep))
     :returns (mv erp
                  (chars (unsigned-byte-listp 8 chars)
                         :hints (("Goal"
                                  :induct t
                                  :in-theory (enable unsigned-byte-p
                                                     integer-range-p
                                                     integerp-when-natp))))
                  (last-pos positionp)
                  (new-parstate parstatep :hyp (parstatep parstate)))
     :parents nil
     (b* (((reterr) nil (irr-position) parstate)
          ((erp char pos parstate) (read-char parstate))
          ((when (not char))
           (retok nil (position-fix pos-so-far) parstate))
          ((unless ; A-Z a-z 0-9 _
               (or (and (<= (char-code #\A) char) (<= char (char-code #\Z)))
                   (and (<= (char-code #\a) char) (<= char (char-code #\z)))
                   (and (<= (char-code #\0) char) (<= char (char-code #\9)))
                   (= char (char-code #\_))))
           (b* ((parstate (unread-char parstate)))
             (retok nil (position-fix pos-so-far) parstate)))
          ((erp chars last-pos parstate)
           (lex-identifier/keyword-loop pos parstate)))
       (retok (cons char chars) last-pos parstate))
     :measure (parsize parstate)
     :hints (("Goal" :in-theory (enable o< o-finp)))
     :verify-guards nil ; done below

     ///

     (verify-guards lex-identifier/keyword-loop
       :hints (("Goal" :in-theory (enable rationalp-when-natp))))

     (defret parsize-of-lex-identifier/keyword-loop-<=
       (<= (parsize new-parstate)
           (parsize parstate))
       :rule-classes :linear
       :hints (("Goal" :induct t)))))

  ///

  (defret parsize-of-lex-identifier/keyword-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-hexadecimal-digit ((parstate parstatep))
  :returns (mv erp
               (hexdig hex-digit-char-p
                       :hints
                       (("Goal" :in-theory (enable hex-digit-char-p
                                                   unsigned-byte-p
                                                   integer-range-p
                                                   integerp-when-natp))))
               (pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a hexadecimal digit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a hexadecimal digit:
     if the character is not a hexadecimal digit, it is an error.
     If the next character is present and is a hexadecimal digit,
     we return the corresponding ACL2 character,
     along with its position in the file."))
  (b* (((reterr) #\0 (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate))
       ((when (not char))
        (reterr-msg :where (position-to-msg pos)
                    :expected "a hexadecimal digit"
                    :found (char-to-msg char)))
       ((unless (or (and (<= (char-code #\0) char) ; 0
                         (<= char (char-code #\9))) ; 9
                    (and (<= (char-code #\A) char) ; A
                         (<= char (char-code #\F))) ; F
                    (and (<= (char-code #\a) char) ; a
                         (<= char (char-code #\f))))) ; f
        (reterr-msg :where (position-to-msg pos)
                    :expected "a hexadecimal digit"
                    :found (char-to-msg char))))
    (retok (code-char char) pos parstate))
  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp
                                           integerp-when-natp)))

  ///

  (defret parsize-of-lex-hexadecimal-digit-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-hexadecimal-digit-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-hex-quad ((parstate parstatep))
  :returns (mv erp
               (quad hex-quad-p)
               (last-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a quadruple of hexadecimal digits."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect four hexadecimal digits,
     so we call @(tsee lex-hexadecimal-digit) four times.
     We return the position of the last one."))
  (b* (((reterr) (irr-hex-quad) (irr-position) parstate)
       ((erp hexdig1 & parstate) (lex-hexadecimal-digit parstate))
       ((erp hexdig2 & parstate) (lex-hexadecimal-digit parstate))
       ((erp hexdig3 & parstate) (lex-hexadecimal-digit parstate))
       ((erp hexdig4 pos parstate) (lex-hexadecimal-digit parstate)))
    (retok (make-hex-quad :1st hexdig1
                          :2nd hexdig2
                          :3rd hexdig3
                          :4th hexdig4)
           pos
           parstate))

  ///

  (defret parsize-of-lex-hex-quad-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-hex-quad-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-*-digit ((pos-so-far positionp) (parstate parstatep))
  :returns (mv erp
               (decdigs dec-digit-char-listp
                        :hints
                        (("Goal"
                          :induct t
                          :in-theory (enable lex-*-digit
                                             dec-digit-char-p
                                             unsigned-byte-p
                                             integer-range-p
                                             integerp-when-natp))))
               (last-pos positionp)
               (next-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex zero or more (decimal) digits, as many as available."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, we read @('*digit'), in ABNF notation,
     i.e. a repetition of zero of more instances of @('digit').")
   (xdoc::p
    "The @('pos-so-far') input is the position that has been read so far,
     just before attempting to read the digits.
     The @('last-pos') output is the position of the last digit read,
     or @('pos-so-far') if there are no digits.
     The @('next-pos') output is the position just after the last digit read,
     or just after @('pos-so-far') if there are no digits.")
   (xdoc::p
    "We read the next character.
     If it does not exist, we return.
     If it exists but is not a digit,
     we put the character back and return.
     Otherwise, we recursively read zero or more,
     and we put the one just read in front.
     We always return the position of the last digit,
     or the input @('pos-so-far') if there is no digit:
     this input is the position read so far,
     just before the zero or more digits to be read."))
  (b* (((reterr) nil (irr-position) (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate))
       ((when (not char))
        (retok nil (position-fix pos-so-far) pos parstate))
       ((unless (and (<= (char-code #\0) char) ; 0
                     (<= char (char-code #\9)))) ; 9
        (b* ((parstate (unread-char parstate)))
          (retok nil (position-fix pos-so-far) pos parstate)))
       (decdig (code-char char))
       ((erp decdigs last-pos next-pos parstate) (lex-*-digit pos parstate)))
    (retok (cons decdig decdigs) last-pos next-pos parstate))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp
                                           integerp-when-natp)))

  ///

  (more-returns
   (decdigs true-listp
            :rule-classes :type-prescription))

  (defret parsize-of-lex-*-digit-uncond
    (<= (parsize new-parstate)
        (- (parsize parstate)
           (len decdigs)))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable fix len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-*-hexadecimal-digit ((pos-so-far positionp) (parstate parstatep))
  :returns (mv erp
               (hexdigs hex-digit-char-listp
                        :hints
                        (("Goal"
                          :induct t
                          :in-theory (enable lex-*-hexadecimal-digit
                                             hex-digit-char-p
                                             unsigned-byte-p
                                             integer-range-p
                                             integerp-when-natp))))
               (last-pos positionp)
               (next-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex zero or more hexadecimal digits, as many as available."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, we read @('*hexadecimal-digit'), in ABNF notation,
     i.e. a repetition of zero of more instances of @('hexadecimal-digit').")
   (xdoc::p
    "The @('pos-so-far') input is the position that has been read so far,
     just before attempting to read the digits.
     The @('last-pos') output is the position of the last digit read,
     or @('pos-so-far') if there are no digits.
     The @('next-pos') output is the position just after the last digit read,
     or just after @('pos-so-far') if there are no digits.")
   (xdoc::p
    "We read the next character.
     If it does not exist, we return.
     If it exists but is not a hexadecimal digit,
     we put the character back and return.
     Otherwise, we recursively read zero or more,
     and we put the one just read in front.
     We always return the position of the last hexadecimal character,
     or the input @('pos-so-far') if there is no hexadecimal character:
     this input is the position read so far,
     just before the zero or more hexadecimal digits to be read."))
  (b* (((reterr) nil (irr-position) (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate))
       ((when (not char))
        (retok nil (position-fix pos-so-far) pos parstate))
       ((unless (or (and (<= (char-code #\0) char) ; 0
                         (<= char (char-code #\9))) ; 9
                    (and (<= (char-code #\A) char) ; A
                         (<= char (char-code #\F))) ; F
                    (and (<= (char-code #\a) char) ; a
                         (<= char (char-code #\f))))) ; f
        (b* ((parstate (unread-char parstate)))
          (retok nil (position-fix pos-so-far) pos parstate)))
       (hexdig (code-char char))
       ((erp hexdigs last-pos next-pos parstate)
        (lex-*-hexadecimal-digit pos parstate)))
    (retok (cons hexdig hexdigs) last-pos next-pos parstate))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp
                                           integerp-when-natp)))

  ///

  (more-returns
   (hexdigs true-listp
            :rule-classes :type-prescription))

  (defret parsize-of-lex-*-hexadecimal-digit-uncond
    (<= (parsize new-parstate)
        (- (parsize parstate)
           (len hexdigs)))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable fix len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-escape-sequence ((parstate parstatep))
  :returns (mv erp
               (escape escapep)
               (last-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex an escape sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect an escape sequence,
     after reading the initial backslash.")
   (xdoc::p
    "We read the next character,
     and based on that we handle the different escape sequences.
     We return the position of the last character of the escape sequence.")
   (xdoc::p
    "If the next character is one for a simple escape,
     we return the simple escape.")
   (xdoc::p
    "If instead the next character is an octal digit,
     we read possibly another one and possibly yet another one,
     to see whether the octal escape sequence consists of
     one, two, or three octal digits.")
   (xdoc::p
    "If instead the next character starts a hexadecimal escape sequence,
     we proceed to read zero or more hexadecimal digits, as many as possible,
     and we check that there is at least one.")
   (xdoc::p
    "If instead the next character starts a universal character name,
     we read one or two quadruples of hexadecimal digits,
     based on the kind of escape sequence.")
   (xdoc::p
    "In all other cases, it is an error:
     although this starts like an escape sequence,
     it is not one."))
  (b* (((reterr) (irr-escape) (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate)))
    (cond
     ((not char)
      (reterr-msg :where (position-to-msg pos)
                  :expected "a single quote ~
                             or a double quote ~
                             or a question mark ~
                             or a backslash ~
                             or a letter in {a, b, f, n, r, t, v, u, U, x} ~
                             or an octal digit"
                  :found (char-to-msg char)))
     ((= char (char-code #\')) ; \ '
      (retok (escape-simple (simple-escape-squote)) pos parstate))
     ((= char (char-code #\")) ; \ "
      (retok (escape-simple (simple-escape-dquote)) pos parstate))
     ((= char (char-code #\?)) ; \ ?
      (retok (escape-simple (simple-escape-qmark)) pos parstate))
     ((= char (char-code #\\)) ; \ \
      (retok (escape-simple (simple-escape-bslash)) pos parstate))
     ((= char (char-code #\a)) ; \ a
      (retok (escape-simple (simple-escape-a)) pos parstate))
     ((= char (char-code #\b)) ; \ b
      (retok (escape-simple (simple-escape-b)) pos parstate))
     ((= char (char-code #\f)) ; \ f
      (retok (escape-simple (simple-escape-f)) pos parstate))
     ((= char (char-code #\n)) ; \ n
      (retok (escape-simple (simple-escape-n)) pos parstate))
     ((= char (char-code #\r)) ; \ r
      (retok (escape-simple (simple-escape-r)) pos parstate))
     ((= char (char-code #\t)) ; \ t
      (retok (escape-simple (simple-escape-t)) pos parstate))
     ((= char (char-code #\v)) ; \ v
      (retok (escape-simple (simple-escape-v)) pos parstate))
     ((and (<= (char-code #\0) char)
           (<= char (char-code #\7))) ; \ octdig
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((and char2
               (<= (char-code #\0) char2)
               (<= char2 (char-code #\7))) ; \ octdig octdig
          (b* (((erp char3 pos3 parstate) (read-char parstate)))
            (cond
             ((and char3
                   (<= (char-code #\0) char3)
                   (<= char3 (char-code #\7))) ; \ octdig octdig octdig
              (retok (escape-oct (oct-escape-three (code-char char)
                                                   (code-char char2)
                                                   (code-char char3)))
                     pos3
                     parstate))
             (t ; \ octdig \octdig other
              (b* ((parstate
                    ;; \ octdig octdig
                    (if char3 (unread-char parstate) parstate)))
                (retok (escape-oct (oct-escape-two (code-char char)
                                                   (code-char char2)))
                       pos2
                       parstate))))))
         (t ; \ octdig other
          (b* ((parstate (if char2 (unread-char parstate) parstate))) ; \octdig
            (retok (escape-oct (oct-escape-one (code-char char)))
                   pos
                   parstate))))))
     ((= char (char-code #\x))
      (b* (((erp hexdigs last-pos next-pos parstate)
            (lex-*-hexadecimal-digit pos parstate)))
        (if hexdigs
            (retok (escape-hex hexdigs) last-pos parstate)
          (reterr-msg :where (position-to-msg next-pos)
                      :expected "one or more hexadecimal digits"
                      :found "none"))))
     ((= char (char-code #\u))
      (b* (((erp quad pos parstate) (lex-hex-quad parstate)))
        (retok (escape-univ (univ-char-name-locase-u quad)) pos parstate)))
     ((= char (char-code #\U))
      (b* (((erp quad1 & parstate) (lex-hex-quad parstate))
           ((erp quad2 pos parstate) (lex-hex-quad parstate)))
        (retok (escape-univ (make-univ-char-name-upcase-u :quad1 quad1
                                                          :quad2 quad2))
               pos
               parstate)))
     (t
      (reterr-msg :where (position-to-msg pos)
                  :expected "a single quote ~
                             or a double quote ~
                             or a question mark ~
                             or a backslash ~
                             or a letter in {a, b, f, n, r, t, v, u, U, x} ~
                             or an octal digit"
                  :found (char-to-msg char)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp
                                           rationalp-when-natp
                                           integerp-when-natp
                                           oct-digit-char-p
                                           unsigned-byte-p
                                           integer-range-p)))

  ///

  (defret parsize-of-lex-escape-sequence-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-escape-sequence-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-*-c-char ((parstate parstatep))
  :returns (mv erp
               (cchars c-char-listp)
               (closing-squote-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex zero or more characters and escape sequences
          in a character constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, lex a @('*c-char'), in ABNF notation,
     i.e. a repetition of zero or more instances of @('c-char').")
   (xdoc::p
    "This is called when we expect a character constant,
     after reading the opening single quote of a character constant.
     If successful, this reads up to and including the closing single quote,
     and returns the position of the latter,
     along with the sequence of characters and escape sequences.")
   (xdoc::p
    "We read the next character;
     it is an error if there is none.
     It is also an error if the character is a new-line.
     If the character is a single quote, we end the recursion and return.
     If the character is a backslah,
     we attempt to read an escape sequence,
     then we read zero or more additional characters and escape sequences,
     and we combine them with the escape sequence.
     In all other cases,
     we take the character as is,
     we read zero or more additional characters and escape sequences,
     and we combine them with the character."))
  (b* (((reterr) nil (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate))
       ((unless char)
        (reterr-msg :where (position-to-msg pos)
                    :expected "an escape sequence or ~
                               any character other than ~
                               single quote or backslash or new-line"
                    :found (char-to-msg char)))
       ((when (= char (char-code #\'))) ; '
        (retok nil pos parstate))
       ((when (= char 10)) ; new-line
        (reterr-msg :where (position-to-msg pos)
                    :expected "an escape sequence or ~
                               any character other than ~
                               single quote or backslash or new-line"
                    :found (char-to-msg char)))
       ((erp cchar & parstate)
        (if (= char (char-code #\\)) ; \
            (b* (((erp escape pos parstate) (lex-escape-sequence parstate))
                 (cchar (c-char-escape escape)))
              (retok cchar pos parstate))
          (b* ((cchar (c-char-char char)))
            (retok cchar pos parstate))))
       ((erp cchars closing-squote-pos parstate) (lex-*-c-char parstate)))
    (retok (cons cchar cchars) closing-squote-pos parstate))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-*-c-char-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-lex-*-c-char-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (- (parsize parstate)
                        (len cchars)))))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable fix len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-*-s-char ((parstate parstatep))
  :returns (mv erp
               (schars s-char-listp)
               (closing-dquote-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex zero or more characters and escape sequences
          in a string literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, lex a @('*s-char'), in ABNF notation,
     i.e. a repetition of zero or more instances of @('s-char').")
   (xdoc::p
    "This is called when we expect a string literal,
     after reading the opening double quote of a string literal.
     If successful, this reads up to and including the closing double quote,
     and returns the position of the latter,
     along with the sequence of characters and escape sequences.")
   (xdoc::p
    "We read the next character;
     it is an error if there is none.
     It is also an error if the character is a new-line.
     If the character is a double quote, we end the recursion and return.
     If the character is a backslah,
     we attempt to read an escape sequence,
     then we read zero or more additional characters and escape sequences,
     and we combine them with the escape sequence.
     In all other cases,
     we take the character as is,
     we read zero or more additional characters and escape sequences,
     and we combine them with the character."))
  (b* (((reterr) nil (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate))
       ((unless char)
        (reterr-msg :where (position-to-msg pos)
                    :expected "an escape sequence or ~
                               any character other than ~
                               double quote or backslash"
                    :found (char-to-msg char)))
       ((when (= char (char-code #\"))) ; "
        (retok nil pos parstate))
       ((when (= char 10)) ; new-line
        (reterr-msg :where (position-to-msg pos)
                    :expected "an escape sequence or ~
                               any character other than ~
                               double quote or backslash"
                    :found (char-to-msg char)))
       ((erp schar & parstate)
        (if (= char (char-code #\\)) ; \
            (b* (((erp escape pos parstate) (lex-escape-sequence parstate))
                 (schar (s-char-escape escape)))
              (retok schar pos parstate))
          (b* ((schar (s-char-char char)))
            (retok schar pos parstate))))
       ((erp schars closing-dquote-pos parstate) (lex-*-s-char parstate)))
    (retok (cons schar schars) closing-dquote-pos parstate))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-*-s-char-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-lex-*-s-char-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (- (parsize parstate)
                        (len schars)))))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable len fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-character-constant ((cprefix? cprefix-optionp)
                                (first-pos positionp)
                                (parstate parstatep))
  :returns (mv erp
               (lexeme lexemep)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a character constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a character constant,
     after the opening single quote,
     and the prefix before that if present,
     have already been read.
     So we read zero or more characters and escape sequences,
     and ensure that there is at least one (according to the grammar).
     In the process of reading those characters and escape sequences,
     we read up to the closing single quote (see @(tsee lex-*-c-char)),
     whose position we use as the ending one of the span we return.
     The starting position of the span is passed to this function as input."))
  (b* (((reterr) (irr-lexeme) (irr-span) parstate)
       ((erp cchars closing-squote-pos parstate) (lex-*-c-char parstate))
       (span (make-span :start first-pos :end closing-squote-pos))
       ((unless cchars)
        (reterr-msg :where (position-to-msg closing-squote-pos)
                    :expected "one or more characters and escape sequences"
                    :found "none")))
    (retok (lexeme-token (token-const (const-char (cconst cprefix? cchars))))
           span
           parstate))

  ///

  (defret parsize-of-lex-character-constant-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-character-constant-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-stringlit ((eprefix? eprefix-optionp)
                       (first-pos positionp)
                       (parstate parstatep))
  :returns (mv erp
               (lexeme lexemep)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a string literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a string literal,
     after the opening double quote,
     and the prefix before that if present,
     have already been read.
     We read zero or more characters and escape sequences.
     In the process of reading those characters and escape sequences,
     we read up to the closing double quote (see @(tsee lex-*-s-char)),
     whose position we use as the ending one of the span we return.
     The starting position of the span is passed to this function as input."))
  (b* (((reterr) (irr-lexeme) (irr-span) parstate)
       ((erp schars closing-dquote-pos parstate) (lex-*-s-char parstate))
       (span (make-span :start first-pos :end closing-dquote-pos)))
    (retok (lexeme-token (token-string (stringlit eprefix? schars)))
           span
           parstate))

  ///

  (defret parsize-of-lex-stringlit-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-stringlit-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-isuffix-if-present ((parstate parstatep))
  :returns (mv erp
               (isuffix? isuffix-optionp)
               (last/next-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex an integer suffix, if present."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a suffix is found,
     the @('last/next-pos') output is the position of its last character.
     Otherwise, it is the first position where the suffix would start.")
   (xdoc::p
    "We read the next character.
     If there is no next character, there is no integer suffix.")
   (xdoc::p
    "If the next character is @('l') or @('L'),
     there must be an integer suffix starting with a length indication.
     We try to read a second @('l') or @('L') if any,
     to decide on whether the length indication
     is for @('long') or @('long long').
     After that, we read more to see if there is @('u') or @('U'),
     which provides a sign indication if present.
     Based on all the cases, we create the appropriate integer suffix.
     We unread any characters that are not part of the suffix,
     since they may form the next lexeme
     (whether that will pass parsing is a separate issue:
     here we follow the lexical rules for longest lexeme).")
   (xdoc::p
    "If the next character is @('u') or @('U'),
     there must be an integer suffix starting with a sign indication.
     We attempt to read an additional length indication,
     in a manner similar to the previous case,
     and we return the appropriate integer suffix at the end,
     unreading any characters that may be part of the next lexeme.")
   (xdoc::p
    "This code turned out to be verbose.
     We could shorten it by merging the treatment of
     lowercase @('l') and uppercase @('L'),
     single or double."))
  (b* (((reterr) nil (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate)))
    (cond
     ((not char) ; EOF
      (retok nil pos parstate))
     ((= char (char-code #\l)) ; l
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; l EOF
          (retok (isuffix-l (lsuffix-locase-l)) pos parstate))
         ((= char2 (char-code #\l)) ; l l
          (b* (((erp char3 pos3 parstate) (read-char parstate)))
            (cond
             ((not char3) ; l l EOF
              (retok (isuffix-l (lsuffix-locase-ll)) pos2 parstate))
             ((= char3 (char-code #\u)) ; l l u
              (retok (make-isuffix-lu :length (lsuffix-locase-ll)
                                      :unsigned (usuffix-locase-u))
                     pos3
                     parstate))
             ((= char3 (char-code #\U)) ; l l U
              (retok (make-isuffix-lu :length (lsuffix-locase-ll)
                                      :unsigned (usuffix-upcase-u))
                     pos3
                     parstate))
             (t ; l l other
              (b* ((parstate (unread-char parstate))) ; l l
                (retok (isuffix-l (lsuffix-locase-ll)) pos2 parstate))))))
         ((= char2 (char-code #\u)) ; l u
          (retok (make-isuffix-lu :length (lsuffix-locase-l)
                                  :unsigned (usuffix-locase-u))
                 pos2
                 parstate))
         ((= char2 (char-code #\U)) ; l U
          (retok (make-isuffix-lu :length (lsuffix-locase-l)
                                  :unsigned (usuffix-upcase-u))
                 pos2
                 parstate))
         (t ; l other
          (b* ((parstate (unread-char parstate))) ; l
            (retok (isuffix-l (lsuffix-locase-l)) pos parstate))))))
     ((= char (char-code #\L)) ; L
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; L EOF
          (retok (isuffix-l (lsuffix-upcase-l)) pos parstate))
         ((= char2 (char-code #\L)) ; L L
          (b* (((erp char3 pos3 parstate) (read-char parstate)))
            (cond
             ((not char3) ; L L EOF
              (retok (isuffix-l (lsuffix-upcase-ll)) pos2 parstate))
             ((= char3 (char-code #\u)) ; L L u
              (retok (make-isuffix-lu :length (lsuffix-upcase-ll)
                                      :unsigned (usuffix-locase-u))
                     pos3
                     parstate))
             ((= char3 (char-code #\U)) ; L L U
              (retok (make-isuffix-lu :length (lsuffix-upcase-ll)
                                      :unsigned (usuffix-upcase-u))
                     pos3
                     parstate))
             (t ; L L other
              (b* ((parstate (unread-char parstate))) ; LL
                (retok (isuffix-l (lsuffix-upcase-ll)) pos2 parstate))))))
         ((= char2 (char-code #\u)) ; L u
          (retok (make-isuffix-lu :length (lsuffix-upcase-l)
                                  :unsigned (usuffix-locase-u))
                 pos2
                 parstate))
         ((= char2 (char-code #\U)) ; L U
          (retok (make-isuffix-lu :length (lsuffix-upcase-l)
                                  :unsigned (usuffix-upcase-u))
                 pos2
                 parstate))
         (t ; L other
          (b* ((parstate (unread-char parstate))) ; L
            (retok (isuffix-l (lsuffix-upcase-l)) pos parstate))))))
     ((= char (char-code #\u)) ; u
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; u EOF
          (retok (isuffix-u (usuffix-locase-u)) pos parstate))
         ((= char2 (char-code #\l)) ; u l
          (b* (((erp char3 pos3 parstate) (read-char parstate)))
            (cond
             ((not char3) ; u l EOF
              (retok (make-isuffix-ul :unsigned (usuffix-locase-u)
                                      :length (lsuffix-locase-l))
                     pos2
                     parstate))
             ((= char3 (char-code #\l)) ; u l l
              (retok (make-isuffix-ul :unsigned (usuffix-locase-u)
                                      :length (lsuffix-locase-ll))
                     pos3
                     parstate))
             (t ; u l other
              (b* ((parstate (unread-char parstate))) ; u l
                (retok (make-isuffix-ul :unsigned (usuffix-locase-u)
                                        :length (lsuffix-locase-l))
                       pos2
                       parstate))))))
         ((= char2 (char-code #\L)) ; u L
          (b* (((erp char3 pos3 parstate) (read-char parstate)))
            (cond
             ((not char3) ; u L EOF
              (retok (make-isuffix-ul :unsigned (usuffix-locase-u)
                                      :length (lsuffix-upcase-l))
                     pos2
                     parstate))
             ((= char3 (char-code #\L)) ; u L L
              (retok (make-isuffix-ul :unsigned (usuffix-locase-u)
                                      :length (lsuffix-upcase-ll))
                     pos3
                     parstate))
             (t ; u L other
              (b* ((parstate (unread-char parstate))) ; u L
                (retok (make-isuffix-ul :unsigned (usuffix-locase-u)
                                        :length (lsuffix-upcase-l))
                       pos2
                       parstate))))))
         (t ; u other
          (b* ((parstate (unread-char parstate)))
            (retok (isuffix-u (usuffix-locase-u)) pos parstate))))))
     ((= char (char-code #\U)) ; U
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; U EOF
          (retok (isuffix-u (usuffix-upcase-u)) pos parstate))
         ((= char2 (char-code #\l)) ; U l
          (b* (((erp char3 pos3 parstate) (read-char parstate)))
            (cond
             ((not char3) ; U l EOF
              (retok (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                      :length (lsuffix-locase-l))
                     pos2
                     parstate))
             ((= char3 (char-code #\l)) ; U l l
              (retok (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                      :length (lsuffix-locase-ll))
                     pos3
                     parstate))
             (t ; U l other
              (b* ((parstate (unread-char parstate))) ; U l
                (retok (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                        :length (lsuffix-locase-l))
                       pos2
                       parstate))))))
         ((= char2 (char-code #\L)) ; U L
          (b* (((erp char3 pos3 parstate) (read-char parstate)))
            (cond
             ((not char3) ; U L EOF
              (retok (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                      :length (lsuffix-upcase-l))
                     pos2
                     parstate))
             ((= char3 (char-code #\L)) ; U L L
              (retok (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                      :length (lsuffix-upcase-ll))
                     pos3
                     parstate))
             (t ; U L other
              (b* ((parstate (unread-char parstate)))
                (retok (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                        :length (lsuffix-upcase-l))
                       pos2
                       parstate))))))
         (t ; U other
          (b* ((parstate (unread-char parstate))) ; U
            (retok (isuffix-u (usuffix-upcase-u)) pos parstate))))))
     (t ; other
      (b* ((parstate (unread-char parstate)))
        (retok nil pos parstate)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-isuffix-if-present-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-isuffix-if-present-cond
    (implies (and (not erp)
                  isuffix?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-fsuffix-if-present ((parstate parstatep))
  :returns (mv erp
               (fsuffix? fsuffix-optionp)
               (last/next-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a floating suffix, if present."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a suffix is found, the @('last/next-pos') output is its position.
     Otherwise, it is the position where the suffix would be.")
   (xdoc::p
    "If there is no next character, there is no suffix.
     Otherwise, there are four possibilities for suffixes.
     If the next character is not part of any suffix,
     we unread the character and return no suffix."))
  (b* (((reterr) nil (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate)))
    (cond
     ((not char)
      (retok nil pos parstate))
     ((= char (char-code #\f)) ; f
      (retok (fsuffix-locase-f) pos parstate))
     ((= char (char-code #\F)) ; F
      (retok (fsuffix-upcase-f) pos parstate))
     ((= char (char-code #\l)) ; l
      (retok (fsuffix-locase-l) pos parstate))
     ((= char (char-code #\L)) ; L
      (retok (fsuffix-upcase-l) pos parstate))
     (t ; other
      (b* ((parstate (unread-char parstate)))
        (retok nil pos parstate)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-fsuffix-if-present-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-fsuffix-if-present-cond
    (implies (and (not erp)
                  fsuffix?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-sign-if-present ((parstate parstatep))
  :returns (mv erp
               (sign? sign-optionp)
               (last/next-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a sign, if present."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a sign is found, the @('last/next-pos') output is its position.
     Otherwise, it is the position where the suffix would be.")
   (xdoc::p
    "If there is no next character, there is no sign.
     Otherwise, we read the next character,
     and return a sign if appropriate,
     otherwise no sign and we put back the character."))
  (b* (((reterr) nil (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate)))
    (cond
     ((not char)
      (retok nil pos parstate))
     ((= char (char-code #\+)) ; +
      (retok (sign-plus) pos parstate))
     ((= char (char-code #\-)) ; -
      (retok (sign-minus) pos parstate))
     (t ; other
      (b* ((parstate (unread-char parstate)))
        (retok nil pos parstate)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-sign-if-present-ucond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-sign-if-present-cond
    (implies (and (not erp)
                  sign?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-dec-expo-if-present ((parstate parstatep))
  :returns (mv erp
               (expo? dec-expo-optionp)
               (last/next-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a decimal exponent, if present."
  :long
  (xdoc::topstring
   (xdoc::p
    "If an exponent is found,
     the @('last/next-pos') output is the position of its last character.
     Otherwise, it is the first position where the exponent would start.")
   (xdoc::p
    "If there is no next character, there is no exponent.
     If the next character is not @('e') or @('E'),
     there is no exponent.
     Otherwise, we read a sign (if present),
     and then we read zero or more digits.
     If there are no digits, there is no exponent:
     we put back the sign character (if it was present),
     and we put back the @('e') or @('E').
     If there are digits, we return an appropriate exponent."))
  (b* (((reterr) nil (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate)))
    (cond
     ((not char)
      (retok nil pos parstate))
     ((or (= char (char-code #\e)) ; e
          (= char (char-code #\E))) ; E
      (b* ((prefix (if (= char (char-code #\e))
                       (dec-expo-prefix-locase-e)
                     (dec-expo-prefix-upcase-e)))
           ((erp sign? sign-pos parstate) (lex-sign-if-present parstate))
           (pos-so-far (if sign? sign-pos pos))
           ((erp digits last-pos & parstate)
            (lex-*-digit pos-so-far parstate))
           ((unless digits)
            (b* ((parstate
                  (if sign? (unread-char parstate) parstate)) ; put back sign
                 (parstate (unread-char parstate))) ; put back e/E
              (retok nil pos parstate))))
        (retok (make-dec-expo :prefix prefix
                              :sign? sign?
                              :digits digits)
               last-pos
               parstate)))
     (t ; other
      (b* ((parstate (unread-char parstate))) ; put back other
        (retok nil pos parstate)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-dec-expo-if-present-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-dec-expo-if-present-cond
    (implies (and (not erp)
                  expo?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-dec-expo ((parstate parstatep))
  :returns (mv erp
               (expo dec-expop)
               (last-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a decimal exponent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect an exponent.
     We try to read a @('e') or @('E'), which must be present.
     Then we read an optional sign.
     Then we read zero or more decimal digits,
     of which there must be at least one."))
  (b* (((reterr) (irr-dec-expo) (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate)))
    (cond
     ((not char)
      (reterr-msg :where (position-to-msg pos)
                  :expected "a character in {e, E}"
                  :found (char-to-msg char)))
     ((or (= char (char-code #\e)) ; e
          (= char (char-code #\E))) ; E
      (b* ((prefix (if (= char (char-code #\e))
                       (dec-expo-prefix-locase-e)
                     (dec-expo-prefix-upcase-e)))
           ((erp sign? sign-last-pos parstate)
            (lex-sign-if-present parstate))
           ((erp digits digits-last-pos digits-next-pos parstate)
            (lex-*-digit sign-last-pos parstate))
           ((unless digits)
            (reterr-msg :where (position-to-msg digits-next-pos)
                        :expected "one or more digits"
                        :found "none")))
        (retok (make-dec-expo :prefix prefix
                              :sign? sign?
                              :digits digits)
               digits-last-pos
               parstate)))
     (t ; other
      (reterr-msg :where (position-to-msg pos)
                  :expected "a character in {e, E}"
                  :found (char-to-msg char)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-dec-expo-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-dec-expo-cond
    (implies (and (not erp)
                  expo?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-bin-expo ((parstate parstatep))
  :returns (mv erp
               (expo bin-expop)
               (last-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a binary exponent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a binary exponent.
     We try to read a @('p') or @('P'), which must be present.
     Then we read an optional sign.
     Then we read zero or more decimal digits,
     of which there must be at least one."))
  (b* (((reterr) (irr-bin-expo) (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate)))
    (cond
     ((not char)
      (reterr-msg :where (position-to-msg pos)
                  :expected "a character in {p, P}"
                  :found (char-to-msg char)))
     ((or (= char (char-code #\p)) ; p
          (= char (char-code #\P))) ; P
      (b* ((prefix (if (= char (char-code #\p))
                       (bin-expo-prefix-locase-p)
                     (bin-expo-prefix-upcase-p)))
           ((erp sign? sign-last-pos parstate)
            (lex-sign-if-present parstate))
           ((erp digits digits-last-pos digits-next-pos parstate)
            (lex-*-digit sign-last-pos parstate))
           ((unless digits)
            (reterr-msg :where (position-to-msg digits-next-pos)
                        :expected "one or more digits"
                        :found "none")))
        (retok (make-bin-expo :prefix prefix
                              :sign? sign?
                              :digits digits)
               digits-last-pos
               parstate)))
     (t ; other
      (reterr-msg :where (position-to-msg pos)
                  :expected "a character in {p, P}"
                  :found (char-to-msg char)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-bin-expo-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-bin-expo-cond
    (implies (and (not erp)
                  expo?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-full-ppnumber ((ends-in-e booleanp)
                             (parstate parstatep))
  :returns (mv erp (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Check that the numerical constant just read
          is a full preprocessing number."
  :long
  (xdoc::topstring
   (xdoc::p
    "In C, integer and floating constants are not lexed ``directly''
     according to their grammar rules in [C].
     First, preprocessing tokens must be recognized,
     defined by <i>preprocessing-token</i> in [C:6.4] [C:A.1.1].
     These include preprocessing numbers,
     defined by <i>pp-number</i> in [C:6.4.8] [C:A.1.9],
     which start with a digit, optionally preceded by a dot,
     and are followed by identifier characters (including digits and letter),
     as well as plus and minus signs immediately preceded by exponent letters,
     as well as periods
     [C:6.4.8/2].
     Thus, preprocessing numbers lexically include
     all integer and floating constants [C:6.4.8/3],
     and much more, e.g. @('638xyyy.e+E-').")
   (xdoc::p
    "As part of translation phase 7 [C:5.1.1.2],
     preprocessing tokens are converted to tokens.
     This includes converting preprocessing numbers
     to integer and floating constants,
     checking that they are in fact integer or floating constants,
     e.g. the example above would not pass the checks.")
   (xdoc::p
    "In our lexer, we lex integer and floating constants directly,
     but we need to ensure that the behavior is the same as
     if we had gone through preprocessing numbers.
     We do that as follow:
     after fully recognizing an integer or floating constant,
     we check whether there is a subsequent character
     of the kind that would be part of a preprocessing number:
     if there is, it is an error,
     because the preprocessing number cannot be converted to a constant,
     due to the extra character(s).")
   (xdoc::p
    "This function performs this check.
     It is called after an integer or floating constant
     has been recognized completely during lexing.
     This function attempts to read the next character,
     and unless there is no next character,
     or the next character is one
     that would not be part of the preprocessing number,
     an error is returned.
     In case of success, there is no additional result (it is just a check),
     except for the possibly updated parser state.")
   (xdoc::p
    "If the next character exists and is
     a letter or a digit or an underscore or a dot,
     it would be part of the preprocessing number,
     so we return an error.
     Otherwise, the check succeeds, except in one case.
     The case is that the next character is @('+') or @('-'),
     but the last character of the integer or floating constant just read
     (before calling this function)
     is @('e') or @('E'):
     in that case, according to the grammar rule of <i>pp-number</i> in [C],
     the @('e+') or @('e-') or @('-E+') or @('E-')
     would be part of the preprocessing number,
     and thus it would cause an error:
     so the check in this function fails in this case.
     This function takes a flag saying whether
     the last character of the read integer or floating constant
     was @('e') or @('E');
     it is passed by the caller, who has read that constant.")
   (xdoc::p
    "Note that, because of the rules on preprocessing numbers,
     in C this code is syntactically illegal")
   (xdoc::codeblock
    "int x = 0xe+1; // illegal")
   (xdoc::p
    "whereas this code is syntactically legal")
   (xdoc::codeblock
    "int x = 0xf+1; // legal")
   (xdoc::p
    "The reason is that @('0xe+1') is a whole preprocessing number,
     while @('0xf+1') is not;
     the latter is initially lexed as
     the preprocessing number @('0xf')
     followed by the punctuator @('+')
     followed by the preprocesing number @('1').
     These three can all be successfully converted
     fron preprocessing tokens to tokens;
     in particular, @('0xf') is a valid hexadecimal integer constant.
     But @('0xe+1') is not a hexadecimal (or integer) constant,
     and so it cannot be converted to one."))
  (b* (((reterr) parstate)
       ((erp char pos parstate) (read-char parstate))
       ((when (not char)) (retok parstate))
       ((when (or (and (<= (char-code #\A) char)
                       (<= char (char-code #\Z)))
                  (and (<= (char-code #\a) char)
                       (<= char (char-code #\a)))
                  (and (<= (char-code #\0) char)
                       (<= char (char-code #\9)))
                  (= char (char-code #\_))
                  (= char (char-code #\.))
                  (and ends-in-e
                       (or (= char (char-code #\+))
                           (= char (char-code #\-))))))
        (reterr-msg :where (position-to-msg pos)
                    :expected (msg "a character other than ~
                                    a letter ~
                                    or a digit ~
                                    or an underscore ~
                                    or a dot~s0"
                                   (if ends-in-e " or a plus or a minus" ""))
                    :found (char-to-msg char)))
       (parstate (unread-char parstate)))
    (retok parstate))
  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp)))

  ///

  (defret parsize-of-check-full-ppnumber-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-hex-iconst/fconst ((hprefix hprefixp)
                               (prefix-last-pos positionp)
                               (parstate parstatep))
  :returns (mv erp
               (const constp)
               (last-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a hexadecimal integer or floating constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a hexadecimal constant,
     after reading the hexadecimal prefix @('0x') or @('0X').")
   (xdoc::p
    "First we read zero or more hexadecimal digits.
     If there are none, we check if the next character is a dot,
     because we may have a constant like @('0x.1') for example.
     If there is no dot, it is an error.
     If there is a dot, we read zero or more hexadecimal digits.
     If there are none, it is an error.
     If there are some, we read the binary exponent,
     which must be present (otherwise it is an error);
     then we read the suffix if present,
     and we return an appropriate hexadecimal constant.")
   (xdoc::p
    "If instead there are hexadecimal digits after the prefix,
     we check whether the next character is a dot.
     If it is, we read zero or more hexadecimal digits,
     then a binary exponent
     (which must be present, otherwise it is an error),
     and finally a suffix if present;
     we return an appropriate hexadecimal floating constant.
     If instead there is no dot,
     we check whether there is
     the starting @('p') or @('P') of a binary exponent:
     if there is, it must be a floating constant,
     so we proceed to read the binary exponent,
     then a suffix if present;
     if there is not, it must be an integer constant.")
   (xdoc::p
    "Just before returning the constant,
     we use @(tsee check-full-ppnumber),
     for the reasons explained there."))
  (b* (((reterr) (irr-const) (irr-position) parstate)
       ;; 0 x/X
       ((erp hexdigs hexdigs-last-pos & parstate)
        (lex-*-hexadecimal-digit prefix-last-pos parstate)))
    ;; 0 x/X [hexdigs]
    (cond
     ((not hexdigs) ; 0 x/X
      (b* (((erp char pos parstate) (read-char parstate)))
        (cond
         ((not char) ; 0 x/X EOF
          (reterr-msg :where (position-to-msg pos)
                      :expected "a hexadecimal digit or a dot"
                      :found (char-to-msg char)))
         ((= char (char-code #\.)) ; 0 x/X .
          (b* (((erp hexdigs2 & hexdigs2-next-pos parstate)
                (lex-*-hexadecimal-digit pos parstate)))
            ;; 0 x/X . [hexdigs2]
            (cond
             ((not hexdigs2) ; 0 x/X .
              (reterr-msg :where (position-to-msg hexdigs2-next-pos)
                          :expected "a hexadecimal digit or a dot"
                          :found (char-to-msg nil)))
             (t ; 0 x/X . hexdigs2
              (b* (((erp expo expo-last-pos parstate)
                    (lex-bin-expo parstate)))
                ;; 0 x/X . hexdigs2 expo
                (b* (((erp fsuffix? suffix-last/next-pos parstate)
                      (lex-fsuffix-if-present parstate))
                     ;; 0 x/X . hexdigs2 expo [fsuffix]
                     ((erp parstate) (check-full-ppnumber nil parstate)))
                  (retok (const-float
                          (make-fconst-hex
                           :prefix hprefix
                           :core (make-hex-core-fconst-frac
                                  :significand (make-hex-frac-const
                                                :before nil
                                                :after hexdigs2)
                                  :expo expo)
                           :suffix? fsuffix?))
                         (cond (fsuffix? suffix-last/next-pos)
                               (t expo-last-pos))
                         parstate)))))))
         (t ; 0 x/X other
          (reterr-msg :where (position-to-msg pos)
                      :expected "a hexadecimal digit or a dot"
                      :found (char-to-msg char))))))
     (t ; 0 x/X hexdigs
      (b* (((erp char pos parstate) (read-char parstate)))
        (cond
         ((not char) ; 0 x/X hexdigs EOF
          (retok (const-int
                  (make-iconst
                   :core (make-dec/oct/hex-const-hex
                          :prefix hprefix
                          :digits hexdigs)
                   :suffix? nil))
                 hexdigs-last-pos
                 parstate))
         ((= char (char-code #\.)) ; 0 x/X hexdigs .
          (b* (((erp hexdigs2 & & parstate)
                (lex-*-hexadecimal-digit pos parstate)))
            ;; 0 x/X hexdigs . [hexdigs2]
            (cond
             ((not hexdigs2) ; 0 x/X hexdigs .
              (b* (((erp expo expo-last-pos parstate)
                    (lex-bin-expo parstate))
                   ;; 0 x/X hexdigs . expo
                   ((erp fsuffix? suffix-last/next-pos parstate)
                    (lex-fsuffix-if-present parstate))
                   ;; 0 x/X hexdigs . expo [suffix]
                   ((erp parstate) (check-full-ppnumber nil parstate)))
                (retok (const-float
                        (make-fconst-hex
                         :prefix hprefix
                         :core (make-hex-core-fconst-frac
                                :significand (make-hex-frac-const
                                              :before hexdigs
                                              :after nil)
                                :expo expo)
                         :suffix? fsuffix?))
                       (cond (fsuffix? suffix-last/next-pos)
                             (t expo-last-pos))
                       parstate)))
             (t ; 0 x/X hexdigs . hexdigs2
              (b* (((erp expo expo-last-pos parstate)
                    (lex-bin-expo parstate))
                   ;; 0 x/X hexdigs . hexdigs2 expo
                   ((erp fsuffix? suffix-last/next-pos parstate)
                    (lex-fsuffix-if-present parstate))
                   ;; 0 x/X hexdigs . hexdigs2 expo [suffix]
                   ((erp parstate) (check-full-ppnumber nil parstate)))
                (retok (const-float
                        (make-fconst-hex
                         :prefix hprefix
                         :core (make-hex-core-fconst-frac
                                :significand (make-hex-frac-const
                                              :before hexdigs
                                              :after hexdigs2)
                                :expo expo)
                         :suffix? fsuffix?))
                       (cond (fsuffix? suffix-last/next-pos)
                             (t expo-last-pos))
                       parstate))))))
         ((or (= char (char-code #\p)) ; 0 x/X hexdigs p
              (= char (char-code #\P))) ; 0 x/X hexdigs P
          (b* ((parstate (unread-char parstate)) ; 0 x/X hexdigs
               ((erp expo expo-last-pos parstate) (lex-bin-expo parstate))
               ;; 0 x/X hexdigs expo
               ((erp fsuffix? suffix-last/next-pos parstate)
                (lex-fsuffix-if-present parstate))
               ;; 0 x/X hexdigs expo [suffix]
               ((erp parstate) (check-full-ppnumber nil parstate)))
            (retok (const-float
                    (make-fconst-hex
                     :prefix hprefix
                     :core (make-hex-core-fconst-int
                            :significand hexdigs
                            :expo expo)
                     :suffix? fsuffix?))
                   (cond (fsuffix? suffix-last/next-pos)
                         (t expo-last-pos))
                   parstate)))
         (t ; 0 x/X hexdigs other
          (b* ((parstate (unread-char parstate)) ; 0 x/X hexdigs
               ((erp isuffix? suffix-last/next-pos parstate)
                (lex-isuffix-if-present parstate))
               ;; 0 x/X hexdigs [suffix]
               ((erp parstate) (check-full-ppnumber (and
                                                   (member (car (last hexdigs))
                                                           '(#\e #\E))
                                                   t)
                                                  parstate)))
            (retok (const-int
                    (make-iconst
                     :core (make-dec/oct/hex-const-hex
                            :prefix hprefix
                            :digits hexdigs)
                     :suffix? isuffix?))
                   (cond (isuffix? suffix-last/next-pos)
                         (t hexdigs-last-pos))
                   parstate))))))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-hex-iconst/fconst-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable nfix))))

  (defret parsize-of-lex-hex-iconst/fconst-cond
    (implies (and (not erp)
                  const?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-dec-iconst/fconst ((first-digit dec-digit-char-p)
                               (first-pos positionp)
                               (parstate parstatep))
  :guard (not (equal first-digit #\0))
  :returns (mv erp
               (const constp)
               (last-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a decimal integer or floating constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a decimal constant,
     after reading the first digit, when that digit is not @('0').
     The first digit, and its position, are passed to this function.")
   (xdoc::p
    "First we read as many additional decimal digits as possible,
     of which there may be none.
     Then we attempt to read the next character,
     and we do different things based on that.")
   (xdoc::p
    "If there is no character after the digits,
     we have an integer decimal constant.")
   (xdoc::p
    "If the next character is a dot,
     then this must be a decimal floating constant.
     We read as many digits as possible after the dot;
     there may no other digits.
     Then we attempt to read a decimal exponent, if any.
     Then a floating suffix, if any.
     Finally, if @(tsee check-full-ppnumber) succeeds
     (see the documentation of that function for details),
     we return the appropriate constant.")
   (xdoc::p
    "If the next character is @('e') or @('E'),
     then this must be a decimal floating constant,
     consisting of an integer and an exponent.
     We read the exponent after putting back the letter;
     the exponent must be present for the constant to be valid.
     We read a floating suffix if present.
     If @(tsee check-full-ppnumber) succeeds,
     we return the appropriate constant.")
   (xdoc::p
    "Otherwise, this must be a decimal integer constant,
     if it is a valid constant at all.
     We put back the character and read an integer suffix if present.
     If @(tsee check-full-ppnumber) passes,
     we return the appropriate integer constant."))
  (b* (((reterr) (irr-const) (irr-position) parstate)
       ;; 1-9
       ((erp decdigs decdigs-last-pos & parstate)
        (lex-*-digit first-pos parstate))
       ;; 1-9 [decdigs]
       ((erp char pos parstate) (read-char parstate)))
    (cond
     ((not char) ; 1-9 [decdigs] EOF
      (retok (const-int
              (make-iconst
               :core (make-dec/oct/hex-const-dec
                      :value (str::dec-digit-chars-value
                              (cons first-digit decdigs)))
               :suffix? nil))
             (cond (decdigs decdigs-last-pos)
                   (t (position-fix first-pos)))
             parstate))
     ((= char (char-code #\.)) ; 1-9 [decdigs] .
      (b* (((erp decdigs2 decdigs2-last-pos & parstate)
            (lex-*-digit pos parstate))
           ;; 1-9 [decdigs] . [decdigs2]
           ((erp expo? expo-last/next-pos parstate)
            (lex-dec-expo-if-present parstate))
           ;; 1-9 [decdigs] . [decdigs2] [expo]
           ((erp fsuffix? suffix-last/next-pos parstate)
            (lex-fsuffix-if-present parstate))
           ;; 1-9 [decdigs] . [decdigs2] [expo] [suffix]
           ((erp parstate) (check-full-ppnumber nil parstate))
           (core (if decdigs2
                     (if expo?
                         (make-dec-core-fconst-frac
                          :significand (make-dec-frac-const
                                        :before (cons first-digit
                                                      decdigs)
                                        :after decdigs2)
                          :expo? expo?)
                       (make-dec-core-fconst-frac
                        :significand (make-dec-frac-const
                                      :before (cons first-digit
                                                    decdigs)
                                      :after decdigs2)
                        :expo? nil))
                   (if expo?
                       (make-dec-core-fconst-frac
                        :significand (make-dec-frac-const
                                      :before (cons first-digit
                                                    decdigs)
                                      :after nil)
                        :expo? expo?)
                     (make-dec-core-fconst-frac
                      :significand (make-dec-frac-const
                                    :before (cons first-digit
                                                  decdigs)
                                    :after nil)
                      :expo? nil)))))
        (retok (const-float
                (make-fconst-dec :core core
                                 :suffix? fsuffix?))
               (cond (fsuffix? suffix-last/next-pos)
                     (expo? expo-last/next-pos)
                     (decdigs2 decdigs2-last-pos)
                     (t pos))
               parstate)))
     ((or (= char (char-code #\e)) ; 1-9 [decdigs] e
          (= char (char-code #\E))) ; 1-9 [decdigs] E
      (b* ((parstate (unread-char parstate)) ; 1-9 [decdigs]
           ((erp expo expo-last-pos parstate) (lex-dec-expo parstate))
           ;; 1-9 [decdigs] expo
           ((erp fsuffix? suffix-last/next-pos parstate)
            (lex-fsuffix-if-present parstate))
           ;; 1-9 [decdigs] expo [suffix]
           ((erp parstate) (check-full-ppnumber nil parstate)))
        (retok (const-float
                (make-fconst-dec
                 :core (make-dec-core-fconst-int
                        :significand (cons first-digit
                                           decdigs)
                        :expo expo)
                 :suffix? fsuffix?))
               (cond (fsuffix? suffix-last/next-pos)
                     (t expo-last-pos))
               parstate)))
     (t ; 1-9 [decdigs] other
      (b* ((parstate (unread-char parstate)) ; 1-9 [decdigs]
           ((erp isuffix? suffix-last/next-pos parstate)
            (lex-isuffix-if-present parstate))
           ;; 1-9 [decdigs] [suffix]
           ((erp parstate) (check-full-ppnumber nil parstate)))
        (retok (const-int
                (make-iconst
                 :core (make-dec/oct/hex-const-dec
                        :value (str::dec-digit-chars-value
                                (cons first-digit decdigs)))
                 :suffix? isuffix?))
               (cond (isuffix? suffix-last/next-pos)
                     (decdigs decdigs-last-pos)
                     (t (position-fix first-pos)))
               parstate)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp
                                           dec-digit-char-p
                                           str::dec-digit-chars-value
                                           str::dec-digit-char-value
                                           posp
                                           fix)))
  :prepwork
  ((local (include-book "kestrel/arithmetic-light/expt" :dir :system))
   (local (include-book "kestrel/arithmetic-light/times" :dir :system)))

  ///

  (defret parsize-of-lex-dec-iconst/fconst-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-dec-fconst ((first-digit-after-dot dec-digit-char-p)
                        (first-pos-after-dot positionp)
                        (parstate parstatep))
  :returns (mv erp
               (const constp)
               (last-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a decimal floating constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expec a decimal floating constant,
     after we have read a dot followed by a decimal digit.")
   (xdoc::p
    "We read as many additional decimal digits as available.
     Then we read an exponent, if present.
     Then a floating suffix, if present.
     Finally, if @(tsee check-full-ppnumber) passes,
     we return an appropriate floating constant."))
  (b* (((reterr) (irr-const) (irr-position) parstate)
       ;; . decdig
       ((erp decdigs decdigs-last-pos & parstate)
        (lex-*-digit first-pos-after-dot parstate))
       ;; . decdig [decdigs]
       ((erp expo? expo-last/next-pos parstate)
        (lex-dec-expo-if-present parstate))
       ;; . decdig [decdigs] [expo]
       ((erp fsuffix? suffix-last/next-pos parstate)
        (lex-fsuffix-if-present parstate))
       ;; . decdig [decdigs] [expo] [suffix]
       ((erp parstate) (check-full-ppnumber nil parstate))
       (core (if expo?
                 (make-dec-core-fconst-frac
                  :significand (make-dec-frac-const
                                :before nil
                                :after (cons first-digit-after-dot
                                             decdigs))
                  :expo? expo?)
               (make-dec-core-fconst-frac
                :significand (make-dec-frac-const
                              :before nil
                              :after (cons first-digit-after-dot
                                           decdigs))
                :expo? nil))))
    (retok (const-float
            (make-fconst-dec :core core
                             :suffix? fsuffix?))
           (cond (fsuffix? suffix-last/next-pos)
                 (expo? expo-last/next-pos)
                 (decdigs decdigs-last-pos)
                 (t (position-fix first-pos-after-dot)))
           parstate))

  ///

  (defret parsize-of-lex-dec-fconst-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-non-octal-digit ((parstate parstatep))
  :returns (mv erp
               (char natp)
               (pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a non-octal digit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only called by @(tsee lex-oct-iconst-/-dec-fconst),
     for the purpose of returning an informative error message
     when a sequence of digits is read that are not all octal,
     but the sequence cannot form a decimal constant.
     The caller first unreads all those digits,
     and then calls this function to find the (first) offeding digit.
     So we expect that a non-octal digit will be found,
     and it is thus an internal error if it is not found
     (which should never happen)."))
  (b* (((reterr) 0 (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate))
       ((unless char)
        (raise "Internal error: no non-octal digit found.")
        (reterr t))
       ((unless (and (<= (char-code #\0) char)
                     (<= char (char-code #\7))))
        (retok char pos parstate)))
    (lex-non-octal-digit parstate))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp)))

  ///

  (defret parsize-of-lex-non-octal-digit-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-lex-non-octal-digit-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-oct-iconst-/-dec-fconst ((zero-pos positionp) (parstate parstatep))
  :returns (mv erp
               (const constp)
               (last-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called after the initial @('0') has been read,
     and when it is not immediately followed by @('x') or @('X').
     (The caller checks whether the next character is @('x') or @('X'),
     and if it is not it puts the character back into the parser state.)
     Thus, it meaans that we are reading
     either an octal integer constant
     or a decimal floating constant.
     Note that there are no octal floating constants,
     and that decimal integer constants do no start with @('0').
     The position of the already read initial @('0')
     is passed as the input @('zero-pos') to this function.")
   (xdoc::p
    "We read all the digits that follow the initial @('0'),
     which could be none, or one, or more.
     If these are all octal digits in fact (i.e. no @('8') or @('9'),
     this could be an octal constant.
     However, it could be also the start of a decimal constant
     whose initial digits, before the dot or exponent,
     happen to be all octal digits as well.
     So we look at the next character first.
     If there is no next character,
     and all the digits are octal,
     then we have an octal constant.
     If there is no next character,
     but not all the digits are octal,
     it is an error,
     because recall that, as explained in @(tsee check-full-ppnumber),
     no all-octal prefix of this sequence could form an octal constant:
     the subsequent non-all-octal digits are
     part of the preprocessing number,
     which means that the octal constant would have extra characters.
     In order to find the first offending digit
     and report an informative error message,
     we unread all the digits and we call @(tsee lex-non-octal-digit)
     to find the offending digit.")
   (xdoc::p
    "If there is a dot or an @('e') or an @('E') just after the digits,
     this cannot be an octal constant,
     because it would mean that the preprocessing number
     has at least those extra characters.
     So it must be a decimal constant, if it is anything valid.
     So we proceed according to the grammar of decimal floating constants.")
   (xdoc::p
    "If there is any other character just after the digits,
     there are two cases.
     If all the digits read are octal,
     we may well have an octal constant,
     so long as the subsequent characters
     are not part of the preprocessing number,
     except for possibly an integer suffix.
     If not all the digits are octal,
     then it cannot be an octal constant,
     but it cannot be a decimal constant either,
     because in the latter case the digits would have to be followed by
     a dot or an exponent;
     so it is an error in that case."))
  (b* (((reterr) (irr-const) (irr-position) parstate)
       ;; 0
       ((erp digits digits-last-pos & parstate)
        (lex-*-digit zero-pos parstate))
       ;; 0 [digits]
       ((erp char pos parstate) (read-char parstate)))
    (cond
     ((not char) ; 0 [digits]
      (cond
       ((oct-digit-char-listp digits) ; 0 [octdigs]
        (retok (const-int
                (make-iconst
                 :core (make-dec/oct/hex-const-oct
                        :leading-zeros (1+ (oct-iconst-leading-zeros digits))
                        :value (str::oct-digit-chars-value digits))
                 :suffix? nil))
               (cond (digits digits-last-pos)
                     (t (position-fix zero-pos)))
               parstate))
       (t ; 0 not-all-octal-digits
        (b* ((parstate (unread-chars (len digits) parstate)) ; 0
             ((erp nonoctdig pos parstate) (lex-non-octal-digit parstate)))
          (reterr-msg :where (position-to-msg pos)
                      :expected "octal digit"
                      :found (char-to-msg nonoctdig))))))
     ((= char (char-code #\.)) ; 0 [digits] .
      (b* (((erp digits2 digits2-last-pos & parstate)
            (lex-*-digit pos parstate))
           ;; 0 [digits] . [digits2]
           ((erp expo? expo-last/next-pos parstate)
            (lex-dec-expo-if-present parstate))
           ;; 0 [digits] . [digits2] [expo]
           ((erp fsuffix? suffix-last/next-pos parstate)
            (lex-fsuffix-if-present parstate))
           ;; 0 [digits] . [digits2] [expo] [suffix]
           ((erp parstate) (check-full-ppnumber nil parstate))
           (core (cond
                  (digits2 ; 0 [digits] . digits2 [expo] [suffix]
                   (cond
                    (expo? ; 0 [digits] . digits2 expo [suffix]
                     (make-dec-core-fconst-frac
                      :significand (make-dec-frac-const
                                    :before (cons #\0 digits)
                                    :after digits2)
                      :expo? expo?))
                    (t ; 0 [digits] . digits2 [suffix]
                     (make-dec-core-fconst-frac
                      :significand (make-dec-frac-const
                                    :before (cons #\0 digits)
                                    :after digits2)
                      :expo? nil))))
                  (t ; 0 [digits] . [expo] [suffix]
                   (cond
                    (expo? ; 0 [digits] . expo [suffix]
                     (make-dec-core-fconst-frac
                      :significand (make-dec-frac-const
                                    :before (cons #\0 digits)
                                    :after nil)
                      :expo? expo?))
                    (t ; 0 [digits] . [suffix]
                     (make-dec-core-fconst-frac
                      :significand (make-dec-frac-const
                                    :before (cons #\0 digits)
                                    :after nil)
                      :expo? nil)))))))
        (retok (const-float
                (make-fconst-dec :core core
                                 :suffix? fsuffix?))
               (cond (fsuffix? suffix-last/next-pos)
                     (expo? expo-last/next-pos)
                     (digits2 digits2-last-pos)
                     (t pos))
               parstate)))
     ((or (= char (char-code #\e)) ; 0 [digits] e
          (= char (char-code #\E))) ; 0 [digits] E
      (b* ((parstate (unread-char parstate)) ; 0 [digits]
           ((erp expo expo-last-pos parstate) (lex-dec-expo parstate))
           ;; 0 [digits] expo
           ((erp fsuffix? suffix-last/next-pos parstate)
            (lex-fsuffix-if-present parstate))
           ;; 0 [digits] expo [suffix]
           ((erp parstate) (check-full-ppnumber nil parstate)))
        (retok (const-float
                (make-fconst-dec
                 :core (make-dec-core-fconst-int
                        :significand (cons #\0 digits)
                        :expo expo)
                 :suffix? fsuffix?))
               (cond (fsuffix? suffix-last/next-pos)
                     (t expo-last-pos))
               parstate)))
     (t ; 0 [digits] other
      (cond
       ((oct-digit-char-listp digits) ; 0 [octdigs] other
        (b* ((parstate (unread-char parstate)) ; 0 [octdigs]
             ((erp isuffix? suffix-last/next-pos parstate)
              (lex-isuffix-if-present parstate))
             ;; 0 [octdigs] [suffix]
             ((erp parstate) (check-full-ppnumber nil parstate)))
          (retok (const-int
                  (make-iconst
                   :core (make-dec/oct/hex-const-oct
                          :leading-zeros (1+ (oct-iconst-leading-zeros digits))
                          :value (str::oct-digit-chars-value digits))
                   :suffix? isuffix?))
                 (cond (isuffix? suffix-last/next-pos)
                       (digits digits-last-pos)
                       (t (position-fix zero-pos)))
                 parstate)))
       (t ; 0 not-all-octal-digits
        (b* ((parstate (unread-chars (len digits) parstate)) ; 0
             ((erp nonoctdig pos parstate) (lex-non-octal-digit parstate)))
          (reterr-msg :where (position-to-msg pos)
                      :expected "octal digit"
                      :found (char-to-msg nonoctdig))))))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  :prepwork
  ((define oct-iconst-leading-zeros ((octdigs oct-digit-char-listp))
     :returns (count natp)
     :parents nil
     (b* (((when (endp octdigs)) 0)
          (octdig (car octdigs)))
       (if (eql octdig #\0)
           (1+ (oct-iconst-leading-zeros (cdr octdigs)))
         0))))

  ///

  (defret parsize-of-lex-oct-iconst-/-dec-fconst-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-iconst/fconst ((first-digit dec-digit-char-p)
                           (first-pos positionp)
                           (parstate parstatep))
  :returns (mv erp
               (const constp)
               (last-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex an integer or floating constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect an integer or floating constant,
     after reading the first (decimal) digit of the constant.
     The first digit and its position are passed to this function.")
   (xdoc::p
    "If the first digit is a @('0'), we check the next character.
     If there is no next character, we have the octal constant @('0').
     If instead the next character is @('x') or @('X'),
     we must have a hexadecimal constant,
     for which we call a separate function.
     If instead the next character is something else,
     we must have an octal integer or decimal floating constant:
     we put back the character and call a separate function.")
   (xdoc::p
    "If instead the first digit is @('1') to @('9'),
     we must have a decimal integer or floating constant,
     for which we use a separate function."))
  (b* (((reterr) (irr-const) (irr-position) parstate))
    (cond
     ((eql first-digit #\0) ; 0
      (b* (((erp char pos parstate) (read-char parstate)))
        (cond
         ((not char) ; 0 EOF
          (retok (const-int
                  (make-iconst
                   :core (make-dec/oct/hex-const-oct
                          :leading-zeros 1
                          :value 0)
                   :suffix? nil))
                 (position-fix first-pos)
                 parstate))
         ((or (= char (char-code #\x)) ; 0 x
              (= char (char-code #\X))) ; 0 X
          (b* ((hprefix (if (= char (char-code #\x))
                            (hprefix-locase-0x)
                          (hprefix-upcase-0x))))
            (lex-hex-iconst/fconst hprefix pos parstate)))
         (t ; 0 other
          (b* ((parstate (unread-char parstate))) ; 0
            (lex-oct-iconst-/-dec-fconst first-pos parstate))))))
     (t ; 1-9
      (lex-dec-iconst/fconst first-digit first-pos parstate))))
  :guard-debug t
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-iconst/fconst-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-block-comment ((first-pos positionp) (parstate parstatep))
  :returns (mv erp
               (lexeme lexemep)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a block comment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a block comment,
     after we have read the initial @('/*').")
   (xdoc::p
    "Following the mutually recursive rules of the grammar,
     we have two mutually recursive loop functions,
     which scan through the characters
     until the end of the comment is reached,
     or until the end of file is reached
     (in which case it is an error).
     In case of success, we retutn a comment lexeme,
     which currently contains no information
     (but that may change in the future).
     The span of the comment is calculated from
     the first position (of the @('/') in @('/*')),
     passed to this function,
     and the last position (of the @('/') in the closing @('*/')),
     returned by the loop function."))
  (b* (((reterr) (irr-lexeme) (irr-span) parstate)
       ((erp last-pos parstate) (lex-rest-of-block-comment first-pos parstate)))
    (retok (lexeme-comment)
           (make-span :start first-pos :end last-pos)
           parstate))

  :prepwork

  ((defines lex-block-comment-loops

     (define lex-rest-of-block-comment ((first-pos positionp)
                                        (parstate parstatep))
       :returns (mv erp
                    (last-pos positionp)
                    (new-parstate parstatep :hyp (parstatep parstate)))
       (b* (((reterr) (irr-position) parstate)
            ((erp char pos parstate) (read-char parstate)))
         (cond
          ((not char) ; EOF
           (reterr-msg :where (position-to-msg pos)
                       :expected "a character"
                       :found (char-to-msg char)
                       :extra (msg "The block comment starting at ~@1 ~
                                    never ends."
                                   (position-to-msg first-pos))))
          ((= char (char-code #\*)) ; *
           (lex-rest-of-block-comment-after-star first-pos parstate))
          (t ; other
           (lex-rest-of-block-comment first-pos parstate))))
       :measure (parsize parstate))

     (define lex-rest-of-block-comment-after-star ((first-pos positionp)
                                                   (parstate parstatep))
       :returns (mv erp
                    (last-pos positionp)
                    (new-parstate parstatep :hyp (parstatep parstate)))
       (b* (((reterr) (irr-position) parstate)
            ((erp char pos parstate) (read-char parstate)))
         (cond
          ((not char) ; EOF
           (reterr-msg :where (position-to-msg pos)
                       :expected "a character"
                       :found (char-to-msg char)
                       :extra (msg "The block comment starting at ~@1 ~
                                    never ends."
                                   (position-to-msg first-pos))))
          ((= char (char-code #\/)) ; /
           (retok pos parstate))
          ((= char (char-code #\*)) ; *
           (lex-rest-of-block-comment-after-star first-pos parstate))
          (t ; other
           (lex-rest-of-block-comment first-pos parstate))))
       :measure (parsize parstate))

     :hints (("Goal" :in-theory (enable o< o-finp)))

     :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

     ///

     (std::defret-mutual parsize-of-lex-block-comment-loops-uncond
       (defret parsize-of-lex-rest-of-block-comment-uncond
         (<= (parsize new-parstate)
             (parsize parstate))
         :rule-classes :linear
         :fn lex-rest-of-block-comment)
       (defret parsize-of-lex-resto-of-block-comment-after-star-uncond
         (<= (parsize new-parstate)
             (parsize parstate))
         :rule-classes :linear
         :fn lex-rest-of-block-comment-after-star))

     (std::defret-mutual parsize-of-lex-block-comment-loops-cond
       (defret parsize-of-lex-rest-of-block-comment-cond
         (implies (not erp)
                  (<= (parsize new-parstate)
                      (1- (parsize parstate))))
         :rule-classes :linear
         :fn lex-rest-of-block-comment)
       (defret parsize-of-lex-resto-of-block-comment-after-star-cond
         (implies (not erp)
                  (<= (parsize new-parstate)
                      (1- (parsize parstate))))
         :rule-classes :linear
         :fn lex-rest-of-block-comment-after-star))))

  ///

  (defret parsize-of-lex-block-comment-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-block-comment-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-line-comment ((first-pos positionp) (parstate parstatep))
  :returns (mv erp
               (lexeme lexemep)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a line comment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a line comment,
     after reading the initial @('//').")
   (xdoc::p
    "We read characters in a loop until
     either we find a new-line character (success)
     or we find end of file (failure).
     In case of success, we return
     a lexeme that currently contains no information
     (but that may change in the future),
     and a span calculated from
     the position of the first @('/') in the opening @('//'),
     which is passed to this function,
     and the position of the closing new-line,
     which is returned by the loop function."))
  (b* (((reterr) (irr-lexeme) (irr-span) parstate)
       ((erp last-pos parstate) (lex-line-comment-loop first-pos parstate)))
    (retok (lexeme-comment)
           (make-span :start first-pos :end last-pos)
           parstate))

  :prepwork

  ((define lex-line-comment-loop ((first-pos positionp) (parstate parstatep))
     :returns (mv erp
                  (last-pos positionp)
                  (new-parstate parstatep :hyp (parstatep parstate)))
     :parents nil
     (b* (((reterr) (irr-position) parstate)
          ((erp char pos parstate) (read-char parstate)))
       (cond
        ((not char) ; EOF
         (reterr-msg :where (position-to-msg pos)
                     :expected "a character"
                     :found (char-to-msg char)
                     :extra (msg "The line comment starting at ~@1 ~
                                  never ends."
                                 (position-to-msg first-pos))))
        ((= char 10) ; new-line
         (retok pos parstate))
        (t ; other
         (lex-line-comment-loop first-pos parstate))))
     :measure (parsize parstate)
     :hints (("Goal" :in-theory (enable o< o-finp)))
     :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

     ///

     (defret parsize-of-lex-line-comment-loop-uncond
       (<= (parsize new-parstate)
           (parsize parstate))
       :rule-classes :linear
       :hints (("Goal" :induct t)))

     (defret parsize-of-lex-line-comment-loop-cond
       (implies (not erp)
                (<= (parsize new-parstate)
                    (1- (parsize parstate))))
       :rule-classes :linear
       :hints (("Goal" :induct t)))))

  ///

  (defret parsize-of-lex-line-comment-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-line-comment-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-lexeme ((parstate parstatep))
  :returns (mv erp
               (lexeme? lexeme-optionp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a lexeme."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level lexing function.
     It returns the next lexeme found in the parser state,
     or @('nil') if we reached the end of the file;
     an error is returned if lexing fails.")
   (xdoc::p
    "First we get the next character, propagating errors.
     If there is no next character, we return @('nil') for no lexeme,
     with the span whose start and end positions
     are both the position just past the end of the file.
     Otherwise, we do a case analysis on that next character.")
   (xdoc::ul
    (xdoc::li
     "If the next character is white space, we return a white-space lexeme.
      No other lexeme starts with a white-space character,
      so this is the only possibility.")
    (xdoc::li
     "If the next character is a letter,
      it could start an identifier or keyword,
      but it could also start character constants or string literals.
      Specifically, if the letter is @('u'), @('U'), or @('L'),
      it could be a prefix of a character constant or string literal.
      We must try this possibility before trying an identifier or keyword,
      because we always need to lex the longest possible sequence of characters
      [C:6.4/4]:
      if we tried identifiers or keywords first,
      for example
      we would erroneously lex the character constant @('u\'a\'')
      as the identifier @('u') followed by
      the unprefixed character constant @('\'a\'').
      According to the grammar, an identifier is also an enumeration constant,
      so the lexing of an identifier is always ambiguous;
      we always consider it as an identifier (not an enumeration constant),
      but we can reclassify it as an enumeration during type checking
      (outside the lexer and parser).")
    (xdoc::li
     "If the next character is @('u'), and there are no subsequent characters,
      we lex it as an identifier.
      If the following character is a single quote,
      we attempt to lex a character constant with the appropriate prefix;
      if the following character is a double quote,
      we attempt to lex a string literal with the appropriate prefix.
      These are the only two real possibilities in these two cases.
      Strictly speaking,
      if the lexing of the character constant or string literal fails,
      we should lex @('u') as an identifier and then continue lexing,
      but at that point the only possibilty would be
      an unprefixed character constant or string literal,
      which would fail again; so we can fail sooner without loss.
      If the character immediately following @('u') is @('8'),
      then we need to look at the character after that.
      If there is none, we lex the identifier @('u8').
      If there is one and is double quote,
      then we attempt to lex a string literal with the appropriate prefix,
      which again is the only possibilty,
      and again we can immediately fail if this fails.
      If the character after @('u8') is not a double quote,
      we put back that character and @('8'),
      and we lex @('u...') as an identifier or keyword.
      Also, if the character after @('u') was not
      any of the ones mentioned above,
      we put it back and we lex @('u...') as an identifier or keyword.")
    (xdoc::li
     "If the next character is @('U') or @('L'),
      we proceed similarly to the case of @('u'),
      but things are simpler because there is no @('8') to handle.")
    (xdoc::li
     "If the next character is a letter or underscore,
      it must start an identifier or keyword.
      This is the only possibility,
      since we have already tried
      a prefixed character constant or string literal.")
    (xdoc::li
     "If the next character is a digit,
      it must start an integer or floating constant.
      This is the only possibility.")
    (xdoc::li
     "If the next character is @('.'),
      it may start a decimal floating constant,
      or it could be the punctuator @('.'),
      or it could start the punctuator @('...').
      So we examine the following characters.
      If there is none, we have the punctuator @('.').
      If the following character is a digit,
      this must start a decimal floating constant.
      If the following character is another @('.),
      and there is a further @('.') after it,
      we have the punctuator @('...').
      In all other cases, we just have the punctuator @('.'),
      and we put back the additional character(s) read,
      since they may be starting a different lexeme.")
    (xdoc::li
     "If the next character is a single quote,
      it must start an unprefixed character constant.")
    (xdoc::li
     "If the next character is a double quote,
      it must start an unprefixed string literal.")
    (xdoc::li
     "If the next character is @('/'),
      it could start a comment,
      or the punctuator @('/='),
      or it could be just the punctuator @('/').
      We examine the following character.
      If there is none, we have the punctuator @('/').
      If the following character is @('*'),
      it must be a block comment.
      If the following character is @('/'),
      it must be a line comment.
      If the following character is @('='),
      it must be the punctuator @('/=').
      If the following character is none of the above,
      we just have the punctuator @('/').")
    (xdoc::li
     "The remaining cases are for punctuators.
      Some punctuators are prefixes of others,
      and so we need to first try and lex the longer ones,
      using code similar to the one for other lexemes explained above.
      Some punctuators are not prefixes of others,
      and so they can be immediately decided.")))

  (b* (((reterr) nil (irr-span) parstate)
       ((erp char first-pos parstate) (read-char parstate))
       ((unless char)
        (retok nil
               (make-span :start first-pos :end first-pos)
               parstate)))

    (cond

     ((or (= char 32) ; SP
          (and (<= 9 char) (<= char 12))) ; HT LF VT FF
      (retok (lexeme-whitespace)
             (make-span :start first-pos :end first-pos)
             parstate))

     ((= char (char-code #\u)) ; u
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; u EOF
          (retok (lexeme-token (token-ident (ident "u")))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\')) ; u '
          (lex-character-constant (cprefix-locase-u) first-pos parstate))
         ((= char2 (char-code #\")) ; u "
          (lex-stringlit (eprefix-locase-u) first-pos parstate))
         ((= char2 (char-code #\8)) ; u 8
          (b* (((erp char3 & parstate) (read-char parstate)))
            (cond
             ((not char3) ; u 8 EOF
              (retok (lexeme-token (token-ident (ident "u8")))
                     (make-span :start first-pos :end pos2)
                     parstate))
             ((= char3 (char-code #\")) ; u 8 "
              (lex-stringlit (eprefix-locase-u8) first-pos parstate))
             (t ; u 8 other
              (b* ((parstate (unread-char parstate)) ; u 8
                   (parstate (unread-char parstate))) ; u
                (lex-identifier/keyword char first-pos parstate))))))
         (t ; u other
          (b* ((parstate (unread-char parstate))) ; u
            (lex-identifier/keyword char first-pos parstate))))))

     ((= char (char-code #\U)) ; U
      (b* (((erp char2 & parstate) (read-char parstate)))
        (cond
         ((not char2) ; U EOF
          (retok (lexeme-token (token-ident (ident "U")))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\')) ; U '
          (lex-character-constant (cprefix-upcase-u) first-pos parstate))
         ((= char2 (char-code #\")) ; U "
          (lex-stringlit (eprefix-upcase-u) first-pos parstate))
         (t ; U other
          (b* ((parstate (unread-char parstate))) ; U
            (lex-identifier/keyword char first-pos parstate))))))

     ((= char (char-code #\L)) ; L
      (b* (((erp char2 & parstate) (read-char parstate)))
        (cond
         ((not char2) ; L EOF
          (retok (lexeme-token (token-ident (ident "L")))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\')) ; L '
          (lex-character-constant (cprefix-upcase-l) first-pos parstate))
         ((= char2 (char-code #\")) ; L "
          (lex-stringlit (eprefix-upcase-l) first-pos parstate))
         (t ; L other
          (b* ((parstate (unread-char parstate))) ; L
            (lex-identifier/keyword char first-pos parstate))))))

     ((or (and (<= (char-code #\A) char) (<= char (char-code #\Z))) ; A-Z
          (and (<= (char-code #\a) char) (<= char (char-code #\z))) ; a-z
          (= char (char-code #\_))) ; _
      (lex-identifier/keyword char first-pos parstate))

     ((and (<= (char-code #\0) char) (<= char (char-code #\9))) ; 0-9
      (b* (((erp const last-pos parstate)
            (lex-iconst/fconst (code-char char) first-pos parstate)))
        (retok (lexeme-token (token-const const))
               (make-span :start first-pos :end last-pos)
               parstate)))

     ((= char (char-code #\.)) ; .
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; . EOF
          (retok (lexeme-token (token-punctuator "."))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((and (<= (char-code #\0) char2) (<= char2 (char-code #\9))) ; . 0-9
          (b* (((erp const last-pos parstate)
                (lex-dec-fconst (code-char char2) pos2 parstate)))
            (retok (lexeme-token (token-const const))
                   (make-span :start first-pos :end last-pos)
                   parstate)))
         ((= char2 (char-code #\.)) ; . .
          (b* (((erp char3 pos3 parstate) (read-char parstate)))
            (cond
             ((not char3) ; . . EOF
              (b* ((parstate (unread-char parstate))) ; .
                (retok (lexeme-token (token-punctuator "."))
                       (make-span :start first-pos :end first-pos)
                       parstate)))
             ((= char3 (char-code #\.)) ; . . .
              (retok (lexeme-token (token-punctuator "..."))
                     (make-span :start first-pos :end pos3)
                     parstate))
             (t ; . . other
              (b* ((parstate (unread-char parstate)) ; . .
                   (parstate (unread-char parstate))) ; .
                (retok (lexeme-token (token-punctuator "."))
                       (make-span :start first-pos :end first-pos)
                       parstate))))))
         (t ; . other
          (b* ((parstate (unread-char parstate))) ; .
            (retok (lexeme-token (token-punctuator "."))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((= char (char-code #\')) ; '
      (lex-character-constant nil first-pos parstate))

     ((= char (char-code #\")) ; "
      (lex-stringlit nil first-pos parstate))

     ((= char (char-code #\/)) ; /
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; / EOF
          (retok (lexeme-token (token-punctuator "/"))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\*)) ; / *
          (lex-block-comment first-pos parstate))
         ((= char2 (char-code #\/)) ; / /
          (lex-line-comment first-pos parstate))
         ((= char2 (char-code #\=)) ; / =
          (retok (lexeme-token (token-punctuator "/="))
                 (make-span :start first-pos :end pos2)
                 parstate))
         (t ; / other
          (b* ((parstate (unread-char parstate))) ; /
            (retok (lexeme-token (token-punctuator "/"))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((or (= char (char-code #\[)) ; [
          (= char (char-code #\])) ; ]
          (= char (char-code #\()) ; (
          (= char (char-code #\))) ; )
          (= char (char-code #\{)) ; {
          (= char (char-code #\})) ; }
          (= char (char-code #\~)) ; ~
          (= char (char-code #\?)) ; ?
          (= char (char-code #\,)) ; ,
          (= char (char-code #\;))) ; ;
      (retok (lexeme-token
              (token-punctuator (str::implode (list (code-char char)))))
             (make-span :start first-pos :end first-pos)
             parstate))

     ((= char (char-code #\*)) ; *
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; * EOF
          (retok (lexeme-token (token-punctuator "*"))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\=)) ; * =
          (retok (lexeme-token (token-punctuator "*="))
                 (make-span :start first-pos :end pos2)
                 parstate))
         (t ; * other
          (b* ((parstate (unread-char parstate)))
            (retok (lexeme-token (token-punctuator "*"))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((= char (char-code #\^)) ; ^
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; ^ EOF
          (retok (lexeme-token (token-punctuator "^"))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\=)) ; ^ =
          (retok (lexeme-token (token-punctuator "^="))
                 (make-span :start first-pos :end pos2)
                 parstate))
         (t ; ^ other
          (b* ((parstate (unread-char parstate)))
            (retok (lexeme-token (token-punctuator "^"))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((= char (char-code #\!)) ; !
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; ! EOF
          (retok (lexeme-token (token-punctuator "!"))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\=)) ; ! =
          (retok (lexeme-token (token-punctuator "!="))
                 (make-span :start first-pos :end pos2)
                 parstate))
         (t ; ! other
          (b* ((parstate (unread-char parstate)))
            (retok (lexeme-token (token-punctuator "!"))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((= char (char-code #\=)) ; =
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; = EOF
          (retok (lexeme-token (token-punctuator "="))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\=)) ; = =
          (retok (lexeme-token (token-punctuator "=="))
                 (make-span :start first-pos :end pos2)
                 parstate))
         (t ; = other
          (b* ((parstate (unread-char parstate)))
            (retok (lexeme-token (token-punctuator "="))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((= char (char-code #\:)) ; :
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; : EOF
          (retok (lexeme-token (token-punctuator ":"))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\>)) ; : >
          (retok (lexeme-token (token-punctuator ":>"))
                 (make-span :start first-pos :end pos2)
                 parstate))
         (t ; : other
          (b* ((parstate (unread-char parstate)))
            (retok (lexeme-token (token-punctuator ":"))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((= char (char-code #\#)) ; #
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; # EOF
          (retok (lexeme-token (token-punctuator "#"))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\#)) ; # #
          (retok (lexeme-token (token-punctuator "##"))
                 (make-span :start first-pos :end pos2)
                 parstate))
         (t ; # other
          (b* ((parstate (unread-char parstate)))
            (retok (lexeme-token (token-punctuator "#"))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((= char (char-code #\&)) ; &
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; & EOF
          (retok (lexeme-token (token-punctuator "&"))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\&)) ; & &
          (retok (lexeme-token (token-punctuator "&&"))
                 (make-span :start first-pos :end pos2)
                 parstate))
         ((= char2 (char-code #\=)) ; & =
          (retok (lexeme-token (token-punctuator "&="))
                 (make-span :start first-pos :end pos2)
                 parstate))
         (t ; & other
          (b* ((parstate (unread-char parstate)))
            (retok (lexeme-token (token-punctuator "&"))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((= char (char-code #\|)) ; |
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; | EOF
          (retok (lexeme-token (token-punctuator "|"))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\|)) ; | |
          (retok (lexeme-token (token-punctuator "||"))
                 (make-span :start first-pos :end pos2)
                 parstate))
         ((= char2 (char-code #\=)) ; | =
          (retok (lexeme-token (token-punctuator "|="))
                 (make-span :start first-pos :end pos2)
                 parstate))
         (t ; | other
          (b* ((parstate (unread-char parstate)))
            (retok (lexeme-token (token-punctuator "|"))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((= char (char-code #\+)) ; +
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; + EOF
          (retok (lexeme-token (token-punctuator "+"))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\+)) ; + +
          (retok (lexeme-token (token-punctuator "++"))
                 (make-span :start first-pos :end pos2)
                 parstate))
         ((= char2 (char-code #\=)) ; + =
          (retok (lexeme-token (token-punctuator "+="))
                 (make-span :start first-pos :end pos2)
                 parstate))
         (t ; + other
          (b* ((parstate (unread-char parstate)))
            (retok (lexeme-token (token-punctuator "+"))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((= char (char-code #\-)) ; -
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; - EOF
          (retok (lexeme-token (token-punctuator "-"))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\>)) ; - >
          (retok (lexeme-token (token-punctuator "->"))
                 (make-span :start first-pos :end pos2)
                 parstate))
         ((= char2 (char-code #\-)) ; - -
          (retok (lexeme-token (token-punctuator "--"))
                 (make-span :start first-pos :end pos2)
                 parstate))
         ((= char2 (char-code #\=)) ; - =
          (retok (lexeme-token (token-punctuator "-="))
                 (make-span :start first-pos :end pos2)
                 parstate))
         (t ; - other
          (b* ((parstate (unread-char parstate)))
            (retok (lexeme-token (token-punctuator "-"))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((= char (char-code #\>)) ; >
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; > EOF
          (retok (lexeme-token (token-punctuator ">"))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\>)) ; > >
          (b* (((erp char3 pos3 parstate) (read-char parstate)))
            (cond
             ((not char3) ; > > EOF
              (retok (lexeme-token (token-punctuator ">>"))
                     (make-span :start first-pos :end pos2)
                     parstate))
             ((= char3 (char-code #\=))
              (retok (lexeme-token (token-punctuator ">>="))
                     (make-span :start first-pos :end pos3)
                     parstate))
             (t ; > > other
              (b* ((parstate (unread-char parstate))) ; > >
                (retok (lexeme-token (token-punctuator ">>"))
                       (make-span :start first-pos :end pos2)
                       parstate))))))
         ((= char2 (char-code #\=)) ; > =
          (retok (lexeme-token (token-punctuator ">="))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         (t ; > other
          (b* ((parstate (unread-char parstate))) ; >
            (retok (lexeme-token (token-punctuator ">"))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((= char (char-code #\%)) ; %
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; % EOF
          (retok (lexeme-token (token-punctuator "%"))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\=)) ; % =
          (retok (lexeme-token (token-punctuator "%="))
                 (make-span :start first-pos :end pos2)
                 parstate))
         ((= char2 (char-code #\:)) ; % :
          (b* (((erp char3 & parstate) (read-char parstate)))
            (cond
             ((not char3) ; % : EOF
              (retok (lexeme-token (token-punctuator "%:"))
                     (make-span :start first-pos :end pos2)
                     parstate))
             ((= char3 (char-code #\%)) ; % : %
              (b* (((erp char4 pos4 parstate) (read-char parstate)))
                (cond
                 ((not char4) ; % : % EOF
                  (b* ((parstate (unread-char parstate))) ; % :
                    (retok (lexeme-token (token-punctuator "%:"))
                           (make-span :start first-pos :end pos2)
                           parstate)))
                 ((= char4 (char-code #\:)) ; % : % :
                  (retok (lexeme-token (token-punctuator "%:%:"))
                         (make-span :start first-pos :end pos4)
                         parstate))
                 (t ; % : % other
                  (b* ((parstate (unread-char parstate)) ; % : %
                       (parstate (unread-char parstate))) ; % :
                    (retok (lexeme-token (token-punctuator "%:"))
                           (make-span :start first-pos :end pos2)
                           parstate))))))
             (t ; % : other
              (b* ((parstate (unread-char parstate))) ; % :
                (retok (lexeme-token (token-punctuator "%:"))
                       (make-span :start first-pos :end pos2)
                       parstate))))))
         (t ; % other
          (b* ((parstate (unread-char parstate))) ; %
            (retok (lexeme-token (token-punctuator "%"))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     ((= char (char-code #\<)) ; <
      (b* (((erp char2 pos2 parstate) (read-char parstate)))
        (cond
         ((not char2) ; < EOF
          (retok (lexeme-token (token-punctuator "<"))
                 (make-span :start first-pos :end first-pos)
                 parstate))
         ((= char2 (char-code #\<)) ; < <
          (b* (((erp char3 pos3 parstate) (read-char parstate)))
            (cond
             ((not char3) ; < < EOF
              (retok (lexeme-token (token-punctuator "<<"))
                     (make-span :start first-pos :end pos2)
                     parstate))
             ((= char3 (char-code #\=)) ; < < =
              (retok (lexeme-token (token-punctuator "<<="))
                     (make-span :start first-pos :end pos3)
                     parstate))
             (t ; < < other
              (b* ((parstate (unread-char parstate))) ; < <
                (retok (lexeme-token (token-punctuator "<<"))
                       (make-span :start first-pos :end pos2)
                       parstate))))))
         ((= char2 (char-code #\=)) ; < =
          (retok (lexeme-token (token-punctuator "<="))
                 (make-span :start first-pos :end pos2)
                 parstate))
         ((= char2 (char-code #\:)) ; < :
          (retok (lexeme-token (token-punctuator "<:"))
                 (make-span :start first-pos :end pos2)
                 parstate))
         ((= char2 (char-code #\%)) ; < %
          (retok (lexeme-token (token-punctuator "<%"))
                 (make-span :start first-pos :end pos2)
                 parstate))
         (t ; < other
          (b* ((parstate (unread-char parstate))) ; <
            (retok (lexeme-token (token-punctuator "<"))
                   (make-span :start first-pos :end first-pos)
                   parstate))))))

     (t (reterr-msg :where (position-to-msg first-pos)
                    :expected "a white-space character ~
                               (space, ~
                               new-line, ~
                               horizontal tab, ~
                               vertical tab, ~
                               form feed) ~
                               or a letter ~
                               or a digit ~
                               or an underscore ~
                               or a round parenthesis ~
                               or a square bracket ~
                               or a curly brace ~
                               or an angle bracket ~
                               or a dot ~
                               or a comma ~
                               or a colon ~
                               or a semicolon ~
                               or a plus ~
                               or a minus ~
                               or a star ~
                               or a slash ~
                               or a percent ~
                               or a tilde ~
                               or an equal sign ~
                               or an exclamation mark ~
                               or a question mark ~
                               or a vertical bar ~
                               or a caret ~
                               or hash"
                    :found (char-to-msg char)))))

  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp
                                           rationalp-when-natp
                                           integerp-when-natp
                                           unsigned-byte-p
                                           integer-range-p
                                           dec-digit-char-p)))

  ///

  (defret parsize-of-lex-lexeme-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-lexeme-cond
    (implies (and (not erp)
                  lexeme?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-token ((parstate parstatep))
  :returns (mv erp
               (token? token-optionp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Read a token."
  :long
  (xdoc::topstring
   (xdoc::p
    "If we find a token, we return it, along with its span.
     If we reach the end of file, we return @('nil') for no token,
     along with a span that covers
     just the position just past the end of file,
     although this span is not that relevant
     (this span comes from @(tsee lex-lexeme)).")
   (xdoc::p
    "First we check whether some token was unread,
     in which case we pop the stack of unread tokens.
     See the discussion in @(tsee parstate).")
   (xdoc::p
    "The token read is pushed onto the @('tokens-read') stack.
     The @('chars-read') stack is cleared.
     See @(tsee parstate).")
   (xdoc::p
    "We call the lexer to get the next lexeme,
     until we find a token lexeme or the end of file.
     That is, we discard white space and comments.
     (Future extensions of this parser may instead
     return certain white space and comments under some conditions.)"))
  (b* (((reterr) nil (irr-span) parstate)
       (parstate.tokens-read (parstate->tokens-read parstate))
       (parstate.tokens-read-len (parstate->tokens-read-len parstate))
       (parstate.tokens-unread (parstate->tokens-unread parstate))
       (parstate.size (parstate->size parstate))
       ((when (and (consp parstate.tokens-unread)
                   (> parstate.size 0)))
        (b* ((token+span (car parstate.tokens-unread))
             (parstate (update-parstate->tokens-unread
                        (cdr parstate.tokens-unread) parstate))
             (parstate (update-parstate->tokens-read
                        (cons token+span parstate.tokens-read) parstate))
             (parstate (update-parstate->tokens-read-len
                        (1+ parstate.tokens-read-len) parstate))
             (parstate (update-parstate->chars-read nil parstate))
             (parstate (update-parstate->size (1- parstate.size) parstate)))
          (retok (token+span->token token+span)
                 (token+span->span token+span)
                 parstate))))
    (read-token-loop parstate))
  :guard-hints (("Goal" :in-theory (enable natp fix len)))

  :prepwork

  ((define read-token-loop ((parstate parstatep))
     :returns (mv erp
                  (token? token-optionp)
                  (span spanp)
                  (new-parstate parstatep :hyp (parstatep parstate)))
     :parents nil
     (b* (((reterr) nil (irr-span) parstate)
          ((erp lexeme? span parstate) (lex-lexeme parstate))
          ((when (not lexeme?))
           (retok nil span parstate))
          ((when (lexeme-case lexeme? :token))
           (b* ((token (lexeme-token->unwrap lexeme?))
                (parstate (update-parstate->tokens-read
                           (cons (make-token+span
                                  :token token
                                  :span span)
                                 (parstate->tokens-read parstate))
                           parstate))
                (parstate (update-parstate->tokens-read-len
                           (1+ (parstate->tokens-read-len parstate))
                           parstate)))
             (retok token span parstate))))
       (read-token-loop parstate))
     :measure (parsize parstate)
     :hints (("Goal" :in-theory (enable o< o-finp)))

     ///

     (defret parsize-of-read-token-loop-uncond
       (<= (parsize new-parstate)
           (parsize parstate))
       :rule-classes :linear
       :hints (("Goal"
                :induct t
                :in-theory (enable parsize))
               '(:use parsize-of-lex-lexeme-uncond)))

     (defret parsize-of-read-token-loop-cond
       (implies (and (not erp)
                     token?)
                (<= (parsize new-parstate)
                    (1- (parsize parstate))))
       :rule-classes :linear
       :hints (("Goal"
                :induct t
                :in-theory (enable parsize))
               '(:use parsize-of-lex-lexeme-cond)))))

  ///

  (defret parsize-of-read-token-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (parsize len fix nfix)
                             (parsize-of-read-token-loop-uncond))
             :use parsize-of-read-token-loop-uncond)))

  (defret parsize-of-read-token-cond
    (implies (and (not erp)
                  token?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (parsize len fix nfix)
                             (parsize-of-read-token-loop-cond))
             :use parsize-of-read-token-loop-cond))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-token ((parstate parstatep))
  :returns (new-parstate parstatep :hyp (parstatep parstate))
  :short "Unread a token."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pop the token from the @('tokens-read') stack
     and we push it onto the @('tokens-unread') stack.")
   (xdoc::p
    "It is an internal error if the @('tokens-read') stack is empty.
     It means that the calling code is wrong.
     In this case, after raising the hard error,
     logically we return a parser state
     where we push an irrelevant character and position,
     so that the theorem about @(tsee parsize) holds unconditionally."))
  (b* ((parstate.tokens-read (parstate->tokens-read parstate))
       (parstate.tokens-read-len (parstate->tokens-read-len parstate))
       (parstate.tokens-unread (parstate->tokens-unread parstate))
       (parstate.size (parstate->size parstate))
       ((unless (and (consp parstate.tokens-read)
                     (> parstate.tokens-read-len 0)))
        (raise "Internal error: no token to unread.")
        (b* ((parstate (update-parstate->tokens-unread
                        (cons (make-token+span
                               :token (irr-token)
                               :span (irr-span))
                              parstate.tokens-unread)
                        parstate))
             (parstate (update-parstate->size (1+ parstate.size) parstate)))
          parstate))
       (token+span (car parstate.tokens-read))
       (parstate (update-parstate->tokens-unread
                  (cons token+span parstate.tokens-unread) parstate))
       (parstate (update-parstate->tokens-read
                  (cdr parstate.tokens-read) parstate))
       (parstate (update-parstate->tokens-read-len
                  (1- parstate.tokens-read-len) parstate))
       (parstate (update-parstate->size (1+ parstate.size) parstate)))
    parstate)
  :guard-hints (("Goal" :in-theory (enable natp len fix)))

  ///

  (defret parsize-of-unread-token
    (equal (parsize new-parstate)
           (1+ (parsize parstate)))
    :hints (("Goal" :in-theory (enable parsize len nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-tokens ((n natp) (parstate parstatep))
  :returns (new-parstate parstatep :hyp (parstatep parstate))
  :short "Unread a specified number of tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "This repeatedly calls @(tsee unread-token)
     to unread zero or more tokens.
     The number of tokens is specified by @('n').
     This number may be 0."))
  (b* (((when (zp n)) (parstate-fix parstate))
       (parstate (unread-token parstate)))
    (unread-tokens (1- n) parstate))

  ///

  (defret parsize-of-unread-tokens
    (equal (parsize new-parstate)
           (+ (parsize parstate) (nfix n)))
    :hints (("Goal"
             :induct t
             :in-theory (enable nfix fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-punctuator ((punct stringp) (parstate parstatep))
  :returns (mv erp
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Read a specific punctuator token."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a specific punctuator.
     We pass the string for the punctuator,
     and we read the next token,
     ensuring it exists and it is that punctuator."))
  (b* (((reterr) (irr-span) parstate)
       ((erp token span parstate) (read-token parstate))
       ((unless (token-punctuatorp token punct)) ; implies non-nil
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected (msg "the punctuator ~x0" punct)
                    :found (token-to-msg token))))
    (retok span parstate))

  ///

  (defret parsize-of-read-punctuator-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-read-punctuator-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-keyword ((keywd stringp) (parstate parstatep))
  :returns (mv erp
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Read a specific keyword token."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a specific keyword.
     We pass the string for the keyword,
     and we read the next token,
     ensuring it exists and it is that keyword."))
  (b* (((reterr) (irr-span) parstate)
       ((erp token span parstate) (read-token parstate))
       ((unless (token-keywordp token keywd)) ; implies non-nil
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected (msg "the keyword \"~s0\"" keywd)
                    :found (token-to-msg token))))
    (retok span parstate))

  ///

  (defret parsize-of-read-keyword-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-read-keyword-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-stringlit ((parstate parstatep))
  :returns (mv erp
               (stringlit stringlitp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Read a string literal token."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a string literal token.
     We read the next token, ensuring it exists and is a string literal.
     We return the string literal if successful."))
  (b* (((reterr) (irr-stringlit) (irr-span) parstate)
       ((erp token span parstate) (read-token parstate))
       ((unless (and token
                     (token-case token :string)))
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a string literal"
                    :found (token-to-msg token)))
       (stringlit (token-string->unwrap token)))
    (retok stringlit span parstate))

  ///

  (defret parsize-of-read-stringlit-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-read-stringlit-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-identifier ((parstate parstatep))
  :returns (mv erp
               (ident identp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Read an identifier token."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect an identifier token.
     We read the next token, ensuring it exists and is an identifier.
     We return the identifier if successful."))
  (b* (((reterr) (irr-ident) (irr-span) parstate)
       ((erp token span parstate) (read-token parstate))
       ((unless (and token
                     (token-case token :ident)))
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier"
                    :found (token-to-msg token)))
       (ident (token-ident->unwrap token)))
    (retok ident span parstate))

  ///

  (defret parsize-of-read-ident-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-read-ident-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define record-checkpoint ((parstate parstatep))
  :returns (new-parstate parstatep :hyp (parstatep parstate))
  :short "Record a checkpoint for possible backtracking."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee parstate),
     we add (by @(tsee cons)ing) to the list of checkpoints
     the current length of the list of tokens read so far."))
  (b* ((tokens-read-len (parstate->tokens-read-len parstate))
       (checkpoints (parstate->checkpoints parstate))
       (new-checkpoints (cons tokens-read-len checkpoints))
       (parstate (update-parstate->checkpoints new-checkpoints parstate)))
    parstate)

  ///

  (defret parsize-of-record-checkpoint
    (equal (parsize new-parstate)
           (parsize parstate))
    :rule-classes (:rewrite :linear)
    :hints (("Goal" :in-theory (enable parsize)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define clear-checkpoint ((parstate parstatep))
  :returns (new-parstate parstatep :hyp (parstatep parstate))
  :short "Clear the latest checkpoint."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when the parser resolves that
     there is no longer a need to backtrack
     to the latest checkpoint.
     This simply removes the latest checkpoint.")
   (xdoc::p
    "It is an internal error if this is called
     when the list of checkpoints is empty.
     If this happens, there is a bug in the parser."))
  (b* ((checkpoints (parstate->checkpoints parstate))
       ((unless (consp checkpoints))
        (raise "Internal error: no checkpoint to clear.")
        (parstate-fix parstate))
       (new-checkpoints (cdr checkpoints))
       (parstate (update-parstate->checkpoints new-checkpoints parstate)))
    parstate)

  ///

  (defret parsize-of-clear-checkpoint
    (equal (parsize new-parstate)
           (parsize parstate))
    :rule-classes (:rewrite :linear)
    :hints (("Goal" :in-theory (enable parsize)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define backtrack-checkpoint ((parstate parstatep))
  :returns (new-parstate parstatep :hyp (parstatep parstate))
  :short "Backtrack to the latest checkpoint."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when the parser needs to backtrack.
     We calculate the number of tokens to unread and we unread them.
     We also remove the checkpoint from the list of checkpoints,
     since it no longer serves a purpose (we have backtracked to it).")
   (xdoc::p
    "It is an internal error if this is called
     when the list of checkpoints is empty.
     If this happens, there is a bug in the parser."))
  (b* ((checkpoints (parstate->checkpoints parstate))
       ((unless (consp checkpoints))
        (raise "Internal error: no checkpoints to backtrack.")
        (parstate-fix parstate))
       (checkpoint (car checkpoints))
       (new-chechpoints (cdr checkpoints))
       (number-tokens-read (parstate->tokens-read-len parstate))
       (number-tokens-to-unread (- number-tokens-read checkpoint))
       ((unless (> number-tokens-to-unread 0))
        (raise "Internal error: ~
                the checkpoint ~x0 is not less than ~
                the number ~x1 of tokens read so far."
               checkpoint
               number-tokens-read)
        (parstate-fix parstate))
       (parstate (unread-tokens number-tokens-to-unread parstate))
       (parstate (update-parstate->checkpoints new-chechpoints parstate)))
    parstate)
  :prepwork
  ((defrulel verify-guards-lemma
     (implies (and (natp x)
                   (natp y)
                   (< 0 (+ x (- y))))
              (natp (+ x (- y))))
     :enable natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-assignment-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is an assignment operator."
  (or (token-punctuatorp token? "=")
      (token-punctuatorp token? "*=")
      (token-punctuatorp token? "/=")
      (token-punctuatorp token? "%=")
      (token-punctuatorp token? "+=")
      (token-punctuatorp token? "-=")
      (token-punctuatorp token? "<<=")
      (token-punctuatorp token? ">>=")
      (token-punctuatorp token? "&=")
      (token-punctuatorp token? "^=")
      (token-punctuatorp token? "|="))
  ///

  (defrule non-nil-when-token-assignment-operator-p
    (implies (token-assignment-operator-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-assignment-operator ((token tokenp))
  :guard (token-assignment-operator-p token)
  :returns (op binopp)
  :short "Map a token that is an assignment operator
          to the corresponding assignment operator."
  (cond ((token-punctuatorp token "=") (binop-asg))
        ((token-punctuatorp token "*=") (binop-asg-mul))
        ((token-punctuatorp token "/=") (binop-asg-div))
        ((token-punctuatorp token "%=") (binop-asg-rem))
        ((token-punctuatorp token "+=") (binop-asg-add))
        ((token-punctuatorp token "-=") (binop-asg-sub))
        ((token-punctuatorp token "<<=") (binop-asg-shl))
        ((token-punctuatorp token ">>=") (binop-asg-shr))
        ((token-punctuatorp token "&=") (binop-asg-and))
        ((token-punctuatorp token "^=") (binop-asg-xor))
        ((token-punctuatorp token "|=") (binop-asg-ior))
        (t (prog2$ (impossible) (irr-binop))))
  :guard-hints (("Goal" :in-theory (enable token-assignment-operator-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-equality-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is an equality operator."
  (or (token-punctuatorp token? "==")
      (token-punctuatorp token? "!="))
  ///

  (defrule non-nil-when-token-equality-operator-p
    (implies (token-equality-operator-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-equality-operator ((token tokenp))
  :guard (token-equality-operator-p token)
  :returns (op binopp)
  :short "Map a token that is an equality operator
          to the corresponding equality operator."
  (cond ((token-punctuatorp token "==") (binop-eq))
        ((token-punctuatorp token "!=") (binop-ne))
        (t (prog2$ (impossible) (irr-binop))))
  :prepwork ((local (in-theory (enable token-equality-operator-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-relational-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is a relational operator."
  (or (token-punctuatorp token? "<")
      (token-punctuatorp token? ">")
      (token-punctuatorp token? "<=")
      (token-punctuatorp token? ">="))
  ///

  (defrule non-nil-when-token-relational-operator-p
    (implies (token-relational-operator-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-relational-operator ((token tokenp))
  :guard (token-relational-operator-p token)
  :returns (op binopp)
  :short "Map a token that is a relational operator
          to the corresponding relational operator."
  (cond ((token-punctuatorp token "<") (binop-lt))
        ((token-punctuatorp token ">") (binop-gt))
        ((token-punctuatorp token "<=") (binop-le))
        ((token-punctuatorp token ">=") (binop-ge))
        (t (prog2$ (impossible) (irr-binop))))
  :prepwork ((local (in-theory (enable token-relational-operator-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-shift-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is a shift operator."
  (or (token-punctuatorp token? "<<")
      (token-punctuatorp token? ">>"))
  ///

  (defrule non-nil-when-token-shift-operator-p
    (implies (token-shift-operator-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-shift-operator ((token tokenp))
  :guard (token-shift-operator-p token)
  :returns (op binopp)
  :short "Map a token that is a shift operator
          to the corresponding shift operator."
  (cond ((token-punctuatorp token "<<") (binop-shl))
        ((token-punctuatorp token ">>") (binop-shr))
        (t (prog2$ (impossible) (irr-binop))))
  :prepwork ((local (in-theory (enable token-shift-operator-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-additive-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is an additive operator."
  (or (token-punctuatorp token? "+")
      (token-punctuatorp token? "-"))
  ///

  (defrule non-nil-when-token-additive-operator-p
    (implies (token-additive-operator-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-additive-operator ((token tokenp))
  :guard (token-additive-operator-p token)
  :returns (op binopp)
  :short "Map a token that is an additive operator
          to the corresponding additive operator."
  (cond ((token-punctuatorp token "+") (binop-add))
        ((token-punctuatorp token "-") (binop-sub))
        (t (prog2$ (impossible) (irr-binop))))
  :prepwork ((local (in-theory (enable token-additive-operator-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-expr-cast/add-or-cast/sub-ambig ((plus/minus tokenp)
                                              (expr/tyname amb-expr/tyname-p)
                                              (incdec inc/dec-op-listp)
                                              (expr exprp))
  :guard (token-additive-operator-p plus/minus)
  :returns (new-expr exprp)
  :short "Create an ambiguous cast expression based on
          a token that is an additive operator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is introduced just to avoid case splits in
     the large clique of mutually recursive parsing functions defined below.
     At some point in those functions, based on a parsed additive operator,
     we need to construct two different kinds of
     syntactically ambiguous cast expressions in our abstract syntax."))
  (cond ((token-punctuatorp plus/minus "+")
         (make-expr-cast/add-ambig
          :type/arg1 expr/tyname
          :inc/dec incdec
          :arg/arg2 expr))
        ((token-punctuatorp plus/minus "-")
         (make-expr-cast/sub-ambig
          :type/arg1 expr/tyname
          :inc/dec incdec
          :arg/arg2 expr))
        (t (prog2$ (impossible) (irr-expr))))
  :guard-hints (("Goal" :in-theory (enable token-additive-operator-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-multiplicative-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is a multiplicative operator."
  (or (token-punctuatorp token? "*")
      (token-punctuatorp token? "/")
      (token-punctuatorp token? "%"))
  ///

  (defrule non-nil-when-token-multiplicative-operator-p
    (implies (token-multiplicative-operator-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-multiplicative-operator ((token tokenp))
  :guard (token-multiplicative-operator-p token)
  :returns (op binopp)
  :short "Map a token that is a multiplicative operator
          to the corresponding additive operator."
  (cond ((token-punctuatorp token "*") (binop-mul))
        ((token-punctuatorp token "/") (binop-div))
        ((token-punctuatorp token "%") (binop-rem))
        (t (prog2$ (impossible) (irr-binop))))
  :prepwork ((local (in-theory (enable token-multiplicative-operator-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-preinc/predec-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is
          a preincrement or predecrement operator."
  (or (token-punctuatorp token? "++")
      (token-punctuatorp token? "--"))
  ///

  (defrule non-nil-when-token-preinc/predec-operator-p
    (implies (token-preinc/predec-operator-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-preinc/predec-operator ((token tokenp))
  :guard (token-preinc/predec-operator-p token)
  :returns (op unopp)
  :short "Map a token that is a preincrement or predecrement operator
          to the corresponding preincrement or predecrement operator."
  (cond ((token-punctuatorp token "++") (unop-preinc))
        ((token-punctuatorp token "--") (unop-predec))
        (t (prog2$ (impossible) (irr-unop))))
  :prepwork ((local (in-theory (enable token-preinc/predec-operator-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-unary-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is a unary operator."
  :long
  (xdoc::topstring
   (xdoc::p
    "By this we mean a unary operator according to the grammar,
     not our abstract syntax, which has a broader notion of unary operator."))
  (or (token-punctuatorp token? "&")
      (token-punctuatorp token? "*")
      (token-punctuatorp token? "+")
      (token-punctuatorp token? "-")
      (token-punctuatorp token? "~")
      (token-punctuatorp token? "!"))
  ///

  (defrule non-nil-when-token-unary-operator-p
    (implies (token-unary-operator-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-unary-operator ((token tokenp))
  :guard (token-unary-operator-p token)
  :returns (op unopp)
  :short "Map a token that is a unary operator
          to the corresponding unary operator."
  :long
  (xdoc::topstring
   (xdoc::p
    "By this we mean a unary operator according to the grammar,
     not our abstract syntax, which has a broader notion of unary operator."))
  (cond ((token-punctuatorp token "&") (unop-address))
        ((token-punctuatorp token "*") (unop-indir))
        ((token-punctuatorp token "+") (unop-plus))
        ((token-punctuatorp token "-") (unop-minus))
        ((token-punctuatorp token "~") (unop-bitnot))
        ((token-punctuatorp token "!") (unop-lognot))
        (t (prog2$ (impossible) (irr-unop))))
  :prepwork ((local (in-theory (enable token-unary-operator-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-primary-expression-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a primary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "A primary expression is
     an identifier (which is a token),
     or a constant (which is a token),
     or a string literal (which is a token),
     or a parenthesizes expression (which starts with a certain punctuator),
     or a generic selection (which starts a certain keyword)."))
  (and token?
       (or (token-case token? :ident)
           (token-case token? :const)
           (token-case token? :string)
           (token-punctuatorp token? "(")
           (token-keywordp token? "_Generic")))
  ///

  (defrule non-nil-when-token-primary-expression-start-p
    (implies (token-primary-expression-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-unary-expression-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a unary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "Looking at the grammar,
     a unary expression may be a postfix expression,
     which always starts with (or is) a primary expression,
     or it is a compound literal,
     which starts with an open parenthesis,
     which is already covered by the possible starts of a primary expression.
     In addition, a unary expression may start with
     a preincrement or predecrement operator,
     or a unary operator as defined in the grammar,
     or a @('sizeof') keyword,
     or an @('_Alignof') keyword.")
   (xdoc::p
    "We also compare the token against
     the GCC extension variants
     @('__alignof') and @('__alignof__') of @('_Alignof').
     Note that this variant is a keywords only if GCC extensions are supported:
     @(tsee lex-identifier/keyword) checks the GCC flag of the parser state.
     So the comparison here with that variant keyword
     will always fail if GCC extensions are not supported,
     because in that case both @('__alignof__')
     would be an identifier token, not a keyword token."))
  (or (token-primary-expression-start-p token?)
      (token-punctuatorp token? "++")
      (token-punctuatorp token? "--")
      (token-punctuatorp token? "&")
      (token-punctuatorp token? "*")
      (token-punctuatorp token? "+")
      (token-punctuatorp token? "-")
      (token-punctuatorp token? "~")
      (token-punctuatorp token? "!")
      (token-keywordp token? "sizeof")
      (token-keywordp token? "_Alignof")
      (token-keywordp token? "__alignof")
      (token-keywordp token? "__alignof__"))
  ///

  (defrule non-nil-when-token-unary-expression-start-p
    (implies (token-unary-expression-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-expression-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "Looking at the grammar,
     an expression always starts with (or is)
     a cast expression,
     which is either a unary expression
     or a cast expression proper.
     The latter starts with an open parenthesis,
     but that is already covered by
     the possible starts of primary expressions.")
   (xdoc::p
    "So we just define this as
     a synonym of @(tsee token-unary-expression-start-p),
     to make it clearer that we are talking about
     all expressions and not just unary expressions."))
  (token-unary-expression-start-p token?)
  ///

  (defrule non-nil-when-token-expression-start-p
    (implies (token-expression-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-postfix-expression-rest-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start
          the rest of a postfix expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "Looking at the grammar,
     a postfix expression may starts with (or is) a primary expression,
     followed by a sequence of constructs for
     array subscripting,
     function calls,
     member access (by value or pointer),
     and postincrement or postdecrement.
     The other kind of postfix expression is different:
     it consists of a parenthesized type name
     followed by an initializer list in curly braces.
     Here we are only concerned with the first kind of postfix expressions,
     the ones that start with a primary expression
     and continue with a sequence of the constructs listed above.
     This predicate recognizes the tokens that may start
     one of these constructs, after the primary expression."))
  (or (token-punctuatorp token? "[")
      (token-punctuatorp token? "(")
      (token-punctuatorp token? ".")
      (token-punctuatorp token? "->")
      (token-punctuatorp token? "++")
      (token-punctuatorp token? "--"))
  ///

  (defrule non-nil-when-token-postfix-expression-rest-start-p
    (implies (token-postfix-expression-rest-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-storage-class-specifier-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is a storage class specifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "All storage class specifiers consist of single keywords."))
  (or (token-keywordp token? "typedef")
      (token-keywordp token? "extern")
      (token-keywordp token? "static")
      (token-keywordp token? "_Thread_local")
      (token-keywordp token? "auto")
      (token-keywordp token? "register"))
  ///

  (defrule non-nil-when-token-storage-class-specifier-p
    (implies (token-storage-class-specifier-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-storage-class-specifier ((token tokenp))
  :guard (token-storage-class-specifier-p token)
  :returns (stor-spec stor-specp)
  :short "Map a token that is a storage class specifier
          to the correspoding storage class specifier."
  (cond ((token-keywordp token "typedef") (stor-spec-typedef))
        ((token-keywordp token "extern") (stor-spec-extern))
        ((token-keywordp token "static") (stor-spec-static))
        ((token-keywordp token "_Thread_local") (stor-spec-threadloc))
        ((token-keywordp token "auto") (stor-spec-auto))
        ((token-keywordp token "register") (stor-spec-register))
        (t (prog2$ (impossible) (irr-stor-spec))))
  :prepwork ((local (in-theory (enable token-storage-class-specifier-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-type-specifier-keyword-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is a type specifier
          that consists of a single keyword."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are a number of type specifiers that consist of single keywords.")
   (xdoc::p
    "We also compare the token against the GCC variants
     @('__signed') and @('__signed__') of @('signed').
     Note that these variants are keywords only if GCC extensions are supported:
     @(tsee lex-identifier/keyword) checks the GCC flag of the parser state.
     So the comparison here with those variant keywords
     will always fail if GCC extensions are not supported,
     because in that case both @('__signed') and @('__signed__')
     would be identifier tokens, not keyword tokens.")
   (xdoc::p
    "We similarly include the GCC extension types
     @('__int128'), @('_Float128'), @('__builtin_va_list')."))
  (or (token-keywordp token? "void")
      (token-keywordp token? "char")
      (token-keywordp token? "short")
      (token-keywordp token? "int")
      (token-keywordp token? "long")
      (token-keywordp token? "float")
      (token-keywordp token? "double")
      (token-keywordp token? "signed")
      (token-keywordp token? "__signed")
      (token-keywordp token? "__signed__")
      (token-keywordp token? "unsigned")
      (token-keywordp token? "_Bool")
      (token-keywordp token? "_Complex")
      (token-keywordp token? "__int128")
      (token-keywordp token? "_Float128")
      (token-keywordp token? "__builtin_va_list"))
  ///

  (defrule non-nil-when-token-type-specifier-keyword-p
    (implies (token-type-specifier-keyword-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-type-specifier-keyword ((token tokenp))
  :guard (token-type-specifier-keyword-p token)
  :returns (tyspec type-specp)
  :short "Map a token that is a type specifier consisting of a single keyword
          to the corresponding type specifier."
  (cond ((token-keywordp token "void") (type-spec-void))
        ((token-keywordp token "char") (type-spec-char))
        ((token-keywordp token "short") (type-spec-short))
        ((token-keywordp token "int") (type-spec-int))
        ((token-keywordp token "long") (type-spec-long))
        ((token-keywordp token "float") (type-spec-float))
        ((token-keywordp token "double") (type-spec-double))
        ((token-keywordp token "signed")
         (type-spec-signed (keyword-uscores-none)))
        ((token-keywordp token "__signed")
         (type-spec-signed (keyword-uscores-start)))
        ((token-keywordp token "__signed__")
         (type-spec-signed (keyword-uscores-both)))
        ((token-keywordp token "unsigned") (type-spec-unsigned))
        ((token-keywordp token "_Bool") (type-spec-bool))
        ((token-keywordp token "_Complex") (type-spec-complex))
        ((token-keywordp token "__int128") (type-spec-int128))
        ((token-keywordp token "_Float128") (type-spec-float128))
        ((token-keywordp token "__builtin_va_list") (type-spec-builtin-va-list))
        (t (prog2$ (impossible) (irr-type-spec))))
  :prepwork ((local (in-theory (enable token-type-specifier-keyword-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-type-specifier-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a type specifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "Looking at the grammar,
     a type specifier may start with certain keywords,
     or it could be an identifier."))
  (or (token-type-specifier-keyword-p token?)
      (token-keywordp token? "_Atomic")
      (token-keywordp token? "struct")
      (token-keywordp token? "union")
      (token-keywordp token? "enum")
      (token-keywordp token? "typeof")
      (token-keywordp token? "__typeof")
      (token-keywordp token? "__typeof__")
      (and token? (token-case token? :ident)))
  ///

  (defrule non-nil-when-token-type-specifier-start-p
    (implies (token-type-specifier-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-type-qualifier-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is a type qualifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "All type qualifiers consist of single keywords.")
   (xdoc::p
    "We also compare the token against the GCC variants
     @('__restrict') and @('__restrict__') of @('restrict').
     Note that these variants are keywords only if GCC extensions are supported:
     @(tsee lex-identifier/keyword) checks the GCC flag of the parser state.
     So the comparison here with those variant keywords
     will always fail if GCC extensions are not supported,
     because in that case both @('__restrict') and @('__restrict__')
     would be identifier tokens, not keyword tokens."))
  (or (token-keywordp token? "const")
      (token-keywordp token? "restrict")
      (token-keywordp token? "__restrict")
      (token-keywordp token? "__restrict__")
      (token-keywordp token? "volatile")
      (token-keywordp token? "_Atomic"))
  ///

  (defrule non-nil-when-token-type-qualifier-p
    (implies (token-type-qualifier-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-type-qualifier ((token tokenp))
  :guard (token-type-qualifier-p token)
  :returns (tyqual type-qualp)
  :short "Map a token that is a type qualifier
          to the correspoding type qualifier."
  (cond ((token-keywordp token "const") (type-qual-const))
        ((token-keywordp token "restrict")
         (type-qual-restrict (keyword-uscores-none)))
        ((token-keywordp token "__restrict")
         (type-qual-restrict (keyword-uscores-start)))
        ((token-keywordp token "__restrict__")
         (type-qual-restrict (keyword-uscores-both)))
        ((token-keywordp token "volatile") (type-qual-volatile))
        ((token-keywordp token "_Atomic") (type-qual-atomic))
        (t (prog2$ (impossible) (irr-type-qual))))
  :prepwork ((local (in-theory (enable token-type-qualifier-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-specifier/qualifier-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a specifier or qualifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "We have predicates to recognize
     the starts of type specifiers and qualifiers;
     alignment specifiers always start with @('_Alignas').")
   (xdoc::p
    "There is an overlap between the starts of type specifiers and qualifiers,
     namely the @('_Atomic') keyword,
     but this does not matter as far as we are looking at
     the starts specifiers or qualifiers.")
   (xdoc::p
    "We also include @('__attribute__'), for attribute specifiers.
     This is a keyword only if GCC extensions are supported."))
  (or (token-type-specifier-start-p token?)
      (token-type-qualifier-p token?)
      (token-keywordp token? "_Alignas")
      (token-keywordp token? "__attribute__"))
  ///

  (defrule non-nil-when-token-specifier/qualifier-start-p
    (implies (token-specifier/qualifier-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-function-specifier-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is a function specifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "All function specifiers consist of single keywords.")
   (xdoc::p
    "We also compare the token against the GCC variants
     @('__inline') and @('__inline__') of @('inline').
     Note that these variants are keywords only if GCC extensions are supported:
     @(tsee lex-identifier/keyword) checks the GCC flag of the parser state.
     So the comparison here with those variant keywords
     will always fail if GCC extensions are not supported,
     because in that case both @('__inline') and @('__inline__')
     would be identifier tokens, not keyword tokens."))
  (or (token-keywordp token? "inline")
      (token-keywordp token? "__inline")
      (token-keywordp token? "__inline__")
      (token-keywordp token? "_Noreturn"))
  ///

  (defrule non-nil-when-token-function-specifier-p
    (implies (token-function-specifier-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-function-specifier ((token tokenp))
  :guard (token-function-specifier-p token)
  :returns (funspec fun-specp)
  :short "Map a token that is a function specifier
          to the corresponding function specifier."
  (cond ((token-keywordp token "inline")
         (fun-spec-inline (keyword-uscores-none)))
        ((token-keywordp token "__inline")
         (fun-spec-inline (keyword-uscores-start)))
        ((token-keywordp token "__inline__")
         (fun-spec-inline (keyword-uscores-both)))
        ((token-keywordp token "_Noreturn") (fun-spec-noreturn))
        (t (prog2$ (impossible) (irr-fun-spec))))
  :prepwork ((local (in-theory (enable token-function-specifier-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-declaration-specifier-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a declaration specifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put together the five cases that define declaration specifiers,
     plus a sixth case for GCC attribute specifiers.
     Recall that @('__attribute__') can be a keyword
     only if GCC extensions are supported."))
  (or (token-storage-class-specifier-p token?)
      (token-type-specifier-start-p token?)
      (token-type-qualifier-p token?)
      (token-function-specifier-p token?)
      (token-keywordp token? "_Alignas")
      (token-keywordp token? "__attribute__"))
  ///

  (defrule non-nil-when-token-declaration-specifier-start-p
    (implies (token-declaration-specifier-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-type-name-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "A type name always starts with
     a (non-empty) sequence of specifiers and qualifiers."))
  (token-specifier/qualifier-start-p token?)
  ///

  (defrule non-nil-when-token-type-name-start-p
    (implies (token-type-name-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-direct-abstract-declarator-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a direct abstract declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may start with an open parenthesis or an open square bracket."))
  (or (token-punctuatorp token? "(")
      (token-punctuatorp token? "["))
  ///

  (defrule non-nil-when-token-direct-abstract-declarator-start-p
    (implies (token-direct-abstract-declarator-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-abstract-declarator-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start an abstract declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "An abstract declarator may start with a pointer,
     which always starts with a star.
     An abstract declarator may also start with a direct abstract declarator."))
  (or (token-punctuatorp token? "*")
      (token-direct-abstract-declarator-start-p token?))
  ///

  (defrule non-nil-when-token-abstract-declarator-start-p
    (implies (token-abstract-declarator-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-direct-declarator-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a direct declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may start with an identifier or an open parenthesis."))
  (or (and token? (token-case token? :ident))
      (token-punctuatorp token? "("))
  ///

  (defrule non-nil-when-token-direct-declarator-start-p
    (implies (token-direct-declarator-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-declarator-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "A declarator may start with a pointer,
     which always starts with a star.
     A declarator may also start with a direct declarator."))
  (or (token-punctuatorp token? "*")
      (token-direct-declarator-start-p token?))
  ///

  (defrule non-nil-when-token-declarator-start-p
    (implies (token-declarator-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-struct-declarator-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a structure declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "A structure declarator may start with a declarator,
     or with a colon."))
  (or (token-declarator-start-p token?)
      (token-punctuatorp token? ":"))
  ///

  (defrule non-nil-when-token-strut-declarator-start-p
    (implies (token-struct-declarator-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-struct-declaration-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a structure declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "A structure declaration may start with a specifier or qualifier,
     or with the @('_Static_assert') keyword.
     If GCC extensions are supported,
     it may also start with the @('__extensions__') keyword;
     note that this is generated by the lexer
     only if GCC extensions are supported,
     so this predicate will fail
     if GCC extensions are not supported
     and the token is @('__extension__'),
     which must be an identifier if GCC extensions are not supported."))
  (or (token-specifier/qualifier-start-p token?)
      (token-keywordp token? "_Static_assert")
      (token-keywordp token? "__extension__"))
  ///

  (defrule non-nil-when-token-strut-declaration-start-p
    (implies (token-struct-declaration-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-designator-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a designator."
  :long
  (xdoc::topstring
   (xdoc::p
    "A designator starts with an open square bracket or a dot."))
  (or (token-punctuatorp token? "[")
      (token-punctuatorp token? "."))
  ///

  (defrule non-nil-when-token-designator-start-p
    (implies (token-designator-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-designation-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a designation."
  :long
  (xdoc::topstring
   (xdoc::p
    "A designation always starts with a designator."))
  (token-designator-start-p token?)
  ///

  (defrule non-nil-when-token-designation-start-p
    (implies (token-designation-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-initializer-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start an initializer."
  :long
  (xdoc::topstring
   (xdoc::p
    "An initializer is either an expression
     or something between curly braces."))
  (or (token-expression-start-p token?)
      (token-punctuatorp token? "{"))
  ///

  (defrule non-nil-when-token-initializer-start-p
    (implies (token-initializer-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-designation?-initializer-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start
          an initializer optionally preceded by a designation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the designation is optional,
     we put together the starts of initializers and designations."))
  (or (token-designation-start-p token?)
      (token-initializer-start-p token?))
  ///

  (defrule non-nil-when-token-designation?-initializer-start-p
    (implies (token-designation?-initializer-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-*-stringlit ((parstate parstatep))
  :returns (mv erp
               (strings stringlit-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a list of zero or more string literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, we parse a @('*stringlit'), in ABNF notation.")
   (xdoc::p
    "If there are no string literals, we return an irrelevant span.
     When combining the span of the first string literal (if present)
     with the span of the remaining zero or more string literals,
     we join spans only if the remaining ones are one or more;
     if there are zero, the span of the first string literal
     is also the span of the whole sequence."))
  (b* (((reterr) nil (irr-span) parstate)
       ((erp token span parstate) (read-token parstate))
       ((unless (and token (token-case token :string)))
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok nil (irr-span) parstate)))
       ;; stringlit
       (string (token-string->unwrap token))
       ((erp strings last-span parstate) (parse-*-stringlit parstate)))
    ;; stringlit stringlits
    (retok (cons string strings)
           (if strings (span-join span last-span) span)
           parstate))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-*-stringlit-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-type-qualifier-list ((parstate parstatep))
  :returns (mv erp
               (tyquals type-qual-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a list of one or more type qualifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "We parse the first one, which must exist.
     Then we check the next token to see if there is be another one,
     in which case we put it back and recursively parse a type qualifier list,
     otherwise we put back it back and return."))
  (b* (((reterr) nil (irr-span) parstate)
       ((erp token span parstate) (read-token parstate)))
    (cond
     ((token-type-qualifier-p token) ; tyqual
      (b* ((tyqual (token-to-type-qualifier token))
           ((erp token & parstate) (read-token parstate)))
        (cond
         ((token-type-qualifier-p token) ; tyqual tyqual
          (b* ((parstate (unread-token parstate)) ; tyqual
               ((erp tyquals last-span parstate) ; tyqual tyquals
                (parse-type-qualifier-list parstate)))
            (retok (cons tyqual tyquals)
                   (span-join span last-span)
                   parstate)))
         (t ; tyqual other
          (b* ((parstate (if token (unread-token parstate) parstate)))
            (retok (list tyqual) span parstate))))))
     (t ; other
      (reterr-msg :where (position-to-msg (span->start span))
                  :expected "a keyword in {~
                               const, ~
                               restrict, ~
                               volatile, ~
                               _Atomic~
                               }"
                  :found (token-to-msg token)))))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-type-qualifier-list-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-parse-type-qualifier-list-cond
    (implies (and (not erp)
                  token?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-pointer ((parstate parstatep))
  :returns (mv erp
               (tyqualss type-qual-list-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a pointer."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the grammar, a `pointer' is a sequence of one or more stars,
     each followed by zero or more type qualifiers.
     In our abstract syntax, we model this notion as
     a list of lists of type qualifiers,
     one inner list for each star (implicit in our abstract syntax),
     with the outer list corresponding to the sequence of stars.")
   (xdoc::p
    "We read a star, which must be present:
     this function is called when we expect a pointer.
     If the next token is a type qualifier,
     we put it back and read a list of one or more type qualifiers;
     then we check the next token if there is another star,
     in which case we recursively call this function.
     If instead the initial star is followed by another star,
     we also call this function recursively.
     We stop when there is not a star."))
  (b* (((reterr) nil (irr-span) parstate)
       ((erp span parstate) (read-punctuator "*" parstate)) ; *
       ((erp token & parstate) (read-token parstate)))
    (cond
     ((token-type-qualifier-p token) ; * tyqual
      (b* ((parstate (unread-token parstate)) ; *
           ((erp tyquals span2 parstate) ; * tyquals
            (parse-type-qualifier-list parstate))
           ((erp token & parstate) (read-token parstate)))
        (cond
         ((token-punctuatorp token "*") ; * tyquals *
          (b* ((parstate (unread-token parstate)) ; * tyquals
               ((erp tyqualss last-span parstate) ; * tyquals * tyquals ...
                (parse-pointer parstate)))
            (retok (cons tyquals tyqualss)
                   (span-join span last-span)
                   parstate)))
         (t ; * tyquals other
          (b* ((parstate
                (if token (unread-token parstate) parstate))) ; * tyquals
            (retok (list tyquals) (span-join span span2) parstate))))))
     ((token-punctuatorp token "*") ; * *
      (b* ((parstate (unread-token parstate)) ; *
           ((erp tyqualss last-span parstate) ; * * [tyquals] ...
            (parse-pointer parstate)))
        (retok (cons nil tyqualss) (span-join span last-span) parstate)))
     (t ; * other
      (b* ((parstate (if token (unread-token parstate) parstate)))
        (retok (list nil) span parstate)))))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-pointer-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-parse-pointer-cond
    (implies (and (not erp)
                  token?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-*-increment/decrement ((parstate parstatep))
  :returns (mv erp
               (ops inc/dec-op-listp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse zero or more increment and decrement operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to handle possibly ambiguous cast expressions.
     We never need the spans of these operators,
     so this function returns no span."))
  (b* (((reterr) nil parstate)
       ((erp token & parstate) (read-token parstate))
       ((when (token-punctuatorp token "++"))
        (b* (((erp ops parstate) (parse-*-increment/decrement parstate)))
          (retok (cons (inc/dec-op-inc) ops) parstate)))
       ((when (token-punctuatorp token "--"))
        (b* (((erp ops parstate) (parse-*-increment/decrement parstate)))
          (retok (cons (inc/dec-op-dec) ops) parstate)))
       (parstate (if token (unread-token parstate) parstate)))
    (retok nil parstate))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-*-increment/decrement
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-expr-unary-with-preinc/predec-ops ((ops inc/dec-op-listp)
                                                (expr exprp))
  :returns (new-expr exprp)
  :short "Apply to an expression
          all the pre-increment and pre-decrement operators in a list."
  :long
  (xdoc::topstring
   (xdoc::p
    "The operators are applied starting from the right,
     i.e. the last one in the list is applied first,
     then the second-to-last,
     and so on until the first (i.e. @(tsee car)).
     If the list is empty, the expression is unchanged."))
  (b* (((when (endp ops)) (expr-fix expr))
       (op (car ops))
       (preop (inc/dec-op-case op :inc (unop-preinc) :dec (unop-predec)))
       (expr1 (make-expr-unary-with-preinc/predec-ops (cdr ops) expr)))
    (make-expr-unary :op preop :arg expr1))
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines parse-exprs/decls
  :short "Parse expressions, declarations, and related entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "In accordance with the mutual recursion in the C grammar,
     and with the mutual recursion @(tsee exprs/decls) in our abstract syntax,
     the functions to parse expressions, declarations, and related entities
     are mutually recursive.")
   (xdoc::p
    "Some functions in this mutually recursive clique
     call other functions in the same clique on the same input,
     which therefore does not immediately decrease.
     Thus, we use a lexicographic measure consisting of
     the size of the parser state followed by
     a constant that ``orders'' the functions,
     based on how the parser makes progress
     by calling ``smaller'' functions even though the input stays the same.
     For example, @(tsee parse-expression)
     calls @(tsee parse-assignment-expression)
     on the same input;
     so we assign a smaller constant to the latter,
     so that it is considered ``smaller'' than the former.")
   (xdoc::p
    "The fact that each function in this clique reduces,
     or at least does not increase, the size of the input
     is proved after the functions are admitted in the ACL2 logic.
     But that fact is needed
     to prove the termination of some of these functions.
     For example, @(tsee parse-conditional-expression)
     calls @(tsee parse-expression),
     and then @(tsee parse-conditional-expression) again,
     under certain conditions.
     For termination, we need to show that the latter call
     is performed on a smaller input,
     which is true for the former call,
     but at termination time that is not known yet.
     Thus, we need to add @(tsee mbt) tests
     about certain inputs decreasing in size,
     which we verify when we verify the guards,
     after proving the input size inequalities
     for all the functions in the clique."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "The grammar rule for expressions is left-recursive,
       so we need to do left recursion elimination.
       The left-recursive rule is equivalent to")
     (xdoc::codeblock
      "expression = assignment-expression *( \",\" assignment-expression )")
     (xdoc::p
      "so we can parse it by first parsing an assignment expression
       and then parsing the rest,
       which is a sequence of zero or more instances of
       a comma followed by an assignment expression.
       The function to parse this sequence is @(tsee parse-expression-rest).
       In the original grammar, as in our abstract syntax,
       the comma operator is left-associative.
       So we pass the first expression (and its span)
       to @(tsee parse-expression-rest),
       where the final expression is constructed:
       see the documentation of that function for details."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp expr span parstate) (parse-assignment-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible)))
      (parse-expression-rest expr span parstate))
    :measure (two-nats-measure (parsize parstate) 16))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-expression-rest ((prev-expr exprp)
                                 (prev-span spanp)
                                 (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-expression):
       see that function's documentation first.
       In order to properly construct the final expression,
       given that the comma operator is left-associative,
       this recursive function takes
       the previous expression (and span) as input;
       the initial one comes from @(tsee parse-expression).")
     (xdoc::p
      "If we reach the end of file or a token that is not a comma,
       it means that the expression is complete.
       we unread the token if one was read
       (i.e. if we did not reach the end of file),
       and we just return the expression (and its span) passed as input:
       we do not need to create another comma expression.
       If instead there is a comma token,
       we read the assignment expression after that,
       and we form a comma expression consisting of
       the one passed as input and the one just parsed:
       this is the new current expression,
       which we pass to the recursive call of this function.
       Spans are joined similarly."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ;; prev-expr
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-punctuatorp token ","))) ; prev-expr not,
          (b* ((parstate
                (if token (unread-token parstate) parstate))) ; prev-expr
            (retok (expr-fix prev-expr) (span-fix prev-span) parstate)))
         ;; prev-expr ,
         (psize (parsize parstate))
         ((erp expr expr-span parstate) ; prev-expr , expr
          (parse-assignment-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (curr-expr (make-expr-comma :first prev-expr :next expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-assignment-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an assignment expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "According to the grammar, this may be
       not only an assignment expression proper,
       but also a conditional expression.
       To be an assignment expression proper,
       it must start with a unary expression,
       which is a kind of conditional expression.
       So we unconditionally parse a conditional expression,
       and then we check to see if it in fact a unary expression:
       if it is, and there is an assignment operator following,
       it must be an assignment expression proper,
       so we recursively parse its right (assignment) expression;
       otherwise,
       the expression we parsed is not an assignment expression proper,
       and instead it is a unary expression,
       which includes unary expressions propers
       but also other kinds of expressions."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp expr span parstate)
          (parse-conditional-expression parstate)) ; expr
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((when (not (expr-unary/postfix/primary-p expr)))
          (retok expr span parstate))
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-assignment-operator-p token))) ; expr not-asgop
          (b* ((parstate (if token (unread-token parstate) parstate))) ; expr
            (retok expr span parstate)))
         ;; expr asgop
         (asgop (token-to-assignment-operator token))
         ((erp expr2 span2 parstate) ; expr asgop expr2
          (parse-assignment-expression parstate)))
      (retok (make-expr-binary :op asgop
                               :arg1 expr
                               :arg2 expr2)
             (span-join span span2)
             parstate))
    :measure (two-nats-measure (parsize parstate) 15))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-conditional-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a conditional expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "According to the grammar, this may be
       not only a conditional expression,
       but also a logical disjunction expression.
       These two both start with a logical disjunction expression,
       which we parse first,
       and then we check whether there is a @('?'):
       if there is, it must be a conditional expression proper;
       if there is not, it must be a logical disjunction expression."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp expr span parstate)
          (parse-logical-or-expression parstate)) ; expr
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-punctuatorp token "?"))) ; expr not?
          (b* ((parstate (if token (unread-token parstate) parstate))) ; expr
            (retok expr span parstate)))
         ;; expr ?
         (psize (parsize parstate))
         ((erp expr2 & parstate) (parse-expression parstate)) ; expr ? expr2
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp & parstate) (read-punctuator ":" parstate)) ; expr ? expr2 :
         ((erp expr3 span3 parstate) ; expr ? expr2 : expr3
          (parse-conditional-expression parstate)))
      (retok (make-expr-cond :test expr :then expr2 :else expr3)
             (span-join span span3)
             parstate))
    :measure (two-nats-measure (parsize parstate) 14))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-logical-or-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a logical disjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp expr span parstate) (parse-logical-and-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible)))
      (parse-logical-or-expression-rest expr span parstate))
    :measure (two-nats-measure (parsize parstate) 13))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-logical-or-expression-rest ((prev-expr exprp)
                                            (prev-span spanp)
                                            (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a logical disjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-logical-or-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ;; prev-expr
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-punctuatorp token "||"))) ; prev-expr not||
          (b* ((parstate
                (if token (unread-token parstate) parstate))) ; prev-expr
            (retok (expr-fix prev-expr) (span-fix prev-span) parstate)))
         ;; prev-expr ||
         (psize (parsize parstate))
         ((erp expr expr-span parstate) ; prev-expr || expr
          (parse-logical-and-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (curr-expr (make-expr-binary :op (binop-logor)
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-logical-or-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-logical-and-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a logical conjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp expr span parstate) (parse-inclusive-or-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible)))
      (parse-logical-and-expression-rest expr span parstate))
    :measure (two-nats-measure (parsize parstate) 12))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-logical-and-expression-rest ((prev-expr exprp)
                                             (prev-span spanp)
                                             (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a logical conjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-logical-and-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ;; prev-expr
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-punctuatorp token "&&"))) ; prev-expr not&&
          (b* ((parstate
                (if token (unread-token parstate) parstate))) ; prev-expr
            (retok (expr-fix prev-expr) (span-fix prev-span) parstate)))
         ;; prev-expr &&
         (psize (parsize parstate))
         ((erp expr expr-span parstate) ; prev-expr && expr
          (parse-inclusive-or-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (curr-expr (make-expr-binary :op (binop-logand)
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-logical-and-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-inclusive-or-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an inclusive disjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp expr span parstate) (parse-exclusive-or-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible)))
      (parse-inclusive-or-expression-rest expr span parstate))
    :measure (two-nats-measure (parsize parstate) 11))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-inclusive-or-expression-rest ((prev-expr exprp)
                                              (prev-span spanp)
                                              (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of an inclusive disjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-inclusive-or-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ;; prev-expr
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-punctuatorp token "|"))) ; prev-expr not|
          (b* ((parstate
                (if token (unread-token parstate) parstate))) ; prev-expr
            (retok (expr-fix prev-expr) (span-fix prev-span) parstate)))
         ;; prev-expr |
         (psize (parsize parstate))
         ((erp expr expr-span parstate) ; prev-expr | expr
          (parse-exclusive-or-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (curr-expr (make-expr-binary :op (binop-bitior)
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-inclusive-or-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-exclusive-or-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an exclusive disjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp expr span parstate) (parse-and-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible)))
      (parse-exclusive-or-expression-rest expr span parstate))
    :measure (two-nats-measure (parsize parstate) 10))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-exclusive-or-expression-rest ((prev-expr exprp)
                                              (prev-span spanp)
                                              (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of an exclusive disjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-exclusive-or-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ;; prev-expr
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-punctuatorp token "^"))) ; prev-expr not^
          (b* ((parstate (if token (unread-token parstate) parstate)))
            (retok (expr-fix prev-expr) (span-fix prev-span) parstate)))
         ;; prev-expr ^
         (psize (parsize parstate))
         ((erp expr expr-span parstate) ; prev-expr ^ expr
          (parse-and-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (curr-expr (make-expr-binary :op (binop-bitxor)
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-exclusive-or-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-and-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a conjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp expr span parstate) (parse-equality-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible)))
      (parse-and-expression-rest expr span parstate))
    :measure (two-nats-measure (parsize parstate) 9))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-and-expression-rest ((prev-expr exprp)
                                     (prev-span spanp)
                                     (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a conjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-and-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ;; prev-expr
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-punctuatorp token "&"))) ; prev-expr not&
          (b* ((parstate
                (if token (unread-token parstate) parstate))) ; prev-expr
            (retok (expr-fix prev-expr) (span-fix prev-span) parstate)))
         ;; prev-expr &
         (psize (parsize parstate))
         ((erp expr expr-span parstate) ; prev-expr & expr
          (parse-equality-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (curr-expr (make-expr-binary :op (binop-bitand)
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-and-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-equality-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an equality expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp expr span parstate) (parse-relational-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible)))
      (parse-equality-expression-rest expr span parstate))
    :measure (two-nats-measure (parsize parstate) 8))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-equality-expression-rest ((prev-expr exprp)
                                          (prev-span spanp)
                                          (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of an equality expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-equality-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ;; prev-expr
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-equality-operator-p token))) ; prev-expr not-eqop
          (b* ((parstate
                (if token (unread-token parstate) parstate))) ; prev-expr
            (retok (expr-fix prev-expr) (span-fix prev-span) parstate)))
         ;; prev-expr eqop
         (psize (parsize parstate))
         ((erp expr expr-span parstate) ;; prev-expr eqop expr
          (parse-relational-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (op (token-to-equality-operator token))
         (curr-expr (make-expr-binary :op op
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-equality-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-relational-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a relational expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp expr span parstate) (parse-shift-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible)))
      (parse-relational-expression-rest expr span parstate))
    :measure (two-nats-measure (parsize parstate) 7))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-relational-expression-rest ((prev-expr exprp)
                                            (prev-span spanp)
                                            (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a relational expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-relational-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ;; prev-expr
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-relational-operator-p token))) ; prev-expr not-relop
          (b* ((parstate (if token (unread-token parstate) parstate)))
            (retok (expr-fix prev-expr) (span-fix prev-span) parstate)))
         ;; prev-expr relop
         (psize (parsize parstate))
         ((erp expr expr-span parstate) ;; prev-expr relop expr
          (parse-shift-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (op (token-to-relational-operator token))
         (curr-expr (make-expr-binary :op op
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-relational-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-shift-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a shift expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp expr span parstate) (parse-additive-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible)))
      (parse-shift-expression-rest expr span parstate))
    :measure (two-nats-measure (parsize parstate) 6))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-shift-expression-rest ((prev-expr exprp)
                                       (prev-span spanp)
                                       (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a shift expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-shift-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ;; prev-expr
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-shift-operator-p token))) ; prev-expr not-shiftop
          (b* ((parstate (if token (unread-token parstate) parstate)))
            (retok (expr-fix prev-expr) (span-fix prev-span) parstate)))
         ;; prev-expr shiftop
         (psize (parsize parstate))
         ((erp expr expr-span parstate) ;; prev-expr shiftop expr
          (parse-additive-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (op (token-to-shift-operator token))
         (curr-expr (make-expr-binary :op op
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-shift-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-additive-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an additive expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp expr span parstate) (parse-multiplicative-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible)))
      (parse-additive-expression-rest expr span parstate))
    :measure (two-nats-measure (parsize parstate) 5))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-additive-expression-rest ((prev-expr exprp)
                                          (prev-span spanp)
                                          (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of an additive expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-additive-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ;; prev-expr
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-additive-operator-p token))) ; prev-expr notaddop
          (b* ((parstate (if token (unread-token parstate) parstate)))
            (retok (expr-fix prev-expr) (span-fix prev-span) parstate)))
         ;; prev-expr addop
         (psize (parsize parstate))
         ((erp expr expr-span parstate) ;; prev-expr addop expr
          (parse-multiplicative-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (op (token-to-additive-operator token))
         (curr-expr (make-expr-binary :op op
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-additive-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-multiplicative-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a multiplicative expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp expr span parstate) (parse-cast-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible)))
      (parse-multiplicative-expression-rest expr span parstate))
    :measure (two-nats-measure (parsize parstate) 4))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-multiplicative-expression-rest ((prev-expr exprp)
                                                (prev-span spanp)
                                                (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a multiplicative expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by
       @(tsee parse-multiplicative-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ;; prev-expr
         ((erp token & parstate) (read-token parstate))
         ((when (not
                 (token-multiplicative-operator-p token))) ; prev-exp notmulop
          (b* ((parstate (if token (unread-token parstate) parstate)))
            (retok (expr-fix prev-expr) (span-fix prev-span) parstate)))
         ;; prev-expr mulop
         (psize (parsize parstate))
         ((erp expr expr-span parstate) ; prev-expr mulop expr
          (parse-cast-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (op (token-to-multiplicative-operator token))
         (curr-expr (make-expr-binary :op op
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-multiplicative-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-cast-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a cast expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We read a token, and there are two cases:")
     (xdoc::ol
      (xdoc::li
       "If the token is an open parenthesis,
        we may have either a cast expression proper or a unary expression,
        and we may need to deal with the ambiguity discussed in @(tsee expr).
        We describe how we handle all of this after describing the other case,
        which is simpler.")
      (xdoc::li
       "If the token is not an open parenthesis
        (including the case there there is no token, at the end of file),
        then we must have a unary expression if we have anything,
        and we call a separate function to parse that.
        Note that if that function fails to find
        a valid initial token for a unary expression,
        the error message mentions an open parenthesis
        among the expected tokens,
        because a primary expression (which is a unary expression in grammar)
        may start with an open parenthesis;
        this covers also the possible open parenthesis
        of a cast expression proper,
        and so the error message is adequate to
        not only expecting (and failing to find) a unary expression,
        but also a cast expression."))
     (xdoc::p
      "Now we describe the more complex first case above,
       the one when the first token is an open parenthesis.
       This may start a cast expression proper or a unary expression,
       more precisely a compound literal (a kind of postfix expression),
       or a parenthesized expression (a kind of primary expression).
       So we must read a second token, and there are four cases:")
     (xdoc::ol
      (xdoc::li
       "If the second token is an identifier,
        things are still ambiguous.
        The identifier may be an expression or a type name.
        We describe this case in more detail below,
        after describing the other three cases, which are simpler.")
      (xdoc::li
       "If the second token may start an expression but is not an identifier,
        then we have resolved the ambiguity:
        we must be parsing a unary expression,
        more precisely a parenthesized expression.
        So we put back the second token,
        we parse the expression,
        and we parse the closed parenthesis.")
      (xdoc::li
       "If the second token may start a type name but is not an identifier,
        things are still ambiguous.
        The parenthesized type name may be part of a cast expression proper,
        or part of a compund literal.
        To resolve this ambiguity,
        we parse the type name,
        we parse the closed parenthesis,
        and then we parse a third token
        (after the type name and the closed parenthesis).
        If this third token is an open curly brace,
        we must be parsing a compound literal:
        so we call a separate function to parse (the rest of) it.
        If instead this third other token is not a curly brace,
        we must be parsing a cast expression proper:
        we put back the token,
        and we recursively parse a cast expression.
        If this third token is absent, it is an error:
        the message describes the possible starts of
        cast expressions (same as unary expressions),
        and open curly braces compound literals.")
      (xdoc::li
       "If the second token is none of the above, it is an error.
        The message mentions all possible starts of expressions and type names:
        since we have already parsed the open parenthesis,
        those are all the possibilities."))
     (xdoc::p
      "Note that identifiers are the only overlap between
       starts of expressions and starts of type names.")
     (xdoc::p
      "Now we describe the more complex first case above,
       which happens when there is an identifier after the open parenthesis.
       We read a third token, and there are different cases based on that:")
     (xdoc::ol
      (xdoc::li
       "If this third token may start the rest of a postfix expression
        (according to @(tsee token-postfix-expression-rest-start-p)),
        then we have resolved the ambiguity:
        we must be parsing a unary expression,
        more precisely a parenthesized postfix expression.
        We put back the third token,
        we put back the identifier,
        we parse the postfix expression,
        and we parse the closing parenthesis.")
      (xdoc::li
       "If this third token is a closing parenthesis,
        things are still ambiguous.
        We describe this case below,
        after describing the next case, which is simpler.")
      (xdoc::li
       "If this third token is anything else, or is absent (end of file),
        it is an error.
        The message mentions all the possible expected tokens there."))
     (xdoc::p
      "Now we describe the more complex second case above,
       when we have a parenthesized identifier.
       We need to read a fourth token:")
     (xdoc::ol
      (xdoc::li
       "If this fourth token is an open curly brace,
        we have resolved the ambiguity.
        We must be reading a compound literal
        that starts with a parenthesized identifier type name.
        We put back the token,
        and we call a separate ACL2 function
        to finish parsing this compound literal.")
      (xdoc::li
       "If this fourth token is a star,
        that star may be either a unary operator,
        in which case we must have been parsing a cast expression proper
        where the identifier is a type name,
        or a binary operator,
        in which case we must have been parsing a multiplicative expression
        where the identifier is an expression.
        Either way, what follows must be a cast expression (proper or not):
        see the grammar for cast and unary expressions.
        If we can parse such a cast expression,
        we still have a syntactic ambiguity,
        which we capture in our abstract syntax,
        deferring the disambiguation to post-parsing analysis;
        see the discussion in @(tsee expr).")
      (xdoc::li
       "If this fourth token is a plus or minus,
        it may be a unary or binary operator, similarly to the star case.
        However, if it is a binary operator,
        then the next expression to parser after that
        is a multiplicative expression, not a cast expression.
        So we parse a multiplicative expression,
        and we return the appropriate syntactically ambiguous expression,
        according to our abstract syntax (see @(tsee expr)).")
      (xdoc::li
       "If this fourth token is an ampersand,
        the handling is similar to the above cases,
        but the next expression to parse is an equality one:
        see the grammar rule for conjunction expressions.")
      (xdoc::li
       "If this fourth token is none of those unary/binary operators,
        but it may be the start of a (cast) expression,
        then we resolve the ambiguity.
        The identifier must be a type name,
        and we must have been parsing a cast expression proper.
        We put back the token,
        and we recursively parse a cast expression.")
      (xdoc::li
       "If none of the above cases applies,
        including the case that the token is absent,
        we have resolved the ambiguity.
        The identifier must have been an expression,
        in parenthesis.
        We put back the token (if present),
        and we return the parenthesized expression.")))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is an open parenthesis,
       ;; we may have a cast expression proper or a unary expression,
       ;; and we may also have the ambiguities discussed in :DOC EXPR.
       ;; We try parsing a possibly ambiguous expression or type name,
       ;; after recording a checkpoint for possible backtracking.
       ((token-punctuatorp token "(") ; (
        (b* ((parstate (record-checkpoint parstate))
             (psize (parsize parstate))
             ((erp expr/tyname & parstate) ; ( expr/tyname
              (parse-expression-or-type-name parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible)))
          (amb?-expr/tyname-case
           expr/tyname
           ;; If we have an ambiguous type name,
           ;; we may be parsing a proper cast expression
           ;; or a compound literal.
           ;; But there is no need to backtrack now,
           ;; so we clear the checkpoint saved earlier.
           ;; We parse the closed parenthesis
           ;; and we read another token to disambiguate
           ;; between a cast expression and a compound literal.
           :tyname ; ( tyname
           (b* ((parstate (clear-checkpoint parstate))
                ((erp & parstate) (read-punctuator ")" parstate)) ; ( tyname )
                ((erp token2 & parstate) (read-token parstate)))
             (cond
              ;; If token2 is an open curly brace,
              ;; we must have a compound literal.
              ;; We put back the open curly brace,
              ;; and we call the function to parse compound literals.
              ((token-punctuatorp token2 "{") ; ( tyname ) {
               (b* ((parstate (unread-token parstate)))
                 (parse-compound-literal expr/tyname.unwrap span parstate)))
              ;; If token2 is not an open curly brace,
              ;; we must be parsing a cast expression proper,
              ;; so we put back the token (if any)
              ;; and we attempt to recursively parse a cast expression,
              ;; which is the argument of the one being parsed.
              (t ; ( tyname ) other
               (b* ((parstate ; ( tyname )
                     (if token2 (unread-token parstate) parstate))
                    ((erp expr last-span parstate) ; ( tyname ) expr
                     (parse-cast-expression parstate)))
                 (retok (make-expr-cast :type expr/tyname.unwrap
                                        :arg expr)
                        (span-join span last-span)
                        parstate)))))
           ;; If we have an unambiguous expression,
           ;; we must be actually parsing a unary expression,
           ;; precisely a postfix expression because
           ;; it starts with an open parenthesis.
           ;; So we backtrack to the previously saved checkpoint,
           ;; namely at the open parenthesis,
           ;; we also put back the open parenthesis,
           ;; and we attempt to parse a postfix expression.
           :expr ; ( expr
           (b* ((parstate (backtrack-checkpoint parstate)) ; (
                ((unless (<= (parsize parstate) psize))
                 (raise "Internal error: ~
                         size ~x0 after backtracking exceeds ~
                         size ~x1 before backtracking."
                        (parsize parstate) psize)
                 ;; Here we have (> (parsize parstate) psize),
                 ;; but we need to return a parser state
                 ;; no larger than the initial one,
                 ;; so we just return the empty parser state.
                 ;; This is just logical: execution stops at the RAISE above.
                 (b* ((parstate (init-parstate nil nil parstate)))
                   (reterr t)))
                (parstate (unread-token parstate))) ;
             (parse-postfix-expression parstate))
           ;; If we have an ambiguous expression or type name,
           ;; we need to read more tokens,
           ;; on the basis of which we may be able to disambiguate things,
           ;; unless we end up with an ambiguous cast.
           ;; First we read any increment and decrement operators that follow.
           :ambig ; ( expr/tyname
           (b* (((erp & parstate)
                 (read-punctuator ")" parstate)) ; ( expr/tyname )
                ((erp incdecops parstate) ; ( expr/tyname ) [ops]
                 (parse-*-increment/decrement parstate))
                ((erp token2 & parstate) (read-token parstate)))
             (cond
              ;; If token2 is an open parenthesis,
              ;; it must start a postfix expression,
              ;; and we are in an ambiguous situation
              ;; (see the first pattern in :DOC EXPR).
              ;; We also clear the checkpoint,
              ;; since we no longer need to backtrack.
              ((token-punctuatorp token2 "(") ; ( expr/tyname ) [ops] (
               (b* ((parstate (clear-checkpoint parstate))
                    (parstate (unread-token parstate)) ; ( expr/tyname ) [ops]
                    ((erp expr last-span parstate) ; ( expr/tyname ) [ops] expr
                     (parse-postfix-expression parstate)))
                 (retok (make-expr-cast/call-ambig
                         :type/fun expr/tyname.unwrap
                         :inc/dec incdecops
                         :arg/rest expr)
                        (span-join span last-span)
                        parstate)))
              ;; If token2 is a star, we have an ambiguity.
              ;; We parse a cast expression after the star,
              ;; which is the same kind of expected expression
              ;; whether the star is unary or binary.
              ;; We also clear the checkpoint,
              ;; since we no longer need to backtrack.
              ((token-punctuatorp token2 "*") ; ( expr/tyname ) [ops] *
               (b* ((parstate (clear-checkpoint parstate))
                    ;; ( expr/tyname ) [ops] * expr
                    ((erp expr last-span parstate)
                     (parse-cast-expression parstate)))
                 (retok (make-expr-cast/mul-ambig
                         :type/arg1 expr/tyname.unwrap
                         :inc/dec incdecops
                         :arg/arg2 expr)
                        (span-join span last-span)
                        parstate)))
              ;; If token2 is a plus or minus, we have an ambiguity.
              ;; We parse a multiplicative expression after the plus or minus,
              ;; which is the kind required if the plus or minus is binary.
              ;; If the plus or minus is unary,
              ;; then we would need to parse a cast expression instead.
              ;; This means that we may be parsing a larger expression,
              ;; in case the plus or minus turns out to be unary
              ;; during post-parsing semantic analysis.
              ;; But in that case we can adjust the expressions accordingly,
              ;; and it should be easier to adjust them like that
              ;; than if we had parsed a smaller cast expression.
              ;; We also clear the checkpoint,
              ;; since we no longer need to backtrack.
              ((or (token-punctuatorp token2 "+") ; ( expr/tyname ) [ops] +
                   (token-punctuatorp token2 "-")) ; ( expr/tyname ) [ops] -
               (b* ((parstate (clear-checkpoint parstate))
                    ;; ( expr/tyname ) [ops] +- expr
                    ((erp expr last-span parstate)
                     (parse-multiplicative-expression parstate)))
                 (retok (make-expr-cast/add-or-cast/sub-ambig
                         token2 expr/tyname.unwrap incdecops expr)
                        (span-join span last-span)
                        parstate)))
              ;; If token2 is an ampersand, we have an ambiguity.
              ;; We parse an equality expression after the ampersand,
              ;; which is the kind required if the ampersand is binary.
              ;; If the ampersand is unary,
              ;; then we would need to parse a cast expression instead.
              ;; This means that we may be parsing a larger expression,
              ;; in case the ampersand turns out to be unary
              ;; during post-parsing semantic analysis.
              ;; But in that case we can adjust the expressions accordingly,
              ;; and it should be easier to adjust them like that
              ;; than if we had parsed a smaller cast expression.
              ;; We also clear the checkpoint,
              ;; since we no longer need to backtrack.
              ((token-punctuatorp token2 "&") ; ( expr/tyname ) [ops] &
               (b* ((parstate (clear-checkpoint parstate))
                    ((erp expr last-span parstate)
                     ;; ( expr/tyname ) [ops] & expr
                     (parse-equality-expression parstate)))
                 (retok (make-expr-cast/and-ambig
                         :type/arg1 expr/tyname.unwrap
                         :inc/dec incdecops
                         :arg/arg2 expr)
                        (span-join span last-span)
                        parstate)))
              ;; If token2 may start a unary expression,
              ;; given that we have already covered the cases of
              ;; open parenthesis, star, plus, minus, and ampersand,
              ;; and that we have already parsed
              ;; past any increment and decrement operators,
              ;; the ambiguity is resolved:
              ;; we must have a cast expression,
              ;; with the ambiguous type name or expression
              ;; actually being a type name,
              ;; and with a unary expression as argument.
              ;; So we put back the token,
              ;; we parse a unary expression,
              ;; we apply any increment and decrement operators to it,
              ;; and we form and return the cast expression.
              ;; We also clear the checkpoint,
              ;; since we no longer need to backtrack.
              ((token-unary-expression-start-p
                token2) ; ( expr/tyname ) [ops] unaryexpr...
               (b* ((parstate (clear-checkpoint parstate))
                    (parstate (unread-token parstate)) ; ( expr/tyname ) [ops]
                    ((erp expr last-span parstate) ; ( expr/tyname ) [ops] expr
                     (parse-unary-expression parstate))
                    (expr
                     (make-expr-unary-with-preinc/predec-ops incdecops expr))
                    (tyname (amb-expr/tyname->tyname expr/tyname.unwrap)))
                 (retok (make-expr-cast :type tyname :arg expr)
                        (span-join span last-span)
                        parstate)))
              ;; If token2 is anything else,
              ;; we must have resolved the ambiguity:
              ;; the ambiguous expression or type name
              ;; is in fact an expression,
              ;; and the increment and decrement operators, if any,
              ;; are postfix operators.
              ;; Furthermore, there may be further postfix constructs,
              ;; e.g. an array access.
              ;; In this case we backtrack all the way
              ;; to the initial open parenthesis,
              ;; we put back that one too,
              ;; and we parse a postfix expression.
              ;; It must be a postfix expression,
              ;; because it starts with an open parenthesis,
              ;; and we are expecting either a cast expression proper
              ;; (which has been excluded at this point)
              ;; or a unary expression that starts with an open parenthesis,
              ;; so in fact it is a primary parenthesized expression,
              ;; or a postfix expression starting with
              ;; a primary parenthesized expression.
              (t ; ( expr/tyname ) [ops] other
               (b* ((parstate (backtrack-checkpoint parstate)) ; (
                    ((unless (<= (parsize parstate) psize))
                     (raise "Internal error: ~
                             size ~x0 after backtracking exceeds ~
                             size ~x1 before backtracking."
                            (parsize parstate) psize)
                     ;; Here we have (> (parsize parstate) psize),
                     ;; but we need to return a parser state
                     ;; no larger than the initial one,
                     ;; so we just return the empty parser state.
                     ;; This is just logical:
                     ;; execution stops at the RAISE above.
                     (b* ((parstate (init-parstate nil nil parstate)))
                       (reterr t)))
                    (parstate (unread-token parstate))) ;
                 (parse-postfix-expression parstate))))))))
       ;; If token is not an open parenthesis,
       ;; we must be parsing a unary expression,
       ;; not a proper cast expression.
       ;; We put back the token (if any)
       ;; and we attempt to parse a unary expression.
       (t ; other
        (b* ((parstate (if token (unread-token parstate) parstate))) ;
          (parse-unary-expression parstate)))))
    :measure (two-nats-measure (parsize parstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-unary-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a unary expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We can always distinguish the alternatives of
       the grammar rule for unary expressions based on the next token,
       except for the potential ambiguity between
       parenthesized expressions or type names after @('sizeof').")
     (xdoc::p
      "If we encounter a @('sizeof') not followed by an open parenthesis,
       there is no potential ambiguity: the operand must be an expression.
       If there is an open parenthesis,
       we parse an expression or type name via a separate function,
       and based on the result we return a @('sizeof') expression with
       an expression, a type name, or an ambiguous type name or expression."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token may start a postfix expression
       ;; (or equivalently a primary expression),
       ;; we put back the token and we parse a postfix expression.
       ;; There is no overlap between postfix expressions
       ;; and the other kinds of unary expressions.
       ((token-primary-expression-start-p token) ; expr...
        (b* ((parstate (unread-token parstate)))
          (parse-postfix-expression parstate)))
       ;; If token is a double plus or double minus
       ;; (i.e. a preincrement or predecrement operator),
       ;; we recursively parse the operand unary expression.
       ((token-preinc/predec-operator-p token) ; preop
        (b* (((erp expr last-span parstate) ; preop expr
              (parse-unary-expression parstate))
             (unop (token-to-preinc/predec-operator token)))
          (retok (make-expr-unary :op unop :arg expr)
                 (span-join span last-span)
                 parstate)))
       ;; If token is a unay operator as defined in the grammar
       ;; (our abstract syntax has a broader notion),
       ;; then we recursively parse a cast expression as operand.
       ((token-unary-operator-p token) ; unop
        (b* (((erp expr last-span parstate) ; unop expr
              (parse-cast-expression parstate))
             (unop (token-to-unary-operator token)))
          (retok (make-expr-unary :op unop :arg expr)
                 (span-join span last-span)
                 parstate)))
       ;; If token is 'sizeof', we need to read another token.
       ((token-keywordp token "sizeof") ; sizeof
        (b* (((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is an open parenthesis,
           ;; we are in a potentially ambiguous situation.
           ;; We parse an expression or type name,
           ;; and then the closed parenthesis.
           ((token-punctuatorp token2 "(") ; sizeof (
            (b* (((erp expr/tyname & parstate) ; sizeof ( exprtyname
                  (parse-expression-or-type-name parstate))
                 ((erp last-span parstate) ; sizeof ( exprtyname )
                  (read-punctuator ")" parstate))
                 (expr
                  (amb?-expr/tyname-case
                   expr/tyname
                   :expr (make-expr-unary :op (unop-sizeof)
                                          :arg expr/tyname.unwrap)
                   :tyname (expr-sizeof expr/tyname.unwrap)
                   :ambig (expr-sizeof-ambig expr/tyname.unwrap))))
              (retok expr (span-join span last-span) parstate)))
           ;; If token2 is not an open parenthesis,
           ;; the operand must be a unary expression.
           (t ; sizeof other
            (b* ((parstate
                  (if token2 (unread-token parstate) parstate)) ; sizeof
                 ((erp expr last-span parstate) ; sizeof expr
                  (parse-unary-expression parstate)))
              (retok (make-expr-unary :op (unop-sizeof)
                                      :arg expr)
                     (span-join span last-span)
                     parstate))))))
       ;; If token is '_Alignof',
       ;; we parse an open parenthesis, a type name, and a closed parenthesis.
       ;; We also allow '__alignof' and '__alignof__',
       ;; which can be keywords only if GCC extensions are supported.
       ((or (token-keywordp token "_Alignof") ; _Alignof
            (token-keywordp token "__alignof") ; __alignof
            (token-keywordp token "__alignof__")) ; __alignof__
        (b* (((erp & parstate) ; _Alignof (
              (read-punctuator "(" parstate))
             ((erp tyname & parstate) ; _Alignof ( typename
              (parse-type-name parstate))
             ((erp last-span parstate) ; _Alignof ( typename )
              (read-punctuator ")" parstate)))
          (retok (make-expr-alignof
                  :type tyname
                  :uscores (cond ((token-keywordp token "_Alignof")
                                  (keyword-uscores-none))
                                 ((token-keywordp token "__alignof")
                                  (keyword-uscores-start))
                                 ((token-keywordp token "__alignof__")
                                  (keyword-uscores-both))))
                 (span-join span last-span)
                 parstate)))
       ;; If token is anything else, it is an error.
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or a constant ~
                               or a string literal ~
                               or a keyword in {~
                               _Alignof, ~
                               _Generic, ~
                               sizeof~
                               } ~
                               or a punctuator in {~
                               \"++\", ~
                               \"--\", ~
                               \"+\", ~
                               \"-\", ~
                               \"~~\", ~
                               \"!\", ~
                               \"*\", ~
                               \"&\", ~
                               \"(\"~
                               }"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-postfix-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a postfix expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "A postfix expression may start with a primary expression
       or with a parenthesized type name,
       both of which start with an open parenthesis.
       So we need to read a token, and see if it is an open parenthesis.
       If it is not, we must have
       a postfix expression that starts with a primary expression:
       we put back the token,
       parse a primary expression,
       and then parse the rest of the postfix expression
       via a separate function (see that function's) documentation.
       Note that if the parsing of the primary expression fails,
       the error message mentions the possibility of an open parenthesis,
       which thus covers the case of a parenthesized type name as well.")
     (xdoc::p
      "If the token is an open parenthesis,
       we read a second token:")
     (xdoc::ol
      (xdoc::li
       "If this second token is an identifier, things are still ambiguous.
        We describe the handling of this case below,
        after describing the other cases, which are simpler.")
      (xdoc::li
       "If this second token may start an expression
        but is not an identifier (the case above),
        then we have a parenthesized expression
        that is a primary expression that starts the postfix expression.
        We put back the token,
        we parse an expression,
        we read the closing parenthesis,
        and we parse the rest of the postfix expression
        via a separate function.")
      (xdoc::li
       "If this second token may start a type name,
        but is not an identifier (the first case above),
        we must have a compound literal.
        We put back the token,
        parse a type name,
        read a closing parenthesis,
        and call a separate function to finish parsing the compound literal.")
      (xdoc::li
       "If this second token is none of the above, including an absent token,
        it is an error, whose message mentions
        the possible starts of expressions and type names."))
     (xdoc::p
      "Now we describe the more complex case above,
       where we have an open parenthesis and an identifier.
       We read a third token:")
     (xdoc::ol
      (xdoc::li
       "If this third token is a closed parenthesis,
        things are still ambiguous, because we could have
        either a parenthesized expression or a parenthesized type name.
        We describe this case below, after describing the other cases,
        which are simpler.")
      (xdoc::li
       "If this third token may be the rest of a postfix expression,
        we put back the token and parse an expression.
        Then we parse a closing parenthesis,
        and this is a primary expression:
        we parse the rest of the postfix expression (if any).")
      (xdoc::li
       "If this third token is none of the above, it is an error."))
     (xdoc::p
      "Now we describe the more complex case above,
       where we have a parenthesized identifier,
       which could be either an expression or a type name.
       We read a fourth token, and consider these cases:")
     (xdoc::ol
      (xdoc::li
       "If this fourth token is an open curly brace,
        we have resolved the ambiguity.
        The postfix expression is a compound literal.
        We put back the curly brace
        and we call a separare function to parse
        the rest of the compound literal.")
      (xdoc::li
       "If this fourth token may start the rest of a postfix expression,
        we have also resolved the ambiguity:
        the identifier must be an expression,
        and we parse the rest of the postfix expression
        after putting back the token.")
      (xdoc::li
       "If this fourth token is none of the above,
        we have an error.")))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is an open parenthesis,
       ;; it may start a compound literal
       ;; or a (parenthesized) primary expresssion.
       ;; So we start by parsing a possibly ambiguous type name or expression
       ;; and we decide what to do next based on that result
       ;; (we also parse past the closed parenthesis).
       ((token-punctuatorp token "(") ; (
        (b* ((psize (parsize parstate))
             ((erp expr/tyname & parstate) ; ( expr/tyname
              (parse-expression-or-type-name parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp close-paren-span parstate) ; ( expr/tyname )
              (read-punctuator ")" parstate)))
          (amb?-expr/tyname-case
           expr/tyname
           ;; If we just parsed a parenthesized type name,
           ;; the only possibility is to have a compound literal.
           :tyname
           (parse-compound-literal expr/tyname.unwrap
                                   (span-join span close-paren-span)
                                   parstate)
           ;; If we just parsed a parenthesized expression,
           ;; we cannot have a compound literal,
           ;; and instead we have just parsed the primary expression
           ;; that always starts a non-compound-literal postfix expression.
           ;; So we proceed to parse the rest of the postfix expression
           :expr
           (b* ((prev-expr (expr-paren expr/tyname.unwrap))
                (prev-span (span-join span close-paren-span)))
             (parse-postfix-expression-rest prev-expr prev-span parstate))
           ;; If we just parsed an ambiguous type name or expression,
           ;; we can actually disambiguate it by looking at what comes next.
           :ambig
           (b* (((erp token2 & parstate) (read-token parstate)))
             (cond
              ;; If token2 is an open curly brace,
              ;; we must have a compound literal,
              ;; and the ambiguous expression or type name must be a type name.
              ((token-punctuatorp token2 "{") ; ( expr/tyname ) {
               (b* ((parstate (unread-token parstate)) ; ( expr/tyname )
                    (tyname (amb-expr/tyname->tyname expr/tyname.unwrap)))
                 (parse-compound-literal tyname
                                         (span-join span close-paren-span)
                                         parstate)))
              ;; If token2 is not an open curly brace,
              ;; we cannot have a compound literal,
              ;; and thus we must have just parsed a parenthesized expression,
              ;; which is the primary expression that starts
              ;; this postfix expression.
              (t ; ( expr/tyname ) other
               (b* ((parstate ; ( expr/tyname )
                     (if token2 (unread-token parstate) parstate))
                    (expr (amb-expr/tyname->expr expr/tyname.unwrap))
                    (prev-expr (expr-paren expr))
                    (prev-span (span-join span close-paren-span)))
                 (parse-postfix-expression-rest prev-expr
                                                prev-span
                                                parstate))))))))
       ;; If token is not an open parenthesis,
       ;; we cannot have a compound literal,
       ;; and thus we parse the primary expression
       ;; that starts the postfix expression.
       (t ; other
        (b* ((parstate (if token (unread-token parstate) parstate)) ;
             (psize (parsize parstate))
             ((erp expr span parstate) ; expr
              (parse-primary-expression parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible)))
          (parse-postfix-expression-rest expr span parstate)))))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-postfix-expression-rest ((prev-expr exprp)
                                         (prev-span spanp)
                                         (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a postfix expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called by @(tsee parse-postfix-expression)
       after parsing the primary expression that starts the postfix expression,
       passing that primary expression and its span to this function.
       This function is analogous to
       @(tsee parse-expression-rest) and similar functions:
       it handles, together with the initial parsing of the primary expression,
       the elimination of the left recursion in
       the grammar rule for postfix expressions.")
     (xdoc::p
      "We read and examine the next token.
       If it may start the rest of a postfix expression
       (see @(tsee token-postfix-expression-rest-start-p)),
       we parse the postfix construct started by that token.
       We combine that with the input expression and span,
       and we recursively call this function
       to see if there are further postfix constructs.
       Note that this recursion associates the postfix expression to the left,
       as implied by the grammar.
       The recursion ends when the next token
       is absent or cannot start a postfix construct."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ;; prev-expr
         ((erp token span parstate) (read-token parstate)))
      (cond
       ((token-punctuatorp token "[") ; prev-expr [
        (b* ((psize (parsize parstate))
             ((erp expr & parstate) ; prev-expr [ expr
              (parse-expression parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp last-span parstate) ; prev-expr [ expr ]
              (read-punctuator "]" parstate))
             (curr-expr (make-expr-arrsub :arg1 prev-expr
                                          :arg2 expr))
             (curr-span (span-join prev-span last-span)))
          (parse-postfix-expression-rest curr-expr curr-span parstate)))
       ((token-punctuatorp token "(") ; prev-expr (
        (b* ((psize (parsize parstate))
             ((erp exprs & parstate) ; prev-expr ( exprs
              (parse-argument-expressions parstate))
             ((unless (mbt (<= (parsize parstate) psize)))
              (reterr :impossible))
             ((erp last-span parstate) ; prev-expr ( exprs )
              (read-punctuator ")" parstate))
             (curr-expr (make-expr-funcall :fun prev-expr
                                           :args exprs))
             (curr-span (span-join prev-span last-span)))
          (parse-postfix-expression-rest curr-expr curr-span parstate)))
       ((token-punctuatorp token ".") ; prev-expr .
        (b* (((erp ident ident-span parstate) ; prev-expr . ident
              (read-identifier parstate))
             (curr-expr (make-expr-member :arg prev-expr
                                          :name ident))
             (curr-span (span-join prev-span ident-span)))
          (parse-postfix-expression-rest curr-expr curr-span parstate)))
       ((token-punctuatorp token "->") ; prev-expr ->
        (b* (((erp ident ident-span parstate) ; prev-expr -> ident
              (read-identifier parstate))
             (curr-expr (make-expr-memberp :arg prev-expr
                                           :name ident))
             (curr-span (span-join prev-span ident-span)))
          (parse-postfix-expression-rest curr-expr curr-span parstate)))
       ((token-punctuatorp token "++") ; prev-expr ++
        (b* ((curr-expr (make-expr-unary :op (unop-postinc)
                                         :arg prev-expr))
             (curr-span (span-join prev-span span)))
          (parse-postfix-expression-rest curr-expr curr-span parstate)))
       ((token-punctuatorp token "--") ; prev-expr --
        (b* ((curr-expr (make-expr-unary :op (unop-postdec)
                                         :arg prev-expr))
             (curr-span (span-join prev-span span)))
          (parse-postfix-expression-rest curr-expr curr-span parstate)))
       (t ; prev-expr other
        (b* ((parstate (if token (unread-token parstate) parstate))) ; prev-expr
          (retok (expr-fix prev-expr) (span-fix prev-span) parstate)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-argument-expressions ((parstate parstatep))
    :returns (mv erp
                 (exprs expr-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse zero or more argument expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called by @(tsee parse-postfix-expression-rest),
       to parse the arguments of a function call.
       These are zero or more assignment expressions,
       as an optional non-empty sequence of assignment expressions
       in the grammar.
       That part of the grammar is left-recursive,
       which we handle as in other left-recursive parts of the grammar.")
     (xdoc::p
      "If GCC extensions are supported,
       this parsing function is also called
       to parse attribute parameters:
       see @(tsee parse-attribute-parameters).")
     (xdoc::p
      "If the next token may start an expression,
       we parse an assignment expression,
       and then we call a separate function
       to parse any additional arguments.
       Otherwise, we return the empty list of argument expressions."))
    (b* (((reterr) nil (irr-span) parstate)
         ((erp token & parstate) (read-token parstate)))
      (cond
       ((token-expression-start-p token) ; expr...
        (b* ((parstate (unread-token parstate))
             (psize (parsize parstate))
             ((erp expr span parstate) ; expr
              (parse-assignment-expression parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             (curr-exprs (list expr))
             (curr-span span))
          (parse-argument-expressions-rest curr-exprs curr-span parstate)))
       (t ; other
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok nil (irr-span) parstate)))))
    :measure (two-nats-measure (parsize parstate) 16))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-argument-expressions-rest ((prev-exprs expr-listp)
                                           (prev-span spanp)
                                           (parstate parstatep))
    :returns (mv erp
                 (exprs expr-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of one or more argument expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called by @(tsee parse-argument-expressions),
       after parsing the first argument expression,
       which we pass to this function as a singleton list.
       Here we read any additional arguments,
       each of which starts with a comma;
       we extend the list of arguments in the course of the recursion.
       We stop when the next token is not a comma.")
     (xdoc::p
      "We could extend the list in reverse (via @(tsee cons)),
       and then reverse it in the caller,
       but it probably does not make a big difference in performance."))
    (b* (((reterr) nil (irr-span) parstate)
         ;; prev-exprs
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-punctuatorp token ",")))
          (b* ((parstate (if token (unread-token parstate) parstate)))
            (retok (expr-list-fix prev-exprs)
                   (span-fix prev-span)
                   parstate)))
         ;; prev-exprs ,
         (psize (parsize parstate))
         ((erp expr span parstate) ; prev-exprs , expr
          (parse-assignment-expression parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (curr-exprs (append prev-exprs (list expr)))
         (curr-span (span-join prev-span span)))
      (parse-argument-expressions-rest curr-exprs curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-primary-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a primary expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called when we expect an expression.")
     (xdoc::p
      "We read a token.")
     (xdoc::p
      "If the token is an identifier or a constant or a string literal,
       that is the whole expression.")
     (xdoc::p
      "If the token is an open parenthesis,
       we parse an expression and a closed parenthesis:
       we have a parenthesized expression.")
     (xdoc::p
      "If the token is the keyword @('_Generic'),
       we parse an open parenthesis and an assignment expression,
       then a comma and a generic association,
       since there must be at least one.
       Then we call a separate function to parse
       zero or more additional generic associations.
       Finally we parse a closed parenthesis and return a generic selection.")
     (xdoc::p
      "If the token is none of the above,
       including the token being absent,
       it is an error."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ((and token (token-case token :ident)) ; identifier
        (retok (expr-ident (token-ident->unwrap token)) span parstate))
       ((and token (token-case token :const)) ; constant
        (retok (expr-const (token-const->unwrap token)) span parstate))
       ((and token (token-case token :string)) ; stringlit
        (b* (((erp strings last-span parstate) ; stringlit stringlits
              (parse-*-stringlit parstate)))
          (retok (expr-string (cons (token-string->unwrap token) strings))
                 (if strings (span-join span last-span) span)
                 parstate)))
       ((token-punctuatorp token "(") ; (
        (b* (((erp expr & parstate) ; ( expr
              (parse-expression parstate))
             ((erp last-span parstate) ; ( expr )
              (read-punctuator ")" parstate)))
          (retok (expr-paren expr)
                 (span-join span last-span)
                 parstate)))
       ((token-keywordp token "_Generic") ; _Generic
        (b* (((erp & parstate) (read-punctuator "(" parstate)) ; _Generic (
             (psize (parsize parstate))
             ((erp expr & parstate) ; _Generic ( expr
              (parse-assignment-expression parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp & parstate)
              (read-punctuator "," parstate)) ; _Generic ( expr ,
             (psize (parsize parstate))
             ((erp genassoc genassoc-span parstate) ; _Generic ( expr , genassoc
              (parse-generic-association parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp genassocs & parstate) ; _Generic ( expr , genassoc ...
              (parse-generic-associations-rest (list genassoc)
                                               genassoc-span
                                               parstate))
             ((erp last-span parstate) ; _Generic ( expr , genassoc ... )
              (read-punctuator ")" parstate)))
          (retok (make-expr-gensel :control expr
                                   :assocs genassocs)
                 (span-join span last-span)
                 parstate)))
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or a constant ~
                               or a string literal ~
                               or an open parenthesis ~
                               or the keyword _Generic"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-generic-associations-rest ((prev-genassocs genassoc-listp)
                                           (prev-span spanp)
                                           (parstate parstatep))
    :returns (mv erp
                 (genassocs genassoc-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse zero or more reamaining generic associations."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after parsing
       the first generic association of a generic selection,
       which is required (i.e. there must be at least one).
       Thus, each generic association to parse (if any),
       is preceded by a comma.
       We stop when there is no more comma.")
     (xdoc::p
      "We pass to this function
       the list of generic expressions parsed so far,
       along with their span.
       This makes it easier to handle the span calculation."))
    (b* (((reterr) nil (irr-span) parstate)
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-punctuatorp token ",")))
          (b* ((parstate (if token (unread-token parstate) parstate)))
            (retok (genassoc-list-fix prev-genassocs)
                   (span-fix prev-span)
                   parstate)))
         ;; ,
         (psize (parsize parstate))
         ((erp genassoc span parstate) ; , genassoc
          (parse-generic-association parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (curr-genassocs (append prev-genassocs (list genassoc)))
         (curr-span (span-join prev-span span)))
      (parse-generic-associations-rest curr-genassocs curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-generic-association ((parstate parstatep))
    :returns (mv erp
                 (genassoc genassocp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a generic association."
    :long
    (xdoc::topstring
     (xdoc::p
      "We read the next token.")
     (xdoc::p
      "If the token may start a type name,
       we put it back and then we parse
       a type name, a colon, and an assignment expression.")
     (xdoc::p
      "If the token is the keyword @('default'),
       we parse a colon and an assignment expression.")
     (xdoc::p
      "If the token is none of the above, it is an error."))
    (b* (((reterr) (irr-genassoc) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ((token-type-name-start-p token) ; typename...
        (b* ((parstate (unread-token parstate))
             (psize (parsize parstate))
             ((erp tyname & parstate) (parse-type-name parstate)) ; typename
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp & parstate) (read-punctuator ":" parstate)) ; typename :
             ((erp expr last-span parstate) ; typename : expr
              (parse-assignment-expression parstate)))
          (retok (make-genassoc-type :type tyname
                                     :expr expr)
                 (span-join span last-span)
                 parstate)))
       ((token-keywordp token "default") ; default
        (b* (((erp & parstate) (read-punctuator ":" parstate)) ; default :
             ((erp expr last-span parstate) ; default : expr
              (parse-assignment-expression parstate)))
          (retok (genassoc-default expr)
                 (span-join span last-span)
                 parstate)))
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or a keyword in {~
                               _Alignas, ~
                               _Atomic, ~
                               _Bool, ~
                               _Complex, ~
                               char, ~
                               const, ~
                               double, ~
                               enum, ~
                               float, ~
                               int, ~
                               long, ~
                               restrict, ~
                               short, ~
                               signed, ~
                               struct, ~
                               union, ~
                               unsigned, ~
                               void, ~
                               volatile~
                               }"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-compound-literal ((tyname tynamep)
                                  (first-span spanp)
                                  (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a compound literal."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after parsing the parenthesized type name.
       So we start by parsing an open curly brace,
       a list of initializers,
       and a closed curly brace."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ((erp & parstate) (read-punctuator "{" parstate)) ; {
         ((erp desiniters final-comma & parstate) ; { inits [,]
          (parse-initializer-list parstate))
         ((erp last-span parstate)
          (read-punctuator "}" parstate))) ; { inits [,] }
      (retok (make-expr-complit :type tyname
                                :elems desiniters
                                :final-comma final-comma)
             (span-join first-span last-span)
             parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-constant-expression ((parstate parstatep))
    :returns (mv erp
                 (cexpr const-exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a constant expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "In the grammar, a constant expression is a conditional expression.
       The grammar does not capture
       the fact that the expression must be constant,
       i.e. evaluatable at compile time.
       In our abstract syntax, a constant expression is defined,
       in line with the grammar,
       just as a wrapper of an expression;
       the wrapper marks the expression as intended to be in fact constant,
       but the check that that is the case is done elsewhere."))
    (b* (((reterr) (irr-const-expr) (irr-span) parstate)
         ((erp expr span parstate) (parse-conditional-expression parstate)))
      (retok (const-expr expr) span parstate))
    :measure (two-nats-measure (parsize parstate) 17))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-static-assert-declaration ((first-span spanp)
                                           (parstate parstatep))
    :returns (mv erp
                 (statassert statassertp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a static assert declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called when we expect a static assert declaration,
       after having read the @('_Static_assert') keyword.
       We pass the span of that keyword to this function,
       so that we can calculate a span for
       the whole static assert declaration.")
     (xdoc::p
      "We read the remaining components of the grammar rule,
       one after the other.
       There are no alternatives."))
    (b* (((reterr) (irr-statassert) (irr-span) parstate)
         ((erp & parstate) (read-punctuator "(" parstate))
         ((erp cexpr & parstate) (parse-constant-expression parstate))
         ((erp & parstate) (read-punctuator "," parstate))
         ((erp stringlit & parstate) (read-stringlit parstate))
         ((erp stringlits & parstate) (parse-*-stringlit parstate))
         ((erp & parstate) (read-punctuator ")" parstate))
         ((erp last-span parstate) (read-punctuator ";" parstate)))
      (retok (make-statassert :test cexpr :message (cons stringlit stringlits))
             (span-join first-span last-span)
             parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-designator ((parstate parstatep))
    :returns (mv erp
                 (designor designorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a designator."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are two kinds of designators,
       easily distinguished by their first token."))
    (b* (((reterr) (irr-designor) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ((token-punctuatorp token "[") ; [
        (b* (((erp cexpr & parstate) (parse-constant-expression parstate)) ; [ cexpr
             ((erp last-span parstate) (read-punctuator "]" parstate))) ; [ cexpr ]
          (retok (designor-sub cexpr) (span-join span last-span) parstate)))
       ((token-punctuatorp token ".") ; .
        (b* (((erp ident last-span parstate) (read-identifier parstate))) ; . ident
          (retok (designor-dot ident) (span-join span last-span) parstate)))
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an open square bracket ~
                               or a dot"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-designator-list ((parstate parstatep))
    :returns (mv erp
                 (designors designor-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a designator list."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is a non-empty sequence of designators, according to the grammar.
       We parse the first one, which must exist,
       and then we check if the next token could start another one,
       in which case we recursively call this function
       and then we combine its results with the first designator.")
     (xdoc::p
      "A designator list in the grammar only appears in a designation,
       where it is followed by an equal sign.
       So there is no overlap between the equal sign
       and the possible starts of a designator."))
    (b* (((reterr) nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp designor span parstate) (parse-designator parstate)) ; designor
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate))
         ((when (not (token-designator-start-p token))) ; designor other
          (b* ((parstate
                (if token (unread-token parstate) parstate))) ; designor
            (retok (list designor) span parstate)))
         ;; designor [
         ;; designor .
         (parstate (unread-token parstate)) ; designor
         ((erp designors more-span parstate) ; designor designors
          (parse-designator-list parstate)))
      (retok (cons designor designors)
             (span-join span more-span)
             parstate))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-initializer ((parstate parstatep))
    :returns (mv erp
                 (initer initerp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an initializer."
    :long
    (xdoc::topstring
     (xdoc::p
      "We read the next token.
       If the token may start an assignment expression,
       we parse an assignment expression:
       it must be a single initializer.
       If the token is an open curly brace,
       we must have an aggregate initializer.
       There is no overlap between these two cases."))
    (b* (((reterr) (irr-initer) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ((token-expression-start-p token) ; expr...
        (b* ((parstate (unread-token parstate)) ;
             ((erp expr span parstate) ; expr
              (parse-assignment-expression parstate)))
          (retok (initer-single expr) span parstate)))
       ((token-punctuatorp token "{") ; {
        (b* (((erp desiniters final-comma & parstate) ; { inits [,]
              (parse-initializer-list parstate))
             ((erp last-span parstate) ; { inits [,] }
              (read-punctuator "}" parstate)))
          (retok (make-initer-list :elems desiniters :final-comma final-comma)
                 (span-join span last-span)
                 parstate)))
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or a constant ~
                               or a string literal ~
                               or a keyword in {~
                               _Alignof, ~
                               _Generic, ~
                               sizeof~
                               } ~
                               or a punctuator in {~
                               \"++\", ~
                               \"--\", ~
                               \"+\", ~
                               \"-\", ~
                               \"~~\", ~
                               \"!\", ~
                               \"*\", ~
                               \"&\", ~
                               \"(\", ~
                               \"{\"~
                               }"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 16))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-designation?-initializer ((parstate parstatep))
    :returns (mv erp
                 (desiniter desiniterp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an initializer with an optional designation."
    :long
    (xdoc::topstring
     (xdoc::p
      "We read the next token.
       If it may start a designation, we try and parse a designation;
       then we try and parse an initializer.
       If the token may start an initializer,
       we parse an initializer.
       Note that there is no overlap between the starts of
       designations and initializers."))
    (b* (((reterr) (irr-desiniter) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ((token-designation-start-p token) ; designation...
        (b* ((parstate (unread-token parstate)) ;
             (psize (parsize parstate))
             ((erp designors span parstate) ; designators
              (parse-designator-list parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp & parstate) ; designators =
              (read-punctuator "=" parstate))
             ((erp initer last-span parstate) ; designators = initializer
              (parse-initializer parstate)))
          (retok (make-desiniter :design designors :init initer)
                 (span-join span last-span)
                 parstate)))
       ((token-initializer-start-p token) ; initializer...
        (b* ((parstate (unread-token parstate))
             ((erp initer span parstate) ; initializer
              (parse-initializer parstate)))
          (retok (make-desiniter :design nil :init initer)
                 span
                 parstate)))
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or a constant ~
                               or a string literal ~
                               or a keyword in {~
                               _Alignof, ~
                               _Generic, ~
                               sizeof~
                               } ~
                               or a punctuator in {~
                               \"++\", ~
                               \"--\", ~
                               \"+\", ~
                               \"-\", ~
                               \"~~\", ~
                               \"!\", ~
                               \"*\", ~
                               \"&\", ~
                               \"(\", ~
                               \"{\"~
                               }"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 17))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-initializer-list ((parstate parstatep))
    :returns (mv erp
                 (desiniters desiniter-listp)
                 (final-comma booleanp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a list of one or more initializers."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is a non-empty sequence of initializers, according to the grammar.
       We parse the first one, which must exist,
       and then we check if there is another one,
       in which case we recursively call this function
       and then we combine its results with the first initializer.
       Initializer lists in the grammar appear within curly braces,
       but a final comma is allowed.
       So, to check if there is one more element to parse,
       it is not enough to find a comma:
       we must check if there is a closed curly brace after the comma.")
     (xdoc::p
      "Note that each element of an initializer list
       is not just an initializer,
       but an initializer with an optional designation.")
     (xdoc::p
      "We also return a boolean result saying whether there is a final comma.
       We parse that comma (if present) in this function.
       So, technically, this function parses slightly more then
       an @('initializer-list') as defined in the ABNF grammar."))
    (b* (((reterr) nil nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp desiniter span parstate) ; initializer
          (parse-designation?-initializer parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ((token-punctuatorp token ",") ; initializer ,
        (b* (((erp token2 span2 parstate) (read-token parstate)))
          (cond
           ((token-punctuatorp token2 "}") ; initializer , }
            (b* ((parstate (unread-token parstate))) ; initializer ,
              (retok (list desiniter)
                     t ; final-comma
                     (span-join span span2)
                     parstate)))
           ((token-designation?-initializer-start-p
             token2) ; initializer , initializer...
            (b* ((parstate (unread-token parstate)) ; initializer ,
                 ((erp desiniters final-comma last-span parstate)
                  ;; initializer , initializers
                  (parse-initializer-list parstate)))
              (retok (cons desiniter desiniters)
                     final-comma
                     (span-join span last-span)
                     parstate)))
           (t ; initializer , other
            (reterr-msg :where (position-to-msg (span->start span2))
                        :expected "an identifier ~
                                   or a constant ~
                                   or a string literal ~
                                   or a keyword in {~
                                   _Alignof, ~
                                   _Generic, ~
                                   sizeof~
                                   } ~
                                   or a punctuator in {~
                                   \"++\", ~
                                   \"--\", ~
                                   \"+\", ~
                                   \"-\", ~
                                   \"~~\", ~
                                   \"!\", ~
                                   \"*\", ~
                                   \"&\", ~
                                   \"(\", ~
                                   \"{\"~
                                   }"
                        :found (token-to-msg token2))))))
       ((token-punctuatorp token "}") ; initializer }
        (b* ((parstate (unread-token parstate))) ; initializer
          (retok (list desiniter)
                 nil ; final-comma
                 span
                 parstate)))
       (t ; initializer other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or a constant ~
                               or a string literal ~
                               or a keyword in {~
                               _Alignof, ~
                               _Generic, ~
                               sizeof~
                               } ~
                               or a punctuator in {~
                               \"++\", ~
                               \"--\", ~
                               \"+\", ~
                               \"-\", ~
                               \"~~\", ~
                               \"!\", ~
                               \"*\", ~
                               \"&\", ~
                               \"(\", ~
                               \"{\", ~
                               \"}\", ~
                               \",\"~
                               }"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 18))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-enumerator ((parstate parstatep))
    :returns (mv erp
                 (enumer enumerp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an enumerator."
    (b* (((reterr) (irr-enumer) (irr-span) parstate)
         ;; An enumerator always starts with (or is) an identifier.
         ((erp ident span parstate) (read-identifier parstate)) ; ident
         ;; The identifier may be the whole enumerator, or there may be more,
         ;; so we read another token.
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is an equal sign, the enumerator continues,
       ;; and there must be a constant expression.
       ((token-punctuatorp token "=") ; ident =
        (b* (((erp cexpr last-span parstate) ; ident = cexpr
              (parse-constant-expression parstate)))
          (retok (make-enumer :name ident :value cexpr)
                 (span-join span last-span)
                 parstate)))
       ;; If token is not an equal sign, we put it back,
       ;; and the enumerator is just the identifier.
       (t ; ident other
        (b* ((parstate (if token (unread-token parstate) parstate))) ; ident
          (retok (make-enumer :name ident :value nil)
                 span
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-enumerator-list ((parstate parstatep))
    :returns (mv erp
                 (enumers enumer-listp)
                 (final-comma booleanp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a list of one or more enumerators."
    :long
    (xdoc::topstring
     (xdoc::p
      "This function is called after parsing the open curly brace.")
     (xdoc::p
      "This function also consumes the final comma, if any,
       and returns a boolean saying whether there was one or not.")
     (xdoc::p
      "This function does not consume the closed curly brace.
       The caller must consume it."))
    (b* (((reterr) nil nil (irr-span) parstate)
         ;; The list must not be empty, so we parse the first enumerator.
         (psize (parsize parstate))
         ((erp enumer enumer-span parstate)
          (parse-enumerator parstate)) ; enumer
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ;; To see if there are more enumerators,
         ;; we read another token.
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is a comma,
       ;; there could be another enumerator,
       ;; or it could be just a final comma,
       ;; so we need to read another token.
       ((token-punctuatorp token ",") ; enumer ,
        (b* (((erp token2 span2 parstate) (read-token parstate)))
          (cond
           ;; If token2 is an identifier,
           ;; the comma is not a final one,
           ;; and we must have another enumerator.
           ;; We put back the identifier,
           ;; recursively call this function,
           ;; and combine the result with the enumerator parsed above.
           ((and token2 (token-case token2 :ident)) ; enumer , ident
            (b* ((parstate (unread-token parstate)) ; enumer ,
                 ((erp enumers final-comma enumers-span parstate)
                  (parse-enumerator-list parstate))) ; enumer , enumers
              (retok (cons enumer enumers)
                     final-comma
                     (span-join enumer-span enumers-span)
                     parstate)))
           ;; If token2 is a closed curly brace,
           ;; the list ends, and the comma is a final one.
           ;; We put back the curly brace.
           ;; We return the singleton list of the enumerator parsed above.
           ((token-punctuatorp token2 "}") ; enumer , }
            (b* ((parstate (unread-token parstate))) ; enumer ,
              (retok (list enumer)
                     t ; final-comma
                     (span-join enumer-span span)
                     parstate)))
           ;; If token2 is anything else, it is an error.
           ;; The comma after an enumerator must be always followed by
           ;; an identiifer or a closed curly brace.
           (t ; enumer , other
            (reterr-msg :where (position-to-msg (span->start span2))
                        :expected "an identifier ~
                                   or a closed curly brace"
                        :found (token-to-msg token2))))))
       ;; If token is a closed curly brace,
       ;; the list ends, and there is no final comma.
       ;; We put back the curly brace.
       ;; We return the singleton list of the enumerator parsed above.
       ((token-punctuatorp token "}") ; enumer }
        (b* ((parstate (unread-token parstate))) ; enumer
          (retok (list enumer)
                 nil ; final-comma
                 enumer-span
                 parstate)))
       ;; If token is neither a comma nor a closed curly brace,
       ;; it is an error, because an enumerator must be always followed by
       ;; a comma or closed curly brace.
       (t ; enumer other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a comma ~
                               or a closed curly brace"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-specifier/qualifier ((tyspec-seenp booleanp)
                                     (parstate parstatep))
    :returns (mv erp
                 (specqual spec/qual-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a specifier or qualifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is one of the elements of
       @('specifier-qualifier-list') in the ABNF grammar;
       the grammar does not have a rule name for that.
       But this is like an alternation of
       a type specifier, a type qualifier, or an alignment specifier.")
     (xdoc::p
      "This function is called when we expect a specifier or qualifier,
       which is the case at the start of a specifier and qualifier list
       (because the list cannot be empty),
       and when the caller @(tsee parse-specifier-qualifier-list)
       determines that there must be another specifier or qualifier.")
     (xdoc::p
      "There is an overlap in the tokens that may start the three cases of
       type specifiers, type qualifiers, and alignment specifiers:
       the @('_Atomic') keyword could start a type specifier,
       in which case it must be followed by a parenthesized type name,
       or it could be a type qualifier (as is).
       So we cannot simply look at the next token
       and call separate functions to parse
       a type specifier or a type qualifier or an alignment specifier.
       We need to read more tokens if we see @('_Atomic'),
       but if we find a parenthesized identifier after that,
       it could be a type name, forming an atomic type specifier,
       but it could instead be a declarator following an atomic type qualifier
       (if the boolean flag passed to this function is @('t')).
       However, we can exploit the fact discussed in
       @(tsee parse-declaration-specifiers),
       using the flag also discussed there.
       If the flag is @('t'), the @('_Atomic') must be a type qualifier;
       if the flag is @('nil'),
       and an open parenthesis follows the @('_Atomic'),
       since no specifier or qualifier may start with an open parenthesis,
       the @('_Atomic') must start a type specifier,
       so we must parse a type name after the open parenthesis,
       and finally the closing parenthesis."))
    (b* (((reterr) (irr-spec/qual) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is a type specifier consisting of a single keyword,
       ;; return that type specifier.
       ((token-type-specifier-keyword-p token) ; void/char/.../_Complex
        (retok (spec/qual-tyspec (token-to-type-specifier-keyword token))
               span
               parstate))
       ;; If token is the keyword _Atomic,
       ;; it may be either a type specifier or a type qualifier,
       ;; so we examine more tokens.
       ((token-keywordp token "_Atomic") ; _Atomic
        (b* (((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is an open parenthesis,
           ;; we check the TYSPEC-SEENP flag,
           ;; as explained in the documentation.
           ((token-punctuatorp token2 "(") ; _Atomic (
            (if tyspec-seenp
                ;; If we have already seen a type specifier,
                ;; this must be a type qualifier.
                (b* ((parstate (unread-token parstate))) ; _Atomic
                  (retok (spec/qual-tyqual (type-qual-atomic))
                         span
                         parstate))
              ;; If we have not already seen a type specifier,
              ;; this must be a type specifier,
              ;; because the open parenthesis cannot be
              ;; another specifier or qualifier.
              (b* (((erp tyname & parstate) ; _Atomic ( typename
                    (parse-type-name parstate))
                   ((erp last-span parstate) ; _Atomic ( typename )
                    (read-punctuator ")" parstate)))
                (retok (spec/qual-tyspec (type-spec-atomic tyname))
                       (span-join span last-span)
                       parstate))))
           ;; If token2 is not an open parenthesis,
           ;; we must have an atomic type qualifier.
           (t ; _Atomic other
            (b* ((parstate ; _Atomic
                  (if token2 (unread-token parstate) parstate)))
              (retok (spec/qual-tyqual (type-qual-atomic))
                     span
                     parstate))))))
       ;; If token is the keyword struct,
       ;; we must have a structure type specifier.
       ((token-keywordp token "struct") ; struct
        (b* (((erp strunispec last-span parstate) ; struct strunispec
              (parse-struct-or-union-specifier parstate)))
          (retok (spec/qual-tyspec (type-spec-struct strunispec))
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword union
       ;; we must have a union type specifier.
       ((token-keywordp token "union") ; union
        (b* (((erp strunispec last-span parstate) ; union strunispec
              (parse-struct-or-union-specifier parstate)))
          (retok (spec/qual-tyspec (type-spec-union strunispec))
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword enum,
       ;; we must have an enumeration type specifier.
       ((token-keywordp token "enum") ; enum
        (b* (((erp enumspec last-span parstate) ; enum enumspec
              (parse-enum-specifier span parstate)))
          (retok (spec/qual-tyspec (type-spec-enum enumspec))
                 (span-join span last-span)
                 parstate)))
       ;; If token is an identifier,
       ;; it is a type specifier, precisely a @('typedef') name.
       ;; It is the responsibility of the caller of this function
       ;; to ensure that this is not (the start of) a declarator:
       ;; when this function is called, it must be the case that
       ;; a specifier or qualifier is expected.
       ((and token (token-case token :ident)) ; ident
        (retok (spec/qual-tyspec
                (type-spec-typedef (token-ident->unwrap token)))
               span
               parstate))
       ;; If token is 'typeof' or '__typeof' or '__typeof__',
       ;; we parse an open parenthesis,
       ;; then a possibly ambiguous expression or type name,
       ;; and finally a closed parenthesis.
       ((or (token-keywordp token "typeof") ; typeof
            (token-keywordp token "__typeof") ; __typeof
            (token-keywordp token "__typeof__")) ; __typeof__
        (b* ((uscores (cond ((token-keywordp token "typeof")
                             (keyword-uscores-none))
                            ((token-keywordp token "__typeof")
                             (keyword-uscores-start))
                            ((token-keywordp token "__typeof__")
                             (keyword-uscores-both))))
             ((erp & parstate) ; typeof (
              (read-punctuator "(" parstate))
             ((erp expr/tyname & parstate) ; typeof ( expr/tyname
              (parse-expression-or-type-name parstate))
             ((erp last-span parstate) ; typeof ( expr/tyname )
              (read-punctuator ")" parstate))
             (tyspec
              (amb?-expr/tyname-case
               expr/tyname
               :expr (make-type-spec-typeof-expr :expr expr/tyname.unwrap
                                                 :uscores uscores)
               :tyname (make-type-spec-typeof-type :type expr/tyname.unwrap
                                                   :uscores uscores)
               :ambig (make-type-spec-typeof-ambig :expr/type expr/tyname.unwrap
                                                   :uscores uscores))))
          (retok (spec/qual-tyspec tyspec)
                 (span-join span last-span)
                 parstate)))
       ;; If token is a type qualifier, which is always a single keyword,
       ;; we have that type qualifier.
       ((token-type-qualifier-p token) ; tyqual
        (retok (spec/qual-tyqual (token-to-type-qualifier token))
               span
               parstate))
       ;; If token is the keyword _Alignas,
       ;; we must have an alignment specifier.
       ((token-keywordp token "_Alignas") ; _Alignas
        (b* (((erp alignspec last-span parstate) ; _Alignas ( ... )
              (parse-alignment-specifier span parstate)))
          (retok (spec/qual-align alignspec)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword '__attribute' or '__attribute__',
       ;; which can only happen if GCC extensions are enabled,
       ;; we must have an attribute specifier.
       ((or (token-keywordp token "__attribute") ; __attribute
            (token-keywordp token "__attribute__")) ; __attribute__
        (b* ((uscores (token-keywordp token "__attribute__"))
             ((erp attrspec last-span parstate) ; attrspec
              (parse-attribute-specifier uscores span parstate)))
          (retok (spec/qual-attrib attrspec)
                 (span-join span last-span)
                 parstate)))
       ;; If token is anything else, it is an error.
       ;; The above cases are all the allowed possibilities for token.
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or a keyword in {~
                               _Alignas, ~
                               _Atomic, ~
                               _Bool, ~
                               _Complex, ~
                               char, ~
                               const, ~
                               double, ~
                               enum, ~
                               float, ~
                               int, ~
                               long, ~
                               restrict, ~
                               short, ~
                               signed, ~
                               struct, ~
                               union, ~
                               unsigned, ~
                               void, ~
                               volatile~
                               }"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-specifier-qualifier-list ((tyspec-seenp booleanp)
                                          (parstate parstatep))
    :returns (mv erp
                 (specquals spec/qual-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a list of one or more specifiers and qualifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('tyspec-seenp') flag has the same purpose
       as in @(tsee parse-declaration-specifiers):
       see that function's documentation.
       Lists of specifiers and qualifiers have the same restrictions
       as lists of declaration specifiers with respect to
       type specifiers, which we use to resolve identifier ambiguities."))
    (b* (((reterr) nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp specqual first-span parstate) ; specqual
          (parse-specifier/qualifier tyspec-seenp parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (tyspec-seenp (or tyspec-seenp
                           (spec/qual-case specqual :tyspec)))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is an identifier,
       ;; syntactically it may be a type specifier (a typedef name),
       ;; or it could be (the start of) a declarator,
       ;; but we use the TYSPEC-SEENP flag to resolve the ambiguity.
       ((and token (token-case token :ident)) ; specqual ident
        (if tyspec-seenp
            ;; If we have already parsed a type specifier,
            ;; the identifier must be (the start of) a declarator,
            ;; so we put it back and return the singleton list of
            ;; the specifier or qualifier that we have parsed above.
            (b* ((parstate (unread-token parstate))) ; declspec
              (retok (list specqual) first-span parstate))
          ;; If we have not already parsed a type specifier,
          ;; the identifier must be a type specifier,
          ;; so we put it back and we recursively call this function,
          ;; combining its results with
          ;; the specifier or qualifier that we have parsed above.
          (b* ((parstate (unread-token parstate)) ; specqual
               ((erp specquals last-span parstate) ; specqual specquals
                (parse-specifier-qualifier-list tyspec-seenp parstate)))
            (retok (cons specqual specquals)
                   (span-join first-span last-span)
                   parstate))))
       ;; If token may start a specifier or qualifier,
       ;; since it is not an identifier (which we have considered above),
       ;; there must be another type specifier or qualifier.
       ;; We recursively call this function, combining the result
       ;; with the previous parsed specifier or qualifier.
       ((token-specifier/qualifier-start-p token)
        ;; specqual specqual...
        (b* ((parstate (unread-token parstate)) ; specqual
             ((erp specquals last-span parstate) ; specqual specquals
              (parse-specifier-qualifier-list tyspec-seenp parstate)))
          (retok (cons specqual specquals)
                 (span-join first-span last-span)
                 parstate)))
       ;; If token is something else,
       ;; there cannot be another specifier and qualifier,
       ;; so we return the singleton list with
       ;; the previous parsed specifier or qualifier.
       (t ; specqual other
        (b* ((parstate (if token (unread-token parstate) parstate))) ; specqual
          (retok (list specqual) first-span parstate)))))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-declaration-specifier ((tyspec-seenp booleanp)
                                       (parstate parstatep))
    :returns (mv erp
                 (declspec declspecp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a declaration specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is an element of a declaration specifier list,
       which is @('declaration-specifiers') in the ABNF grammar,
       but there is no explicit @('declaration-specifier') rule name.
       Nonetheless, since we need to parse a list of these,
       it is clearly useful to have a parsing function for each.
       If this had its own grammar rule,
       it would be defined as an alternation of
       a storage class specifier,
       a type specifier,
       a type qualifier,
       a function specifier,
       an alignment specifier,
       or an attribute specifier (the last one is a GCC extension).")
     (xdoc::p
      "A declaration specifier (list) may always be followed by a declarator.
       It may also be followed by an abstract declarator
       when forming a parameter declaration,
       but in that case the abstract declarator is optional,
       so the declaration specifier may be followed by
       a comma or a closed parenthesis.")
     (xdoc::p
      "This function is called when we expect a declaration specifier,
       which is the case at the start of a declaration specifier list
       (because the list cannot be empty),
       and when the caller @(tsee parse-declaration-specifiers)
       determines that there must be another specifier or qualifier.")
     (xdoc::p
      "This is similar to @(tsee parse-specifier/qualifier),
       but more complex because there are more alternatives.
       The syntactic overlap between
       the @('_Atomic') type qualifier and the @('_Atomic') type specifier
       is resolved in the same way as in @(tsee parse-specifier/qualifier),
       which motivates the @('tyspec-seenp') flag passed to this function;
       see that function's documentation."))
    (b* (((reterr) (irr-declspec) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is a storage class specifier,
       ;; which always consists of a single keyword,
       ;; return that storage class specifier.
       ((token-storage-class-specifier-p token) ; typedef/.../register
        (retok (declspec-stocla (token-to-storage-class-specifier token))
               span
               parstate))
       ;; If token is a type specifier consisting of a single keyword,
       ;; return that type specifier.
       ((token-type-specifier-keyword-p token) ; void/.../_Complex
        (retok (declspec-tyspec (token-to-type-specifier-keyword token))
               span
               parstate))
       ;; If token is the keyword _Atomic,
       ;; it may be either a type specifier or a type qualifier,
       ;; so we examine more tokens.
       ((token-keywordp token "_Atomic") ; _Atomic
        (b* (((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is an open parenthesis,
           ;; we check the TYSPEC-SEENP flag,
           ;; as explained in the documentation.
           ((token-punctuatorp token2 "(") ; _Atomic (
            (if tyspec-seenp
                ;; If we have already seen a type specifier,
                ;; this must be a type qualifier.
                (b* ((parstate (unread-token parstate))) ; _Atomic
                  (retok (declspec-tyqual (type-qual-atomic))
                         span
                         parstate))
              ;; If we have not already seen a type specifier,
              ;; this must be a type specifier,
              ;; because the open parenthesis cannot be
              ;; another declaration specifier.
              (b* (((erp tyname & parstate) ; _Atomic ( typename
                    (parse-type-name parstate))
                   ((erp last-span parstate) ; _Atomic ( typename )
                    (read-punctuator ")" parstate)))
                (retok (declspec-tyspec (type-spec-atomic tyname))
                       (span-join span last-span)
                       parstate))))
           ;; If token2 is not an open parenthesis,
           ;; we must have an atomic type qualifier.
           (t ; _Atomic other
            (b* ((parstate ; _Atomic
                  (if token2 (unread-token parstate) parstate)))
              (retok (declspec-tyqual (type-qual-atomic))
                     span
                     parstate))))))
       ;; If token is the keyword struct,
       ;; we must have a structure type specifier.
       ((token-keywordp token "struct") ; struct
        (b* (((erp strunispec last-span parstate) ; struct strunispec
              (parse-struct-or-union-specifier parstate)))
          (retok (declspec-tyspec (type-spec-struct strunispec))
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword union
       ;; we must have a union type specifier.
       ((token-keywordp token "union") ; union
        (b* (((erp strunispec last-span parstate) ; union strunispec
              (parse-struct-or-union-specifier parstate)))
          (retok (declspec-tyspec (type-spec-union strunispec))
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword enum,
       ;; we must have an enumeration type specifier.
       ((token-keywordp token "enum") ; enum
        (b* (((erp enumspec last-span parstate) ; enum enumspec
              (parse-enum-specifier span parstate)))
          (retok (declspec-tyspec (type-spec-enum enumspec))
                 (span-join span last-span)
                 parstate)))
       ;; If token is an identifier,
       ;; it is a type specifier, precisely a @('typedef') name.
       ;; It is the responsibility of the caller of this function
       ;; to ensure that this is not (the start of) a declarator:
       ;; when this function is called, it must be the case that
       ;; a specifier or qualifier is expected.
       ((and token (token-case token :ident)) ; ident
        (retok (declspec-tyspec (type-spec-typedef (token-ident->unwrap token)))
               span
               parstate))
       ;; If token is 'typeof' or '__typeof' or '__typeof__',
       ;; we parse an open parenthesis,
       ;; then a possibly ambiguous expression or type name,
       ;; and finally a closed parenthesis.
       ((or (token-keywordp token "typeof") ; typeof
            (token-keywordp token "__typeof") ; __typeof
            (token-keywordp token "__typeof__")) ; __typeof__
        (b* ((uscores (cond ((token-keywordp token "typeof")
                             (keyword-uscores-none))
                            ((token-keywordp token "__typeof")
                             (keyword-uscores-start))
                            ((token-keywordp token "__typeof__")
                             (keyword-uscores-both))))
             ((erp & parstate) ; typeof (
              (read-punctuator "(" parstate))
             ((erp expr/tyname & parstate) ; typeof ( expr/tyname
              (parse-expression-or-type-name parstate))
             ((erp last-span parstate) ; typeof ( expr/tyname )
              (read-punctuator ")" parstate))
             (tyspec
              (amb?-expr/tyname-case
               expr/tyname
               :expr (make-type-spec-typeof-expr :expr expr/tyname.unwrap
                                                 :uscores uscores)
               :tyname (make-type-spec-typeof-type :type expr/tyname.unwrap
                                                   :uscores uscores)
               :ambig (make-type-spec-typeof-ambig :expr/type expr/tyname.unwrap
                                                   :uscores uscores))))
          (retok (declspec-tyspec tyspec)
                 (span-join span last-span)
                 parstate)))
       ;; If token is a type qualifier, which is always a single keyword,
       ;; we have that type qualifier.
       ((token-type-qualifier-p token) ; tyqual
        (retok (declspec-tyqual (token-to-type-qualifier token))
               span
               parstate))
       ;; If token is a function specifier, which is always a single keyword,
       ;; we have that function specifier.
       ((token-function-specifier-p token) ; inline/_Noreturn
        (retok (declspec-funspec (token-to-function-specifier token))
               span
               parstate))
       ;; If token is the keyword _Alignas,
       ;; we must have an alignment specifier.
       ((token-keywordp token "_Alignas") ; _Alignas
        (b* (((erp alignspec last-span parstate) ; _Alignas ( ... )
              (parse-alignment-specifier span parstate)))
          (retok (declspec-align alignspec)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword '__attribute' or '__attribute__',
       ;; which can only happen if GCC extensions are enabled,
       ;; we must have an attribute specifier.
       ((or (token-keywordp token "__attribute") ; __attribute
            (token-keywordp token "__attribute__")) ; __attribute__
        (b* ((uscores (token-keywordp token "__attribute__"))
             ((erp attrspec last-span parstate) ; attrspec
              (parse-attribute-specifier uscores span parstate)))
          (retok (declspec-attrib attrspec)
                 (span-join span last-span)
                 parstate)))
       ;; If token is anything else, it is an error.
       ;; The above cases are all the allowed possibilities for token.
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or a keyword in {~
                               _Alignas, ~
                               _Atomic, ~
                               _Bool, ~
                               _Complex, ~
                               _Noreturn, ~
                               _Thread_local, ~
                               auto, ~
                               char, ~
                               const, ~
                               double, ~
                               enum, ~
                               extern, ~
                               float, ~
                               inline, ~
                               int, ~
                               long, ~
                               register, ~
                               restrict, ~
                               short, ~
                               signed, ~
                               static, ~
                               struct, ~
                               typedef, ~
                               union, ~
                               unsigned, ~
                               void, ~
                               volatile~
                               }"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-declaration-specifiers ((tyspec-seenp booleanp)
                                        (parstate parstatep))
    :returns (mv erp
                 (declspecs declspec-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a list of one or more declaration specifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "We parse a declaration specifier,
       which must exist because the list must not be empty.
       Then we need to decide whether we have reached the end of the list
       or there may be another declaration specifier.
       If the next token is an identifier,
       it could be a @('typedef') name
       or (the start of) a declarator.
       To resolve this ambiguity,
       we exploit the fact that
       a list of declaration specifiers must contain
       at least one type specifier [C:6.7.2/2]
       and only the multisets listed in [C:6.7.2/2].
       One of those multisets is a single identifier (a @('typedef') name).
       So we carry around a flag saying whether
       we have encountered at least one type specifier in the list or not.
       Initially the flag is @('nil'),
       and it gets set when @(tsee parse-declaration-specifier)
       returns amy type specifier.
       This flag participates in the decision of whether an identifier
       must be another declaration specifier (a type specifier)
       or (the start of) a declarator:
       if the flag is @('t'),
       it means that we have already encountered
       at least one type specifier,
       and therefore the identifier cannot be another one,
       and it must be (the start of) a declarator;
       if the flag is @('nil'),
       the identifier cannot be (the start of) a declarator,
       because we have not found a type specifier yet,
       and thus the identifier must be the missing type specifier."))
    (b* (((reterr) nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp declspec first-span parstate) ; declspec
          (parse-declaration-specifier tyspec-seenp parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (tyspec-seenp (or tyspec-seenp
                           (declspec-case declspec :tyspec)))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is an identifier,
       ;; syntactically it may be a type specifier (a typedef name),
       ;; or it could be (the start of) a declarator,
       ;; but we use the TYSPEC-SEENP flag to resolve the ambiguity,
       ;; as explained in the documentation above.
       ((and token (token-case token :ident)) ; declspec ident
        (if tyspec-seenp
            ;; If we have already parsed a type specifier,
            ;; the identifier must be (the start of) a declarator,
            ;; so we put it back and return the singleton list of
            ;; the declaration specifier that we have parsed above.
            (b* ((parstate (unread-token parstate))) ; declspec
              (retok (list declspec) first-span parstate))
          ;; If we have not already parsed a type specifier,
          ;; the identifier must be a type specifier,
          ;; so we put it back and we recursively call this function,
          ;; combining its results with
          ;; the declaration specifier that we have parsed above.
          (b* ((parstate (unread-token parstate)) ; declspec
               ((erp declspecs last-span parstate) ; declspec declspecs
                (parse-declaration-specifiers tyspec-seenp parstate)))
            (retok (cons declspec declspecs)
                   (span-join first-span last-span)
                   parstate))))
       ;; If token may start a declaration specifier,
       ;; since it is not an identifier (which we have considered above),
       ;; there must be another declaration specifier.
       ;; We recursively call this function, combining the result
       ;; with the previous parsed specifier or qualifier.
       ((token-declaration-specifier-start-p token) ; declspec declspec...
        (b* ((parstate (unread-token parstate)) ; declspec
             ((erp declspecs last-span parstate) ; declspec declspecs
              (parse-declaration-specifiers tyspec-seenp parstate)))
          (retok (cons declspec declspecs)
                 (span-join first-span last-span)
                 parstate)))
       ;; If token is something else,
       ;; there cannot be another declaration specifier,
       ;; so we return the singleton list with
       ;; the previous parsed declaratio specifier.
       (t ; declspec other
        (b* ((parstate (if token (unread-token parstate) parstate))) ; declspec
          (retok (list declspec) first-span parstate)))))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-struct-or-union-specifier ((parstate parstatep))
    :returns (mv erp
                 (strunispec strunispecp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse or structure or union specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after parsing
       the initial @('struct') or @('union') keyword.
       The returned @(tsee strunispec) value captures
       the structure or union specifier without the indication of
       whether it is a structure or a union,
       which is done in @(tsee type-spec) instead;
       this is how we have factored our abstract syntax."))
    (b* (((reterr) (irr-strunispec) (irr-span) parstate)
         ;; There must be at least one token (identifier of open curly brace),
         ;; so we read one.
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is an identifier,
       ;; it may be the whole structure or union specifier,
       ;; or there may be more, so we read another token.
       ((and token (token-case token :ident)) ; ident
        (b* ((ident (token-ident->unwrap token))
             ((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is an open curly brace,
           ;; we must have a list of structure declarations
           ;; enclosed in curly braces.
           ;; So we parse those.
           ((token-punctuatorp token2 "{") ; ident {
            (b* (((erp structdecls & parstate) ; ident { structdecls
                  (parse-struct-declaration-list parstate))
                 ((erp last-span parstate) ; ident { structdecls }
                  (read-punctuator "}" parstate)))
              (retok (make-strunispec :name ident
                                      :members structdecls)
                     (span-join span last-span)
                     parstate)))
           ;; If token2 is not an open curly brace,
           ;; the identifier was the whole structure or union specifier,
           ;; so we put back token2 and return the specifier.
           (t ; ident other
            (b* ((parstate
                  (if token2 (unread-token parstate) parstate))) ; ident
              (retok (make-strunispec :name ident
                                      :members nil)
                     span
                     parstate))))))
       ;; If token is an open curly brace,
       ;; we must have a structure or union specifier without identifier
       ;; but with a list of structure declarations between curly braces.
       ;; So we parse those.
       ((token-punctuatorp token "{") ; {
        (b* (((erp structdecls & parstate) ; { structdecls
              (parse-struct-declaration-list parstate))
             ((erp last-span parstate) ; { structdecls }
              (read-punctuator "}" parstate)))
          (retok (make-strunispec :name nil
                                  :members structdecls)
                 (span-join span last-span)
                 parstate)))
       ;; If token is neither an identifier nor an open curly brace,
       ;; we cannot have a structure or union specifier here.
       (t
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or an open curly brace"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-enum-specifier ((first-span spanp) (parstate parstatep))
    :returns (mv erp
                 (enumspec enumspecp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an enumeration specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after parsing the initial @('enum') keyword.")
     (xdoc::p
      "The span of the @('enum') keyword is passed as input here."))
    (b* (((reterr) (irr-enumspec) (irr-span) parstate)
         ;; There must be at least one token (identifier of open curly brace),
         ;; so we read one.
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is an identifier,
       ;; it may be the whole specifier, or there may be more,
       ;; so we read another token.
       ((and token (token-case token :ident)) ; ident
        (b* ((ident (token-ident->unwrap token))
             ((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is an open curly brace,
           ;; there must be a list of enumerators, which we parse.
           ;; Then we read the closed curly brace.
           ((token-punctuatorp token2 "{") ; ident {
            (b* (((erp enumers final-comma & parstate)
                  (parse-enumerator-list parstate)) ; ident { enumers [,]
                 ((erp last-span parstate) ; ident { enumers [,] }
                  (read-punctuator "}" parstate)))
              (retok (make-enumspec :name ident
                                    :list enumers
                                    :final-comma final-comma)
                     (span-join first-span last-span)
                     parstate)))
           ;; If token2 is not an open curly brace,
           ;; the identifier must be the whole enumeration specifier.
           (t ; ident other
            (b* ((parstate
                  (if token2 (unread-token parstate) parstate))) ; ident
              (retok (make-enumspec :name ident
                                    :list nil
                                    :final-comma nil)
                     (span-join first-span span)
                     parstate))))))
       ;; If token is an open curly brace,
       ;; we must have an enumeration specifier without identifier.
       ;; We parse the list of enumerators, and the closed curly brace.
       ((token-punctuatorp token "{") ; {
        (b* (((erp enumers final-comma & parstate)
              (parse-enumerator-list parstate)) ; { enumers [,]
             ((erp last-span parstate) ; { enumers [,] }
              (read-punctuator "}" parstate)))
          (retok (make-enumspec :name nil
                                :list enumers
                                :final-comma final-comma)
                 (span-join first-span last-span)
                 parstate)))
       ;; If token is neither an identifier nor an open curly brace,
       ;; it is an error, because the 'enum' keyword must be alwways followed by
       ;; an identifier or an open curly brace.
       (t
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or a closed curly brace"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-alignment-specifier ((first-span spanp) (parstate parstatep))
    :returns (mv erp
                 (alignspec align-specp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an alignment specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after parsing the initial @('_Alignas') keyword.")
     (xdoc::p
      "The span of the @('_Alignas') keyword is passed as input here."))
    (b* (((reterr) (irr-align-spec) (irr-span) parstate)
         ;; There must be an open parenthesis.
         ((erp & parstate) (read-punctuator "(" parstate)) ; (
         ;; Next comes a possibly ambiguous expression or type name.
         ((erp expr/tyname & parstate) ; ( expr/tyname
          (parse-expression-or-type-name parstate))
         ;; There must be a closed parenthesis.
         ((erp last-span parstate) ; ( expr/tyname )
          (read-punctuator ")" parstate)))
      (amb?-expr/tyname-case
       expr/tyname
       ;; If we parsed an expression,
       ;; we return an @('_Alignas') with an expression.
       :expr (retok (align-spec-alignas-expr (const-expr expr/tyname.unwrap))
                    (span-join first-span last-span)
                    parstate)
       ;; If we parsed a type name,
       ;; we return an @('_Alignas') with a type name.
       :tyname (retok (align-spec-alignas-type expr/tyname.unwrap)
                      (span-join first-span last-span)
                      parstate)
       ;; If we parsed an ambiguous expression or type name,
       ;; we return an ambiguous @('_Alignas').
       :ambig (retok (align-spec-alignas-ambig expr/tyname.unwrap)
                     (span-join first-span last-span)
                     parstate)))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-array/function-abstract-declarator ((parstate parstatep))
    :returns (mv erp
                 (dirabsdeclor dirabsdeclorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an array or function abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "These are the kinds of direct abstract declarators
       that can be chained, one after the other.
       See @(tsee parse-direct-abstract-declarator).")
     (xdoc::p
      "This function is called when we expect this kind of declarator."))
    (b* (((reterr) (irr-dirabsdeclor) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is an open square bracket,
       ;; we must have an array abstract declarator.
       ((token-punctuatorp token "[") ; [
        (b* (((erp token2 span2 parstate) (read-token parstate)))
          (cond
           ;; If token2 is a closed square bracket, we have a declarator [].
           ((token-punctuatorp token2 "]") ; [ ]
            (retok (make-dirabsdeclor-array :decl? nil
                                            :tyquals nil
                                            :expr? nil)
                   (span-join span span2)
                   parstate))
           ;; If token2 is a star, it may start an expression,
           ;; or we may have a variable length array declarator.
           ;; So we read another token
           ((token-punctuatorp token2 "*") ; [ *
            (b* (((erp token3 span3 parstate) (read-token parstate)))
              (cond
               ;; If token3 is a closed square bracket,
               ;; we have a variable length array declarator.
               ((token-punctuatorp token3 "]") ; [ * ]
                (retok (make-dirabsdeclor-array-star :decl? nil)
                       (span-join span span3)
                       parstate))
               ;; If token3 is not a closed square bracket,
               ;; the star must start an (assignment) expression.
               (t ; [ * other
                (b* ((parstate
                      (if token3 (unread-token parstate) parstate)) ; [ *
                     (parstate (unread-token parstate)) ; [
                     ((erp expr & parstate) ; [ expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirabsdeclor-array :decl? nil
                                                  :tyquals nil
                                                  :expr? expr)
                         (span-join span last-span)
                         parstate))))))
           ;; If token2 is the keyword 'static',
           ;; the keyword may be followed by a list of type qualifiers,
           ;; and then must be followed by an assignment expression.
           ((token-keywordp token2 "static") ; [ static
            (b* (((erp token3 & parstate) (read-token parstate)))
              (cond
               ;; If token3 is a type qualifier,
               ;; we must have a list of type qualifiers,
               ;; which we parse,
               ;; and then we parse the assignment expression.
               ((token-type-qualifier-p token3) ; [ static tyqual
                (b* ((parstate (unread-token parstate)) ; [ static
                     ((erp tyquals & parstate) ; [ static tyquals
                      (parse-type-qualifier-list parstate))
                     ((erp expr & parstate) ; [ static tyquals expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ static tyquals expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirabsdeclor-array-static1
                          :decl? nil
                          :tyquals tyquals
                          :expr expr)
                         (span-join span last-span)
                         parstate)))
               ;; If token3 is not a type qualifier,
               ;; we must have an assignment expression.
               (t ; [ static other
                (b* ((parstate
                      (if token3 (unread-token parstate) parstate)) ; [ static
                     ((erp expr & parstate) ; [ static expr
                      (parse-assignment-expression parstate)) ; [ static expr
                     ((erp last-span parstate) ; [ static expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirabsdeclor-array-static1
                          :decl? nil
                          :tyquals nil
                          :expr expr)
                         (span-join span last-span)
                         parstate))))))
           ;; If token2 is a type qualifier,
           ;; we must have a list of type qualifiers,
           ;; possibly followed by the keyword 'static',
           ;; and necessarily followed by an assignment expression.
           ((token-type-qualifier-p token2) ; [ tyqual
            (b* ((parstate (unread-token parstate)) ; [
                 ((erp tyquals & parstate) ; [ tyquals
                  (parse-type-qualifier-list parstate))
                 ((erp token3 span3 parstate) (read-token parstate)))
              (cond
               ;; If token3 is the keyword 'static',
               ;; we must have an assignment expression after that.
               ((token-keywordp token3 "static") ; [ tyquals static
                (b* (((erp expr & parstate) ; [ tyquals static expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ tyquals static expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirabsdeclor-array-static2
                          :decl? nil
                          :tyquals tyquals
                          :expr expr)
                         (span-join span last-span)
                         parstate)))
               ;; If token3 is a closed square bracket,
               ;; there is no expression, and we have determined the variant.
               ((token-punctuatorp token3 "]") ; [ tyquals ]
                (retok (make-dirabsdeclor-array
                        :decl? nil
                        :tyquals tyquals
                        :expr? nil)
                       (span-join span span3)
                       parstate))
               ;; If token3 is not the keyword 'static'
               ;; and is not a closed square bracket,
               ;; we must have an assignment expression here.
               (t ; [ tyquals other
                (b* ((parstate
                      (if token3 (unread-token parstate) parstate)) ; [ tyquals
                     ((erp expr & parstate) ; [ tyquals expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ tyquals expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirabsdeclor-array
                          :decl? nil
                          :tyquals tyquals
                          :expr? expr)
                         (span-join span last-span)
                         parstate))))))
           ;; If token2 is anything else,
           ;; we must have just an assignment expression.
           (t ; [ other
            (b* ((parstate (if token2 (unread-token parstate) parstate)) ; [
                 ((erp expr & parstate) ; [ expr
                  (parse-assignment-expression parstate))
                 ((erp last-span parstate) ; [ expr ]
                  (read-punctuator "]" parstate)))
              (retok (make-dirabsdeclor-array :decl? nil
                                              :tyquals nil
                                              :expr? expr)
                     (span-join span last-span)
                     parstate))))))
       ;; If token is an open parenthesis,
       ;; we must have a function abstract declarator.
       ((token-punctuatorp token "(") ; (
        (b* (((erp token2 span2 parstate) (read-token parstate)))
          (cond
           ;; If token2 is a closed parenthesis,
           ;; we have no parameters.
           ((token-punctuatorp token2 ")") ; ( )
            (retok (make-dirabsdeclor-function :decl? nil
                                               :params nil
                                               :ellipsis nil)
                   (span-join span span2)
                   parstate))
           ;; If token2 is not a closed parenthesis,
           ;; we must have a parameter type list,
           ;; which we parse.
           (t ; ( other
            (b* ((parstate (if token2 (unread-token parstate) parstate)) ; (
                 ((erp paramdecls ellipsis & parstate) ; ( params [, ...]
                  (parse-parameter-declaration-list parstate))
                 ((erp last-span parstate) ; ( params [, ...] )
                  (read-punctuator ")" parstate)))
              (retok (make-dirabsdeclor-function :decl? nil
                                                 :params paramdecls
                                                 :ellipsis ellipsis)
                     (span-join span last-span)
                     parstate))))))
       ;; If token is anything else,
       ;; we cannot have either an array or a function abstract declarator.
       ;; So it is an error, because we were expecting one.
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an open parenthesis ~
                               or an open square bracket"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-direct-abstract-declarator ((parstate parstatep))
    :returns (mv erp
                 (dirabsdeclor dirabsdeclorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a direct abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "A direct abstract declarator must start with:
       (i) a parenthesized abstract declarator; or
       (ii) an array abstract declarator
       that starts with an open square bracket
       and ends with a closed square bracket; or
       (iii) a function abstract declarator,
       which is a parenthesized parameter type list.
       After one of these three possibilities,
       there may be zero or more
       array or function abstract declarators.
       So we have either a sequence of
       one or more array and function abstract declarators,
       or a parenthesized abstract declarator
       followed by a sequence of
       zero or more array and function abstract declarators."))
    (b* (((reterr) (irr-dirabsdeclor) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is an open parenthesis,
       ;; we could have a parenthesized abstract declarator,
       ;; or a function abstract declarator.
       ((token-punctuatorp token "(") ; (
        (b* (((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 may start an abstract declarator,
           ;; we must have a parenthesized abstract declarator,
           ;; and not a function abstract declarator,
           ;; because abstract declarators and parameter type lists
           ;; have disjoint starting tokens,
           ;; and a closed parenthesis
           ;; (if the function declarator were @('()'))
           ;; cannot start an abstract declarator either.
           ;; We put back token2,
           ;; we parse an abstract declarator,
           ;; and we also read the closed parenthesis.
           ;; Then we call the function to read
           ;; zero or more array and function abstract declarators,
           ;; combining the abstract declarator we just read with them.
           ((token-abstract-declarator-start-p token2) ; ( absdeclor...
            (b* ((parstate (unread-token parstate)) ; (
                 (psize (parsize parstate))
                 ((erp absdeclor & parstate) ; ( absdeclor
                  (parse-abstract-declarator parstate))
                 ((unless (mbt (<= (parsize parstate) (1- psize))))
                  (reterr :impossible))
                 ((erp last-span parstate) ; ( absdeclor )
                  (read-punctuator ")" parstate)))
              (parse-direct-abstract-declarator-rest
               (dirabsdeclor-paren absdeclor)
               (span-join span last-span)
               parstate)))
           ;; If token2 may not start an abstract declarator,
           ;; we must have a function abstract declarator,
           ;; which we read with a separate function,
           ;; and then we call the function to read
           ;; zero or more subsequent array and function abstract declarators,
           ;; combining the one we just read into them.
           (t ; ( other
            (b* ((parstate (if token2 (unread-token parstate) parstate)) ; (
                 (parstate (unread-token parstate)) ;
                 (psize (parsize parstate))
                 ((erp dirabsdeclor span parstate) ; dirabsdeclor
                  (parse-array/function-abstract-declarator parstate))
                 ((unless (mbt (<= (parsize parstate) (1- psize))))
                  (reterr :impossible)))
              (parse-direct-abstract-declarator-rest dirabsdeclor
                                                     span
                                                     parstate))))))
       ;; If token is an open square,
       ;; we must have an array abstract declarator,
       ;; which we parse using a separate function,
       ;; and then we use another function to parse
       ;; zero or more subsequent array and function abstract declarators,
       ;; combining into them the one we just read.
       ((token-punctuatorp token "[") ; [
        (b* ((parstate (unread-token parstate)) ;
             (psize (parsize parstate))
             ((erp dirabsdeclor span parstate) ; dirabsdeclor
              (parse-array/function-abstract-declarator parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible)))
          (parse-direct-abstract-declarator-rest dirabsdeclor
                                                 span
                                                 parstate)))
       ;; If token is anything else,
       ;; we cannot have a direct abstract declarator.
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an open parenthesis ~
                               or an open square bracket"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-direct-abstract-declarator-rest
    ((prev-dirabsdeclor dirabsdeclorp)
     (prev-span spanp)
     (parstate parstatep))
    :returns (mv erp
                 (dirabsdeclor dirabsdeclorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a direct abstract declartor."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after parsing
       either the initial parenthesized abstract declarator
       or the first array or function abstract declarator.
       Whichever it is, it is passed to this function, along with its span,
       and in this function we read zero or more
       additional array and function abstract declarators,
       combining them with the one passed to this function."))
    (b* (((reterr) (irr-dirabsdeclor) (irr-span) parstate)
         ;; We read the next token, to determine whether
         ;; there is another array or function abstract declarator.
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is an open parenthesis or an open square bracket,
       ;; we must have a function or array abstract declarator.
       ;; We put back the token
       ;; and call the function to parse the next declarator.
       ;; We combine the previous one into the next:
       ;; note that PARSE-ARRAY/FUNCTION-ABSTRACT-DECLARATOR
       ;; always returns a direct abstract declarator
       ;; whose DECL? component is NIL (as we prove)
       ;; so when we store the previous declarator there,
       ;; we are not overwriting anything.
       ;; We also join the spans, and we recursively call this function.
       ((or (token-punctuatorp token "(") ; (
            (token-punctuatorp token "[")) ; [
        (b* ((parstate (unread-token parstate)) ;
             (psize (parsize parstate))
             ((erp next-dirabsdeclor next-span parstate) ; dirabsdeclor
              (parse-array/function-abstract-declarator parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((unless (mbt (dirabsdeclor-decl?-nil-p next-dirabsdeclor)))
              (reterr :impossible))
             (curr-dirabsdeclor
              (combine-dirabsdeclor-into-dirabsdeclor prev-dirabsdeclor
                                                      next-dirabsdeclor))
             (curr-span (span-join prev-span next-span)))
          (parse-direct-abstract-declarator-rest curr-dirabsdeclor
                                                 curr-span
                                                 parstate)))
       ;; If token is not an open parenthesis or an open square bracket,
       ;; we have reached the end of the sequence of zero or more
       ;; array and function abstract declarators.
       (t ; other
        (b* ((parstate (if token (unread-token parstate) parstate))) ;
          (retok (dirabsdeclor-fix prev-dirabsdeclor)
                 (span-fix prev-span)
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-abstract-declarator ((parstate parstatep))
    :returns (mv erp
                 (absdeclor absdeclorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "An abstract declarator may consist of
       a pointer,
       or a direct abstract declarator,
       or a pointer followed by a direct abstract declarator."))
    (b* (((reterr) (irr-absdeclor) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is a star, we must have a pointer,
       ;; so we parse it, after putting back the token.
       ;; Then we read another token,
       ;; to see if we have a direct abstract declarator after the pointer.
       ((token-punctuatorp token "*") ; *
        (b* ((parstate (unread-token parstate))
             (psize (parsize parstate))
             ((erp tyqualss tyqualss-span parstate) ; pointer
              (parse-pointer parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 may start a direct abstract declarator,
           ;; we put the token back
           ;; and we attempt to parse the direct abstract declarator.
           ((token-direct-abstract-declarator-start-p token2)
            ;; pointer dirabsdeclor...
            (b* ((parstate (unread-token parstate))
                 ((erp dirabsdeclor dirabsdeclor-span parstate)
                  ;; pointer dirabsdeclor
                  (parse-direct-abstract-declarator parstate)))
              (retok (make-absdeclor :pointers tyqualss
                                     :decl? dirabsdeclor)
                     (span-join tyqualss-span dirabsdeclor-span)
                     parstate)))
           ;; If token2 may not start a direct abstract declarator,
           ;; our abstract declarator just consists of the pointer part.
           (t ; pointer other
            (b* ((parstate
                  (if token2 (unread-token parstate) parstate))) ; pointer
              (retok (make-absdeclor :pointers tyqualss
                                     :decl? nil)
                     tyqualss-span
                     parstate))))))
       ;; If token may start a direct abstract declarator,
       ;; our abstract declarator is just that, without the pointer part.
       ((token-direct-abstract-declarator-start-p token) ; dirabsdeclor...
        (b* ((parstate (unread-token parstate)) ;
             ((erp dirabsdeclor span parstate) ; dirabsdeclor
              (parse-direct-abstract-declarator parstate)))
          (retok (make-absdeclor :pointers nil
                                 :decl? dirabsdeclor)
                 span
                 parstate)))
       ;; If token is anything else, it is an error,
       ;; because this function is called when we expect an abstract declarator.
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a star ~
                               or an open parenthesis ~
                               or an open square bracket"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-array/function-declarator ((prev-dirdeclor dirdeclorp)
                                           (prev-span spanp)
                                           (parstate parstatep))
    :returns (mv erp
                 (dirdeclor dirdeclorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an array or function declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "These are the kinds of direct declarators
       that can be chained, one after the other.
       See @(tsee parse-direct-declarator).")
     (xdoc::p
      "This function is called when we expect this kind of declarator.")
     (xdoc::p
      "The @('prev-dirdeclor') input to this function
       is the direct declarator parsed so far,
       which must be extended with the next array or function declarator.
       The @('prev-span') input is the span of that direct declarator.")
     (xdoc::p
      "Although there are two possible variants for function declarators,
       since an identifier is a type specifier and thus a parameter declaration,
       we cannot disambiguate the @(':function-params') and @(':function-names')
       variants during parsing;
       we always generate @(':function-params') during parsing,
       and potentially re-classify it to @(':function-names')
       during post-parsing semantic analysis."))
    (b* (((reterr) (irr-dirdeclor) (irr-span) parstate)
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is an open square bracket,
       ;; we have an array construct, which may be of different variants,
       ;; so we read more tokens.
       ((token-punctuatorp token "[") ; [
        (b* (((erp token2 span2 parstate) (read-token parstate)))
          (cond
           ;; If token2 is a type qualifier,
           ;; we put it back and read a list of type qualifiers,
           ;; but the array variant is still not determined,
           ;; so we read another token after that.
           ((token-type-qualifier-p token2) ; [ tyqual
            (b* ((parstate (unread-token parstate)) ; [
                 ((erp tyquals & parstate) ; [ tyquals
                  (parse-type-qualifier-list parstate))
                 ((erp token3 span3 parstate) (read-token parstate)))
              (cond
               ;; If token3 is a star, it may start an expression,
               ;; or it may be just a star for a variable length array.
               ;; So we need to read another token to disambiguate.
               ((token-punctuatorp token3 "*") ; [ tyquals *
                (b* (((erp token4 span4 parstate) (read-token parstate)))
                  (cond
                   ;; If token4 is a closed square bracket,
                   ;; we have a variable length array declarator.
                   ((token-punctuatorp token4 "]") ; [ tyquals * ]
                    (retok (make-dirdeclor-array-star :decl prev-dirdeclor
                                                      :tyquals tyquals)
                           (span-join prev-span span4)
                           parstate))
                   ;; If token4 is not a square bracket,
                   ;; the star must start an expression,
                   ;; so we put the tokens back
                   ;; and we proceed to parse an assignment expression.
                   ;; We have determined the array variant.
                   (t ; [ tyquals * other
                    (b* ((parstate ; [ tyquals *
                          (if token4 (unread-token parstate) parstate))
                         (parstate (unread-token parstate)) ; [ tyquals
                         ((erp expr & parstate) ; [ tyquals expr
                          (parse-assignment-expression parstate))
                         ((erp last-span parstate) ; [ tyquals expr ]
                          (read-punctuator "]" parstate)))
                      (retok (make-dirdeclor-array :decl prev-dirdeclor
                                                   :tyquals tyquals
                                                   :expr? expr)
                             (span-join prev-span last-span)
                             parstate))))))
               ;; If token3 may start an (assignment) expression,
               ;; we parse it, and we have determined the array variant.
               ;; We have already considered the case of a star above,
               ;; so this can only be an expression at this point.
               ((token-expression-start-p token3) ; [ tyquals expr...
                (b* ((parstate (unread-token parstate)) ; [ tyquals
                     ((erp expr & parstate) ; [ tyquals expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ tyquals expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirdeclor-array :decl prev-dirdeclor
                                               :tyquals tyquals
                                               :expr? expr)
                         (span-join prev-span last-span)
                         parstate)))
               ;; If token3 is a closed square bracket,
               ;; we have determined the variant, and we have no expression.
               ((token-punctuatorp token3 "]") ; [ tyquals ]
                (retok (make-dirdeclor-array :decl prev-dirdeclor
                                             :tyquals tyquals
                                             :expr? nil)
                       (span-join prev-span span3)
                       parstate))
               ;; If token3 is the 'static' keyword,
               ;; we have determined the variant,
               ;; and we must have an expression.
               ((token-keywordp token3 "static") ; [ tyquals static
                (b* (((erp expr & parstate) ; [ tyquals static expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ tyquals static expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirdeclor-array-static2 :decl prev-dirdeclor
                                                       :tyquals tyquals
                                                       :expr expr)
                         (span-join prev-span last-span)
                         parstate)))
               ;; If token3 is anything else, it is an error.
               (t ; [ tyquals other
                (reterr-msg :where (position-to-msg (span->start span3))
                            :expected "an expression ~
                                       or the 'static' keyword ~
                                       or a closed square bracket"
                            :found (token-to-msg token3))))))
           ;; If token2 is a star, it may start an expression,
           ;; or it may be just a star for a variable length array.
           ;; So we need to read another token to disambiguate.
           ((token-punctuatorp token2 "*") ; [ *
            (b* (((erp token3 span3 parstate) (read-token parstate)))
              (cond
               ;; If token3 is a closed square bracket,
               ;; we have a variable length array declarator.
               ((token-punctuatorp token3 "]") ; [ * ]
                (retok (make-dirdeclor-array-star :decl prev-dirdeclor
                                                  :tyquals nil)
                       (span-join prev-span span3)
                       parstate))
               ;; If token3 is not a star,
               ;; we must have an expression,
               ;; and we have determined the array declarator variant.
               (t ; [ * other
                (b* ((parstate
                      (if token3 (unread-token parstate) parstate)) ; [ *
                     (parstate (unread-token parstate)) ; [
                     ((erp expr & parstate) ; [ expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirdeclor-array :decl prev-dirdeclor
                                               :tyquals nil
                                               :expr? expr)
                         (span-join prev-span last-span)
                         parstate))))))
           ;; If token2 may start an assignment expression,
           ;; we have determined the variant.
           ;; Note that we have already considered the case of a star above.
           ((token-expression-start-p token2) ; [ expr...
            (b* ((parstate (unread-token parstate)) ; [
                 ((erp expr & parstate) ; [ expr
                  (parse-assignment-expression parstate))
                 ((erp last-span parstate) ; [ expr ]
                  (read-punctuator "]" parstate)))
              (retok (make-dirdeclor-array :decl prev-dirdeclor
                                           :tyquals nil
                                           :expr? expr)
                     (span-join prev-span last-span)
                     parstate)))
           ;; If token2 is the 'static' keyword,
           ;; we may have type qualifiers,
           ;; and we must have an expression;
           ;; we have determined the variant.
           ((token-keywordp token2 "static") ; [ static
            (b* (((erp token3 & parstate) (read-token parstate)))
              (cond
               ;; If token3 is a type qualifier,
               ;; we put it back and parse a list of type qualifiers,
               ;; and then we parse an expression.
               ((token-type-qualifier-p token3) ; [ static tyqual
                (b* ((parstate (unread-token parstate)) ; [ static
                     ((erp tyquals & parstate) ; [ static tyquals
                      (parse-type-qualifier-list parstate))
                     ((erp expr & parstate) ; [ static tyquals expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ static tyquals expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirdeclor-array-static1 :decl prev-dirdeclor
                                                       :tyquals tyquals
                                                       :expr expr)
                         (span-join prev-span last-span)
                         parstate)))
               ;; If token3 is not a type qualifier,
               ;; we must have an expression.
               (t ; [ static other
                (b* ((parstate (unread-token parstate)) ; [ static
                     ((erp expr & parstate) ; [ static expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ static expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirdeclor-array-static1 :decl prev-dirdeclor
                                                       :tyquals nil
                                                       :expr expr)
                         (span-join prev-span last-span)
                         parstate))))))
           ;; If token2 is a closed square bracket,
           ;; we have an empty array construct.
           ((token-punctuatorp token2 "]") ; [ ]
            (retok (make-dirdeclor-array :decl prev-dirdeclor
                                         :tyquals nil
                                         :expr? nil)
                   (span-join prev-span span2)
                   parstate))
           ;; If token2 is anything else, it is an error.
           (t ; [ other
            (reterr-msg :where (position-to-msg (span->start span2))
                        :expected "a type qualifier ~
                                   or an expression ~
                                   or the 'static' keyword ~
                                   or a closed square bracket"
                        :found (token-to-msg token2))))))
       ;; If token is an open parenthesis,
       ;; we have a function construct,
       ;; which may be of two variants,
       ;; but we only generate the :FUNCTION-PARAMS variant,
       ;; as explained above.
       ((token-punctuatorp token "(") ; (
        (b* (((erp token2 span2 parstate) (read-token parstate)))
          (cond
           ;; If token2 is a closed parenthesis,
           ;; we have no parameter declarations.
           ((token-punctuatorp token2 ")") ; ( )
            (retok (make-dirdeclor-function-params :decl prev-dirdeclor
                                                   :params nil
                                                   :ellipsis nil)
                   (span-join prev-span span2)
                   parstate))
           ;; If token2 is anything else,
           ;; we must have a list of one or more parameter declarations.
           (t ; ( other
            (b* ((parstate (if token2 (unread-token parstate) parstate))
                 ((erp paramdecls ellipsis & parstate) ; ( params [, ...]
                  (parse-parameter-declaration-list parstate))
                 ((erp last-span parstate) ; ( params [, ...] )
                  (read-punctuator ")" parstate)))
              (retok (make-dirdeclor-function-params :decl prev-dirdeclor
                                                     :params paramdecls
                                                     :ellipsis ellipsis)
                     (span-join prev-span last-span)
                     parstate))))))
       ;; If token is not an open parenthesis or an open square bracket,
       ;; it is an internal implementation error:
       ;; this function should be always called
       ;; when the next token is an open parenthesis or open square bracket.
       (t ;; other
        (prog2$
         (raise "Internal error: unexpected token ~x0." token)
         (reterr t)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-direct-declarator ((parstate parstatep))
    :returns (mv erp
                 (dirdeclor dirdeclorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a direct declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "A direct declarator always starts with
       either an identifier or a parenthesized declarator,
       and continues with zero or more array or function constructs
       that augment the declarator.
       First we parse the initial identifier or parenthesized declarator,
       then we call a separate function to parse
       the zero or more array or function constructs."))
    (b* (((reterr) (irr-dirdeclor) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is an identifier,
       ;; that must be the start of the direct declarator.
       ((and token (token-case token :ident)) ; ident
        (parse-direct-declarator-rest (dirdeclor-ident
                                       (token-ident->unwrap token))
                                      span
                                      parstate))
       ;; If token is an open parenthesis,
       ;; we must have a parenthesized declarator.
       ((token-punctuatorp token "(") ; (
        (b* ((psize (parsize parstate))
             ((erp declor & parstate) (parse-declarator parstate)) ; ( declor
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp last-span parstate)
              (read-punctuator ")" parstate))) ; ( declor )
          (parse-direct-declarator-rest (dirdeclor-paren declor)
                                        (span-join span last-span)
                                        parstate)))
       ;; If token is anything else, it is an error:
       ;; we do not have a direct declarator.
       (t
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or an open parenthesis"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-direct-declarator-rest ((prev-dirdeclor dirdeclorp)
                                        (prev-span spanp)
                                        (parstate parstatep))
    :returns (mv erp
                 (dirdeclor dirdeclorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a direct declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after parsing
       the identifier or parenthesized declarator
       that starts the direct declarator,
       and which is a direct declarator itself,
       and is passed to this function as the @('prev-dirdeclor') input,
       along with its span."))
    (b* (((reterr) (irr-dirdeclor) (irr-span) parstate)
         ;; We read the next token, to determine whether
         ;; there is another array or function declarator.
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is an open parenthesis or an open square bracket,
       ;; we must have a function or array declarator.
       ;; We put back the token
       ;; and call the function to parse the next declarator,
       ;; which combines that with the previous one passed to this function,
       ;; obtaining an extended direct declarator
       ;; which we recursively pass to this function
       ;; for possibly further extension.
       ((or (token-punctuatorp token "(") ; (
            (token-punctuatorp token "[")) ; [
        (b* ((parstate (unread-token parstate)) ;
             (psize (parsize parstate))
             ((erp curr-dirdeclor curr-span parstate) ; dirdeclor
              (parse-array/function-declarator prev-dirdeclor
                                               prev-span
                                               parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible)))
          (parse-direct-declarator-rest curr-dirdeclor
                                        curr-span
                                        parstate)))
       ;; If token is not an open parenthesis or an open square bracket,
       ;; we have reached the end of the sequence of zero or more
       ;; array and function abstract declarators.
       (t ; other
        (b* ((parstate (if token (unread-token parstate) parstate))) ;
          (retok (dirdeclor-fix prev-dirdeclor)
                 (span-fix prev-span)
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-declarator ((parstate parstatep))
    :returns (mv erp
                 (declor declorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "A declarator has an optional pointer part
       followed by a mandatory direct declarator."))
    (b* (((reterr) (irr-declor) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is a star, we must have a pointer,
       ;; so we parse it, and then we parse a direct declarator.
       ((token-punctuatorp token "*") ; *
        (b* ((parstate (unread-token parstate)) ;
             ((erp tyqualss & parstate) (parse-pointer parstate)) ; pointer
             ((erp dirdeclor last-span parstate) ; pointer dirdeclor
              (parse-direct-declarator parstate)))
          (retok (make-declor :pointers tyqualss
                              :decl dirdeclor)
                 (span-join span last-span)
                 parstate)))
       ;; If token is not a star, we must have a direct declarator.
       (t ; other
        (b* ((parstate (if token (unread-token parstate) parstate)) ;
             ((erp dirdeclor span parstate) ; dirdeclor
              (parse-direct-declarator parstate)))
          (retok (make-declor :pointers nil
                              :decl dirdeclor)
                 span
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-struct-declarator ((parstate parstatep))
    :returns (mv erp
                 (structdeclor structdeclorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a structure declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "A structure declarator consists of
       a declarator,
       or a declarator followed by colon and a constant expression,
       or a colon and a constant expression."))
    (b* (((reterr) (irr-structdeclor) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token may start a declarator, we parse it,
       ;; and then we see whether there is a colon with an expression.
       ((token-declarator-start-p token) ; declor...
        (b* ((parstate (unread-token parstate)) ;
             (psize (parsize parstate))
             ((erp declor span parstate) (parse-declarator parstate)) ; declor
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is a colon,
           ;; we must have a constant expression after it.
           ((token-punctuatorp token2 ":") ; declor :
            (b* (((erp cexpr last-span parstate) ; declor : expr
                  (parse-constant-expression parstate)))
              (retok (make-structdeclor :declor? declor
                                        :expr? cexpr)
                     (span-join span last-span)
                     parstate)))
           ;; If token2 is not a colon,
           ;; the declarator is the whole structure declarator.
           (t ; declor other
            (b* ((parstate (if token2 (unread-token parstate) parstate)))
              (retok (make-structdeclor :declor? declor
                                        :expr? nil)
                     span
                     parstate))))))
       ;; If token is a colon,
       ;; we must be in the case in which there is no declarator
       ;; and there is just the colon and a constant expression.
       ((token-punctuatorp token ":") ; :
        (b* (((erp cexpr last-span parstate) ; : expr
              (parse-constant-expression parstate)))
          (retok (make-structdeclor :declor? nil
                                    :expr? cexpr)
                 (span-join span last-span)
                 parstate)))
       ;; If token is anything else, it is an error.
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a declarator or a colon"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-struct-declarator-list ((parstate parstatep))
    :returns (mv erp
                 (structdeclors structdeclor-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a list of one or more structure declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "We parse a structure declarator, which must be present.
       Then if we have a comma we recursively call this function
       to parse one or more structure declarators."))
    (b* (((reterr) nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp structdeclor span parstate) ; structdeclor
          (parse-struct-declarator parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is a comma,
       ;; we must have at least another structure declarator.
       ((token-punctuatorp token ",") ; structdeclor ,
        (b* (((erp structdeclors last-span  parstate)
              ;; structdeclor , structdeclors
              (parse-struct-declarator-list parstate)))
          (retok (cons structdeclor structdeclors)
                 (span-join span last-span)
                 parstate)))
       ;; If token is not a comma,
       ;; we have reached the end of the structure declarator list.
       (t ; structdeclor other
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok (list structdeclor)
                 span
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-struct-declaration ((parstate parstatep))
    :returns (mv erp
                 (structdecl structdeclp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a structure declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "A structure declaration is either an assert declaration,
       which is easily recognized by the starting @('_Static_assert') keyword,
       or a list of one or more specifiers and qualifiers
       optionally followed by a list of one or more structure declarators.
       If GCC extensions are supported,
       a non-assert structure declaration
       may start with the @('__extension__') keyword,
       and may end (before the semicolon) with attribute specifiers."))
    (b* (((reterr) (irr-structdecl) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is the '_Static_assert' keyword,
       ;; we have a static assertion.
       ((token-keywordp token "_Static_assert") ; _Static_assert
        (b* (((erp statassert span parstate) ; staticassertion
              (parse-static-assert-declaration span parstate)))
          (retok (structdecl-statassert statassert)
                 span
                 parstate)))
       ;; Otherwise, we must have a specifier and qualifier list,
       ;; optionally preceded by the '__extension__' keyword
       ;; if GCC extensions are supported.
       (t ; other
        (b* (((mv extension parstate)
              (if (and (token-keywordp token "__extension__")
                       (parstate->gcc parstate))
                  (mv t parstate)
                (b* ((parstate (if token (unread-token parstate) parstate)))
                  (mv nil parstate))))
             ;; [__extension__]
             (psize (parsize parstate))
             ((erp specquals span parstate) ; [__extension__] specquals
              (parse-specifier-qualifier-list nil parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp token2 span2 parstate) (read-token parstate)))
          (cond
           ;; If token2 may start a structure declarator,
           ;; we must have a list of one or more structure declarators,
           ;; which we parse, and then we parse the final semicolon,
           ;; preceded by zero or more attribute specifiers
           ;; if GCC extensions are supported.
           ((token-struct-declarator-start-p token2)
            ;; [__extension__] specquals structdeclor...
            (b* ((parstate (unread-token parstate))
                 ;; [__extension__] specquals
                 (psize (parsize parstate))
                 ((erp structdeclors & parstate)
                  ;; [__extension__] specquals structdeclors
                  (parse-struct-declarator-list parstate))
                 ((unless (mbt (<= (parsize parstate) (1- psize))))
                  (reterr :impossible))
                 ((erp attrspecs & parstate)
                  ;; [__extension__] specquals structdeclors [attrspecs]
                  (parse-*-attribute-specifier parstate))
                 ((erp last-span parstate)
                  ;; [__extension__] specquals structdeclors [attrspecs] ;
                  (read-punctuator ";" parstate)))
              (retok (make-structdecl-member :extension extension
                                             :specqual specquals
                                             :declor structdeclors
                                             :attrib attrspecs)
                     (span-join span last-span)
                     parstate)))
           ;; If token2 is the keyword '__attribute__',
           ;; GCC extensions must be supported
           ;; (otherwise '__attribute__' would not be a keyword).
           ;; We parse one or more attribute specifiers,
           ;; and then the final semicolon.
           ((token-keywordp token2 "__attribute__")
            ;; [__extension__] specquals __attribute__
            (b* ((parstate (unread-token parstate))
                 ;; [__extension__] specquals
                 ((erp attrspecs & parstate)
                  ;; [__extension__] specquals [attrspecs]
                  (parse-*-attribute-specifier parstate))
                 ((erp last-span parstate)
                  ;; [__extension__] specquals [attrspecs] ;
                  (read-punctuator ";" parstate)))
              (retok (make-structdecl-member :extension extension
                                             :specqual specquals
                                             :declor nil
                                             :attrib attrspecs)
                     (span-join span last-span)
                     parstate)))
           ;; If token2 is a semicolon,
           ;; we have reached the end of the structure declaration.
           ((token-punctuatorp token2 ";") ; specquals ;
            (retok (make-structdecl-member :extension extension
                                           :specqual specquals
                                           :declor nil
                                           :attrib nil)
                   (span-join span span2)
                   parstate))
           ;; If token2 is anything else, it is an error.
           (t ; specquals other
            (reterr-msg :where (position-to-msg (span->start span2))
                        :expected "a structure declarator or a semicolon"
                        :found (token-to-msg token2))))))))
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-struct-declaration-list ((parstate parstatep))
    :returns (mv erp
                 (structdecls structdecl-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a list of one or more structure declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "We parse the first structure declaration, which must be present.
       Then we recursively call this function if the next token
       may start another structure declaration."))
    (b* (((reterr) nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp structdecl span parstate) ; structdecl
          (parse-struct-declaration parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token may start another structure declaration,
       ;; recursively call this function.
       ((token-struct-declaration-start-p token) ; structdecl structdecl...
        (b* ((parstate (unread-token parstate))
             ((erp structdecls last-span parstate) ; structdecl structdecls
              (parse-struct-declaration-list parstate)))
          (retok (cons structdecl structdecls)
                 (span-join span last-span)
                 parstate)))
       ;; Otherwise, we have reached the end of the structure declarations.
       (t ; structdecl other
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok (list structdecl) span parstate)))))
    :measure (two-nats-measure (parsize parstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-parameter-declaration ((parstate parstatep))
    :returns (mv erp
                 (paramdecl paramdeclp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a parameter declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "A parameter declaration always starts with
       a list of one or more declaration specifiers, which we parse.
       Then we may have a declarator, an abstract declarator, or nothing.")
     (xdoc::p
      "As explained in @(tsee amb-declor/absdeclor),
       there is a complex syntactic overlap
       between declarators and abstract declarators.
       Thus, unless there is no (abstract or non-abstract) declarator,
       which we recognize by the presence of a comma or closed parenthesis,
       we parse a possibly ambiguous declarator or abstract declarator,
       and generate a parameter declarator accordingly,
       and then a parameter declaration with the declaration specifiers."))
    (b* (((reterr) (irr-paramdecl) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp declspecs span parstate) ; declspecs
          (parse-declaration-specifiers nil parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is a comma or a closed parenthesis,
       ;; there is no parameter declarator.
       ((or (token-punctuatorp token ")") ; declspecs )
            (token-punctuatorp token ",")) ; declspecs ,
        (b* ((parstate (unread-token parstate))) ; declspecs
          (retok (make-paramdecl :spec declspecs
                                 :decl (paramdeclor-none))
                 span
                 parstate)))
       ;; Otherwise, we parse
       ;; a possibly ambiguous declarator or abstract declarator,
       ;; and return a parameter declaration in accordance.
       (t ; declspecs other
        (b* ((parstate (if token (unread-token parstate) parstate)) ; declspecs
             ((erp declor/absdeclor
                   last-span
                   parstate) ; declspecs declor/absdeclor
              (parse-declarator-or-abstract-declarator parstate)))
          (amb?-declor/absdeclor-case
           declor/absdeclor
           ;; If we parsed an unambiguous declarator,
           ;; we return a parameter declaration with that.
           :declor
           (retok (make-paramdecl
                   :spec declspecs
                   :decl (paramdeclor-declor declor/absdeclor.unwrap))
                  (span-join span last-span)
                  parstate)
           ;; If we parsed an unambiguous abstract declarator,
           ;; we return a parameter declaration with that.
           :absdeclor
           (retok (make-paramdecl
                   :spec declspecs
                   :decl (paramdeclor-absdeclor declor/absdeclor.unwrap))
                  (span-join span last-span)
                  parstate)
           ;; If we parsed an ambiguous declarator or abstract declarator,
           ;; we return a parameter declaration with that.
           :ambig
           (retok (make-paramdecl
                   :spec declspecs
                   :decl (paramdeclor-ambig declor/absdeclor.unwrap))
                  (span-join span last-span)
                  parstate))))))
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-parameter-declaration-list ((parstate parstatep))
    :returns (mv erp
                 (paramdecls paramdecl-listp)
                 (ellipsis booleanp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a list of one or more parameter declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "We parse the first parameter declaration, which must be present.
       Then if there is a comma there may be another parameter declaration,
       but not necessarily, because we may have an ellipsis instead.
       So we must read a bit further to check that;
       if there may be indeed another parameter declaration,
       we recursively parse the remaining list of one or more."))
    (b* (((reterr) nil nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp paramdecl span parstate) ; paramdecl
          (parse-parameter-declaration parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is a comma, we might have another parameter declaration,
       ;; but we need to check whether we have an ellipsis instead.
       ((token-punctuatorp token ",") ; paramdecl ,
        (b* (((erp token2 span2 parstate) (read-token parstate)))
          (cond
           ;; If token2 is an ellipsis,
           ;; we have reached the end of the parameter declaration list.
           ((token-punctuatorp token2 "...") ; paramdecl , ...
            (retok (list paramdecl)
                   t
                   (span-join span span2)
                   parstate))
           ;; If token2 is not an ellipsis,
           ;; we must have more parameter declarators.
           (t ; paramdecl , other
            (b* ((parstate ; paramdecl ,
                  (if token2 (unread-token parstate) parstate))
                 ((erp paramdecls ellipsis last-span parstate)
                  ;; paramdecl , paramdecls [, ...]
                  (parse-parameter-declaration-list parstate)))
              (retok (cons paramdecl paramdecls)
                     ellipsis
                     (span-join span last-span)
                     parstate))))))
       ;; If token is not a comma,
       ;; we have reached the end of the parameter declaration list.
       (t ; paramdecl other
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok (list paramdecl)
                 nil
                 span
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-type-name ((parstate parstatep))
    :returns (mv erp
                 (tyname tynamep)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a type name."
    :long
    (xdoc::topstring
     (xdoc::p
      "A type name always starts with one or more specifiers and qualifiers,
       which may be followed by an abstract declarator.
       We parse the specifier and qualifier list,
       and then we parse the abstract declarator if present."))
    (b* (((reterr) (irr-tyname) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp specquals span parstate) ; specquals
          (parse-specifier-qualifier-list nil parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token may start an abstract declarator, we parse it.
       ((token-abstract-declarator-start-p token) ; specquals absdeclor...
        (b* ((parstate (unread-token parstate)) ; specquals
             ((erp absdeclor last-span parstate) ; specquals absdeclor
              (parse-abstract-declarator parstate)))
          (retok (make-tyname :specqual specquals
                              :decl? absdeclor)
                 (span-join span last-span)
                 parstate)))
       ;; Otherwise, there is no abstract declarator.
       (t ; specquals other
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok (make-tyname :specqual specquals
                              :decl? nil)
                 span
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-expression-or-type-name ((parstate parstatep))
    :returns (mv erp
                 (expr/tyname amb?-expr/tyname-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an expression or a type name."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called when either an expression or a type name is allowed.
       As discussed in @(tsee amb-expr/tyname),
       there is a complex syntactic overlap between expressions and type names,
       which cannot be disambiguated purely syntactically.
       Thus, this parsing function returns
       a possibly ambiguous expression or type name.")
     (xdoc::p
      "We try to parse both an expression and a type name,
       using the checkpointing and backtracking feature.
       If only one succeeds, there is no ambiguity,
       and we return either an expression or a type name (wrapped).
       If both succeed, there is an ambiguity,
       which we return as such.
       If none succeeds, it is an error.")
     (xdoc::p
      "A complication is that some type names are prefixes of expressions
       (e.g. @('a') is a prefix of @('a+b')),
       and some expressions are prefixes of type names
       (e.g. @('a') is a prefix of @('a*')).
       But all the places where either an expression or a type name is allowed
       are enclosed by the parentheses in the C grammar.
       We exploit this fact by checking, under some conditions,
       after parsing an expression and after parsing a type name,
       that the next token is a closed parenthesis;
       if the check fails, the parsing is considered to have failed.
       This check ensures that, when both parsing attempts succeed,
       we have parsed the whole phrase, and not just a prefix.")
     (xdoc::p
      "The size of the input after backtracking
       should not exceed the size of the input before backtracking.
       For now we insert a run-time check without @(tsee mbt),
       but we plan to revisit this to see if we can have an @(tsee mbt)."))
    (b* (((reterr) (irr-amb?-expr/tyname) (irr-span) parstate)
         (parstate (record-checkpoint parstate)) ; we will backtrack here
         (psize (parsize parstate))
         ((mv erp-expr expr span-expr parstate) (parse-expression parstate)))
      (if erp-expr
          ;; If the parsing of an expression fails,
          ;; we must have a type name.
          (b* ((parstate (backtrack-checkpoint parstate)) ; backtrack
               ((unless (<= (parsize parstate) psize))
                (raise "Internal error: ~
                        size ~x0 after backtracking exceeds ~
                        size ~x1 before backtracking."
                       (parsize parstate) psize)
                ;; Here we have (> (parsize parstate) psize),
                ;; but we need to return a parser state
                ;; no larger than the initial one,
                ;; so we just return the empty parser state.
                ;; This is just logical: execution stops at the RAISE above.
                (b* ((parstate (init-parstate nil nil parstate)))
                  (reterr t)))
               ((erp tyname span parstate) (parse-type-name parstate))
               ;; Ensure there is a closed parenthesis,
               ;; but put it back since it is not part of the type name.
               ((erp & parstate) (read-punctuator ")" parstate))
               (parstate (unread-token parstate))) ; put back )
            (retok (amb?-expr/tyname-tyname tyname) span parstate))
        ;; If the parsing of an expression succeeds,
        ;; we read a token to see whether a closed parenthesis follows.
        (b* (((erp token & parstate) (read-token parstate)))
          (if (token-punctuatorp token ")")
              ;; If a closed parenthesis follows,
              ;; the parsing of the expression has succeeded,
              ;; but we must see whether
              ;; the parsing of a type name will also succeed.
              ;; So we backtrack
              ;; (which will also put back the closed parenthesis)
              ;; and we attempt to parse a type name.
              (b* ((parstate (backtrack-checkpoint parstate)) ; backtrack
                   ((unless (<= (parsize parstate) psize))
                    (raise "Internal error: ~
                            size ~x0 after backtracking exceeds ~
                            size ~x1 before backtracking."
                           (parsize parstate) psize)
                    ;; Here we have (> (parsize parstate) psize),
                    ;; but we need to return a parser state
                    ;; no larger than the initial one,
                    ;; so we just return the empty parser state.
                    ;; This is just logical:
                    ;; execution stops at the RAISE above.
                    (b* ((parstate (init-parstate nil nil parstate)))
                      (reterr t)))
                   (parstate
                    (record-checkpoint parstate)) ; we may backtrack again
                   ((mv erp tyname span-tyname parstate)
                    (parse-type-name parstate)))
                (if erp
                    ;; If the parsing of a type name fails,
                    ;; we have an unambiguous expression, already parsed.
                    ;; We re-parse it (which must succeed),
                    ;; after backtracking,
                    ;; so that we end up in the right parser state.
                    ;; This re-parsing is not ideal:
                    ;; we may revisit this with
                    ;; a more elaborate backtracking scheme
                    ;; that lets us backtrack from backtracking.
                    (b* ((parstate (backtrack-checkpoint parstate)) ; backtrack
                         ((unless (<= (parsize parstate) psize))
                          (raise "Internal error: ~
                                  size ~x0 after backtracking exceeds ~
                                  size ~x1 before backtracking."
                                 (parsize parstate) psize)
                          ;; Here we have (> (parsize parstate) psize),
                          ;; but we need to return a parser state
                          ;; no larger than the initial one,
                          ;; so we just return the empty parser state.
                          ;; This is just logical:
                          ;; execution stops at the RAISE above.
                          (b* ((parstate (init-parstate nil nil parstate)))
                            (reterr t)))
                         ((mv erp expr1 span-expr1 parstate)
                          (parse-expression parstate))
                         ((when erp)
                          (raise "Internal error: ~
                                  parsing the same expression ~x0 twice ~
                                  gives the error ~x1."
                                 expr erp)
                          (reterr t))
                         ((unless (equal expr1 expr))
                          (raise "Internal error: ~
                                  parsing the same expression ~x0 twice ~
                                  gives a different expression ~x1."
                                 expr expr1)
                          (reterr t))
                         ((unless (equal span-expr1 span-expr))
                          (raise "Internal error: ~
                                  parsing the same expression ~x0 twice ~
                                  gives a different span ~x1 from ~x2."
                                 expr span-expr1 span-expr)
                          (reterr t)))
                      (retok (amb?-expr/tyname-expr expr) span-expr parstate))
                  ;; If the parsing of a type name succeeds,
                  ;; we read a token to see whether
                  ;; a closed parenthesis follows.
                  (b* (((erp token & parstate) (read-token parstate)))
                    (if (token-punctuatorp token ")")
                        ;; If a closed parenthesis follows,
                        ;; we have an ambiguous expression or type name.
                        ;; We double-check that the two spans are the same;
                        ;; this is always expected to succeed,
                        ;; because we have checked that in both cases
                        ;; we have reached a closed parenthesis,
                        ;; and the parser reads only balanced parentheses.
                        ;; We put back the closed parenthesis.
                        (b* ((parstate
                              (clear-checkpoint parstate)) ; no backtracking
                             ((unless (equal span-expr span-tyname))
                              (raise "Internal error:
                                      span ~x0 of expression ~x1 differs from ~
                                      span ~x2 of type name ~x3."
                                     span-expr expr span-tyname tyname)
                              (reterr t))
                             (parstate (unread-token parstate)))
                          (retok (amb?-expr/tyname-ambig
                                  (make-amb-expr/tyname :expr expr
                                                        :tyname tyname))
                                 span-expr ; = span-tyname
                                 parstate))
                      ;; If a closed parenthesis does not follow,
                      ;; we regard the parsing of the type name to have failed,
                      ;; perhaps because we have only parsed
                      ;; a prefix of an expression.
                      ;; So we must have an expression instead,
                      ;; which we have already parsed,
                      ;; but again we need to re-parse it.
                      (b* ((parstate
                            (backtrack-checkpoint parstate)) ; backtrack
                           ((unless (<= (parsize parstate) psize))
                            (raise "Internal error: ~
                                    size ~x0 after backtracking exceeds ~
                                    size ~x1 before backtracking."
                                   (parsize parstate) psize)
                            ;; Here we have (> (parsize parstate) psize),
                            ;; but we need to return a parser state
                            ;; no larger than the initial one,
                            ;; so we just return the empty parser state.
                            ;; This is just logical:
                            ;; execution stops at the RAISE above.
                            (b* ((parstate (init-parstate nil nil parstate)))
                              (reterr t)))
                           ((mv erp expr1 span-expr1 parstate)
                            (parse-expression parstate))
                           ((when erp)
                            (raise "Internal error: ~
                                    parsing the same expression ~x0 twice ~
                                    gives the error ~x1."
                                   expr erp)
                            (reterr t))
                           ((unless (equal expr1 expr))
                            (raise "Internal error: ~
                                    parsing the same expression ~x0 twice ~
                                    gives a different expression ~x1."
                                   expr expr1)
                            (reterr t))
                           ((unless (equal span-expr1 span-expr))
                            (raise "Internal error: ~
                                    parsing the same expression ~x0 twice ~
                                    gives a different span ~x1 from ~x2."
                                   expr span-expr1 span-expr)
                            (reterr t)))
                        (retok (amb?-expr/tyname-expr expr)
                               span-expr
                               parstate))))))
            ;; If no closed parenthesis follows the parsed expression,
            ;; we regard the parsing of the expression to have failed,
            ;; perhaps because we have only parsed a prefix of a type name.
            ;; So we must have a type name instead.
            ;; We backtrack, which also puts back the token just read if any,
            ;; and we attempt to parse a type name.
            (b* ((parstate (backtrack-checkpoint parstate)) ; backtrack
                 ((unless (<= (parsize parstate) psize))
                  (raise "Internal error: ~
                          size ~x0 after backtracking exceeds ~
                          size ~x1 before backtracking."
                         (parsize parstate) psize)
                  ;; Here we have (> (parsize parstate) psize),
                  ;; but we need to return a parser state
                  ;; no larger than the initial one,
                  ;; so we just return the empty parser state.
                  ;; This is just logical: execution stops at the RAISE above.
                  (b* ((parstate (init-parstate nil nil parstate)))
                    (reterr t)))
                 ((erp tyname span parstate) (parse-type-name parstate))
                 ;; Ensure there is a closed parenthesis,
                 ;; but put it back since it is not part of the type name.
                 ((erp & parstate) (read-punctuator ")" parstate))
                 (parstate (unread-token parstate))) ; put back )
              (retok (amb?-expr/tyname-tyname tyname) span parstate))))))
    :measure (two-nats-measure (parsize parstate) 17))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-declarator-or-abstract-declarator ((parstate parstatep))
    :returns (mv erp
                 (declor/absdeclor amb?-declor/absdeclor-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a declarator or an abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called when expecting
       either a declarator or an abstract declarator
       (this happens in a parameter declaration,
       after establishing that the parameter declarator is present).
       Thus, this parsing function returns
       a possibly ambiguous declarator or abstract declarator.")
     (xdoc::p
      "We try to parse both a declarator and an abstract declarator,
       using the checkpointing and backtracking feature.
       If only one succeeds, there is no ambiguity,
       and we return either a declarator or an abstract declarator (wrapped).
       If both succeed, there is an ambiguity,
       which we return as such.
       If none succeeds, it is an error.")
     (xdoc::p
      "A complication is that an abstract declarator
       may be a prefix of a declarator,
       e.g. @('int *') is a prefix of @('int *x').
       In this case, we can disambiguate the situation
       in favor or a declarator,
       exploiting the fact that an ambiguous declarator or abstract declarator
       only occurs in a parameter declaration,
       which is always follows by a comma or closed parenthesis.
       So, if we successfully parse an abstract declarator,
       we also ensure that the next token is a comma or closed parenthesis,
       otherwise we regard the parsing of the abstract declarator
       to have failed."))
    (b* (((reterr) (irr-amb?-declor/absdeclor) (irr-span) parstate)
         (parstate (record-checkpoint parstate)) ; we will backtrack here
         (psize (parsize parstate))
         ((mv erp-declor declor span-declor parstate)
          (parse-declarator parstate)))
      (if erp-declor
          ;; If the parsing of a declarator fails,
          ;; we must have an abstract declarator.
          (b* ((parstate (backtrack-checkpoint parstate)) ; backtrack
               ((unless (<= (parsize parstate) psize))
                (raise "Internal error: ~
                        size ~x0 after backtracking exceeds ~
                        size ~x1 before backtracking."
                       (parsize parstate) psize)
                ;; Here we have (> (parsize parstate) psize),
                ;; but we need to return a parser state
                ;; no larger than the initial one,
                ;; so we just return the empty parser state.
                ;; This is just logical: execution stops at the RAISE above.
                (b* ((parstate (init-parstate nil nil parstate)))
                  (reterr t)))
               ((erp absdeclor span parstate)
                (parse-abstract-declarator parstate)))
            (retok (amb?-declor/absdeclor-absdeclor absdeclor) span parstate))
        ;; If the parsing of a declarator succeeds,
        ;; we must see whether the parsing of an abstract declarator
        ;; also succeeds, after backtracking.
        (b* ((parstate (backtrack-checkpoint parstate)) ; backtrack
             ((unless (<= (parsize parstate) psize))
              (raise "Internal error: ~
                      size ~x0 after backtracking exceeds ~
                      size ~x1 before backtracking."
                     (parsize parstate) psize)
              ;; Here we have (> (parsize parstate) psize),
              ;; but we need to return a parser state
              ;; no larger than the initial one,
              ;; so we just return the empty parser state.
              ;; This is just logical:
              ;; execution stops at the RAISE above.
              (b* ((parstate (init-parstate nil nil parstate)))
                (reterr t)))
             (parstate (record-checkpoint parstate)) ; we may backtrack again
             ((mv erp absdeclor span-absdeclor parstate)
              (parse-abstract-declarator parstate)))
          (if erp
              ;; If the parsing of an abstract declarator fails,
              ;; we have an unambiguous declarator, already parsed.
              ;; We re-parse it (which must succeed),
              ;; after backtracking,
              ;; so that we end up in the right parser state.
              ;; This re-parsing is not ideal:
              ;; we may revisit this with
              ;; a more elaborate backtracking scheme
              ;; that lets us backtrack from backtracking.
              (b* ((parstate (backtrack-checkpoint parstate)) ; backtrack
                   ((unless (<= (parsize parstate) psize))
                    (raise "Internal error: ~
                            size ~x0 after backtracking exceeds ~
                            size ~x1 before backtracking."
                           (parsize parstate) psize)
                    ;; Here we have (> (parsize parstate) psize),
                    ;; but we need to return a parser state
                    ;; no larger than the initial one,
                    ;; so we just return the empty parser state.
                    ;; This is just logical:
                    ;; execution stops at the RAISE above.
                    (b* ((parstate (init-parstate nil nil parstate)))
                      (reterr t)))
                   ((mv erp declor1 span-declor1 parstate)
                    (parse-declarator parstate))
                   ((when erp)
                    (raise "Internal error: ~
                            parsing the same declarator ~x0 twice ~
                            gives the error ~x1."
                           declor erp)
                    (reterr t))
                   ((unless (equal declor1 declor))
                    (raise "Internal error: ~
                            parsing the same declarator ~x0 twice ~
                            gives a different declarator ~x1."
                           declor declor1)
                    (reterr t))
                   ((unless (equal span-declor1 span-declor))
                    (raise "Internal error: ~
                            parsing the same declarator ~x0 twice ~
                            gives a different span ~x1 from ~x2."
                           declor span-declor1 span-declor)
                    (reterr t)))
                (retok (amb?-declor/absdeclor-declor declor)
                       span-declor
                       parstate))
            ;; If the parsing of an abstract declarator succeeds,
            ;; we still need to check whether
            ;; it is followed by a comma or closed parenthesis,
            ;; as explained in the documentation of the function above.
            ;; So we read a token.
            (b* (((erp token & parstate) (read-token parstate)))
              (if (or (token-punctuatorp token ",")
                      (token-punctuatorp token ")"))
                  ;; If a comma or closed parenthesis follows,
                  ;; the parsing of the abstract declarator has succeeded,
                  ;; we have an ambiguous declarator or abstract declarator.
                  ;; We double-check that the two spans are the same;
                  ;; we have not yet analyzed in detail
                  ;; whether this check should always succeed,
                  ;; but we will revisit the issue if we observe failures
                  ;; (in which case we can handle things similarly to
                  ;; our handling in PARSE-EXPRESSION-OR-TYPE-NAME).
                  (b* ((parstate (clear-checkpoint parstate)) ; no backtracking
                       ((unless (equal span-absdeclor span-declor))
                        (raise "Internal error: ~
                                span ~x0 of declarator ~x1 differs from ~
                                span ~x2 of abstract declarator ~x3."
                               span-declor declor span-absdeclor absdeclor)
                        (reterr t))
                       (parstate (unread-token parstate))) ; put back , or )
                    (retok (amb?-declor/absdeclor-ambig
                            (make-amb-declor/absdeclor :declor declor
                                                       :absdeclor absdeclor))
                           span-declor ; = span-absdeclor
                           parstate))
                ;; If a comma or closed parenthesis does not follow,
                ;; the abstract declarator must be a prefix of a declarator,
                ;; so it means that we have an unambiguous declarator.
                ;; We must backtrack and re-parse it;
                ;; note that the backtracking
                ;; also puts back the token just read.
                (b* ((parstate (backtrack-checkpoint parstate)) ; backtrack
                     ((unless (<= (parsize parstate) psize))
                      (raise "Internal error: ~
                              size ~x0 after backtracking exceeds ~
                              size ~x1 before backtracking."
                             (parsize parstate) psize)
                      ;; Here we have (> (parsize parstate) psize),
                      ;; but we need to return a parser state
                      ;; no larger than the initial one,
                      ;; so we just return the empty parser state.
                      ;; This is just logical:
                      ;; execution stops at the RAISE above.
                      (b* ((parstate (init-parstate nil nil parstate)))
                        (reterr t)))
                     ((mv erp declor1 span-declor1 parstate)
                      (parse-declarator parstate))
                     ((when erp)
                      (raise "Internal error: ~
                              parsing the same declarator ~x0 twice ~
                              gives the error ~x1."
                             declor erp)
                      (reterr t))
                     ((unless (equal declor1 declor))
                      (raise "Internal error: ~
                              parsing the same declarator ~x0 twice ~
                              gives a different declarator ~x1."
                             declor declor1)
                      (reterr t))
                     ((unless (equal span-declor1 span-declor))
                      (raise "Internal error: ~
                              parsing the same declarator ~x0 twice ~
                              gives a different span ~x1 from ~x2."
                             declor span-declor1 span-declor)
                      (reterr t)))
                  (retok (amb?-declor/absdeclor-declor declor)
                         span-declor
                         parstate))))))))
    :measure (two-nats-measure (parsize parstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-attribute-parameters ((parstate parstatep))
    :returns (mv erp
                 (attrparams expr-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse attribute parameters."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is only used if GCC extensions are supported.
       See the ABNF grammar rule for @('attribute-parameters').")
     (xdoc::p
      "If parsing is successful, we return a list of zero or more expressions,
       which are the parameters.
       We re-use @(tsee parse-argument-expressions)
       to parse the zero or more comma-separated expressions.
       This parsing function does exactly what is needed here."))
    (b* (((reterr) nil (irr-span) parstate)
         ((erp open-span parstate) (read-punctuator "(" parstate))
         ((erp exprs & parstate) (parse-argument-expressions parstate))
         ((erp close-span parstate) (read-punctuator ")" parstate)))
      (retok exprs (span-join open-span close-span) parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-attribute ((parstate parstatep))
    :returns (mv erp
                 (attr attribp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an attribute."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is only used if GCC extensions are supported.
       See the ABNF grammar rule for @('attribute')."))
    (b* (((reterr) (irr-attrib) (irr-span) parstate)
         ((erp ident ident-span parstate) (read-identifier parstate)) ; ident
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is an open parenthesis, the attribute has parameters.
       ((token-punctuatorp token "(") ; ident (
        (b* ((parstate (unread-token parstate)) ; ident
             ((erp exprs span parstate) ; ident ( exprs )
              (parse-attribute-parameters parstate)))
          (retok (make-attrib-name-param :name ident :param exprs)
                 (span-join ident-span span)
                 parstate)))
       ;; If token is anything else, the attribute is just a name.
       (t ; ident other
        (b* ((parstate (if token (unread-token parstate) parstate))) ; ident
          (retok (attrib-name ident) ident-span parstate)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-attribute-list ((parstate parstatep))
    :returns (mv erp
                 (attrs attrib-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse a list of one or more attributes, separated by commas."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is only used if GCC extensions are supported.
       See the ABNF grammar rule for @('attribute-list')."))
    (b* (((reterr) nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp attr span parstate) (parse-attribute parstate)) ; attr
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is a comma,
       ;; we recursively parse one or more additional attributes,
       ;; and we combine them with the one parsed just above.
       ((token-punctuatorp token ",") ; attr ,
        (b* (((erp attrs last-span parstate) ; attr , attrs
              (parse-attribute-list parstate)))
          (retok (cons attr attrs) (span-join span last-span) parstate)))
       ;; If token is not a comma,
       ;; we have just the one attribute we parsed above.
       (t ; attr other
        (b* ((parstate (if token (unread-token parstate) parstate))) ; attr
          (retok (list attr) span parstate)))))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-attribute-specifier ((uscores booleanp)
                                     (first-span spanp)
                                     (parstate parstatep))
    :returns (mv erp
                 (attrspec attrib-specp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse an attribute specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is only used if GCC extensions are supported.
       See the ABNF grammar rule for @('attribute-specifier').")
     (xdoc::p
      "This is called after parsing the initial @('__attribute__'),
       whose span we pass to this parsing function as input."))
    (b* (((reterr) (irr-attrib-spec) (irr-span) parstate)
         ;; __attribute__
         ((erp & parstate) (read-punctuator "(" parstate)) ; __attribute__ (
         ((erp & parstate) (read-punctuator "(" parstate)) ; __attribute__ ( (
         ((erp attrs & parstate) ; __attribute__ ( ( attrs
          (parse-attribute-list parstate))
         ((erp & parstate) ; __attribute__ ( ( attrs )
          (read-punctuator ")" parstate))
         ((erp last-span parstate) ; __attribute__ ( ( attrs ) )
          (read-punctuator ")" parstate)))
      (retok (make-attrib-spec :uscores uscores :attribs attrs)
             (span-join first-span last-span)
             parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-*-attribute-specifier ((parstate parstatep))
    :returns (mv erp
                 (attrspecs attrib-spec-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls)
    :short "Parse zero or more attribute specifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "We parse a @('*attribute-specifier') in ABNF notation,
       i.e. a repetition of zero or more attribute specifiers;
       see ABNF grammar rule for @('attribute-specifier').")
     (xdoc::p
      "If the next token is the @('__attribute__') keyword,
       we finish parsing the attribute specifier,
       and we recursively call this function
       to parse zero or more additional attribute specifiers,
       which we combine with the one just parsed.")
     (xdoc::p
      "If there are no attribute specifiers, we return an irrelevant span.
       When combining the span of the first attribute specifier (if present)
       with the span of the remaining zero or more attribute specifiers,
       we join spans only if the remaining ones are one or more;
       if there are zero, the span of the first attribute specifier
       is also the span of the whole sequence.")
     (xdoc::p
      "If GCC extensions are not supported,
       this parsing function always returns the empty list,
       because @('__attribute__') is a keyword
       only if GCC extensions are supported."))
    (b* (((reterr) nil (irr-span) parstate)
         ((erp token first-span parstate) (read-token parstate))
         ((unless (or (token-keywordp token "__attribute")
                      (token-keywordp token "__attribute__")))
          (b* ((parstate (if token (unread-token parstate) parstate)))
            (retok nil (irr-span) parstate)))
         ;; __attribute__
         (uscores (token-keywordp token "__attribute__"))
         (psize (parsize parstate))
         ((erp attrspec span parstate)
          (parse-attribute-specifier uscores first-span parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ;; __attribute__ ( ( ... ) )
         ((erp attrspecs last-span parstate)
          ;; __attribute__ ( ( ... ) ) [attrspecs]
          (parse-*-attribute-specifier parstate)))
      (retok (cons attrspec attrspecs)
             (if attrspecs (span-join span last-span) span)
             parstate))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :prepwork ((local (in-theory (disable acl2::member-of-cons)))) ; for speed

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable o< o-finp nfix fix)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual parsize-of-parse-exprs/decls-uncond
    (defret parsize-of-parse-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-expression)
    (defret parsize-of-parse-expression-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-expression-rest)
    (defret parsize-of-parse-assignment-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-assignment-expression)
    (defret parsize-of-parse-conditional-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-conditional-expression)
    (defret parsize-of-parse-logical-or-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-logical-or-expression)
    (defret parsize-of-parse-logical-or-expression-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-logical-or-expression-rest)
    (defret parsize-of-parse-logical-and-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-logical-and-expression)
    (defret parsize-of-parse-logical-and-expression-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-logical-and-expression-rest)
    (defret parsize-of-parse-inclusive-or-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-inclusive-or-expression)
    (defret parsize-of-parse-inclusive-or-expression-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-inclusive-or-expression-rest)
    (defret parsize-of-parse-exclusive-or-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-exclusive-or-expression)
    (defret parsize-of-parse-exclusive-or-expression-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-exclusive-or-expression-rest)
    (defret parsize-of-parse-and-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-and-expression)
    (defret parsize-of-parse-and-expression-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-and-expression-rest)
    (defret parsize-of-parse-equality-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-equality-expression)
    (defret parsize-of-parse-equality-expression-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-equality-expression-rest)
    (defret parsize-of-parse-relational-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-relational-expression)
    (defret parsize-of-parse-relational-expression-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-relational-expression-rest)
    (defret parsize-of-parse-shift-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-shift-expression)
    (defret parsize-of-parse-shift-expression-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-shift-expression-rest)
    (defret parsize-of-parse-additive-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-additive-expression)
    (defret parsize-of-parse-additive-expression-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-additive-expression-rest)
    (defret parsize-of-parse-multiplicative-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-multiplicative-expression)
    (defret parsize-of-parse-multiplicative-expression-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-multiplicative-expression-rest)
    (defret parsize-of-parse-cast-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-cast-expression)
    (defret parsize-of-parse-unary-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-unary-expression)
    (defret parsize-of-parse-postfix-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-postfix-expression)
    (defret parsize-of-parse-postfix-expression-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-postfix-expression-rest)
    (defret parsize-of-parse-argument-expressions-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-argument-expressions)
    (defret parsize-of-parse-argument-expressions-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-argument-expressions-rest)
    (defret parsize-of-parse-primary-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-primary-expression)
    (defret parsize-of-parse-generic-associations-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-generic-associations-rest)
    (defret parsize-of-parse-generic-association-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-generic-association)
    (defret parsize-of-parse-compound-literal-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-compound-literal)
    (defret parsize-of-parse-constant-expression-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-constant-expression)
    (defret parsize-of-parse-static-assert-declaration-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-static-assert-declaration)
    (defret parsize-of-parse-designator-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-designator)
    (defret parsize-of-parse-designator-list-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-designator-list)
    (defret parsize-of-parse--initializer-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-initializer)
    (defret parsize-of-parse-designation?-initializer-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-designation?-initializer)
    (defret parsize-of-parse-initializer-list-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-initializer-list)
    (defret parsize-of-parse-enumerator-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-enumerator)
    (defret parsize-of-parse-enumerator-list-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-enumerator-list)
    (defret parsize-of-parse-specifier/qualifier-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-specifier/qualifier)
    (defret parsize-of-parse-specifier-qualifier-list-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-specifier-qualifier-list)
    (defret parsize-of-parse-declaration-specifier-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-declaration-specifier)
    (defret parsize-of-parse-declaration-specifiers-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-declaration-specifiers)
    (defret parsize-of-parse-struct-or-union-specifier-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-struct-or-union-specifier)
    (defret parsize-of-parse-enum-specifier-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-enum-specifier)
    (defret parsize-of-parse-alignment-specifier-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-alignment-specifier)
    (defret parsize-of-parse-array/function-abstract-declarator-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-array/function-abstract-declarator)
    (defret parsize-of-parse-direct-abstract-declarator-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-direct-abstract-declarator)
    (defret parsize-of-parse-direct-abstract-declarator-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-direct-abstract-declarator-rest)
    (defret parsize-of-parse-abstract-declarator-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-abstract-declarator)
    (defret parsize-of-parse-array/function-declarator-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-array/function-declarator)
    (defret parsize-of-parse-direct-declarator-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-direct-declarator)
    (defret parsize-of-parse-direct-declarator-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-direct-declarator-rest)
    (defret parsize-of-parse-declarator-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-declarator)
    (defret parsize-of-parse-struct-declarator-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-struct-declarator)
    (defret parsize-of-parse-struct-declarator-list-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-struct-declarator-list)
    (defret parsize-of-parse-struct-declaration-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-struct-declaration)
    (defret parsize-of-parse-struct-declaration-list-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-struct-declaration-list)
    (defret parsize-of-parse-parameter-declaration-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-parameter-declaration)
    (defret parsize-of-parse-parameter-declaration-list-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-parameter-declaration-list)
    (defret parsize-of-parse-type-name-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-type-name)
    (defret parsize-of-parse-expression-or-type-name-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-expression-or-type-name)
    (defret parsize-of-parse-declarator-or-abstract-declarator-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-declarator-or-abstract-declarator)
    (defret parsize-of-parse-attribute-parameters-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-attribute-parameters)
    (defret parsize-of-parse-attribute-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-attribute)
    (defret parsize-of-parse-attribute-list-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-attribute-list)
    (defret parsize-of-parse-attribute-specifier-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-attribute-specifier)
    (defret parsize-of-parse-*-attribute-specifier-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-*-attribute-specifier)
    :hints
    (("Goal" :in-theory (enable fix nfix))
     (cond
      ((acl2::occur-lst '(acl2::flag-is 'parse-cast-expression)
                        clause)
       '(:expand (parse-cast-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-postfix-expression)
                        clause)
       '(:expand (parse-postfix-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-generic-association)
                        clause)
       '(:expand (parse-generic-association parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-abstract-declarator)
                        clause)
       '(:expand (parse-direct-abstract-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-declarator)
                        clause)
       '(:expand (parse-direct-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-specifier-qualifier-list)
                        clause)
       '(:expand (parse-specifier-qualifier-list tyspec-seenp parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration-specifiers)
                        clause)
       '(:expand (parse-declaration-specifiers tyspec-seenp parstate))))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual parsize-of-parse-exprs/decls-cond
    (defret parsize-of-parse-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-expression)
    (defret parsize-of-parse-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-expression-rest)
    (defret parsize-of-parse-assignment-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-assignment-expression)
    (defret parsize-of-parse-conditional-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-conditional-expression)
    (defret parsize-of-parse-logical-or-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-logical-or-expression)
    (defret parsize-of-parse-logical-or-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-logical-or-expression-rest)
    (defret parsize-of-parse-logical-and-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-logical-and-expression)
    (defret parsize-of-parse-logical-and-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-logical-and-expression-rest)
    (defret parsize-of-parse-inclusive-or-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-inclusive-or-expression)
    (defret parsize-of-parse-inclusive-or-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-inclusive-or-expression-rest)
    (defret parsize-of-parse-exclusive-or-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-exclusive-or-expression)
    (defret parsize-of-parse-exclusive-or-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-exclusive-or-expression-rest)
    (defret parsize-of-parse-and-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-and-expression)
    (defret parsize-of-parse-and-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-and-expression-rest)
    (defret parsize-of-parse-equality-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-equality-expression)
    (defret parsize-of-parse-equality-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-equality-expression-rest)
    (defret parsize-of-parse-relational-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-relational-expression)
    (defret parsize-of-parse-relational-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-relational-expression-rest)
    (defret parsize-of-parse-shift-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-shift-expression)
    (defret parsize-of-parse-shift-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-shift-expression-rest)
    (defret parsize-of-parse-additive-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-additive-expression)
    (defret parsize-of-parse-additive-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-additive-expression-rest)
    (defret parsize-of-parse-multiplicative-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-multiplicative-expression)
    (defret parsize-of-parse-multiplicative-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-multiplicative-expression-rest)
    (defret parsize-of-parse-cast-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-cast-expression)
    (defret parsize-of-parse-unary-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-unary-expression)
    (defret parsize-of-parse-postfix-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-postfix-expression)
    (defret parsize-of-parse-postfix-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-postfix-expression-rest)
    (defret parsize-of-parse-argument-expressions-cond
      t
      :rule-classes nil
      :fn parse-argument-expressions)
    (defret parsize-of-parse-argument-expressions-rest-cond
      t
      :rule-classes nil
      :fn parse-argument-expressions-rest)
    (defret parsize-of-parse-primary-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-primary-expression)
    (defret parsize-of-parse-generic-associations-rest-cond
      t
      :rule-classes nil
      :fn parse-generic-associations-rest)
    (defret parsize-of-parse-generic-association-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-generic-association)
    (defret parsize-of-parse-compound-literal-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-compound-literal)
    (defret parsize-of-parse-constant-expression-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-constant-expression)
    (defret parsize-of-parse-static-assert-declaration-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-static-assert-declaration)
    (defret parsize-of-parse-designator-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-designator)
    (defret parsize-of-parse-designator-list-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-designator-list)
    (defret parsize-of-parse-initializer-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-initializer)
    (defret parsize-of-parse-designation?-initializer-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-designation?-initializer)
    (defret parsize-of-parse-initializer-list-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-initializer-list)
    (defret parsize-of-parse-enumerator-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-enumerator)
    (defret parsize-of-parse-enumerator-list-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-enumerator-list)
    (defret parsize-of-parse-specifier/qualifier-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-specifier/qualifier)
    (defret parsize-of-parse-specifier-qualifier-list-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-specifier-qualifier-list)
    (defret parsize-of-parse-declaration-specifier-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-declaration-specifier)
    (defret parsize-of-parse-declaration-specifiers-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-declaration-specifiers)
    (defret parsize-of-parse-struct-or-union-specifier-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-struct-or-union-specifier)
    (defret parsize-of-parse-enum-specifier-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-enum-specifier)
    (defret parsize-of-parse-alignment-specifier-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-alignment-specifier)
    (defret parsize-of-parse-array/function-abstract-declarator-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-array/function-abstract-declarator)
    (defret parsize-of-parse-direct-abstract-declarator-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-direct-abstract-declarator)
    (defret parsize-of-parse-direct-abstract-declarator-rest-cond
      t
      :rule-classes nil
      :fn parse-direct-abstract-declarator-rest)
    (defret parsize-of-parse-abstract-declarator-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-abstract-declarator)
    (defret parsize-of-parse-array/function-declarator-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-array/function-declarator)
    (defret parsize-of-parse-direct-declarator-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-direct-declarator)
    (defret parsize-of-parse-direct-declarator-rest-cond
      t
      :rule-classes nil
      :fn parse-direct-declarator-rest)
    (defret parsize-of-parse-declarator-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-declarator)
    (defret parsize-of-parse-struct-declarator-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-struct-declarator)
    (defret parsize-of-parse-struct-declarator-list-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-struct-declarator-list)
    (defret parsize-of-parse-struct-declaration-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-struct-declaration)
    (defret parsize-of-parse-struct-declaration-list-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-struct-declaration-list)
    (defret parsize-of-parse-parameter-declaration-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-parameter-declaration)
    (defret parsize-of-parse-parameter-declaration-list-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-parameter-declaration-list)
    (defret parsize-of-parse-type-name-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-type-name)
    (defret parsize-of-parse-expression-or-type-name-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-expression-or-type-name)
    (defret parsize-of-parse-declarator-or-abstract-declarator-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-declarator-or-abstract-declarator)
    (defret parsize-of-parse-attribute-parameters-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-attribute-parameters)
    (defret parsize-of-parse-attribute-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-attribute)
    (defret parsize-of-parse-attribute-list-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-attribute-list)
    (defret parsize-of-parse-attribute-specifier-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-attribute-specifier)
    (defret parsize-of-parse-*-attribute-specifier-cond
      t
      :rule-classes nil
      :fn parse-*-attribute-specifier)
    :hints
    (("Goal" :in-theory (enable fix nfix))
     (cond
      ((acl2::occur-lst '(acl2::flag-is 'parse-expression)
                        clause)
       '(:expand (parse-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-assignment-expression)
                        clause)
       '(:expand (parse-assignment-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-logical-or-expression)
                        clause)
       '(:expand (parse-logical-or-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-logical-and-expression)
                        clause)
       '(:expand (parse-logical-and-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-inclusive-or-expression)
                        clause)
       '(:expand (parse-inclusive-or-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-exclusive-or-expression)
                        clause)
       '(:expand (parse-exclusive-or-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-and-expression)
                        clause)
       '(:expand (parse-and-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-equality-expression)
                        clause)
       '(:expand (parse-equality-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-relational-expression)
                        clause)
       '(:expand (parse-relational-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-shift-expression)
                        clause)
       '(:expand (parse-shift-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-additive-expression)
                        clause)
       '(:expand (parse-additive-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-multiplicative-expression)
                        clause)
       '(:expand (parse-multiplicative-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-cast-expression)
                        clause)
       '(:expand (parse-cast-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-postfix-expression)
                        clause)
       '(:expand (parse-postfix-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-generic-association)
                        clause)
       '(:expand (parse-generic-association parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-abstract-declarator)
                        clause)
       '(:expand (parse-direct-abstract-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-declarator)
                        clause)
       '(:expand (parse-direct-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-specifier-qualifier-list)
                        clause)
       '(:expand (parse-specifier-qualifier-list tyspec-seenp parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration-specifiers)
                        clause)
       '(:expand (parse-declaration-specifiers tyspec-seenp parstate))))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret dirabsdeclor-decl?-nil-p-of-parse-array/function-abstract-declarator
    (implies (not erp)
             (dirabsdeclor-decl?-nil-p dirabsdeclor))
    :hints (("Goal"
             :in-theory (enable dirabsdeclor-decl?-nil-p)
             :expand (parse-array/function-abstract-declarator parstate)))
    :fn parse-array/function-abstract-declarator)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards parse-expression
    :hints (("Goal" :in-theory (e/d (acl2::member-of-cons
                                     token-additive-operator-p)
                                    ((:e tau-system))))))) ; for speed

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-asm-name-specifier ((uscores keyword-uscores-p)
                                  (first-span spanp)
                                  (parstate parstatep))
  :returns (mv erp
               (asmspec asm-name-specp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse an assembler name specifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used only if GCC extensions are supported.")
   (xdoc::p
    "This is called after parsing the initial @('asm') or @('__asm__').
     We pass to this function a flag distinguishing the two keywords
     (i.e. whether it has underscores or not),
     as well as the span of that keyword.
     We parse the rest of the assembler name specifier,
     and return its abstract syntax representation.
     We ensure that there is at least one string literal;
     see grammar rule for @('asm-name-specifier'), which uses @('1*')."))
  (b* (((reterr) (irr-asm-name-spec) (irr-span) parstate)
       ;; asm
       ((erp & parstate) (read-punctuator "(" parstate)) ; asm (
       ((erp token span parstate) (read-token parstate))
       ((unless (and token (token-case token :string)))
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a string literal"
                    :found (token-to-msg token)))
       (parstate (unread-token parstate)) ; asm-or-__asm__ (
       ((erp strings & parstate) ; asm-or-__asm__ ( strings
        (parse-*-stringlit parstate))
       ((erp last-span parstate) ; asm-or-__asm__ ( strings )
        (read-punctuator ")" parstate)))
    (retok (make-asm-name-spec :strings strings
                               :uscores uscores)
           (span-join first-span last-span)
           parstate))

  ///

  (defret parsize-of-parse-asm-name-specifier-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-asm-name-specifier-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-?-asm-name-specifier ((parstate parstatep))
  :returns (mv erp
               (asmspec? asm-name-spec-optionp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse an optional assembler name specifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "The optionality is conveyed by
     the question mark in the name of this function.
     If the next token is the @('asm') or @('__asm__') keyword,
     we must have an assembler name specifier, which we parse.
     Otherwise, we put back the token
     and return no assembler name specifier;
     in this case, the returned span is an irrelevant one."))
  (b* (((reterr) nil (irr-span) parstate)
       ((erp token span parstate) (read-token parstate)))
    (cond
     ((token-keywordp token "asm")
      (parse-asm-name-specifier (keyword-uscores-none) span parstate))
     ((token-keywordp token "__asm")
      (parse-asm-name-specifier (keyword-uscores-start) span parstate))
     ((token-keywordp token "__asm__")
      (parse-asm-name-specifier (keyword-uscores-both) span parstate))
     (t
      (b* ((parstate (if token (unread-token parstate) parstate)))
        (retok nil (irr-span) parstate)))))

  ///

  (defret parsize-of-parse-?-asm-name-specifier
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-init-declarator ((parstate parstatep))
  :returns (mv erp
               (initdeclor initdeclorp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse an initializer declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "An initializer declarator consists of a declarator,
     optionally followed by an equal sign and an initializer."))
  (b* (((reterr) (irr-initdeclor) (irr-span) parstate)
       ((erp declor span parstate) (parse-declarator parstate)) ; declor
       ((erp token & parstate) (read-token parstate)))
    (cond
     ;; If token is an equal sign, there must be an initializer.
     ((token-punctuatorp token "=") ; declor =
      (b* (((erp initer last-span parstate) ; declor = initer
            (parse-initializer parstate)))
        (retok (make-initdeclor :declor declor :init? initer)
               (span-join span last-span)
               parstate)))
     ;; Otherwise, there is no initializer.
     (t ; declor other
      (b* ((parstate (if token (unread-token parstate) parstate))) ; declor
        (retok (make-initdeclor :declor declor :init? nil)
               span
               parstate)))))

  ///

  (defret parsize-of-parse-init-declarator-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-init-declarator-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-init-declarator-list ((parstate parstatep))
  :returns (mv erp
               (initdeclors initdeclor-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a list of one or more initializer declarators."
  :long
  (xdoc::topstring
   (xdoc::p
    "We parse the first one, which must be present.
     If there is a comma after that,
     we recursively parse one or more after the comma."))
  (b* (((reterr) nil (irr-span) parstate)
       ((erp initdeclor span parstate) ; initdeclor
        (parse-init-declarator parstate))
       ((erp token & parstate) (read-token parstate)))
    (cond
     ;; If token is a comma,
     ;; recursively parse one or more initializer declarators,
     ;; and combine with the one just parsed.
     ((token-punctuatorp token ",") ; initdeclor ,
      (b* (((erp initdeclors last-span parstate) ; initdeclor , initdeclors
            (parse-init-declarator-list parstate)))
        (retok (cons initdeclor initdeclors)
               (span-join span last-span)
               parstate)))
     ;; If token is anything else, we have reached the end of the list.
     (t ; initdeclor other
      (b* ((parstate (if token (unread-token parstate) parstate)))
        (retok (list initdeclor) span parstate)))))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-init-declarator-list-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-parse-init-declarator-list-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-declaration ((parstate parstatep))
  :returns (mv erp
               (decl declp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "A declaration is either an assert declaration,
     recognized by the starting @('_Static_assert') keyword,
     or a list of one or more declaration specifiers
     optionally followed by a list of one or more initializer declarators
     and mandatorily followed by a semicolon.")
   (xdoc::p
    "If GCC extensions are supported, we must also allow for
     an optional assembler name specifier,
     as well as for zero or more attribute specifiers,
     ending a declaration, just before the semicolon;
     and we must also allow for an @('__extension__') keyword
     just before the declaration.
     See the ABNF grammar rule for @('declaration')."))
  (b* (((reterr) (irr-decl) (irr-span) parstate)
       ((erp token span parstate) (read-token parstate)))
    (cond
     ;; If token may start a declaration specifier, we put it back and
     ;; we parse a list or one or more declaration specifiers.
     ;; Then we read more tokens to see if we have initializer declarators.
     ;; But if GCC extensions are supported,
     ;; and if token is the '__extension__' keyword,
     ;; we need to take that into account as well.
     ((or (token-declaration-specifier-start-p token) ; declspec...
          (and (token-keywordp token "__extension__") ; __extension__
               (parstate->gcc parstate)))
      (b* (((mv extension parstate)
            (if (and (token-keywordp token "__extension__")
                     (parstate->gcc parstate))
                (mv t parstate)
              (b* ((parstate (unread-token parstate)))
                (mv nil parstate))))
           ;; [__extension__]
           ((erp declspecs span parstate) ; [__extension__] declspecs
            (parse-declaration-specifiers nil parstate))
           ((erp token2 span2 parstate) (read-token parstate)))
        (cond
         ;; If token2 is the keyword 'asm' or '__asm' or '__asm__',
         ;; and if GCC extensions are supported,
         ;; we have no initializer declarators;
         ;; parse the assembler name specifier,
         ;; any attribute specifiers after that,
         ;; and the ending semicolon.
         ((and (or (token-keywordp token2 "asm")
                   (token-keywordp token2 "__asm")
                   (token-keywordp token2 "__asm__"))
               (parstate->gcc parstate))
          ;; [__extension__] declspecs asm
          (b* ((uscores (cond ((token-keywordp token2 "asm")
                               (keyword-uscores-none))
                              ((token-keywordp token2 "__asm")
                               (keyword-uscores-start))
                              ((token-keywordp token2 "__asm__")
                               (keyword-uscores-both))))
               ((erp asmspec & parstate)
                ;; [__extension__] declspecs asmspec
                (parse-asm-name-specifier uscores span2 parstate))
               ((erp attrspecs & parstate)
                ;; [__extension__] declspecs asmspec [attrspecs]
                (parse-*-attribute-specifier parstate))
               ((erp last-span parstate)
                ;; [__extension__] declspecs asmspec [attrspecs] ;
                (read-punctuator ";" parstate)))
            (retok (make-decl-decl :extension extension
                                   :specs declspecs
                                   :init nil
                                   :asm? asmspec
                                   :attrib attrspecs)
                   (span-join span last-span)
                   parstate)))
         ;; If token2 is the keyword '__attribute__',
         ;; and if GCC extensions are supported,
         ;; we have no initializer declarators;
         ;; we parse the attribute specifiers,
         ;; and the ending semicolon.
         ;; Note that we have no assembler name specifier in this case.
         ((and (token-keywordp token2 "__attribute__")
               (parstate->gcc parstate))
          ;; [__extension__] declspecs __attribute__
          (b* ((parstate (unread-token parstate))
               ((erp attrspecs & parstate)
                ;; [__extension__] declspecs attrspecs
                (parse-*-attribute-specifier parstate))
               ((erp last-span parstate)
                ;; [__extension__] declspecs attrspecs ;
                (read-punctuator ";" parstate)))
            (retok (make-decl-decl :extension extension
                                   :specs declspecs
                                   :init nil
                                   :asm? nil
                                   :attrib attrspecs)
                   (span-join span last-span)
                   parstate)))
         ;; If token2 may start a declarator,
         ;; which is equivalent to saying that
         ;; it may start an initializer declarator,
         ;; we parse the list of one or more initializer declarators,
         ;; then an optional assembler name specifier,
         ;; then a list of zero or more attribute specifiers,
         ;; and then the final semicolon.
         ((token-declarator-start-p token2)
          ;; [__extension__] declspecs declor...
          (b* ((parstate (unread-token parstate))
               ;; [__extension__] declspecs
               ((erp initdeclors & parstate)
                ;; [__extension__] declspecs initdeclors
                (parse-init-declarator-list parstate))
               ((erp asmspec? & parstate)
                ;; [__extension__] declspecs initdeclors [asmspec]
                (if (parstate->gcc parstate)
                    (parse-?-asm-name-specifier parstate)
                  (retok nil (irr-span) parstate)))
               ((erp attrspecs & parstate)
                ;; [__extension__] declspecs initdeclors [asmspec] [attrspecs]
                (if (parstate->gcc parstate)
                    (parse-*-attribute-specifier parstate)
                  (retok nil (irr-span) parstate)))
               ((erp last-span parstate)
                ;; [__extension__] declspecs initdeclors [asmspec] [attrspecs] ;
                (read-punctuator ";" parstate)))
            (retok (make-decl-decl :extension extension
                                   :specs declspecs
                                   :init initdeclors
                                   :asm? asmspec?
                                   :attrib attrspecs)
                   (span-join span last-span)
                   parstate)))
         ;; If token2 is a semicolon,
         ;; we have no initializer declarators.
         ;; If GCC extensions are supported,
         ;; this also means that we have no attribute specifiers.
         ((token-punctuatorp token2 ";") ; [__extension__] declspecs ;
          (retok (make-decl-decl :extension extension
                                 :specs declspecs
                                 :init nil
                                 :asm? nil
                                 :attrib nil)
                 (span-join span span2)
                 parstate))
         ;; If token2 is anything else, it is an error.
         (t ; [__extension__] declspecs other
          (reterr-msg :where (position-to-msg (span->start span2))
                      :expected "a declarator or a semicolon"
                      :found (token-to-msg token2))))))
     ;; If token is the keyword @('_Static_assert'),
     ;; we have an assert declaration.
     ((token-keywordp token "_Static_assert") ; _Static_assert
      (b* (((erp statassert last-span parstate) ; statassert
            (parse-static-assert-declaration span parstate)))
        (retok (decl-statassert statassert)
               (span-join span last-span)
               parstate)))
     ;; If token is anything else, it is an error.
     (t ; other
      (reterr-msg :where (position-to-msg (span->start span))
                  :expected "a declaration specifier ~
                             or the _Static_assert keyword"
                  :found (token-to-msg token)))))

  ///

  (defret parsize-of-parse-declaration-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-declaration-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-declaration-list ((parstate parstatep))
  :returns (mv erp
               (decls decl-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a list of one or more declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We parse the first one, which must be present.
     Then we stop if the next token is an open curly brace,
     because the only place where we parse declaration lists
     is in function definitions, between declarator and body.
     Otherwise we recursively call this function to parse more."))
  (b* (((reterr) nil (irr-span) parstate)
       ((erp decl span parstate) (parse-declaration parstate)) ; decl
       ((erp token & parstate) (read-token parstate)))
    (cond
     ;; If token is an open curly brace, we stop.
     ((token-punctuatorp token "{")  ; decl {
      (retok (list decl) span parstate))
     ;; If token is anything else, we parse more declarations.
     (t ; decl other
      (b* ((parstate (if token (unread-token parstate) parstate)) ; decl
           ((erp decls last-span parstate) ; decl decls
            (parse-declaration-list parstate)))
        (retok (cons decl decls)
               (span-join span last-span)
               parstate)))))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-declaration-list-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-parse-declaration-list-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-declaration-or-statement ((parstate parstatep))
  :returns (mv erp
               (decl/stmt amb?-decl/stmt-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a declaration or a statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when a block item
     may be a declaration or an expression statement,
     which have a complex syntactic overlap,
     as explained in @(tsee amb-decl/stmt).
     Thus, this parsing function returns
     a possibly ambiguous declaration or statement.")
   (xdoc::p
    "We try to parse both a declaration
     and an expression followed by a semicolon
     (note that a declaration always ends in semicolon).
     If only one succeeds, there is no ambiguity,
     and we return either a declaration or a statement (wrapped);
     since the statement is always an expression statement,
     we actually return an expression in this case.
     If both succeed, there is an ambiguity,
     which we return as such.
     If none succeeds, it is an error."))
  (b* (((reterr) (irr-amb?-decl/stmt) (irr-span) parstate)
       (parstate (record-checkpoint parstate)) ; we will backtrack here
       (psize (parsize parstate))
       ((mv erp expr span-expr parstate) (parse-expression parstate)))
    (if erp
        ;; If the parsing of an expression fails,
        ;; we must have a declaration.
        (b* ((parstate (backtrack-checkpoint parstate)) ; backtrack
             ((unless (<= (parsize parstate) psize))
              (raise "Internal error: ~
                        size ~x0 after backtracking exceeds ~
                        size ~x1 before backtracking."
                     (parsize parstate) psize)
              ;; Here we have (> (parsize parstate) psize),
              ;; but we need to return a parser state
              ;; no larger than the initial one,
              ;; so we just return the empty parser state.
              ;; This is just logical: execution stops at the RAISE above.
              (b* ((parstate (init-parstate nil nil parstate)))
                (reterr t)))
             ((erp decl span parstate) (parse-declaration parstate)))
          (retok (amb?-decl/stmt-decl decl) span parstate))
      ;; If the parsing of an expression succeeds,
      ;; we also need to parse a semicolon.
      ;; Note that an expression may be a prefix of a declaration,
      ;; e.g. 'x y;', where 'x' and 'y' are identifiers,
      ;; must be a declaration, even though x could be an expression.
      (b* (((erp token span-semicolon parstate) (read-token parstate))
           (span-stmt (span-join span-expr span-semicolon)))
        (if (token-punctuatorp token ";")
            ;; If a semicolon follows,
            ;; the parsing of an expression statement has succeeded,
            ;; but we must see whether we can also parse a declaration.
            ;; So we backtrack and we attempt to parse a declaration.
            (b* ((parstate (backtrack-checkpoint parstate)) ; backtrack
                 ((unless (<= (parsize parstate) psize))
                  (raise "Internal error: ~
                            size ~x0 after backtracking exceeds ~
                            size ~x1 before backtracking."
                         (parsize parstate) psize)
                  ;; Here we have (> (parsize parstate) psize),
                  ;; but we need to return a parser state
                  ;; no larger than the initial one,
                  ;; so we just return the empty parser state.
                  ;; This is just logical:
                  ;; execution stops at the RAISE above.
                  (b* ((parstate (init-parstate nil nil parstate)))
                    (reterr t)))
                 (parstate
                  (record-checkpoint parstate)) ; we may backtrack again
                 ((mv erp decl span-decl parstate)
                  (parse-declaration parstate)))
              (if erp
                  ;; If the parsing of a declaration fails,
                  ;; we have an expression statement.
                  ;; We need to backtrack and re-parse it right now,
                  ;; but we will look into improving this inefficiency.
                  (b* ((parstate (backtrack-checkpoint parstate)) ; backtrack
                       ((unless (<= (parsize parstate) psize))
                        (raise "Internal error: ~
                              size ~x0 after backtracking exceeds ~
                              size ~x1 before backtracking."
                               (parsize parstate) psize)
                        ;; Here we have (> (parsize parstate) psize),
                        ;; but we need to return a parser state
                        ;; no larger than the initial one,
                        ;; so we just return the empty parser state.
                        ;; This is just logical:
                        ;; execution stops at the RAISE above.
                        (b* ((parstate (init-parstate nil nil parstate)))
                          (reterr t)))
                       ((mv erp expr1 span-expr1 parstate)
                        (parse-expression parstate))
                       ((when erp)
                        (raise "Internal error: ~
                              parsing the same expression ~x0 twice ~
                              gives the error ~x1."
                               expr erp)
                        (reterr t))
                       ((unless (equal expr1 expr))
                        (raise "Internal error: ~
                              parsing the same expression ~x0 twice ~
                              gives a different expression ~x1."
                               expr expr1)
                        (reterr t))
                       ((unless (equal span-expr1 span-expr))
                        (raise "Internal error: ~
                              parsing the same expression ~x0 twice ~
                              gives a different span ~x1 from ~x2."
                               expr span-expr1 span-expr)
                        (reterr t))
                       ((mv erp span-semicolon1 parstate)
                        (read-punctuator ";" parstate))
                       ((when erp)
                        (raise "Internal error: ~
                              parsing the semicolon twice ~
                              after the same expression ~x0 ~
                              gives the error ~x1."
                               expr erp)
                        (reterr t))
                       ((unless (equal span-semicolon1 span-semicolon))
                        (raise "Internal error: ~
                              parsing the same semicolon twice ~
                              after the same expression ~x0 ~
                              gives a span ~x1 different from ~
                              the span ~x2 from the previous time."
                               expr span-semicolon1 span-semicolon)
                        (reterr t)))
                    (retok (amb?-decl/stmt-stmt expr)
                           (span-join span-expr span-semicolon)
                           parstate))
                ;; If the parsing of a declaration succeeds,
                ;; we return an ambiguous declaration or statement.
                ;; We double-check that the spans are the same,
                ;; which is always expected to succeed.
                (b* ((parstate (clear-checkpoint parstate)) ; no backtracking
                     ((unless (equal span-stmt span-decl))
                      (raise "Internal error:
                              span ~x0 of expression statement ~x1 ~
                              differs from ~
                              span ~x2 of declaration ~x3."
                             span-stmt expr span-decl decl)
                      (reterr t)))
                  (retok (amb?-decl/stmt-ambig
                          (make-amb-decl/stmt :stmt expr
                                              :decl decl))
                         span-stmt ; = span-decl
                         parstate))))
          ;; If a semicolon does not follow the expression,
          ;; we cannot have an expression statement.
          ;; Thus, we backtrack and proceed to parse a declaration.
          (b* ((parstate (backtrack-checkpoint parstate)) ; backtrack
               ((unless (<= (parsize parstate) psize))
                (raise "Internal error: ~
                        size ~x0 after backtracking exceeds ~
                        size ~x1 before backtracking."
                       (parsize parstate) psize)
                ;; Here we have (> (parsize parstate) psize),
                ;; but we need to return a parser state
                ;; no larger than the initial one,
                ;; so we just return the empty parser state.
                ;; This is just logical:
                ;; execution stops at the RAISE above.
                (b* ((parstate (init-parstate nil nil parstate)))
                  (reterr t)))
               ((erp decl span parstate) (parse-declaration parstate)))
            (retok (amb?-decl/stmt-decl decl) span parstate))))))

  ///

  (defret parsize-of-parse-declaration-or-statement-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-declaration-or-statement-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines parse-stmts/blocks
  :short "Parse statements, blocks, and related entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "This clique of mutually recursive functions shares some characteristics
     with the clique to parse expressions, declarations, and related entities.
     See @(tsee parse-exprs/decls) for a discussion of
     technicalities that also apply to this clique."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-statement ((parstate parstatep))
    :returns (mv erp
                 (stmt stmtp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-stmts/blocks)
    :short "Parse a statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "Most statements start with distinct keywords or punctuators
       (one punctuator, the open curly brace),
       but both labeled statements and expression statements
       may start with an identifier.
       However, for a labeled statement,
       the token after the identifier is a colon,
       which cannot be an expression.
       So we are able to distinguish all kinds of statements
       based on the first one or two tokens.")
     (xdoc::p
      "The well-known dangling-else grammatical ambiguity is dealt with
       by associating the @('else') with the closest @('if'),
       as required in [C:6.8.4/3].")
     (xdoc::p
      "There is a syntactic overlap between the two kinds of @('for') loops,
       the one with an expression and the one with a declaration.
       An identifier may be a declaration specifier
       or (the start of) an expression.
       For now we handle the situation approximately:
       if the token there may start an expresison,
       we commit to parsing an expression;
       otherwise we parse a declaration.
       In other words, we may fail to accept the case of
       a declaration that starts with a @('typedef') name for now.
       We plan to rectify this situation soon."))
    (b* (((reterr) (irr-stmt) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is an identifier,
       ;; we could have a labeled statement or an expression statement.
       ;; So we need to read another token.
       ((and token (token-case token :ident)) ; ident
        (b* ((ident (token-ident->unwrap token))
             ((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is a colon,
           ;; we must have a labeled statement.
           ((token-punctuatorp token2 ":") ; ident :
            (b* (((erp stmt last-span parstate) ; ident : stmt
                  (parse-statement parstate)))
              (retok (make-stmt-labeled :label (label-name ident)
                                        :stmt stmt)
                     (span-join span last-span)
                     parstate)))
           ;; If token2 is not a colon,
           ;; we put it back along with the previous token,
           ;; and we attempt to parse an expression followed by a semicolon.
           (t ; ident other
            (b* ((parstate
                  (if token2 (unread-token parstate) parstate)) ; ident
                 (parstate (unread-token parstate)) ;
                 ((erp expr span parstate) (parse-expression parstate)) ; expr
                 ((erp last-span parstate)
                  (read-punctuator ";" parstate))) ; expr ;
              (retok (stmt-expr expr)
                     (span-join span last-span)
                     parstate))))))
       ;; If token is an open curly brace,
       ;; we must have a compound statement.
       ((token-punctuatorp token "{") ; {
        (b* (((erp token2 span2 parstate) (read-token parstate)))
          (cond
           ;; If token2 is a closed curly brace,
           ;; we have an empty compound statement.
           ((token-punctuatorp token2 "}") ; { }
            (retok (stmt-compound nil)
                   (span-join span span2)
                   parstate))
           ;; Otherwise, we parse a list of one or more block items.
           (t ; { other
            (b* ((parstate (if token2 (unread-token parstate) parstate)) ; {
                 ((erp items & parstate) ; { blockitems
                  (parse-block-item-list parstate))
                 ((erp last-span parstate) ; { blockitems }
                  (read-punctuator "}" parstate)))
              (retok (stmt-compound items)
                     (span-join span last-span)
                     parstate))))))
       ;; If token is a semicolon,
       ;; we have an expression statement without expression.
       ((token-punctuatorp token ";") ; ;
        (retok (stmt-expr nil) span parstate))
       ;; If token is the 'case' keyword,
       ;; we must have a labeled statement.
       ((token-keywordp token "case") ; case
        (b* (((erp cexpr & parstate) ; case constexpr
              (parse-constant-expression parstate))
             ((erp & parstate)
              (read-punctuator ":" parstate)) ; case constexpr :
             ((erp stmt last-span parstate) ; case constexpr : stmt
              (parse-statement parstate)))
          (retok (make-stmt-labeled :label (label-const cexpr)
                                    :stmt stmt)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the default keyword,
       ;; we must have a labeled statement.
       ((token-keywordp token "default") ; default
        (b* (((erp & parstate) (read-punctuator ":" parstate)) ; default :
             ((erp stmt last-span parstate) ; default : stmt
              (parse-statement parstate)))
          (retok (make-stmt-labeled :label (label-default)
                                    :stmt stmt)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the 'goto' keyword, we have a jump statement.
       ((token-keywordp token "goto") ; goto
        (b* (((erp ident & parstate) (read-identifier parstate)) ; goto ident
             ((erp last-span parstate) ; goto ident ;
              (read-punctuator ";" parstate)))
          (retok (stmt-goto ident)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword 'continue', we have a jump statement.
       ((token-keywordp token "continue") ; continue
        (b* (((erp last-span parstate) ; continue ;
              (read-punctuator ";" parstate)))
          (retok (stmt-continue)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword 'break', we have a jump statement.
       ((token-keywordp token "break") ; break
        (b* (((erp last-span parstate) ; break ;
              (read-punctuator ";" parstate)))
          (retok (stmt-break)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword 'return', we have a jump statement.
       ;; There may be an expression or not.
       ((token-keywordp token "return") ; return
        (b* (((erp token2 span2 parstate) (read-token parstate)))
          (cond
           ;; If token2 may start an expression, we must have an expression.
           ((token-expression-start-p token2) ; return expr...
            (b* ((parstate (unread-token parstate)) ; return
                 ((erp expr & parstate)
                  (parse-expression parstate)) ; return expr
                 ((erp last-span parstate) ; return expr ;
                  (read-punctuator ";" parstate)))
              (retok (stmt-return expr)
                     (span-join span last-span)
                     parstate)))
           ;; If token2 is a semicolon, there is no expression.
           ((token-punctuatorp token2 ";") ; return ;
            (retok (stmt-return nil)
                   (span-join span span2)
                   parstate))
           ;; If token2 is anything else, it is an error.
           (t ; return other
            (reterr-msg :where (position-to-msg (span->start span2))
                        :expected "an expression or a semicolon"
                        :found (token-to-msg token2))))))
       ;; If token is the keyword 'if', we have a selection statement.
       ;; If there is an 'else'
       ;; after the parenthesized expression and the statement,
       ;; we continue parsing that as part of the current selection statement
       ;; (see documenttion of this function above).
       ((token-keywordp token "if") ; if
        (b* (((erp & parstate) (read-punctuator "(" parstate)) ; if (
             ((erp expr & parstate) (parse-expression parstate)) ; if ( expr
             ((erp & parstate) (read-punctuator ")" parstate)) ; if ( expr )
             (psize (parsize parstate))
             ((erp stmt stmt-span parstate) ; if ( expr ) stmt
              (parse-statement parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is the 'else' keyword,
           ;; we continue to parse this selection statement.
           ((token-keywordp token2 "else") ; if ( expr ) stmt else
            (b* (((erp stmt-else last-span parstate)
                  ;; if ( expr ) stmt else stmt
                  (parse-statement parstate)))
              (retok (make-stmt-ifelse :test expr
                                       :then stmt
                                       :else stmt-else)
                     (span-join span last-span)
                     parstate)))
           ;; If token is not the 'else' keyword,
           ;; we have an 'if' statement without 'else'.
           (t ; if ( expr ) stmt other
            (b* ((parstate ; if ( expr ) stmt
                  (if token2 (unread-token parstate) parstate)))
              (retok (make-stmt-if :test expr
                                   :then stmt)
                     (span-join span stmt-span)
                     parstate))))))
       ;; If token is the 'switch' keyword, we have a selection statement.
       ((token-keywordp token "switch") ; switch
        (b* (((erp & parstate) (read-punctuator "(" parstate)) ; switch (
             ((erp expr & parstate) (parse-expression parstate)) ; switch ( expr
             ((erp & parstate) (read-punctuator ")" parstate)) ; switch ( expr )
             ((erp stmt last-span parstate) ; switch ( expr ) stmt
              (parse-statement parstate)))
          (retok (make-stmt-switch :target expr
                                   :body stmt)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the 'while' keyword, we have an iteration statement.
       ((token-keywordp token "while") ; while
        (b* (((erp & parstate) (read-punctuator "(" parstate)) ; while (
             ((erp expr & parstate) (parse-expression parstate)) ; while ( expr
             ((erp & parstate) (read-punctuator ")" parstate)) ; while ( expr )
             ((erp stmt last-span parstate) ; while ( expr ) stmt
              (parse-statement parstate)))
          (retok (make-stmt-while :test expr
                                  :body stmt)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the 'do' keyword, we have an iteration statement.
       ((token-keywordp token "do") ; do
        (b* (((erp stmt & parstate) (parse-statement parstate)) ; do stmt
             ((erp & parstate) (read-keyword "while" parstate)) ; do stmt while
             ((erp & parstate) (read-punctuator "(" parstate)) ; do stmt while (
             ((erp expr & parstate) ; do stmt while ( expr
              (parse-expression parstate))
             ((erp & parstate) ; do stmt while ( expr )
              (read-punctuator ")" parstate))
             ((erp last-span parstate) ; do stmt while ( expr ) ;
              (read-punctuator ";" parstate)))
          (retok (make-stmt-dowhile :body stmt
                                    :test expr)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the 'for' keyword, we have an iteration statement.
       ((token-keywordp token "for") ; for
        (b* (((erp & parstate) (read-punctuator "(" parstate)) ; for (
             ((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is a semicolon,
           ;; we have no initializing expression or declaration.
           ((token-punctuatorp token2 ";") ; for ( ;
            (b* (((erp token3 span3 parstate) (read-token parstate)))
              (cond
               ;; If token3 may start an expression,
               ;; we must have a test expression.
               ((token-expression-start-p token3) ; for ( ; expr...
                (b* ((parstate (unread-token parstate)) ; for ( ;
                     ((erp test-expr & parstate) ; for ( ; expr
                      (parse-expression parstate))
                     ((erp & parstate) ; for ( ; expr ;
                      (read-punctuator ";" parstate))
                     ((erp token4 span4 parstate) (read-token parstate)))
                  (cond
                   ;; If token4 may start an expression,
                   ;; we must have an update expression.
                   ((token-expression-start-p token4) ; for ( ; expr ; expr...
                    (b* ((parstate (unread-token parstate)) ; for ( ; expr ;
                         ((erp next-expr & parstate) ; for ( ; expr ; expr
                          (parse-expression parstate))
                         ((erp & parstate) ; for ( ; expr ; expr )
                          (read-punctuator ")" parstate))
                         ((erp stmt last-span parstate)
                          ;; for ( ; expr ; expr ) stmt
                          (parse-statement parstate)))
                      (retok (make-stmt-for-expr :init nil
                                                 :test test-expr
                                                 :next next-expr
                                                 :body stmt)
                             (span-join span last-span)
                             parstate)))
                   ;; If token4 is a closed parenthesis,
                   ;; we have no update expression.
                   ((token-punctuatorp token4 ")") ; for ( ; expr ; )
                    (b* (((erp stmt last-span parstate) ; for ( ; expr ; ) stmt
                          (parse-statement parstate)))
                      (retok (make-stmt-for-expr :init nil
                                                 :test test-expr
                                                 :next nil
                                                 :body stmt)
                             (span-join span last-span)
                             parstate)))
                   ;; If token4 is anything else, it is an error.
                   (t ; for ( ; expr ; other
                    (reterr-msg :where (position-to-msg (span->start span4))
                                :expected "an expression ~
                                           or a closed parenthesis"
                                :found (token-to-msg token4))))))
               ;; If token3 is a semicolon, we have no test expression.
               ((token-punctuatorp token3 ";") ; for ( ; ;
                (b* (((erp token4 span4 parstate) (read-token parstate)))
                  (cond
                   ;; If token4 may start an expression,
                   ;; we must have an update expression.
                   ((token-expression-start-p token4) ; for ( ; ; expr...
                    (b* ((parstate (unread-token parstate)) ; for ( ; ;
                         ((erp next-expr & parstate) ; for ( ; ; expr
                          (parse-expression parstate))
                         ((erp & parstate) ; for ( ; ; expr )
                          (read-punctuator ")" parstate))
                         ((erp stmt last-span parstate) ; for ( ; ; expr ) stmt
                          (parse-statement parstate)))
                      (retok (make-stmt-for-expr :init nil
                                                 :test nil
                                                 :next next-expr
                                                 :body stmt)
                             (span-join span last-span)
                             parstate)))
                   ;; If token4 is a closed parenthesis,
                   ;; we have no udpate expression.
                   ((token-punctuatorp token4 ")") ; for ( ; ; )
                    (b* (((erp stmt last-span parstate) ; for ( ; ; ) stmt
                          (parse-statement parstate)))
                      (retok (make-stmt-for-expr :init nil
                                                 :test nil
                                                 :next nil
                                                 :body stmt)
                             (span-join span last-span)
                             parstate)))
                   ;; If token4 is anything else, it is an error.
                   (t ; for ( ; ; other
                    (reterr-msg :where (position-to-msg (span->start span4))
                                :expected "an expression ~
                                           or a closed parenthesis"
                                :found (token-to-msg token4))))))
               ;; If token3 is anything else, it is an error.
               (t ; for ( ; other
                (reterr-msg :where (position-to-msg (span->start span3))
                            :expected "an expression ~
                                       or a semicolon"
                            :found (token-to-msg token3))))))
           ;; If token2 is not a semicolon,
           ;; we may have an initializing expression or declaration.
           ;; Since the initializing expression must be followed by semicolon,
           ;; we are in the same situation as when parsing
           ;; a declaration or an expression statement,
           ;; so we use the parsing function for that.
           (t ; for ( other
            (b* ((parstate (if token2 (unread-token parstate) parstate)) ; for (
                 ((erp decl/stmt & parstate) ; for ( decl/stmt
                  (parse-declaration-or-statement parstate)))
              (amb?-decl/stmt-case
               decl/stmt
               ;; If the initialization part is a declaration,
               ;; the 'for' is not ambiguous, and we parse the rest.
               :decl
               (b* ((decl (amb?-decl/stmt-decl->unwrap decl/stmt))
                    ((erp token3 span3 parstate) (read-token parstate)))
                 (cond
                  ;; If token3 may start an expression,
                  ;; we must have a test expression.
                  ((token-expression-start-p token3) ; for ( ; expr...
                   (b* ((parstate (unread-token parstate)) ; for ( ;
                        ((erp test-expr & parstate) ; for ( ; expr
                         (parse-expression parstate))
                        ((erp & parstate) ; for ( ; expr ;
                         (read-punctuator ";" parstate))
                        ((erp token4 span4 parstate) (read-token parstate)))
                     (cond
                      ;; If token4 may start an expression,
                      ;; we must have an update expression.
                      ((token-expression-start-p token4)
                       ;; for ( ; expr ; expr...
                       (b* ((parstate (unread-token parstate)) ; for ( ; expr ;
                            ((erp next-expr & parstate) ; for ( ; expr ; expr
                             (parse-expression parstate))
                            ((erp & parstate) ; for ( ; expr ; expr )
                             (read-punctuator ")" parstate))
                            ((erp stmt last-span parstate)
                             ;; for ( ; expr ; expr ) stmt
                             (parse-statement parstate)))
                         (retok (make-stmt-for-decl :init decl
                                                    :test test-expr
                                                    :next next-expr
                                                    :body stmt)
                                (span-join span last-span)
                                parstate)))
                      ;; If token4 is a closed parenthesis,
                      ;; we have no update expression.
                      ((token-punctuatorp token4 ")") ; for ( ; expr ; )
                       (b* (((erp stmt last-span parstate)
                              ;; for ( ; expr ; ) stmt
                             (parse-statement parstate)))
                         (retok (make-stmt-for-decl :init decl
                                                    :test test-expr
                                                    :next nil
                                                    :body stmt)
                                (span-join span last-span)
                                parstate)))
                      ;; If token4 is anything else, it is an error.
                      (t ; for ( ; expr ; other
                       (reterr-msg :where (position-to-msg (span->start span4))
                                   :expected "an expression ~
                                           or a closed parenthesis"
                                   :found (token-to-msg token4))))))
                  ;; If token3 is a semicolon, we have no test expression.
                  ((token-punctuatorp token3 ";") ; for ( ; ;
                   (b* (((erp token4 span4 parstate) (read-token parstate)))
                     (cond
                      ;; If token4 may start an expression,
                      ;; we must have an update expression.
                      ((token-expression-start-p token4) ; for ( ; ; expr...
                       (b* ((parstate (unread-token parstate)) ; for ( ; ;
                            ((erp next-expr & parstate) ; for ( ; ; expr
                             (parse-expression parstate))
                            ((erp & parstate) ; for ( ; ; expr )
                             (read-punctuator ")" parstate))
                            ((erp stmt last-span parstate)
                              ;; for ( ; ; expr ) stmt
                             (parse-statement parstate)))
                         (retok (make-stmt-for-decl :init decl
                                                    :test nil
                                                    :next next-expr
                                                    :body stmt)
                                (span-join span last-span)
                                parstate)))
                      ;; If token4 is a closed parenthesis,
                      ;; we have no udpate expression.
                      ((token-punctuatorp token4 ")") ; for ( ; ; )
                       (b* (((erp stmt last-span parstate) ; for ( ; ; ) stmt
                             (parse-statement parstate)))
                         (retok (make-stmt-for-decl :init decl
                                                    :test nil
                                                    :next nil
                                                    :body stmt)
                                (span-join span last-span)
                                parstate)))
                      ;; If token4 is anything else, it is an error.
                      (t ; for ( ; ; other
                       (reterr-msg :where (position-to-msg (span->start span4))
                                   :expected "an expression ~
                                           or a closed parenthesis"
                                   :found (token-to-msg token4))))))
                  ;; If token3 is anything else, it is an error.
                  (t ; for ( ; other
                   (reterr-msg :where (position-to-msg (span->start span3))
                               :expected "an expression ~
                                       or a semicolon"
                               :found (token-to-msg token3)))))
               ;; If the initialization part is an expression,
               ;; the 'for' is not ambiguous, and we parse the rest.
               :stmt
               (b* ((expr (amb?-decl/stmt-stmt->unwrap decl/stmt))
                    ((erp token3 span3 parstate) (read-token parstate)))
                 (cond
                  ;; If token3 may start an expression,
                  ;; we must have a test expression.
                  ((token-expression-start-p token3) ; for ( ; expr...
                   (b* ((parstate (unread-token parstate)) ; for ( ;
                        ((erp test-expr & parstate) ; for ( ; expr
                         (parse-expression parstate))
                        ((erp & parstate) ; for ( ; expr ;
                         (read-punctuator ";" parstate))
                        ((erp token4 span4 parstate) (read-token parstate)))
                     (cond
                      ;; If token4 may start an expression,
                      ;; we must have an update expression.
                      ((token-expression-start-p token4)
                        ;; for ( ; expr ; expr...
                       (b* ((parstate (unread-token parstate)) ; for ( ; expr ;
                            ((erp next-expr & parstate) ; for ( ; expr ; expr
                             (parse-expression parstate))
                            ((erp & parstate) ; for ( ; expr ; expr )
                             (read-punctuator ")" parstate))
                            ((erp stmt last-span parstate)
                             ;; for ( ; expr ; expr ) stmt
                             (parse-statement parstate)))
                         (retok (make-stmt-for-expr :init expr
                                                    :test test-expr
                                                    :next next-expr
                                                    :body stmt)
                                (span-join span last-span)
                                parstate)))
                      ;; If token4 is a closed parenthesis,
                      ;; we have no update expression.
                      ((token-punctuatorp token4 ")") ; for ( ; expr ; )
                       (b* (((erp stmt last-span parstate)
                              ;; for ( ; expr ; ) stmt
                             (parse-statement parstate)))
                         (retok (make-stmt-for-expr :init expr
                                                    :test test-expr
                                                    :next nil
                                                    :body stmt)
                                (span-join span last-span)
                                parstate)))
                      ;; If token4 is anything else, it is an error.
                      (t ; for ( ; expr ; other
                       (reterr-msg :where (position-to-msg (span->start span4))
                                   :expected "an expression ~
                                           or a closed parenthesis"
                                   :found (token-to-msg token4))))))
                  ;; If token3 is a semicolon, we have no test expression.
                  ((token-punctuatorp token3 ";") ; for ( ; ;
                   (b* (((erp token4 span4 parstate) (read-token parstate)))
                     (cond
                      ;; If token4 may start an expression,
                      ;; we must have an update expression.
                      ((token-expression-start-p token4) ; for ( ; ; expr...
                       (b* ((parstate (unread-token parstate)) ; for ( ; ;
                            ((erp next-expr & parstate) ; for ( ; ; expr
                             (parse-expression parstate))
                            ((erp & parstate) ; for ( ; ; expr )
                             (read-punctuator ")" parstate))
                            ((erp stmt last-span parstate)
                              ;; for ( ; ; expr ) stmt
                             (parse-statement parstate)))
                         (retok (make-stmt-for-expr :init expr
                                                    :test nil
                                                    :next next-expr
                                                    :body stmt)
                                (span-join span last-span)
                                parstate)))
                      ;; If token4 is a closed parenthesis,
                      ;; we have no udpate expression.
                      ((token-punctuatorp token4 ")") ; for ( ; ; )
                       (b* (((erp stmt last-span parstate) ; for ( ; ; ) stmt
                             (parse-statement parstate)))
                         (retok (make-stmt-for-expr :init expr
                                                    :test nil
                                                    :next nil
                                                    :body stmt)
                                (span-join span last-span)
                                parstate)))
                      ;; If token4 is anything else, it is an error.
                      (t ; for ( ; ; other
                       (reterr-msg :where (position-to-msg (span->start span4))
                                   :expected "an expression ~
                                           or a closed parenthesis"
                                   :found (token-to-msg token4))))))
                  ;; If token3 is anything else, it is an error.
                  (t ; for ( ; other
                   (reterr-msg :where (position-to-msg (span->start span3))
                               :expected "an expression ~
                                       or a semicolon"
                               :found (token-to-msg token3)))))
               ;; If the initialization part is ambiguous,
               ;; we have an ambiguous 'for', and we parse the rest.
               :ambig
               (b* ((decl/expr (amb?-decl/stmt-ambig->unwrap decl/stmt))
                    ((erp token3 span3 parstate) (read-token parstate)))
                 (cond
                  ;; If token3 may start an expression,
                  ;; we must have a test expression.
                  ((token-expression-start-p token3) ; for ( ; expr...
                   (b* ((parstate (unread-token parstate)) ; for ( ;
                        ((erp test-expr & parstate) ; for ( ; expr
                         (parse-expression parstate))
                        ((erp & parstate) ; for ( ; expr ;
                         (read-punctuator ";" parstate))
                        ((erp token4 span4 parstate) (read-token parstate)))
                     (cond
                      ;; If token4 may start an expression,
                      ;; we must have an update expression.
                      ((token-expression-start-p token4)
                        ;; for ( ; expr ; expr...
                       (b* ((parstate (unread-token parstate)) ; for ( ; expr ;
                            ((erp next-expr & parstate) ; for ( ; expr ; expr
                             (parse-expression parstate))
                            ((erp & parstate) ; for ( ; expr ; expr )
                             (read-punctuator ")" parstate))
                            ((erp stmt last-span parstate)
                             ;; for ( ; expr ; expr ) stmt
                             (parse-statement parstate)))
                         (retok (make-stmt-for-ambig :init decl/expr
                                                     :test test-expr
                                                     :next next-expr
                                                     :body stmt)
                                (span-join span last-span)
                                parstate)))
                      ;; If token4 is a closed parenthesis,
                      ;; we have no update expression.
                      ((token-punctuatorp token4 ")") ; for ( ; expr ; )
                       (b* (((erp stmt last-span parstate)
                              ;; for ( ; expr ; ) stmt
                             (parse-statement parstate)))
                         (retok (make-stmt-for-ambig :init decl/expr
                                                     :test test-expr
                                                     :next nil
                                                     :body stmt)
                                (span-join span last-span)
                                parstate)))
                      ;; If token4 is anything else, it is an error.
                      (t ; for ( ; expr ; other
                       (reterr-msg :where (position-to-msg (span->start span4))
                                   :expected "an expression ~
                                           or a closed parenthesis"
                                   :found (token-to-msg token4))))))
                  ;; If token3 is a semicolon, we have no test expression.
                  ((token-punctuatorp token3 ";") ; for ( ; ;
                   (b* (((erp token4 span4 parstate) (read-token parstate)))
                     (cond
                      ;; If token4 may start an expression,
                      ;; we must have an update expression.
                      ((token-expression-start-p token4) ; for ( ; ; expr...
                       (b* ((parstate (unread-token parstate)) ; for ( ; ;
                            ((erp next-expr & parstate) ; for ( ; ; expr
                             (parse-expression parstate))
                            ((erp & parstate) ; for ( ; ; expr )
                             (read-punctuator ")" parstate))
                            ((erp stmt last-span parstate)
                              ;; for ( ; ; expr ) stmt
                             (parse-statement parstate)))
                         (retok (make-stmt-for-ambig :init decl/expr
                                                     :test nil
                                                     :next next-expr
                                                     :body stmt)
                                (span-join span last-span)
                                parstate)))
                      ;; If token4 is a closed parenthesis,
                      ;; we have no udpate expression.
                      ((token-punctuatorp token4 ")") ; for ( ; ; )
                       (b* (((erp stmt last-span parstate) ; for ( ; ; ) stmt
                             (parse-statement parstate)))
                         (retok (make-stmt-for-ambig :init decl/expr
                                                     :test nil
                                                     :next nil
                                                     :body stmt)
                                (span-join span last-span)
                                parstate)))
                      ;; If token4 is anything else, it is an error.
                      (t ; for ( ; ; other
                       (reterr-msg :where (position-to-msg (span->start span4))
                                   :expected "an expression ~
                                           or a closed parenthesis"
                                   :found (token-to-msg token4))))))
                  ;; If token3 is anything else, it is an error.
                  (t ; for ( ; other
                   (reterr-msg :where (position-to-msg (span->start span3))
                               :expected "an expression ~
                                       or a semicolon"
                               :found (token-to-msg token3)))))))))))
       ;; If token may start an expression,
       ;; we must have an expression statement.
       ((token-expression-start-p token) ; expr...
        (b* ((parstate (unread-token parstate)) ;
             ((erp expr span parstate) (parse-expression parstate)) ; expr
             ((erp last-span parstate) (read-punctuator ";" parstate))) ; expr ;
          (retok (stmt-expr expr)
                 (span-join span last-span)
                 parstate)))
       ;; If token is anything else, it is an error.
       (t
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or a keyword in {~
                               break, ~
                               case, ~
                               continue, ~
                               default, ~
                               do, ~
                               for, ~
                               goto, ~
                               if, ~
                               return, ~
                               switch, ~
                               while~
                               } ~
                               or a punctuator in {~
                               \"++\", ~
                               \"--\", ~
                               \"+\", ~
                               \"-\", ~
                               \"~~\", ~
                               \"!\", ~
                               \"*\", ~
                               \"&\", ~
                               \"(\", ~
                               \"{\", ~
                               \";\"~
                               }"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-block-item ((parstate parstatep))
    :returns (mv erp
                 (item block-itemp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-stmts/blocks)
    :short "Parse a block item."
    :long
    (xdoc::topstring
     (xdoc::p
      "As explained in @(tsee amb-decl/stmt),
       there is a complex syntactic overlap
       between expression statements and declarations,
       which are the two kinds of block items;
       the overlap cannot be disambiguated purely syntactically.
       Thus, under the appropriate conditions,
       we parse a possibly ambiguous declaration or statement."))
    (b* (((reterr) (irr-block-item) (irr-span) parstate)
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is an identifier, we need to read another token.
       ((and token (token-case token :ident)) ; ident
        (b* (((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is a colon, we must have a labeled statement.
           ;; We put back colon and label, and parse a statement.
           ((token-punctuatorp token2 ":") ; ident :
            (b* ((parstate (unread-token parstate)) ; ident
                 (parstate (unread-token parstate)) ;
                 ((erp stmt span parstate) (parse-statement parstate))) ; stmt
              (retok (block-item-stmt stmt) span parstate)))
           ;; Otherwise, we may have a declaration or an expression statement,
           ;; so we read a possibly ambiguous declaration or statement.
           (t ; ident other
            (b* ((parstate (if token2 (unread-token parstate) parstate)) ; ident
                 (parstate (unread-token parstate)) ;
                 ((erp decl/stmt span parstate) ; decl/stmt
                  (parse-declaration-or-statement parstate)))
              (amb?-decl/stmt-case
               decl/stmt
               ;; If we parse an unambiguous declaration,
               ;; we return a block item that is a declaration.
               :decl
               (retok (block-item-decl decl/stmt.unwrap)
                      span
                      parstate)
               ;; If we parse an unambiguous statement,
               ;; we return a block item that is a statement.
               :stmt
               (retok (block-item-stmt (stmt-expr decl/stmt.unwrap))
                      span
                      parstate)
               ;; If we parse an ambiguous declaration or statement,
               ;; we return an ambiguous block item.
               :ambig
               (retok (block-item-ambig decl/stmt.unwrap)
                      span
                      parstate)))))))
       ;; If token may start a declaration specifier,
       ;; since we have already considered the case of an identifier above,
       ;; we must have a declaration.
       ((token-declaration-specifier-start-p token) ; declspec...
        (b* ((parstate (unread-token parstate)) ;
             ((erp decl span parstate) ; decl
              (parse-declaration parstate)))
          (retok (block-item-decl decl) span parstate)))
       ;; Otherwise, we must have a statement.
       (t ; other
        (b* ((parstate (if token (unread-token parstate) parstate)) ;
             ((erp stmt span parstate) ; stmt
              (parse-statement parstate)))
          (retok (block-item-stmt stmt) span parstate)))))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-block-item-list ((parstate parstatep))
    :returns (mv erp
                 (items block-item-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-stmts/blocks)
    :short "Parse a list of one or more block items."
    :long
    (xdoc::topstring
     (xdoc::p
      "We parse the first block item, which must be present.
       Then, unless we have a closed curly brace,
       we recursively parse one or more block items."))
    (b* (((reterr) nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp item span parstate) (parse-block-item parstate)) ; item
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is a closed curly brace, we have reached the end of the list.
       ((token-punctuatorp token "}") ; item }
        (b* ((parstate (unread-token parstate))) ; item
          (retok (list item) span parstate)))
       ;; Otherwise, we recursively parse more block items,
       ;; and we combine them with the one just parsed.
       (t ; item other
        (b* ((parstate (if token (unread-token parstate) parstate)) ; item
             ((erp items last-span parstate) ; item items
              (parse-block-item-list parstate)))
          (retok (cons item items)
                 (span-join span last-span)
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable nfix fix)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual parsize-of-parse-stmts/blocks-uncond
    (defret parsize-of-parse-statement-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-statement)
    (defret parsize-of-parse-block-item-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-block-item)
    (defret parsize-of-parse-block-item-list-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-block-item-list)
    :hints (("Goal" :expand ((parse-statement parstate)
                             (parse-block-item parstate)
                             (parse-block-item-list parstate)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual parsize-of-parse-stmts/blocks-cond
    (defret parsize-of-parse-statement-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-statement)
    (defret parsize-of-parse-block-item-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-block-item)
    (defret parsize-of-parse-block-item-list-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-block-item-list)
    :hints (("Goal"
             :in-theory (enable fix)
             :expand ((parse-statement parstate)
                      (parse-block-item parstate)
                      (parse-block-item-list parstate)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards parse-statement))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-external-declaration ((parstate parstatep))
  :returns (mv erp
               (extdecl extdeclp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse an external declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "An external declaration is
     either a function definition,
     which starts with a non-empty sequence of declaration specifiers,
     or a declaration,
     which also starts with a non-empty sequence of declaration specifiers,
     unless it is a static assert declaration,
     which starts with the keyword @('_Static_assert').")
   (xdoc::p
    "No declaration specifier starts with the keyword @('_Static_assert'),
     so this keyword tells us that we must have a static assert declaration.
     In this case, we parse a static assert declaration.")
   (xdoc::p
    "Otherwise, we read one or more declaration specifiers,
     since those are present both in declarations and in function definitions.
     Then we must have a declarator in either case,
     but based on what follows it,
     we can decide whether we have a declarator or a function definition.")
   (xdoc::p
    "If GCC extensions are supported, we must also taken into account
     the possible presence of attributes and assembler name specifiers,
     as well as of an @('__external__') keyword."))
  (b* (((reterr) (irr-extdecl) (irr-span) parstate)
       ((erp token span parstate) (read-token parstate)))
    (cond
     ;; If token is the keyword '_Static_assert',
     ;; we have a static assertion declaration.
     ((token-keywordp token "_Static_assert") ; _Static_assert
      (b* (((erp statassert span parstate) ; statassert
            (parse-static-assert-declaration span parstate)))
        (retok (extdecl-decl (decl-statassert statassert)) span parstate)))
     ;; Otherwise, we must have a list of one or more declaration specifiers,
     ;; possibly preceded by an '__extension__' keyword
     ;; if GCC extensions are supported.
     (t
      (b* (((mv extension parstate)
            (if (and (token-keywordp token "__extension__")
                     (parstate->gcc parstate))
                (mv t parstate)
              (b* ((parstate (if token (unread-token parstate) parstate)))
                (mv nil parstate))))
           ;; [__extension__]
           ((erp declspecs span parstate) ; [__extension__] declspecs
            (parse-declaration-specifiers nil parstate))
           ((erp token2 span2 parstate) (read-token parstate)))
        (cond
         ;; If token2 is a semicolon,
         ;; we must have a declaration without initialization declarators.
         ((token-punctuatorp token2 ";") ; [__extension__] declspecs ;
          (retok (extdecl-decl (make-decl-decl :extension extension
                                               :specs declspecs
                                               :init nil
                                               :asm? nil
                                               :attrib nil))
                 (span-join span span2)
                 parstate))
         ;; If token2 is the 'asm' or '__asm' or '__asm__' keyword,
         ;; and if GCC extensions are supported,
         ;; we parse an assembler name specifier,
         ;; and this external declaration must be a declaration
         ;; (we do not support attributes of function definitions).
         ;; We also conditionally parse any attributes before the semicolon.
         ((and (or (token-keywordp token2 "asm")
                   (token-keywordp token2 "__asm")
                   (token-keywordp token2 "__asm__"))
               (parstate->gcc parstate))
          ;; [__extension__] declspecs asm
          (b* ((uscores (cond ((token-keywordp token2 "asm")
                               (keyword-uscores-none))
                              ((token-keywordp token2 "__asm")
                               (keyword-uscores-start))
                              ((token-keywordp token2 "__asm__")
                               (keyword-uscores-both))))
               ((erp asmspec & parstate)
                ;; [__extension__] declspecs asmspec
                (parse-asm-name-specifier uscores span2 parstate))
               ((erp attrspecs & parstate)
                ;; [__extension__] declspecs asmspec [attrspecs]
                (parse-*-attribute-specifier parstate))
               ((erp last-span parstate)
                ;; [__extension__] declspecs asmspec [attrspecs] ;
                (read-punctuator ";" parstate)))
            (retok (extdecl-decl (make-decl-decl :extension extension
                                                 :specs declspecs
                                                 :init nil
                                                 :asm? asmspec
                                                 :attrib attrspecs))
                   (span-join span last-span)
                   parstate)))
         ;; If token2 is the '__attribute__' keyword,
         ;; and if GCC extensions are supported,
         ;; we parse one or more attribute specifiers,
         ;; and this external declaration must be a declaration
         ;; (we do not support attributes of function definitions).
         ((and (token-keywordp token2 "__attribute__")
               (parstate->gcc parstate))
          ;; [__extension__] declspecs __attribute__
          (b* ((parstate (unread-token parstate)) ; [__extension__] declspecs
               ((erp attrspecs & parstate) ; [__extension__] declspecs attrspecs
                (parse-*-attribute-specifier parstate))
               ((erp last-span parstate) ; [__extension__] declspecs attrspecs ;
                (read-punctuator ";" parstate)))
            (retok (extdecl-decl (make-decl-decl :extension extension
                                                 :specs declspecs
                                                 :init nil
                                                 :asm? nil
                                                 :attrib attrspecs))
                   (span-join span last-span)
                   parstate)))
         ;; If token2 is not a semicolon,
         ;; and either GCC extensions are not supported
         ;; or token2 is not any of the keywords
         ;; 'asm', '__asm', '__asm__', or '__attribute__'.
         ;; we must have at least one declarator, which we parse.
         (t ; [__extension__] declspecs other
          (b* ((parstate (if token2 (unread-token parstate) parstate))
               ((erp declor & parstate) ; [__extension__] declspecs declor
                (parse-declarator parstate))
               ((erp token3 span3 parstate) (read-token parstate)))
            (cond
             ;; If token3 is an equal sign,
             ;; we must be parsing an intialization declarator,
             ;; and therefore the external declaration must be a declaration.
             ;; We parse the rest of the initialization declarator,
             ;; then possibly more initialization declarators.
             ;; If GCC extensions are supported,
             ;; we also parse an optional assembler name specifier
             ;; as well as zero or more attribute specifiers,
             ;; before the ending semicolon.
             ((token-punctuatorp token3 "=")
              ;; [__extension__] declspecs declor =
              (b* (((erp initer & parstate)
                    ;; [__extension__] declspecs declor = initer
                    (parse-initializer parstate))
                   ((erp token4 span4 parstate) (read-token parstate)))
                (cond
                 ;; If token4 is a semicolon,
                 ;; we have reached the end of the declarator.
                 ((token-punctuatorp token4 ";")
                  ;; [__extension__] declspecs declor = initer ;
                  (retok (extdecl-decl
                          (make-decl-decl
                           :extension extension
                           :specs declspecs
                           :init (list (make-initdeclor
                                        :declor declor
                                        :init? initer))
                           :asm? nil
                           :attrib nil))
                         (span-join span span4)
                         parstate))
                 ;; If token4 is a comma,
                 ;; we must have more initialization declarators.
                 ((token-punctuatorp token4 ",")
                  ;; [__extension__] declspecs declor = initer ,
                  (b* (((erp initdeclors & parstate)
                        ;; [__extension__] declspecs declor =
                        ;;     initer , initdeclors
                        (parse-init-declarator-list parstate))
                       ((erp asmspec? & parstate)
                        ;; [__extension__] declspecs declor =
                        ;;   initer , initdeclors [asmspec]
                        (if (parstate->gcc parstate)
                            (parse-?-asm-name-specifier parstate)
                          (retok nil (irr-span) parstate)))
                       ((erp attrspecs & parstate)
                        ;; [__extension__] declspecs declor =
                        ;;   initer, initdeclors [asmspec] [attrspecs]
                        (if (parstate->gcc parstate)
                            (parse-*-attribute-specifier parstate)
                          (retok nil (irr-span) parstate)))
                       ((erp last-span parstate)
                        ;; [__extension__] declspecs declor =
                        ;;   initer , initdeclors [asmspec] [attrspecs] ;
                        (read-punctuator ";" parstate)))
                    (retok (extdecl-decl
                            (make-decl-decl
                             :extension extension
                             :specs declspecs
                             :init (cons (make-initdeclor
                                          :declor declor
                                          :init? initer)
                                         initdeclors)
                             :asm? asmspec?
                             :attrib attrspecs))
                           (span-join span last-span)
                           parstate)))
                 ;; If token4 is the keyword 'asm' or '__asm' or '__asm__',
                 ;; and GCC extensions are supported,
                 ;; we have just one declarator with the initializer,
                 ;; followed by an assembler name specifier,
                 ;; and possibly by attribute specifiers.
                 ((and (or (token-keywordp token4 "asm")
                           (token-keywordp token4 "__asm")
                           (token-keywordp token4 "__asm__"))
                       (parstate->gcc parstate))
                  ;; [__extension__] declspecs declor = initer asm
                  (b* ((uscore (cond ((token-keywordp token4 "asm")
                                      (keyword-uscores-none))
                                     ((token-keywordp token4 "__asm")
                                      (keyword-uscores-start))
                                     ((token-keywordp token4 "__asm__")
                                      (keyword-uscores-both))))
                       ((erp asmspec & parstate)
                        ;; [__extension__] declspecs declor = initer asmspec
                        (parse-asm-name-specifier uscore span4 parstate))
                       ((erp attrspecs & parstate)
                        ;; [__extension__] declspecs declor =
                        ;;   initer asmspec [attrspecs]
                        (parse-*-attribute-specifier parstate))
                       ((erp last-span parstate)
                        ;; [__extension__] declspecs declor =
                        ;;   initer asmspec [attrspecs] ;
                        (read-punctuator ";" parstate)))
                    (retok (extdecl-decl
                            (make-decl-decl
                             :extension extension
                             :specs declspecs
                             :init (list (make-initdeclor
                                          :declor declor
                                          :init? initer))
                             :asm? asmspec
                             :attrib attrspecs))
                           (span-join span last-span)
                           parstate)))
                 ;; If token4 is the keyword '__attribute__'
                 ;; and GCC extensions are supported,
                 ;; we have just one declarator with the initializer,
                 ;; followed by attribute specifiers, which we parse.
                 ((and (token-keywordp token4 "__attribute__")
                       (parstate->gcc parstate))
                  ;; [__extension__] declspecs declor = initer __attribute__
                  (b* ((parstate (unread-token parstate))
                       ;; [__extension__] declspecs declor = initer
                       ((erp attrspecs & parstate)
                        (parse-*-attribute-specifier parstate))
                       ;; [__extension__] declspecs declor = initer attrspecs
                       ((erp last-span parstate)
                        ;; [__extension__] declspecs declor = initer attrspecs ;
                        (read-punctuator ";" parstate)))
                    (retok (extdecl-decl
                            (make-decl-decl
                             :extension extension
                             :specs declspecs
                             :init (list (make-initdeclor
                                          :declor declor
                                          :init? initer))
                             :asm? nil
                             :attrib attrspecs))
                           (span-join span last-span)
                           parstate)))
                 ;; If token4 is anything else, it is an error.
                 (t ; [__extension__] declspecs declor = initer other
                  (reterr-msg :where (position-to-msg (span->start span4))
                              :expected "a semicolon or a comma"
                              :found (token-to-msg token4))))))
             ;; If token3 is a semicolon,
             ;; we must be parsing an intialization declarator,
             ;; without initializer,
             ;; and the external declaration must be a declaration,
             ;; which the semicolon concludes.
             ((token-punctuatorp token3 ";")
              ;; [__extension__] declspecs declor ;
              (retok (extdecl-decl
                      (make-decl-decl
                       :extension extension
                       :specs declspecs
                       :init (list (make-initdeclor
                                    :declor declor
                                    :init? nil))
                       :asm? nil
                       :attrib nil))
                     (span-join span span3)
                     parstate))
             ;; If token3 is a comma,
             ;; we must be parsing
             ;; an external declaration that is a declaration.
             ;; There must be more initialization declarations,
             ;; which we parse.
             ;; If GCC extensions are supported,
             ;; we also parse an optional assembler name specifier
             ;; as well as zero or more attribute specifiers,
             ;; just before the final semicolon.
             ((token-punctuatorp token3 ",")
              ;; [__extension__] declspecs declor ,
              (b* (((erp initdeclors & parstate)
                    ;; [__extension__] declspecs declor , initdeclors
                    (parse-init-declarator-list parstate))
                   ((erp asmspec? & parstate)
                    ;; [__extension__] declspecs declor , initdeclors [asmspec]
                    (parse-?-asm-name-specifier parstate))
                   ((erp attrspecs & parstate)
                    ;; [__extension__] declspecs declor, initdeclors
                    ;;   [asmspec] [attrspecs]
                    (if (parstate->gcc parstate)
                        (parse-*-attribute-specifier parstate)
                      (retok nil (irr-span) parstate)))
                   ((erp last-span parstate)
                    ;; [__extension__] declspecs declor , initdeclors
                    ;;   [asmspec] [attrspecs] ;
                    (read-punctuator ";" parstate)))
                (retok (extdecl-decl
                        (make-decl-decl
                         :extension extension
                         :specs declspecs
                         :init (cons (make-initdeclor
                                      :declor declor
                                      :init? nil)
                                     initdeclors)
                         :asm? asmspec?
                         :attrib attrspecs))
                       (span-join span last-span)
                       parstate)))
             ;; If token3 is the 'asm' or '__asm' or '__asm__' keyword
             ;; and GCC extensions are supported,
             ;; this external declaration must be a declaration,
             ;; and we parse the assembler name specifier,
             ;; followed by zero or more attribute specifiers,
             ;; and then the final semicolon.
             ((and (or (token-keywordp token3 "asm")
                       (token-keywordp token3 "__asm")
                       (token-keywordp token3 "__asm__"))
                   (parstate->gcc parstate))
              ;; [__extension__] declspecs declor asm
              (b* ((uscores (cond ((token-keywordp token3 "asm")
                                   (keyword-uscores-none))
                                  ((token-keywordp token3 "__asm")
                                   (keyword-uscores-start))
                                  ((token-keywordp token3 "__asm__")
                                   (keyword-uscores-both))))
                   ((erp asmspec & parstate)
                    ;; [__extension__] declspecs declor asmspec
                    (parse-asm-name-specifier uscores span3 parstate))
                   ((erp attrspecs & parstate)
                    ;; [__extension__] declspecs declor asmspec [attrspecs]
                    (parse-*-attribute-specifier parstate))
                   ((erp last-span parstate)
                    ;; [__extension__] declspecs declor asmspec [attrspecs] ;
                    (read-punctuator ";" parstate)))
                (retok (extdecl-decl
                        (make-decl-decl
                         :extension extension
                         :specs declspecs
                         :init (list (make-initdeclor
                                      :declor declor
                                      :init? nil))
                         :asm? asmspec
                         :attrib attrspecs))
                       (span-join span last-span)
                       parstate)))
             ;; If token3 is the '__attribute__' keyword
             ;; and GCC extensions are supported,
             ;; this external declaration must be a declaration,
             ;; and we parse one or more attribute specifiers.
             ((and (token-keywordp token3 "__attribute__")
                   (parstate->gcc parstate))
              ;; [__extension__] declspecs declor __attribute
              (b* ((parstate (unread-token parstate))
                   ;; [__extension__] declspecs declor
                   ((erp attrspecs & parstate)
                    ;; [__extension__] declspecs declor attrspecs
                    (parse-*-attribute-specifier parstate))
                   ((erp last-span parstate)
                    ;; [__extension__] declspecs declor attrspecs ;
                    (read-punctuator ";" parstate)))
                (retok (extdecl-decl
                        (make-decl-decl
                         :extension extension
                         :specs declspecs
                         :init (list (make-initdeclor
                                      :declor declor
                                      :init? nil))
                         :asm? nil
                         :attrib attrspecs))
                       (span-join span last-span)
                       parstate)))
             ;; If token3 is something else,
             ;; the external declaration must be a function definition.
             ;; Since we have just parsed the declarator,
             ;; we check and see whether we have the compound statement
             ;; or a list of one or more declarations first.
             ;; Thus, if the token is an open curly brace,
             ;; we must have the function body,
             ;; and no declarations
             ;; between the declarator and the function body.
             ;; We put back the token and we parse the statement,
             ;; which must be a compound statement as required by the grammar.
             ((token-punctuatorp token3 "{")
              ;; [__extension__] declspecs declor {
              (b* ((parstate (unread-token parstate))
                   ;; [__extension__] declspecs declor
                   ((erp stmt last-span parstate)
                    ;; [__extension__] declspecs declor stmt
                    (parse-statement parstate)))
                (retok (extdecl-fundef
                        (make-fundef :extension extension
                                     :spec declspecs
                                     :declor declor
                                     :decls nil
                                     :body stmt))
                       (span-join span last-span)
                       parstate)))
             ;; If token is not an open curly brace,
             ;; we must have one or more declarations, which we parse.
             ;; Then we parse the compound statement.
             (t ; [__extension__] declspecs declor other
              (b* ((parstate ; [__extension__] declspecs declor
                    (if token3 (unread-token parstate) parstate))
                   ((erp decls & parstate)
                    ;; [__extension__] declspecs declor decls
                    (parse-declaration-list parstate))
                   ((erp token4 span4 parstate) (read-token parstate))
                   ((unless (token-punctuatorp token4 "{"))
                    (reterr-msg :where (position-to-msg (span->start span4))
                                :expected "an open curly brace"
                                :found (token-to-msg token4)))
                   ;; [__extension__] declspecs declor decls {
                   (parstate (unread-token parstate))
                   ;; [__extension__] declspecs declor decls
                   ((erp stmt last-span parstate)
                    ;; [__extension__] declspecs declor decls stmt
                    (parse-statement parstate)))
                (retok (extdecl-fundef
                        (make-fundef :extension extension
                                     :spec declspecs
                                     :declor declor
                                     :decls decls
                                     :body stmt))
                       (span-join span last-span)
                       parstate)))))))))))

  ///

  (defret parsize-of-parse-external-declaration-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-external-declaration-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-external-declaration-list ((parstate parstatep))
  :returns (mv erp
               (extdecls extdecl-listp)
               (span spanp)
               (eof-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a list of one or more external declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called by @(tsee parse-translation-unit)
     to parse all the external declarations in a file.
     If successful, we return the list of external declarations.")
   (xdoc::p
    "We also return the position just past the end of the file.
     The latter is used for a check performed by the caller.")
   (xdoc::p
    "We parse the first external declaration, which must be present.
     Then, unless we have reached the end of the file,
     we recursively parse more external declarations."))
  (b* (((reterr) nil (irr-span) (irr-position) parstate)
       ((erp extdecl first-span parstate) ; extdecl
        (parse-external-declaration parstate))
       ((erp token span parstate) (read-token parstate))
       ((when (not token)) ; extdecl EOF
        (retok (list extdecl) first-span (span->start span) parstate))
       ;; extdecl other
       (parstate (unread-token parstate)) ; extdecl
       ((erp extdecls last-span eof-pos parstate) ; extdecl extdecls
        (parse-external-declaration-list parstate)))
    (retok (cons extdecl extdecls)
           (span-join first-span last-span)
           eof-pos
           parstate))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-external-declaration-list-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-parse-external-declaration-list-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-translation-unit ((parstate parstatep))
  :returns (mv erp
               (tunit transunitp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a translation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called, by @(tsee parse-file),
     on the initial parsing state,
     which contains all the file data bytes.
     We parse one or more external declarations,
     consistently with the grammar.")
   (xdoc::p
    "We also ensure that the file ends in new-line,
     as prescribed in [C:5.1.1.2/2].
     We check that the end-of-file position,
     returned by @(tsee parse-external-declaration-list),
     is at column 0:
     this means that, since the file is not empty,
     the last character is a new-line,
     otherwise that position would be at a non-zero column."))
  (b* (((reterr) (irr-transunit) parstate)
       ((erp extdecls & eof-pos parstate)
        (parse-external-declaration-list parstate))
       ((unless (= (position->column eof-pos) 0))
        (reterr (msg "The file does not end in new-line."))))
    (retok (transunit extdecls) parstate))

  ///

  (defret parsize-of-parse-translation-unit-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-translation-unit-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-file ((path filepathp) (data byte-listp) (gcc booleanp))
  :returns (mv erp (tunit transunitp))
  :short "Parse (the data bytes of) a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also pass a flag saying whether GCC extensions should be accepted.")
   (xdoc::p
    "If successful, the result is a translation unit.
     We create a local stobj with the parser state,
     we initialize it with the data bytes,
     and we attempt to parse them as a translation unit.
     The final parser state is discarded, as is the case for local stobjs,
     since it is no longer needed.")
   (xdoc::p
    "If an error occurs, we enhance it with
     information about the file path.
     It is the case that @('erp') is a message,
     but currently we do not have that information statically available,
     so we add a run-time check that should always succeed."))
  (with-local-stobj
    parstate
    (mv-let (erp tunit parstate)
        (b* ((parstate (init-parstate data gcc parstate))
             ((mv erp tunit parstate) (parse-translation-unit parstate)))
          (if erp
              (if (msgp erp)
                  (mv (msg "Error in file ~x0: ~@1"
                           (filepath->unwrap path) erp)
                      (irr-transunit)
                      parstate)
                (prog2$
                 (raise "Internal error: ~x0 is not a message." erp)
                 (mv t (irr-transunit) parstate)))
            (mv nil tunit parstate)))
      (mv erp tunit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-fileset ((fileset filesetp) (gcc booleanp))
  :returns (mv erp (tunits transunit-ensemblep))
  :short "Parse a file set."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also pass a flag saying whether GCC extensions should be accepted.")
   (xdoc::p
    "We go through each file of the file set and parse it,
     obtaining a translation unit for each,
     which we return in an ensemble of translation units
     that corresponds to the file set.
     The file paths are the same for the file set
     and for the translation unit ensembles
     (they are the keys of the maps)."))
  (b* (((reterr) (irr-transunit-ensemble))
       (filemap (fileset->unwrap fileset))
       ((erp tunitmap) (parse-fileset-loop filemap gcc)))
    (retok (transunit-ensemble tunitmap)))

  :prepwork
  ((define parse-fileset-loop ((filemap filepath-filedata-mapp)
                               (gcc booleanp))
     :returns (mv erp (tunitmap filepath-transunit-mapp))
     (b* (((reterr) nil)
          ((when (omap::emptyp filemap)) (retok nil))
          ((mv filepath filedata) (omap::head filemap))
          ((erp tunit) (parse-file filepath (filedata->unwrap filedata) gcc))
          ((erp tunitmap) (parse-fileset-loop (omap::tail filemap) gcc)))
       (retok (omap::update (filepath-fix filepath) tunit tunitmap)))
     :verify-guards :after-returns

     ///

     (defret keys-of-parse-fileset-loop
       (implies (not erp)
                (equal (omap::keys tunitmap)
                       (omap::keys filemap)))
       :hyp (filepath-filedata-mapp filemap)
       :hints (("Goal" :induct t)))))

  ///

  (defret filepaths-of-parse-fileset
    (implies (not erp)
             (equal (omap::keys (transunit-ensemble->unwrap tunits))
                    (omap::keys (fileset->unwrap fileset))))))
