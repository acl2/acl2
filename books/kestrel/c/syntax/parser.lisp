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
(include-book "kestrel/std/util/error-value-tuples" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

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
  (:stringlit ((unwrap stringlit)))
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
       :stringlit "a string literal"
       :punctuator (msg "the punctuator ~x0" token.unwrap))
    "end of file"))

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

(fty::defprod parstate
  :short "Fixtype of parser states."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our parsing functions take and return parser states.")
   (xdoc::p
    "The primary component of a parser state
     is the input sequence of bytes remaining,
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
     where one or more bytes are decoded into the character
     (currently just one byte,
     but that may change if we add support for non-ASCII UTF-8 Unicode).")
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
    "We could look into turning the parser state into a stobj in the future,
     if efficiency is an issue.
     The code of the parser already treats the parser state
     in a single-threaded way."))
  ((bytes byte-list)
   (position position)
   (chars-read char+position-list)
   (chars-unread char+position-list)
   (tokens-read token+span-list)
   (tokens-unread token+span-list)
   (checkpoints nat-list))
  :pred parstatep
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;

(defmacro+ irr-parstate ()
  :short "An irrelevant parser state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in functions that take a parser state as input,
     so a natural choice for an irrelevant parser state to return
     is the result of fixing the input parser state.")
   (xdoc::p
    "This macro assumes that the variable @('pstate') is in scope
     and has the type of parser states.
     This is normally a function formal."))
  '(parstate-fix pstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-parstate ((data byte-listp))
  :returns (pstate parstatep)
  :short "Initial parser state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given (the data of) a file to parse,
     the initial parsing state consists of
     the data to parse,
     no unread characters or tokens,
     no read characters or tokens,
     the initial file position,
     and no checkpoints."))
  (make-parstate :bytes data
                 :position (position-init)
                 :chars-read nil
                 :chars-unread nil
                 :tokens-read nil
                 :tokens-unread nil
                 :checkpoints nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parsize ((pstate parstatep))
  :returns (size natp)
  :short "Size of the parsing state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used as the measure for termination of the parsing functions.
     The size is measured as the sum of
     the lists of bytes, characters, and tokens that can be read."))
  (+ (len (parstate->bytes pstate))
     (len (parstate->chars-unread pstate))
     (len (parstate->tokens-unread pstate)))

  ///

  (defrule parsize-of-parstate-fix
    (equal (parsize (parstate-fix pstate))
           (parsize pstate))))

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
     meant to be Unicode code points,
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
        (t (msg "the non-ASCII character starting with byte ~x0" char)))
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

(define read-char ((pstate parstatep))
  :returns (mv erp (char? nat-optionp) (pos positionp) (new-pstate parstatep))
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
     Since currently we only support ASCII,
     one byte is always enough for a character;
     in the future, we may generalize this to perform UTF-8 decoding.")
   (xdoc::p
    "Looking at the rules in the ABNF grammar for basic and extended characters,
     we see that the ASCII codes of the three non-new-line extended characters
     (namely dollar, at sign, and backquote)
     fill gaps in the ASCII codes of the basic characters,
     so that the codes 9, 11, 12, and 32-126 are all valid characters,
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
    "If the next byte read has any other value, we deem it illegal,
     and return an error message with the current file position.
     We intentionally exclude most ASCII control characters,
     except for the basic ones and for the new-line ones,
     since there should be little need to use those in C code.
     Furthermore, some are dangerous, particularly backspace,
     since it may make the code look different from what it is,
     similarly to "
    (xdoc::ahref "https://en.wikipedia.org/wiki/Trojan_Source" "Trojan Source")
    " in Unicode.
     However, if we encounter practical code
     that uses some of these ASCII control characters,
     we can easily add support for them,
     in the ABNF grammar and in the parser."))
  (b* (((reterr) nil (irr-position) (irr-parstate))
       ((parstate pstate) pstate)
       ((when (consp pstate.chars-unread))
        (b* ((char+pos (car pstate.chars-unread)))
          (retok (char+position->char char+pos)
                 (char+position->position char+pos)
                 (change-parstate
                  pstate
                  :chars-unread (cdr pstate.chars-unread)
                  :chars-read (cons char+pos pstate.chars-read)))))
       ((unless (consp pstate.bytes))
        (retok nil pstate.position (irr-parstate)))
       (byte (car pstate.bytes)))
    (cond ((or (= byte 9)
               (= byte 11)
               (= byte 12)
               (and (<= 32 byte) (<= byte 126)))
           (retok byte
                  pstate.position
                  (change-parstate
                   pstate
                   :bytes (cdr pstate.bytes)
                   :position (position-inc-column 1 pstate.position)
                   :chars-read (cons (make-char+position
                                      :char byte
                                      :position pstate.position)
                                     pstate.chars-read))))
          ((= byte 10)
           (retok 10
                  pstate.position
                  (change-parstate
                   pstate
                   :bytes (cdr pstate.bytes)
                   :position (position-inc-line 1 pstate.position)
                   :chars-read (cons (make-char+position
                                      :char 10
                                      :position pstate.position)
                                     pstate.chars-read))))
          ((= byte 13)
           (if (and (consp (cdr pstate.bytes))
                    (= (cadr pstate.bytes) 10))
               (retok 10
                      pstate.position
                      (change-parstate
                       pstate
                       :bytes (cddr pstate.bytes)
                       :position (position-inc-line 1 pstate.position)
                       :chars-read (cons (make-char+position
                                          :char 10
                                          :position pstate.position)
                                         pstate.chars-read)))
             (retok 10
                    pstate.position
                    (change-parstate
                     pstate
                     :bytes (cdr pstate.bytes)
                     :position (position-inc-line 1 pstate.position)
                     :chars-read (cons (make-char+position
                                        :char 10
                                        :position pstate.position)
                                       pstate.chars-read)))))
          (t (reterr-msg :where (position-to-msg pstate.position)
                         :expected "an ASCII character with code ~
                                    in the range 9-13 or in the range 32-126"
                         :found (char-to-msg byte)))))
  :prepwork ((local (in-theory (enable acl2-numberp-when-bytep
                                       rationalp-when-bytep
                                       natp-when-bytep))))

  ///

  (defret parsize-of-read-char-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize len))))

  (defret parsize-of-read-char-cond
    (implies (and (not erp)
                  char?)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parsize len fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-char ((pstate parstatep))
  :returns (new-pstate parstatep)
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
  (b* (((parstate pstate) pstate)
       ((unless (consp pstate.chars-read))
        (raise "Internal error: no character to unread.")
        (change-parstate pstate
                         :chars-unread (cons (make-char+position
                                              :char 0
                                              :position (irr-position))
                                             pstate.chars-unread)))
       (char+pos (car pstate.chars-read)))
    (change-parstate pstate
                     :chars-unread (cons char+pos pstate.chars-unread)
                     :chars-read (cdr pstate.chars-read)))

  ///

  (defret parsize-of-unread-char
    (equal (parsize new-pstate)
           (1+ (parsize pstate)))
    :hints (("Goal" :in-theory (enable parsize len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-chars ((n natp) (pstate parstatep))
  :returns (new-pstate parstatep)
  :short "Unread a specified number of characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "This repeatedly calls @(tsee unread-char)
     to unread zero or more characters.
     The number of characters is specified by @('n').
     This number may be 0."))
  (b* (((when (zp n)) (parstate-fix pstate))
       (pstate (unread-char pstate)))
    (unread-chars (1- n) pstate))

  ///

  (defret parsize-of-unread-chars
    (equal (parsize new-pstate)
           (+ (parsize pstate) (nfix n)))
    :hints (("Goal"
             :induct t
             :in-theory (enable nfix fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-ident/keyword ((first-char (unsigned-byte-p 8 first-char))
                           (first-pos positionp)
                           (pstate parstatep))
  :guard (or (and (<= (char-code #\A) first-char)
                  (<= first-char (char-code #\Z)))
             (and (<= (char-code #\a) first-char)
                  (<= first-char (char-code #\z)))
             (= first-char (char-code #\_)))
  :returns (mv erp (lexeme lexemep) (span spanp) (new-pstate parstatep))
  :short "Lex an identifier or keyword."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called after the first character of the identifier
     has been already read;
     that character is passed to this function.")
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
     but we use @('(unsigned-byte-p 8)'),
     in the guard of this function and in the return type of the loop,
     because @(tsee nats=>string) has that as guard
     (more precisely, lists of that).
     If the ASCII string is a keyword, we return a keyword token.
     Otherwise, we return an identifier token."))
  (b* (((reterr) (irr-lexeme) (irr-span) (irr-parstate))
       ((erp rest-chars last-pos pstate)
        (lex-ident/keyword-loop first-pos pstate))
       (span (make-span :start first-pos :end last-pos))
       (chars (cons first-char rest-chars))
       (string (acl2::nats=>string chars)))
    (if (member-equal string '("auto"
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
        (retok (lexeme-token (token-keyword string)) span pstate)
      (retok (lexeme-token (token-ident (ident string))) span pstate)))

  :prepwork

  ((define lex-ident/keyword-loop ((pos-so-far positionp)
                                   (pstate parstatep))
     :returns (mv erp
                  (chars (unsigned-byte-listp 8 chars)
                         :hints (("Goal"
                                  :induct t
                                  :in-theory (enable unsigned-byte-p
                                                     integer-range-p
                                                     integerp-when-natp))))
                  (last-pos positionp)
                  (new-pstate parstatep))
     :parents nil
     (b* (((reterr) nil (irr-position) (irr-parstate))
          ((erp char pos pstate) (read-char pstate))
          ((when (not char))
           (retok nil (position-fix pos-so-far) pstate))
          ((unless (or (and (<= (char-code #\A) char) (<= char (char-code #\Z)))
                       (and (<= (char-code #\a) char) (<= char (char-code #\z)))
                       (and (<= (char-code #\0) char) (<= char (char-code #\9)))
                       (= char (char-code #\_)))) ; A-Z a-z 0-9 _
           (b* ((pstate (unread-char pstate)))
             (retok nil (position-fix pos-so-far) pstate)))
          ((erp chars last-pos pstate) (lex-ident/keyword-loop pos pstate)))
       (retok (cons char chars) last-pos pstate))
     :measure (parsize pstate)
     :hints (("Goal" :in-theory (enable o< o-finp)))
     :verify-guards nil ; done below

     ///

     (verify-guards lex-ident/keyword-loop
       :hints (("Goal" :in-theory (enable rationalp-when-natp))))

     (defret parsize-of-lex-ident/keyword-loop-<=
       (<= (parsize new-pstate)
           (parsize pstate))
       :rule-classes :linear
       :hints (("Goal" :induct t)))))

  ///

  (defret parsize-of-lex-ident/keyword-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-hex-digit ((pstate parstatep))
  :returns (mv erp
               (hexdig hex-digit-char-p
                       :hints
                       (("Goal" :in-theory (enable hex-digit-char-p
                                                   unsigned-byte-p
                                                   integer-range-p
                                                   integerp-when-natp))))
               (pos positionp)
               (new-pstate parstatep))
  :short "Lex a hexadecimal digit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a hexadecimal digit:
     if the character is not a hexadecimal digit, it is an error.
     If the next character is present and is a hexadecimal digit,
     we return the corresponding ACL2 character,
     along with its position in the file."))
  (b* (((reterr) #\0 (irr-position) (irr-parstate))
       ((erp char pos pstate) (read-char pstate))
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
    (retok (code-char char) pos pstate))
  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp
                                           integerp-when-natp)))

  ///

  (defret parsize-of-lex-hex-digit-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-hex-digit-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-dec-digits ((pos-so-far positionp) (pstate parstatep))
  :returns (mv erp
               (decdigs dec-digit-char-listp
                        :hints
                        (("Goal"
                          :induct t
                          :in-theory (enable lex-dec-digits
                                             dec-digit-char-p
                                             unsigned-byte-p
                                             integer-range-p
                                             integerp-when-natp))))
               (last-pos positionp)
               (next-pos positionp)
               (new-pstate parstatep))
  :short "Lex zero or more decimal digits, as many as available."
  :long
  (xdoc::topstring
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
     If it exists but is not a decimal digit,
     we put the character back and return.
     Otherwise, we recursively read zero or more,
     and we put the one just read in front.
     We always return the position of the last decimal character,
     or the input @('pos-so-far') if there is no decimal character:
     this input is the position read so far,
     just before the zero or more decimal digits to be read."))
  (b* (((reterr) nil (irr-position) (irr-position) (irr-parstate))
       ((erp char pos pstate) (read-char pstate))
       ((when (not char))
        (retok nil (position-fix pos-so-far) pos pstate))
       ((unless (and (<= (char-code #\0) char) ; 0
                     (<= char (char-code #\9)))) ; 9
        (b* ((pstate (unread-char pstate)))
          (retok nil (position-fix pos-so-far) pos pstate)))
       (decdig (code-char char))
       ((erp decdigs last-pos next-pos pstate) (lex-dec-digits pos pstate)))
    (retok (cons decdig decdigs) last-pos next-pos pstate))
  :measure (parsize pstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp
                                           integerp-when-natp)))

  ///

  (more-returns
   (decdigs true-listp
            :rule-classes :type-prescription))

  (defret parsize-of-lex-dec-digits-uncond
    (<= (parsize new-pstate)
        (- (parsize pstate)
           (len decdigs)))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable fix len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-hex-digits ((pos-so-far positionp) (pstate parstatep))
  :returns (mv erp
               (hexdigs hex-digit-char-listp
                        :hints
                        (("Goal"
                          :induct t
                          :in-theory (enable lex-hex-digits
                                             hex-digit-char-p
                                             unsigned-byte-p
                                             integer-range-p
                                             integerp-when-natp))))
               (last-pos positionp)
               (next-pos positionp)
               (new-pstate parstatep))
  :short "Lex zero or more hexadecimal digits, as many as available."
  :long
  (xdoc::topstring
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
  (b* (((reterr) nil (irr-position) (irr-position) (irr-parstate))
       ((erp char pos pstate) (read-char pstate))
       ((when (not char))
        (retok nil (position-fix pos-so-far) pos pstate))
       ((unless (or (and (<= (char-code #\0) char) ; 0
                         (<= char (char-code #\9))) ; 9
                    (and (<= (char-code #\A) char) ; A
                         (<= char (char-code #\F))) ; F
                    (and (<= (char-code #\a) char) ; a
                         (<= char (char-code #\f))))) ; f
        (b* ((pstate (unread-char pstate)))
          (retok nil (position-fix pos-so-far) pos pstate)))
       (hexdig (code-char char))
       ((erp hexdigs last-pos next-pos pstate)
        (lex-hex-digits pos pstate)))
    (retok (cons hexdig hexdigs) last-pos next-pos pstate))
  :measure (parsize pstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp
                                           integerp-when-natp)))

  ///

  (more-returns
   (hexdigs true-listp
            :rule-classes :type-prescription))

  (defret parsize-of-lex-hex-digits-uncond
    (<= (parsize new-pstate)
        (- (parsize pstate)
           (len hexdigs)))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable fix len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-hex-quad ((pstate parstatep))
  :returns (mv erp
               (quad hex-quad-p)
               (last-pos positionp)
               (new-pstate parstatep))
  :short "Lex a quadruple of hexadecimal digits."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect four hexadecimal digits,
     so we call @(tsee lex-hex-digit) four times.
     We return the position of the last one."))
  (b* (((reterr) (irr-hex-quad) (irr-position) (irr-parstate))
       ((erp hexdig1 & pstate) (lex-hex-digit pstate))
       ((erp hexdig2 & pstate) (lex-hex-digit pstate))
       ((erp hexdig3 & pstate) (lex-hex-digit pstate))
       ((erp hexdig4 pos pstate) (lex-hex-digit pstate)))
    (retok (make-hex-quad :1st hexdig1
                          :2nd hexdig2
                          :3rd hexdig3
                          :4th hexdig4)
           pos
           pstate))

  ///

  (defret parsize-of-lex-hex-quad-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-hex-quad-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-escape ((pstate parstatep))
  :returns (mv erp (escape escapep) (last-pos positionp) (new-pstate parstatep))
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
     we read another one and possibly yet another one,
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
  (b* (((reterr) (irr-escape) (irr-position) (irr-parstate))
       ((erp char pos pstate) (read-char pstate)))
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
      (retok (escape-simple (simple-escape-squote)) pos pstate))
     ((= char (char-code #\")) ; \ "
      (retok (escape-simple (simple-escape-dquote)) pos pstate))
     ((= char (char-code #\?)) ; \ ?
      (retok (escape-simple (simple-escape-qmark)) pos pstate))
     ((= char (char-code #\\)) ; \ \
      (retok (escape-simple (simple-escape-bslash)) pos pstate))
     ((= char (char-code #\a)) ; \ a
      (retok (escape-simple (simple-escape-a)) pos pstate))
     ((= char (char-code #\b)) ; \ b
      (retok (escape-simple (simple-escape-b)) pos pstate))
     ((= char (char-code #\f)) ; \ f
      (retok (escape-simple (simple-escape-f)) pos pstate))
     ((= char (char-code #\n)) ; \ n
      (retok (escape-simple (simple-escape-n)) pos pstate))
     ((= char (char-code #\r)) ; \ r
      (retok (escape-simple (simple-escape-r)) pos pstate))
     ((= char (char-code #\t)) ; \ t
      (retok (escape-simple (simple-escape-t)) pos pstate))
     ((= char (char-code #\v)) ; \ v
      (retok (escape-simple (simple-escape-v)) pos pstate))
     ((and (<= (char-code #\0) char)
           (<= char (char-code #\7))) ; \ octdig
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2)
          (retok (escape-oct (oct-escape-one (code-char char)))
                 pos
                 pstate))
         ((and (<= (char-code #\0) char2)
               (<= char2 (char-code #\7))) ; \ octdig octdig
          (b* (((erp char3 pos3 pstate) (read-char pstate)))
            (cond
             ((not char3)
              (retok (escape-oct (oct-escape-two (code-char char)
                                                 (code-char char2)))
                     pos2
                     pstate))
             ((and (<= (char-code #\0) char3)
                   (<= char3 (char-code #\7))) ; \ octdig octdig octdig
              (retok (escape-oct (oct-escape-three (code-char char)
                                                   (code-char char2)
                                                   (code-char char3)))
                     pos3
                     pstate))
             (t ; \ octdig \octdig other
              (b* ((pstate (unread-char pstate))) ; \ octdig octdig
                (retok (escape-oct (oct-escape-two (code-char char)
                                                   (code-char char2)))
                       pos2
                       pstate))))))
         (t ; \ octdig other
          (b* ((pstate (unread-char pstate)))
            (retok (escape-oct (oct-escape-one (code-char char)))
                   pos
                   pstate))))))
     ((= char (char-code #\x))
      (b* (((erp hexdigs last-pos next-pos pstate)
            (lex-hex-digits pos pstate)))
        (if hexdigs
            (retok (escape-hex hexdigs) last-pos pstate)
          (reterr-msg :where (position-to-msg next-pos)
                      :expected "one or more hexadecimal digits"
                      :found "none"))))
     ((= char (char-code #\u))
      (b* (((erp quad pos pstate) (lex-hex-quad pstate)))
        (retok (escape-univ (univ-char-name-locase-u quad)) pos pstate)))
     ((= char (char-code #\U))
      (b* (((erp quad1 & pstate) (lex-hex-quad pstate))
           ((erp quad2 pos pstate) (lex-hex-quad pstate)))
        (retok (escape-univ (make-univ-char-name-upcase-u :quad1 quad1
                                                          :quad2 quad2))
               pos
               pstate)))
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

  (defret parsize-of-lex-escape-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-escape-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-c-chars ((pstate parstatep))
  :returns (mv erp
               (cchars c-char-listp)
               (closing-squote-pos positionp)
               (new-pstate parstatep))
  :short "Lex zero or more characters and escape sequences
          in a character constant."
  :long
  (xdoc::topstring
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
  (b* (((reterr) nil (irr-position) (irr-parstate))
       ((erp char pos pstate) (read-char pstate))
       ((unless char)
        (reterr-msg :where (position-to-msg pos)
                    :expected "an escape sequence or ~
                               any character other than ~
                               single quote or backslash"
                    :found (char-to-msg char)))
       ((when (= char (char-code #\'))) ; '
        (retok nil pos pstate))
       ((when (= char 10)) ; new-line
        (reterr-msg :where (position-to-msg pos)
                    :expected "an escape sequence or ~
                               any character other than ~
                               single quote or backslash"
                    :found (char-to-msg char)))
       ((erp cchar & pstate)
        (if (= char (char-code #\\)) ; \
            (b* (((erp escape pos pstate) (lex-escape pstate))
                 (cchar (c-char-escape escape)))
              (retok cchar pos pstate))
          (b* ((cchar (c-char-char char)))
            (retok cchar pos pstate))))
       ((erp cchars closing-squote-pos pstate) (lex-c-chars pstate)))
    (retok (cons cchar cchars) closing-squote-pos pstate))
  :measure (parsize pstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-c-chars-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-lex-c-chars-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (- (parsize pstate)
                        (len cchars)))))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable fix len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-s-chars ((pstate parstatep))
  :returns (mv erp
               (schars s-char-listp)
               (closing-dquote-pos positionp)
               (new-pstate parstatep))
  :short "Lex zero or more characters and escape sequences
          in a string literal."
  :long
  (xdoc::topstring
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
  (b* (((reterr) nil (irr-position) (irr-parstate))
       ((erp char pos pstate) (read-char pstate))
       ((unless char)
        (reterr-msg :where (position-to-msg pos)
                    :expected "an escape sequence or ~
                               any character other than ~
                               double quote or backslash"
                    :found (char-to-msg char)))
       ((when (= char (char-code #\"))) ; "
        (retok nil pos pstate))
       ((when (= char 10)) ; new-line
        (reterr-msg :where (position-to-msg pos)
                    :expected "an escape sequence or ~
                               any character other than ~
                               double quote or backslash"
                    :found (char-to-msg char)))
       ((erp schar & pstate)
        (if (= char (char-code #\\)) ; \
            (b* (((erp escape pos pstate) (lex-escape pstate))
                 (schar (s-char-escape escape)))
              (retok schar pos pstate))
          (b* ((schar (s-char-char char)))
            (retok schar pos pstate))))
       ((erp schars closing-dquote-pos pstate) (lex-s-chars pstate)))
    (retok (cons schar schars) closing-dquote-pos pstate))
  :measure (parsize pstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-s-chars-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-lex-s-chars-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (- (parsize pstate)
                        (len schars)))))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable len fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-cconst ((cprefix? cprefix-optionp)
                    (first-pos positionp)
                    (pstate parstatep))
  :returns (mv erp (lexeme lexemep) (span spanp) (new-pstate parstatep))
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
     we read up to the closing single quote (see @(tsee lex-c-chars)),
     whose position we use as the ending one of the span we return.
     The starting position of the span is passed to this function as input."))
  (b* (((reterr) (irr-lexeme) (irr-span) (irr-parstate))
       ((erp cchars closing-squote-pos pstate) (lex-c-chars pstate))
       (span (make-span :start first-pos :end closing-squote-pos))
       ((unless cchars)
        (reterr-msg :where (position-to-msg closing-squote-pos)
                    :expected "one or more characters and escape sequences"
                    :found "none")))
    (retok (lexeme-token (token-const (const-char (cconst cprefix? cchars))))
           span
           pstate))

  ///

  (defret parsize-of-lex-cconst-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-cconst-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-stringlit ((eprefix? eprefix-optionp)
                       (first-pos positionp)
                       (pstate parstatep))
  :returns (mv erp (lexeme lexemep) (span spanp) (new-pstate parstatep))
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
     we read up to the closing double quote (see @(tsee lex-s-chars)),
     whose position we use as the ending one of the span we return.
     The starting position of the span is passed to this function as input."))
  (b* (((reterr) (irr-lexeme) (irr-span) (irr-parstate))
       ((erp schars closing-dquote-pos pstate) (lex-s-chars pstate))
       (span (make-span :start first-pos :end closing-dquote-pos)))
    (retok (lexeme-token (token-stringlit (stringlit eprefix? schars)))
           span
           pstate))

  ///

  (defret parsize-of-lex-stringlit-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-stringlit-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-isuffix-if-present ((pstate parstatep))
  :returns (mv erp
               (isuffix? isuffix-optionp)
               (last/next-pos positionp)
               (new-pstate parstatep))
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
  (b* (((reterr) nil (irr-position) (irr-parstate))
       ((erp char pos pstate) (read-char pstate)))
    (cond
     ((not char) ; EOF
      (retok nil pos pstate))
     ((= char (char-code #\l)) ; l
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; l EOF
          (retok (isuffix-l (lsuffix-locase-l)) pos pstate))
         ((= char2 (char-code #\l)) ; l l
          (b* (((erp char3 pos3 pstate) (read-char pstate)))
            (cond
             ((not char3) ; l l EOF
              (retok (isuffix-l (lsuffix-locase-ll)) pos2 pstate))
             ((= char3 (char-code #\u)) ; l l u
              (retok (make-isuffix-lu :length (lsuffix-locase-ll)
                                      :unsigned (usuffix-locase-u))
                     pos3
                     pstate))
             ((= char3 (char-code #\U)) ; l l U
              (retok (make-isuffix-lu :length (lsuffix-locase-ll)
                                      :unsigned (usuffix-upcase-u))
                     pos3
                     pstate))
             (t ; l l other
              (b* ((pstate (unread-char pstate))) ; l l
                (retok (isuffix-l (lsuffix-locase-ll)) pos2 pstate))))))
         ((= char2 (char-code #\u)) ; l u
          (retok (make-isuffix-lu :length (lsuffix-locase-l)
                                  :unsigned (usuffix-locase-u))
                 pos2
                 pstate))
         ((= char2 (char-code #\U)) ; l U
          (retok (make-isuffix-lu :length (lsuffix-locase-l)
                                  :unsigned (usuffix-upcase-u))
                 pos2
                 pstate))
         (t ; l other
          (b* ((pstate (unread-char pstate))) ; l
            (retok (isuffix-l (lsuffix-locase-l)) pos pstate))))))
     ((= char (char-code #\L)) ; L
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; L EOF
          (retok (isuffix-l (lsuffix-upcase-l)) pos pstate))
         ((= char2 (char-code #\l)) ; L L
          (b* (((erp char3 pos3 pstate) (read-char pstate)))
            (cond
             ((not char3) ; L L EOF
              (retok (isuffix-l (lsuffix-upcase-ll)) pos2 pstate))
             ((= char3 (char-code #\u)) ; L L u
              (retok (make-isuffix-lu :length (lsuffix-upcase-ll)
                                      :unsigned (usuffix-locase-u))
                     pos3
                     pstate))
             ((= char3 (char-code #\U)) ; L L U
              (retok (make-isuffix-lu :length (lsuffix-upcase-ll)
                                      :unsigned (usuffix-upcase-u))
                     pos3
                     pstate))
             (t ; L L other
              (b* ((pstate (unread-char pstate))) ; LL
                (retok (isuffix-l (lsuffix-upcase-ll)) pos2 pstate))))))
         ((= char2 (char-code #\u)) ; L u
          (retok (make-isuffix-lu :length (lsuffix-upcase-l)
                                  :unsigned (usuffix-locase-u))
                 pos2
                 pstate))
         ((= char2 (char-code #\U)) ; L U
          (retok (make-isuffix-lu :length (lsuffix-upcase-l)
                                  :unsigned (usuffix-upcase-u))
                 pos2
                 pstate))
         (t ; L other
          (b* ((pstate (unread-char pstate))) ; L
            (retok (isuffix-l (lsuffix-upcase-l)) pos pstate))))))
     ((= char (char-code #\u)) ; u
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; u EOF
          (retok (isuffix-u (usuffix-locase-u)) pos pstate))
         ((= char2 (char-code #\l)) ; u l
          (b* (((erp char3 pos3 pstate) (read-char pstate)))
            (cond
             ((not char3) ; u l EOF
              (retok (make-isuffix-ul :unsigned (usuffix-locase-u)
                                      :length (lsuffix-locase-l))
                     pos2
                     pstate))
             ((= char3 (char-code #\l)) ; u l l
              (retok (make-isuffix-ul :unsigned (usuffix-locase-u)
                                      :length (lsuffix-locase-ll))
                     pos3
                     pstate))
             (t ; u l other
              (b* ((pstate (unread-char pstate))) ; u l
                (retok (make-isuffix-ul :unsigned (usuffix-locase-u)
                                        :length (lsuffix-locase-l))
                       pos2
                       pstate))))))
         ((= char2 (char-code #\L)) ; u L
          (b* (((erp char3 pos3 pstate) (read-char pstate)))
            (cond
             ((not char3) ; u L EOF
              (retok (make-isuffix-ul :unsigned (usuffix-locase-u)
                                      :length (lsuffix-upcase-l))
                     pos2
                     pstate))
             ((= char3 (char-code #\L)) ; u L L
              (retok (make-isuffix-ul :unsigned (usuffix-locase-u)
                                      :length (lsuffix-upcase-ll))
                     pos3
                     pstate))
             (t ; u L other
              (b* ((pstate (unread-char pstate))) ; u L
                (retok (make-isuffix-ul :unsigned (usuffix-locase-u)
                                        :length (lsuffix-upcase-l))
                       pos2
                       pstate))))))
         (t ; u other
          (b* ((pstate (unread-char pstate)))
            (retok (isuffix-u (usuffix-locase-u)) pos pstate))))))
     ((= char (char-code #\U)) ; U
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; U EOF
          (retok (isuffix-u (usuffix-upcase-u)) pos pstate))
         ((= char2 (char-code #\l)) ; U l
          (b* (((erp char3 pos3 pstate) (read-char pstate)))
            (cond
             ((not char3) ; U l EOF
              (retok (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                      :length (lsuffix-locase-l))
                     pos2
                     pstate))
             ((= char3 (char-code #\l)) ; U l l
              (retok (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                      :length (lsuffix-locase-ll))
                     pos3
                     pstate))
             (t ; U l other
              (b* ((pstate (unread-char pstate))) ; U l
                (retok (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                        :length (lsuffix-locase-l))
                       pos2
                       pstate))))))
         ((= char2 (char-code #\L)) ; U L
          (b* (((erp char3 pos3 pstate) (read-char pstate)))
            (cond
             ((not char3) ; U L EOF
              (retok (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                      :length (lsuffix-upcase-l))
                     pos2
                     pstate))
             ((= char3 (char-code #\L)) ; U L L
              (retok (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                      :length (lsuffix-upcase-ll))
                     pos3
                     pstate))
             (t ; U L other
              (b* ((pstate (unread-char pstate)))
                (retok (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                        :length (lsuffix-upcase-l))
                       pos2
                       pstate))))))
         (t ; U other
          (b* ((pstate (unread-char pstate))) ; U
            (retok (isuffix-u (usuffix-upcase-u)) pos pstate))))))
     (t ; other
      (b* ((pstate (unread-char pstate)))
        (retok nil pos pstate)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-isuffix-if-present-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-isuffix-if-present-cond
    (implies (and (not erp)
                  isuffix?)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-fsuffix-if-present ((pstate parstatep))
  :returns (mv erp
               (fsuffix? fsuffix-optionp)
               (last/next-pos positionp)
               (new-pstate parstatep))
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
  (b* (((reterr) nil (irr-position) (irr-parstate))
       ((erp char pos pstate) (read-char pstate)))
    (cond
     ((not char)
      (retok nil pos pstate))
     ((= char (char-code #\f)) ; f
      (retok (fsuffix-locase-f) pos pstate))
     ((= char (char-code #\F)) ; F
      (retok (fsuffix-upcase-f) pos pstate))
     ((= char (char-code #\l)) ; l
      (retok (fsuffix-locase-l) pos pstate))
     ((= char (char-code #\L)) ; L
      (retok (fsuffix-upcase-l) pos pstate))
     (t ; other
      (b* ((pstate (unread-char pstate)))
        (retok nil pos pstate)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-fsuffix-if-present-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-fsuffix-if-present-cond
    (implies (and (not erp)
                  fsuffix?)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-sign-if-present ((pstate parstatep))
  :returns (mv erp
               (sign? sign-optionp)
               (last/next-pos positionp)
               (new-pstate parstatep))
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
  (b* (((reterr) nil (irr-position) (irr-parstate))
       ((erp char pos pstate) (read-char pstate)))
    (cond
     ((not char)
      (retok nil pos pstate))
     ((= char (char-code #\+)) ; +
      (retok (sign-plus) pos pstate))
     ((= char (char-code #\-)) ; -
      (retok (sign-minus) pos pstate))
     (t ; other
      (b* ((pstate (unread-char pstate)))
        (retok nil pos pstate)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-sign-if-present-ucond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-sign-if-present-cond
    (implies (and (not erp)
                  sign?)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-dec-expo-if-present ((pstate parstatep))
  :returns (mv erp
               (expo? dec-expo-optionp)
               (last/next-pos positionp)
               (new-pstate parstatep))
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
  (b* (((reterr) nil (irr-position) (irr-parstate))
       ((erp char pos pstate) (read-char pstate)))
    (cond
     ((not char)
      (retok nil pos pstate))
     ((or (= char (char-code #\e)) ; e
          (= char (char-code #\E))) ; E
      (b* ((prefix (if (= char (char-code #\e))
                       (dec-expo-prefix-locase-e)
                     (dec-expo-prefix-upcase-e)))
           ((erp sign? sign-pos pstate) (lex-sign-if-present pstate))
           (pos-so-far (if sign? sign-pos pos))
           ((erp digits last-pos & pstate)
            (lex-dec-digits pos-so-far pstate))
           ((unless digits)
            (b* ((pstate (if sign? (unread-char pstate) pstate)) ; put back sign
                 (pstate (unread-char pstate))) ; put back e/E
              (retok nil pos pstate))))
        (retok (make-dec-expo :prefix prefix
                              :sign? sign?
                              :digits digits)
               last-pos
               pstate)))
     (t ; other
      (b* ((pstate (unread-char pstate))) ; put back other
        (retok nil pos pstate)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-dec-expo-if-present-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-dec-expo-if-present-cond
    (implies (and (not erp)
                  expo?)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-dec-expo ((pstate parstatep))
  :returns (mv erp
               (expo dec-expop)
               (last-pos positionp)
               (new-pstate parstatep))
  :short "Lex a decimal exponent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect an exponent.
     We try to read a @('e') or @('E'), which must be present.
     Then we read an optional sign.
     Then we read zero or more decimal digits,
     of which there must be at least one."))
  (b* (((reterr) (irr-dec-expo) (irr-position) (irr-parstate))
       ((erp char pos pstate) (read-char pstate)))
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
           ((erp sign? sign-last-pos pstate)
            (lex-sign-if-present pstate))
           ((erp digits digits-last-pos digits-next-pos pstate)
            (lex-dec-digits sign-last-pos pstate))
           ((unless digits)
            (reterr-msg :where (position-to-msg digits-next-pos)
                        :expected "one or more digits"
                        :found "none")))
        (retok (make-dec-expo :prefix prefix
                              :sign? sign?
                              :digits digits)
               digits-last-pos
               pstate)))
     (t ; other
      (reterr-msg :where (position-to-msg pos)
                  :expected "a character in {e, E}"
                  :found (char-to-msg char)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-dec-expo-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-dec-expo-cond
    (implies (and (not erp)
                  expo?)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-bin-expo ((pstate parstatep))
  :returns (mv erp
               (expo bin-expop)
               (last-pos positionp)
               (new-pstate parstatep))
  :short "Lex a binary exponent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a binary exponent.
     We try to read a @('p') or @('P'), which must be present.
     Then we read an optional sign.
     Then we read zero or more decimal digits,
     of which there must be at least one."))
  (b* (((reterr) (irr-bin-expo) (irr-position) (irr-parstate))
       ((erp char pos pstate) (read-char pstate)))
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
           ((erp sign? sign-last-pos pstate)
            (lex-sign-if-present pstate))
           ((erp digits digits-last-pos digits-next-pos pstate)
            (lex-dec-digits sign-last-pos pstate))
           ((unless digits)
            (reterr-msg :where (position-to-msg digits-next-pos)
                        :expected "one or more digits"
                        :found "none")))
        (retok (make-bin-expo :prefix prefix
                              :sign? sign?
                              :digits digits)
               digits-last-pos
               pstate)))
     (t ; other
      (reterr-msg :where (position-to-msg pos)
                  :expected "a character in {p, P}"
                  :found (char-to-msg char)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-bin-expo-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-bin-expo-cond
    (implies (and (not erp)
                  expo?)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-full-ppnumber ((ends-in-e booleanp)
                             (pstate parstatep))
  :returns (mv erp (new-pstate parstatep))
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
  (b* (((reterr) (irr-parstate))
       ((erp char pos pstate) (read-char pstate))
       ((when (not char)) (retok pstate))
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
       (pstate (unread-char pstate)))
    (retok pstate))
  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp)))

  ///

  (defret parsize-of-check-full-ppnumber-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-hex-iconst/fconst ((hprefix hprefixp)
                               (prefix-last-pos positionp)
                               (pstate parstatep))
  :returns (mv erp
               (const constp)
               (last-pos positionp)
               (new-pstate parstatep))
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
  (b* (((reterr) (irr-const) (irr-position) (irr-parstate))
       ;; 0 x/X
       ((erp hexdigs hexdigs-last-pos & pstate)
        (lex-hex-digits prefix-last-pos pstate)))
    ;; 0 x/X [hexdigs]
    (cond
     ((not hexdigs) ; 0 x/X
      (b* (((erp char pos pstate) (read-char pstate)))
        (cond
         ((not char) ; 0 x/X EOF
          (reterr-msg :where (position-to-msg pos)
                      :expected "a hexadecimal digit or a dot"
                      :found (char-to-msg char)))
         ((= char (char-code #\.)) ; 0 x/X .
          (b* (((erp hexdigs2 & hexdigs2-next-pos pstate)
                (lex-hex-digits pos pstate)))
            ;; 0 x/X . [hexdigs2]
            (cond
             ((not hexdigs2) ; 0 x/X .
              (reterr-msg :where (position-to-msg hexdigs2-next-pos)
                          :expected "a hexadecimal digit or a dot"
                          :found (char-to-msg nil)))
             (t ; 0 x/X . hexdigs2
              (b* (((erp expo expo-last-pos pstate)
                    (lex-bin-expo pstate)))
                ;; 0 x/X . hexdigs2 expo
                (b* (((erp fsuffix? suffix-last/next-pos pstate)
                      (lex-fsuffix-if-present pstate))
                     ;; 0 x/X . hexdigs2 expo [fsuffix]
                     ((erp pstate) (check-full-ppnumber nil pstate)))
                  (retok (const-float
                          (make-fconst-hex
                           :prefix hprefix
                           :core (make-hex-core-fconst-frac
                                  :significand (make-hex-frac-const
                                                :before nil
                                                :after hexdigs2)
                                  :expo expo)
                           :suffix fsuffix?))
                         (cond (fsuffix? suffix-last/next-pos)
                               (t expo-last-pos))
                         pstate)))))))
         (t ; 0 x/X other
          (reterr-msg :where (position-to-msg pos)
                      :expected "a hexadecimal digit or a dot"
                      :found (char-to-msg char))))))
     (t ; 0 x/X hexdigs
      (b* (((erp char pos pstate) (read-char pstate)))
        (cond
         ((not char) ; 0 x/X hexdigs EOF
          (retok (const-int
                  (make-iconst
                   :dec/oct/hex (make-dec/oct/hex-const-hex
                                 :prefix hprefix
                                 :digits hexdigs)
                   :suffix nil))
                 hexdigs-last-pos
                 pstate))
         ((= char (char-code #\.)) ; 0 x/X hexdigs .
          (b* (((erp hexdigs2 & & pstate)
                (lex-hex-digits pos pstate)))
            ;; 0 x/X hexdigs . [hexdigs2]
            (cond
             ((not hexdigs2) ; 0 x/X hexdigs .
              (b* (((erp expo expo-last-pos pstate)
                    (lex-bin-expo pstate))
                   ;; 0 x/X hexdigs . expo
                   ((erp fsuffix? suffix-last/next-pos pstate)
                    (lex-fsuffix-if-present pstate))
                   ;; 0 x/X hexdigs . expo [suffix]
                   ((erp pstate) (check-full-ppnumber nil pstate)))
                (retok (const-float
                        (make-fconst-hex
                         :prefix hprefix
                         :core (make-hex-core-fconst-frac
                                :significand (make-hex-frac-const
                                              :before hexdigs
                                              :after nil)
                                :expo expo)
                         :suffix fsuffix?))
                       (cond (fsuffix? suffix-last/next-pos)
                             (t expo-last-pos))
                       pstate)))
             (t ; 0 x/X hexdigs . hexdigs2
              (b* (((erp expo expo-last-pos pstate)
                    (lex-bin-expo pstate))
                   ;; 0 x/X hexdigs . hexdigs2 expo
                   ((erp fsuffix? suffix-last/next-pos pstate)
                    (lex-fsuffix-if-present pstate))
                   ;; 0 x/X hexdigs . hexdigs2 expo [suffix]
                   ((erp pstate) (check-full-ppnumber nil pstate)))
                (retok (const-float
                        (make-fconst-hex
                         :prefix hprefix
                         :core (make-hex-core-fconst-frac
                                :significand (make-hex-frac-const
                                              :before hexdigs
                                              :after hexdigs2)
                                :expo expo)
                         :suffix fsuffix?))
                       (cond (fsuffix? suffix-last/next-pos)
                             (t expo-last-pos))
                       pstate))))))
         ((or (= char (char-code #\p)) ; 0 x/X hexdigs p
              (= char (char-code #\P))) ; 0 x/X hexdigs P
          (b* ((pstate (unread-char pstate)) ; 0 x/X hexdigs
               ((erp expo expo-last-pos pstate) (lex-bin-expo pstate))
               ;; 0 x/X hexdigs expo
               ((erp fsuffix? suffix-last/next-pos pstate)
                (lex-fsuffix-if-present pstate))
               ;; 0 x/X hexdigs expo [suffix]
               ((erp pstate) (check-full-ppnumber nil pstate)))
            (retok (const-float
                    (make-fconst-hex
                     :prefix hprefix
                     :core (make-hex-core-fconst-int
                            :significand hexdigs
                            :expo expo)
                     :suffix fsuffix?))
                   (cond (fsuffix? suffix-last/next-pos)
                         (t expo-last-pos))
                   pstate)))
         (t ; 0 x/X hexdigs other
          (b* ((pstate (unread-char pstate)) ; 0 x/X hexdigs
               ((erp isuffix? suffix-last/next-pos pstate)
                (lex-isuffix-if-present pstate))
               ;; 0 x/X hexdigs [suffix]
               ((erp pstate) (check-full-ppnumber (and
                                                   (member (car (last hexdigs))
                                                           '(#\e #\E))
                                                   t)
                                                  pstate)))
            (retok (const-int
                    (make-iconst
                     :dec/oct/hex (make-dec/oct/hex-const-hex
                                   :prefix hprefix
                                   :digits hexdigs)
                     :suffix isuffix?))
                   (cond (isuffix? suffix-last/next-pos)
                         (t hexdigs-last-pos))
                   pstate))))))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-hex-iconst/fconst-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable nfix))))

  (defret parsize-of-lex-hex-iconst/fconst-cond
    (implies (and (not erp)
                  const?)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-dec-iconst/fconst ((first-digit dec-digit-char-p)
                               (first-pos positionp)
                               (pstate parstatep))
  :guard (not (equal first-digit #\0))
  :returns (mv erp
               (const constp)
               (last-pos positionp)
               (new-pstate parstatep))
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
  (b* (((reterr) (irr-const) (irr-position) (irr-parstate))
       ;; 1-9
       ((erp decdigs decdigs-last-pos & pstate)
        (lex-dec-digits first-pos pstate))
       ;; 1-9 [decdigs]
       ((erp char pos pstate) (read-char pstate)))
    (cond
     ((not char) ; 1-9 [decdigs] EOF
      (retok (const-int
              (make-iconst
               :dec/oct/hex (make-dec/oct/hex-const-dec
                             :value (str::dec-digit-chars-value
                                     (cons first-digit decdigs)))
               :suffix nil))
             (cond (decdigs decdigs-last-pos)
                   (t (position-fix first-pos)))
             pstate))
     ((= char (char-code #\.)) ; 1-9 [decdigs] .
      (b* (((erp decdigs2 decdigs2-last-pos & pstate)
            (lex-dec-digits pos pstate))
           ;; 1-9 [decdigs] . [decdigs2]
           ((erp expo? expo-last/next-pos pstate)
            (lex-dec-expo-if-present pstate))
           ;; 1-9 [decdigs] . [decdigs2] [expo]
           ((erp fsuffix? suffix-last/next-pos pstate)
            (lex-fsuffix-if-present pstate))
           ;; 1-9 [decdigs] . [decdigs2] [expo] [suffix]
           ((erp pstate) (check-full-ppnumber nil pstate))
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
                                 :suffix fsuffix?))
               (cond (fsuffix? suffix-last/next-pos)
                     (expo? expo-last/next-pos)
                     (decdigs2 decdigs2-last-pos)
                     (t pos))
               pstate)))
     ((or (= char (char-code #\e)) ; 1-9 [decdigs] e
          (= char (char-code #\E))) ; 1-9 [decdigs] E
      (b* ((pstate (unread-char pstate)) ; 1-9 [decdigs]
           ((erp expo expo-last-pos pstate) (lex-dec-expo pstate))
           ;; 1-9 [decdigs] expo
           ((erp fsuffix? suffix-last/next-pos pstate)
            (lex-fsuffix-if-present pstate))
           ;; 1-9 [decdigs] expo [suffix]
           ((erp pstate) (check-full-ppnumber nil pstate)))
        (retok (const-float
                (make-fconst-dec
                 :core (make-dec-core-fconst-int
                        :significand (cons first-digit
                                           decdigs)
                        :expo expo)
                 :suffix fsuffix?))
               (cond (fsuffix? suffix-last/next-pos)
                     (t expo-last-pos))
               pstate)))
     (t ; 1-9 [decdigs] other
      (b* ((pstate (unread-char pstate)) ; 1-9 [decdigs]
           ((erp isuffix? suffix-last/next-pos pstate)
            (lex-isuffix-if-present pstate))
           ;; 1-9 [decdigs] [suffix]
           ((erp pstate) (check-full-ppnumber nil pstate)))
        (retok (const-int
                (make-iconst
                 :dec/oct/hex (make-dec/oct/hex-const-dec
                               :value (str::dec-digit-chars-value
                                       (cons first-digit decdigs)))
                 :suffix isuffix?))
               (cond (isuffix? suffix-last/next-pos)
                     (decdigs decdigs-last-pos)
                     (t (position-fix first-pos)))
               pstate)))))
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
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-dec-fconst ((first-digit-after-dot dec-digit-char-p)
                        (first-pos-after-dot positionp)
                        (pstate parstatep))
  :returns (mv erp (const constp) (last-pos positionp) (new-pstate parstatep))
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
  (b* (((reterr) (irr-const) (irr-position) (irr-parstate))
       ;; . decdig
       ((erp decdigs decdigs-last-pos & pstate)
        (lex-dec-digits first-pos-after-dot pstate))
       ;; . decdig [decdigs]
       ((erp expo? expo-last/next-pos pstate)
        (lex-dec-expo-if-present pstate))
       ;; . decdig [decdigs] [expo]
       ((erp fsuffix? suffix-last/next-pos pstate)
        (lex-fsuffix-if-present pstate))
       ;; . decdig [decdigs] [expo] [suffix]
       ((erp pstate) (check-full-ppnumber nil pstate))
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
                             :suffix fsuffix?))
           (cond (fsuffix? suffix-last/next-pos)
                 (expo? expo-last/next-pos)
                 (decdigs decdigs-last-pos)
                 (t (position-fix first-pos-after-dot)))
           pstate))

  ///

  (defret parsize-of-lex-dec-fconst-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-non-octal-digit ((pstate parstatep))
  :returns (mv erp (char natp) (pos positionp) (new-pstate parstatep))
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
  (b* (((reterr) 0 (irr-position) (irr-parstate))
       ((erp char pos pstate) (read-char pstate))
       ((unless char)
        (raise "Internal error: no non-octal digit found.")
        (reterr t))
       ((unless (and (<= (char-code #\0) char)
                     (<= char (char-code #\7))))
        (retok char pos pstate)))
    (lex-non-octal-digit pstate))
  :measure (parsize pstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp)))

  ///

  (defret parsize-of-lex-non-octal-digit-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-lex-non-octal-digit-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-oct-iconst-/-dec-fconst ((zero-pos positionp) (pstate parstatep))
  :returns (mv erp (const constp) (last-pos positionp) (new-pstate parstatep))
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
  (b* (((reterr) (irr-const) (irr-position) (irr-parstate))
       ;; 0
       ((erp digits digits-last-pos & pstate)
        (lex-dec-digits zero-pos pstate))
       ;; 0 [digits]
       ((erp char pos pstate) (read-char pstate)))
    (cond
     ((not char) ; 0 [digits]
      (cond
       ((oct-digit-char-listp digits) ; 0 [octdigs]
        (retok (const-int
                (make-iconst
                 :dec/oct/hex
                 (make-dec/oct/hex-const-oct
                  :leading-zeros (1+ (oct-iconst-leading-zeros digits))
                  :value (str::oct-digit-chars-value digits))
                 :suffix nil))
               (cond (digits digits-last-pos)
                     (t (position-fix zero-pos)))
               pstate))
       (t ; 0 not-all-octal-digits
        (b* ((pstate (unread-chars (len digits) pstate)) ; 0
             ((erp nonoctdig pos pstate) (lex-non-octal-digit pstate)))
          (reterr-msg :where (position-to-msg pos)
                      :expected "octal digit"
                      :found (char-to-msg nonoctdig))))))
     ((= char (char-code #\.)) ; 0 [digits] .
      (b* (((erp digits2 digits2-last-pos & pstate)
            (lex-dec-digits pos pstate))
           ;; 0 [digits] . [digits2]
           ((erp expo? expo-last/next-pos pstate)
            (lex-dec-expo-if-present pstate))
           ;; 0 [digits] . [digits2] [expo]
           ((erp fsuffix? suffix-last/next-pos pstate)
            (lex-fsuffix-if-present pstate))
           ;; 0 [digits] . [digits2] [expo] [suffix]
           ((erp pstate) (check-full-ppnumber nil pstate))
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
                                 :suffix fsuffix?))
               (cond (fsuffix? suffix-last/next-pos)
                     (expo? expo-last/next-pos)
                     (digits2 digits2-last-pos)
                     (t pos))
               pstate)))
     ((or (= char (char-code #\e)) ; 0 [digits] e
          (= char (char-code #\E))) ; 0 [digits] E
      (b* ((pstate (unread-char pstate)) ; 0 [digits]
           ((erp expo expo-last-pos pstate) (lex-dec-expo pstate))
           ;; 0 [digits] expo
           ((erp fsuffix? suffix-last/next-pos pstate)
            (lex-fsuffix-if-present pstate))
           ;; 0 [digits] expo [suffix]
           ((erp pstate) (check-full-ppnumber nil pstate)))
        (retok (const-float
                (make-fconst-dec
                 :core (make-dec-core-fconst-int
                        :significand (cons #\0 digits)
                        :expo expo)
                 :suffix fsuffix?))
               (cond (fsuffix? suffix-last/next-pos)
                     (t expo-last-pos))
               pstate)))
     (t ; 0 [digits] other
      (cond
       ((oct-digit-char-listp digits) ; 0 [octdigs] other
        (b* ((pstate (unread-char pstate)) ; 0 [octdigs]
             ((erp isuffix? suffix-last/next-pos pstate)
              (lex-isuffix-if-present pstate))
             ;; 0 [octdigs] [suffix]
             ((erp pstate) (check-full-ppnumber nil pstate)))
          (retok (const-int
                  (make-iconst
                   :dec/oct/hex
                   (make-dec/oct/hex-const-oct
                    :leading-zeros (1+ (oct-iconst-leading-zeros digits))
                    :value (str::oct-digit-chars-value digits))
                   :suffix isuffix?))
                 (cond (isuffix? suffix-last/next-pos)
                       (digits digits-last-pos)
                       (t (position-fix zero-pos)))
                 pstate)))
       (t ; 0 not-all-octal-digits
        (b* ((pstate (unread-chars (len digits) pstate)) ; 0
             ((erp nonoctdig pos pstate) (lex-non-octal-digit pstate)))
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
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-iconst/fconst ((first-digit dec-digit-char-p)
                           (first-pos positionp)
                           (pstate parstatep))
  :returns (mv erp (const constp) (last-pos positionp) (new-pstate parstatep))
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
  (b* (((reterr) (irr-const) (irr-position) (irr-parstate)))
    (cond
     ((eql first-digit #\0) ; 0
      (b* (((erp char pos pstate) (read-char pstate)))
        (cond
         ((not char) ; 0 EOF
          (retok (const-int
                  (make-iconst
                   :dec/oct/hex (make-dec/oct/hex-const-oct
                                 :leading-zeros 1
                                 :value 0)
                   :suffix nil))
                 (position-fix first-pos)
                 pstate))
         ((or (= char (char-code #\x)) ; 0 x
              (= char (char-code #\X))) ; 0 X
          (b* ((hprefix (if (= char (char-code #\x))
                            (hprefix-locase-0x)
                          (hprefix-upcase-0x))))
            (lex-hex-iconst/fconst hprefix pos pstate)))
         (t ; 0 other
          (b* ((pstate (unread-char pstate))) ; 0
            (lex-oct-iconst-/-dec-fconst first-pos pstate))))))
     (t ; 1-9
      (lex-dec-iconst/fconst first-digit first-pos pstate))))
  :guard-debug t
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-iconst/fconst-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-block-comment ((first-pos positionp) (pstate parstatep))
  :returns (mv erp (lexeme lexemep) (span spanp) (new-pstate parstatep))
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
  (b* (((reterr) (irr-lexeme) (irr-span) (irr-parstate))
       ((erp last-pos pstate) (lex-rest-of-block-comment first-pos pstate)))
    (retok (lexeme-comment)
           (make-span :start first-pos :end last-pos)
           pstate))

  :prepwork

  ((defines lex-block-comment-loops
     :parents (none) ; nil causes an error

     (define lex-rest-of-block-comment ((first-pos positionp)
                                        (pstate parstatep))
       :returns (mv erp (last-pos positionp) (new-pstate parstatep))
       (b* (((reterr) (irr-position) (irr-parstate))
            ((erp char pos pstate) (read-char pstate)))
         (cond
          ((not char) ; EOF
           (reterr-msg :where (position-to-msg pos)
                       :expected "a character"
                       :found (char-to-msg char)
                       :extra (msg "The block comment starting at ~@1 ~
                                    never ends."
                                   (position-to-msg first-pos))))
          ((= char (char-code #\*)) ; *
           (lex-rest-of-block-comment-after-star first-pos pstate))
          (t ; other
           (lex-rest-of-block-comment first-pos pstate))))
       :measure (parsize pstate))

     (define lex-rest-of-block-comment-after-star ((first-pos positionp)
                                                   (pstate parstatep))
       :returns (mv erp (last-pos positionp) (new-pstate parstatep))
       (b* (((reterr) (irr-position) (irr-parstate))
            ((erp char pos pstate) (read-char pstate)))
         (cond
          ((not char) ; EOF
           (reterr-msg :where (position-to-msg pos)
                       :expected "a character"
                       :found (char-to-msg char)
                       :extra (msg "The block comment starting at ~@1 ~
                                    never ends."
                                   (position-to-msg first-pos))))
          ((= char (char-code #\/)) ; /
           (retok pos pstate))
          ((= char (char-code #\*)) ; *
           (lex-rest-of-block-comment-after-star first-pos pstate))
          (t ; other
           (lex-rest-of-block-comment first-pos pstate))))
       :measure (parsize pstate))

     :hints (("Goal" :in-theory (enable o< o-finp)))

     :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

     ///

     (std::defret-mutual parsize-of-lex-block-comment-loops-uncond
       (defret parsize-of-lex-rest-of-block-comment-uncond
         (<= (parsize new-pstate)
             (parsize pstate))
         :rule-classes :linear
         :fn lex-rest-of-block-comment)
       (defret parsize-of-lex-resto-of-block-comment-after-star-uncond
         (<= (parsize new-pstate)
             (parsize pstate))
         :rule-classes :linear
         :fn lex-rest-of-block-comment-after-star))

     (std::defret-mutual parsize-of-lex-block-comment-loops-cond
       (defret parsize-of-lex-rest-of-block-comment-cond
         (implies (not erp)
                  (<= (parsize new-pstate)
                      (1- (parsize pstate))))
         :rule-classes :linear
         :fn lex-rest-of-block-comment)
       (defret parsize-of-lex-resto-of-block-comment-after-star-cond
         (implies (not erp)
                  (<= (parsize new-pstate)
                      (1- (parsize pstate))))
         :rule-classes :linear
         :fn lex-rest-of-block-comment-after-star))))

  ///

  (defret parsize-of-lex-block-comment-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-block-comment-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-line-comment ((first-pos positionp) (pstate parstatep))
  :returns (mv erp (lexeme lexemep) (span spanp) (new-pstate parstatep))
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
  (b* (((reterr) (irr-lexeme) (irr-span) (irr-parstate))
       ((erp last-pos pstate) (lex-line-comment-loop first-pos pstate)))
    (retok (lexeme-comment)
           (make-span :start first-pos :end last-pos)
           pstate))

  :prepwork

  ((define lex-line-comment-loop ((first-pos positionp) (pstate parstatep))
     :returns (mv erp (last-pos positionp) (new-pstate parstatep))
     :parents nil
     (b* (((reterr) (irr-position) (irr-parstate))
          ((erp char pos pstate) (read-char pstate)))
       (cond
        ((not char) ; EOF
         (reterr-msg :where (position-to-msg pos)
                     :expected "a character"
                     :found (char-to-msg char)
                     :extra (msg "The line comment starting at ~@1 ~
                                  never ends."
                                 (position-to-msg first-pos))))
        ((= char 10) ; new-line
         (retok pos pstate))
        (t ; other
         (lex-line-comment-loop first-pos pstate))))
     :measure (parsize pstate)
     :hints (("Goal" :in-theory (enable o< o-finp)))
     :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

     ///

     (defret parsize-of-lex-line-comment-loop-uncond
       (<= (parsize new-pstate)
           (parsize pstate))
       :rule-classes :linear
       :hints (("Goal" :induct t)))

     (defret parsize-of-lex-line-comment-loop-cond
       (implies (not erp)
                (<= (parsize new-pstate)
                    (1- (parsize pstate))))
       :rule-classes :linear
       :hints (("Goal" :induct t)))))

  ///

  (defret parsize-of-lex-line-comment-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-line-comment-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-lexeme ((pstate parstatep))
  :returns (mv erp (lexeme? lexeme-optionp) (span spanp) (new-pstate parstatep))
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

  (b* (((reterr) nil (irr-span) (irr-parstate))
       ((erp char first-pos pstate) (read-char pstate))
       ((unless char)
        (retok nil
               (make-span :start first-pos :end first-pos)
               pstate)))

    (cond

     ((or (= char 32) ; SP
          (and (<= 9 char) (<= char 12))) ; HT LF VT FF
      (retok (lexeme-whitespace)
             (make-span :start first-pos :end first-pos)
             pstate))

     ((= char (char-code #\u)) ; u
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; u EOF
          (retok (lexeme-token (token-ident (ident "u")))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\')) ; u '
          (lex-cconst (cprefix-locase-u) first-pos pstate))
         ((= char2 (char-code #\")) ; u "
          (lex-stringlit (eprefix-locase-u) first-pos pstate))
         ((= char2 (char-code #\8)) ; u 8
          (b* (((erp char3 & pstate) (read-char pstate)))
            (cond
             ((not char3) ; u 8 EOF
              (retok (lexeme-token (token-ident (ident "u8")))
                     (make-span :start first-pos :end pos2)
                     pstate))
             ((= char3 (char-code #\")) ; u 8 "
              (lex-stringlit (eprefix-locase-u8) first-pos pstate))
             (t ; u 8 other
              (b* ((pstate (unread-char pstate)) ; u 8
                   (pstate (unread-char pstate))) ; u
                (lex-ident/keyword char first-pos pstate))))))
         (t ; u other
          (b* ((pstate (unread-char pstate))) ; u
            (lex-ident/keyword char first-pos pstate))))))

     ((= char (char-code #\U)) ; U
      (b* (((erp char2 & pstate) (read-char pstate)))
        (cond
         ((not char2) ; U EOF
          (retok (lexeme-token (token-ident (ident "U")))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\')) ; U '
          (lex-cconst (cprefix-upcase-u) first-pos pstate))
         ((= char2 (char-code #\")) ; U "
          (lex-stringlit (eprefix-upcase-u) first-pos pstate))
         (t ; U other
          (b* ((pstate (unread-char pstate))) ; U
            (lex-ident/keyword char first-pos pstate))))))

     ((= char (char-code #\L)) ; L
      (b* (((erp char2 & pstate) (read-char pstate)))
        (cond
         ((not char2) ; L EOF
          (retok (lexeme-token (token-ident (ident "L")))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\')) ; L '
          (lex-cconst (cprefix-upcase-l) first-pos pstate))
         ((= char2 (char-code #\")) ; L "
          (lex-stringlit (eprefix-upcase-l) first-pos pstate))
         (t ; L other
          (b* ((pstate (unread-char pstate))) ; L
            (lex-ident/keyword char first-pos pstate))))))

     ((or (and (<= (char-code #\A) char) (<= char (char-code #\Z))) ; A-Z
          (and (<= (char-code #\a) char) (<= char (char-code #\z))) ; a-z
          (= char (char-code #\_))) ; _
      (lex-ident/keyword char first-pos pstate))

     ((and (<= (char-code #\0) char) (<= char (char-code #\9))) ; 0-9
      (b* (((erp const last-pos pstate)
            (lex-iconst/fconst (code-char char) first-pos pstate)))
        (retok (lexeme-token (token-const const))
               (make-span :start first-pos :end last-pos)
               pstate)))

     ((= char (char-code #\.)) ; .
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; . EOF
          (retok (lexeme-token (token-punctuator "."))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((and (<= (char-code #\0) char2) (<= char2 (char-code #\9))) ; . 0-9
          (b* (((erp const last-pos pstate)
                (lex-dec-fconst (code-char char2) pos2 pstate)))
            (retok (lexeme-token (token-const const))
                   (make-span :start first-pos :end last-pos)
                   pstate)))
         ((= char2 (char-code #\.)) ; . .
          (b* (((erp char3 pos3 pstate) (read-char pstate)))
            (cond
             ((not char3) ; . . EOF
              (b* ((pstate (unread-char pstate))) ; .
                (retok (lexeme-token (token-punctuator "."))
                       (make-span :start first-pos :end first-pos)
                       pstate)))
             ((= char3 (char-code #\.)) ; . . .
              (retok (lexeme-token (token-punctuator "..."))
                     (make-span :start first-pos :end pos3)
                     pstate))
             (t ; . . other
              (b* ((pstate (unread-char pstate)) ; . .
                   (pstate (unread-char pstate))) ; .
                (retok (lexeme-token (token-punctuator "."))
                       (make-span :start first-pos :end first-pos)
                       pstate))))))
         (t ; . other
          (b* ((pstate (unread-char pstate))) ; .
            (retok (lexeme-token (token-punctuator "."))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

     ((= char (char-code #\')) ; '
      (lex-cconst nil first-pos pstate))

     ((= char (char-code #\")) ; "
      (lex-stringlit nil first-pos pstate))

     ((= char (char-code #\/)) ; /
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; / EOF
          (retok (lexeme-token (token-punctuator "/"))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\*)) ; / *
          (lex-block-comment first-pos pstate))
         ((= char2 (char-code #\/)) ; / /
          (lex-line-comment first-pos pstate))
         ((= char2 (char-code #\=)) ; / =
          (retok (lexeme-token (token-punctuator "/="))
                 (make-span :start first-pos :end pos2)
                 pstate))
         (t ; / other
          (b* ((pstate (unread-char pstate))) ; /
            (retok (lexeme-token (token-punctuator "/"))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

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
             pstate))

     ((= char (char-code #\*)) ; *
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; * EOF
          (retok (lexeme-token (token-punctuator "*"))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\=)) ; * =
          (retok (lexeme-token (token-punctuator "*="))
                 (make-span :start first-pos :end pos2)
                 pstate))
         (t ; * other
          (b* ((pstate (unread-char pstate)))
            (retok (lexeme-token (token-punctuator "*"))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

     ((= char (char-code #\^)) ; ^
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; ^ EOF
          (retok (lexeme-token (token-punctuator "^"))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\=)) ; ^ =
          (retok (lexeme-token (token-punctuator "^="))
                 (make-span :start first-pos :end pos2)
                 pstate))
         (t ; ^ other
          (b* ((pstate (unread-char pstate)))
            (retok (lexeme-token (token-punctuator "^"))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

     ((= char (char-code #\!)) ; !
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; ! EOF
          (retok (lexeme-token (token-punctuator "!"))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\=)) ; ! =
          (retok (lexeme-token (token-punctuator "!="))
                 (make-span :start first-pos :end pos2)
                 pstate))
         (t ; ! other
          (b* ((pstate (unread-char pstate)))
            (retok (lexeme-token (token-punctuator "!"))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

     ((= char (char-code #\=)) ; =
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; = EOF
          (retok (lexeme-token (token-punctuator "="))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\=)) ; = =
          (retok (lexeme-token (token-punctuator "=="))
                 (make-span :start first-pos :end pos2)
                 pstate))
         (t ; = other
          (b* ((pstate (unread-char pstate)))
            (retok (lexeme-token (token-punctuator "="))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

     ((= char (char-code #\:)) ; :
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; : EOF
          (retok (lexeme-token (token-punctuator ":"))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\>)) ; : >
          (retok (lexeme-token (token-punctuator ":>"))
                 (make-span :start first-pos :end pos2)
                 pstate))
         (t ; : other
          (b* ((pstate (unread-char pstate)))
            (retok (lexeme-token (token-punctuator ":"))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

     ((= char (char-code #\#)) ; #
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; # EOF
          (retok (lexeme-token (token-punctuator "#"))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\#)) ; # #
          (retok (lexeme-token (token-punctuator "##"))
                 (make-span :start first-pos :end pos2)
                 pstate))
         (t ; # other
          (b* ((pstate (unread-char pstate)))
            (retok (lexeme-token (token-punctuator "#"))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

     ((= char (char-code #\&)) ; &
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; & EOF
          (retok (lexeme-token (token-punctuator "&"))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\&)) ; & &
          (retok (lexeme-token (token-punctuator "&&"))
                 (make-span :start first-pos :end pos2)
                 pstate))
         ((= char2 (char-code #\=)) ; & =
          (retok (lexeme-token (token-punctuator "&="))
                 (make-span :start first-pos :end pos2)
                 pstate))
         (t ; & other
          (b* ((pstate (unread-char pstate)))
            (retok (lexeme-token (token-punctuator "&"))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

     ((= char (char-code #\|)) ; |
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; | EOF
          (retok (lexeme-token (token-punctuator "|"))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\|)) ; | |
          (retok (lexeme-token (token-punctuator "||"))
                 (make-span :start first-pos :end pos2)
                 pstate))
         ((= char2 (char-code #\=)) ; | =
          (retok (lexeme-token (token-punctuator "|="))
                 (make-span :start first-pos :end pos2)
                 pstate))
         (t ; | other
          (b* ((pstate (unread-char pstate)))
            (retok (lexeme-token (token-punctuator "|"))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

     ((= char (char-code #\+)) ; +
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; + EOF
          (retok (lexeme-token (token-punctuator "+"))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\+)) ; + +
          (retok (lexeme-token (token-punctuator "++"))
                 (make-span :start first-pos :end pos2)
                 pstate))
         ((= char2 (char-code #\=)) ; + =
          (retok (lexeme-token (token-punctuator "+="))
                 (make-span :start first-pos :end pos2)
                 pstate))
         (t ; + other
          (b* ((pstate (unread-char pstate)))
            (retok (lexeme-token (token-punctuator "+"))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

     ((= char (char-code #\-)) ; -
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; - EOF
          (retok (lexeme-token (token-punctuator "-"))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\>)) ; - >
          (retok (lexeme-token (token-punctuator "->"))
                 (make-span :start first-pos :end pos2)
                 pstate))
         ((= char2 (char-code #\-)) ; - -
          (retok (lexeme-token (token-punctuator "--"))
                 (make-span :start first-pos :end pos2)
                 pstate))
         ((= char2 (char-code #\=)) ; - =
          (retok (lexeme-token (token-punctuator "-="))
                 (make-span :start first-pos :end pos2)
                 pstate))
         (t ; - other
          (b* ((pstate (unread-char pstate)))
            (retok (lexeme-token (token-punctuator "-"))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

     ((= char (char-code #\>)) ; >
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; > EOF
          (retok (lexeme-token (token-punctuator ">"))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\>)) ; > >
          (b* (((erp char3 pos3 pstate) (read-char pstate)))
            (cond
             ((not char3) ; > > EOF
              (retok (lexeme-token (token-punctuator ">>"))
                     (make-span :start first-pos :end pos2)
                     pstate))
             ((= char3 (char-code #\=))
              (retok (lexeme-token (token-punctuator ">>="))
                     (make-span :start first-pos :end pos3)
                     pstate))
             (t ; > > other
              (b* ((pstate (unread-char pstate))) ; > >
                (retok (lexeme-token (token-punctuator ">>"))
                       (make-span :start first-pos :end pos2)
                       pstate))))))
         ((= char2 (char-code #\=)) ; > =
          (retok (lexeme-token (token-punctuator ">="))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         (t ; > other
          (b* ((pstate (unread-char pstate))) ; >
            (retok (lexeme-token (token-punctuator ">"))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

     ((= char (char-code #\%)) ; %
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; % EOF
          (retok (lexeme-token (token-punctuator "%"))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\=)) ; % =
          (retok (lexeme-token (token-punctuator "%="))
                 (make-span :start first-pos :end pos2)
                 pstate))
         ((= char2 (char-code #\:)) ; % :
          (b* (((erp char3 & pstate) (read-char pstate)))
            (cond
             ((not char3) ; % : EOF
              (retok (lexeme-token (token-punctuator "%:"))
                     (make-span :start first-pos :end pos2)
                     pstate))
             ((= char3 (char-code #\%)) ; % : %
              (b* (((erp char4 pos4 pstate) (read-char pstate)))
                (cond
                 ((not char4) ; % : % EOF
                  (b* ((pstate (unread-char pstate))) ; % :
                    (retok (lexeme-token (token-punctuator "%:"))
                           (make-span :start first-pos :end pos2)
                           pstate)))
                 ((= char4 (char-code #\:)) ; % : % :
                  (retok (lexeme-token (token-punctuator "%:%:"))
                         (make-span :start first-pos :end pos4)
                         pstate))
                 (t ; % : % other
                  (b* ((pstate (unread-char pstate)) ; % : %
                       (pstate (unread-char pstate))) ; % :
                    (retok (lexeme-token (token-punctuator "%:"))
                           (make-span :start first-pos :end pos2)
                           pstate))))))
             (t ; % : other
              (b* ((pstate (unread-char pstate))) ; % :
                (retok (lexeme-token (token-punctuator "%:"))
                       (make-span :start first-pos :end pos2)
                       pstate))))))
         (t ; % other
          (b* ((pstate (unread-char pstate))) ; %
            (retok (lexeme-token (token-punctuator "%"))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

     ((= char (char-code #\<)) ; <
      (b* (((erp char2 pos2 pstate) (read-char pstate)))
        (cond
         ((not char2) ; < EOF
          (retok (lexeme-token (token-punctuator "<"))
                 (make-span :start first-pos :end first-pos)
                 pstate))
         ((= char2 (char-code #\<)) ; < <
          (b* (((erp char3 pos3 pstate) (read-char pstate)))
            (cond
             ((not char3) ; < < EOF
              (retok (lexeme-token (token-punctuator "<<"))
                     (make-span :start first-pos :end pos2)
                     pstate))
             ((= char3 (char-code #\=)) ; < < =
              (retok (lexeme-token (token-punctuator "<<="))
                     (make-span :start first-pos :end pos3)
                     pstate))
             (t ; < < other
              (b* ((pstate (unread-char pstate))) ; < <
                (retok (lexeme-token (token-punctuator "<<"))
                       (make-span :start first-pos :end pos2)
                       pstate))))))
         ((= char2 (char-code #\=)) ; < =
          (retok (lexeme-token (token-punctuator "<="))
                 (make-span :start first-pos :end pos2)
                 pstate))
         ((= char2 (char-code #\:)) ; < :
          (retok (lexeme-token (token-punctuator "<:"))
                 (make-span :start first-pos :end pos2)
                 pstate))
         ((= char2 (char-code #\%)) ; < %
          (retok (lexeme-token (token-punctuator "<%"))
                 (make-span :start first-pos :end pos2)
                 pstate))
         (t ; < other
          (b* ((pstate (unread-char pstate))) ; <
            (retok (lexeme-token (token-punctuator "<"))
                   (make-span :start first-pos :end first-pos)
                   pstate))))))

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
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-lex-lexeme-cond
    (implies (and (not erp)
                  lexeme?)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-token ((pstate parstatep))
  :returns (mv erp
               (token? token-optionp)
               (span spanp)
               (new-pstate parstatep))
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
  (b* (((reterr) nil (irr-span) (irr-parstate))
       ((parstate pstate) pstate)
       ((when (consp pstate.tokens-unread))
        (b* ((token+span (car pstate.tokens-unread)))
          (retok (token+span->token token+span)
                 (token+span->span token+span)
                 (change-parstate
                  pstate
                  :tokens-unread (cdr pstate.tokens-unread)
                  :tokens-read (cons token+span pstate.tokens-read)
                  :chars-read nil)))))
    (read-token-loop pstate))

  :prepwork

  ((define read-token-loop ((pstate parstatep))
     :returns (mv erp
                  (token? token-optionp)
                  (span spanp)
                  (new-pstate parstatep))
     :parents nil
     (b* (((reterr) nil (irr-span) (irr-parstate))
          ((erp lexeme? span pstate) (lex-lexeme pstate))
          ((when (not lexeme?))
           (retok nil span pstate))
          ((when (lexeme-case lexeme? :token))
           (b* ((token (lexeme-token->unwrap lexeme?))
                (pstate (change-parstate
                         pstate
                         :tokens-read (cons (make-token+span
                                             :token token
                                             :span span)
                                            (parstate->tokens-read pstate)))))
             (retok token span pstate))))
       (read-token-loop pstate))
     :measure (parsize pstate)
     :hints (("Goal" :in-theory (enable o< o-finp)))

     ///

     (defret parsize-of-read-token-loop-uncond
       (<= (parsize new-pstate)
           (parsize pstate))
       :rule-classes :linear
       :hints (("Goal"
                :induct t
                :in-theory (enable parsize))
               '(:use parsize-of-lex-lexeme-uncond)))

     (defret parsize-of-read-token-loop-cond
       (implies (and (not erp)
                     token?)
                (<= (parsize new-pstate)
                    (1- (parsize pstate))))
       :rule-classes :linear
       :hints (("Goal"
                :induct t
                :in-theory (enable parsize))
               '(:use parsize-of-lex-lexeme-cond)))))

  ///

  (defret parsize-of-read-token-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (parsize len fix)
                             (parsize-of-read-token-loop-uncond))
             :use parsize-of-read-token-loop-uncond)))

  (defret parsize-of-read-token-cond
    (implies (and (not erp)
                  token?)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (parsize len fix)
                             (parsize-of-read-token-loop-cond))
             :use parsize-of-read-token-loop-cond))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-token ((pstate parstatep))
  :returns (new-pstate parstatep)
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
  (b* (((parstate pstate) pstate)
       ((unless (consp pstate.tokens-read))
        (raise "Internal error: no token to unread.")
        (change-parstate pstate
                         :tokens-unread (cons (make-token+span
                                               :token (irr-token)
                                               :span (irr-span))
                                              pstate.tokens-unread)))
       (token+span (car pstate.tokens-read)))
    (change-parstate pstate
                     :tokens-unread (cons token+span pstate.tokens-unread)
                     :tokens-read (cdr pstate.tokens-read)))

  ///

  (defret parsize-of-unread-token
    (equal (parsize new-pstate)
           (1+ (parsize pstate)))
    :hints (("Goal" :in-theory (enable parsize len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-tokens ((n natp) (pstate parstatep))
  :returns (new-pstate parstatep)
  :short "Unread a specified number of tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "This repeatedly calls @(tsee unread-token)
     to unread zero or more tokens.
     The number of tokens is specified by @('n').
     This number may be 0."))
  (b* (((when (zp n)) (parstate-fix pstate))
       (pstate (unread-token pstate)))
    (unread-tokens (1- n) pstate))

  ///

  (defret parsize-of-unread-tokens
    (equal (parsize new-pstate)
           (+ (parsize pstate) (nfix n)))
    :hints (("Goal"
             :induct t
             :in-theory (enable nfix fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-punctuator ((punct stringp) (pstate parstatep))
  :returns (mv erp (span spanp) (new-pstate parstatep))
  :short "Read a specific punctuator token."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a specific punctuator.
     We pass the string for the punctuator,
     and we read the next token,
     ensuring it exists and it is that punctuator."))
  (b* (((reterr) (irr-span) (irr-parstate))
       ((erp token span pstate) (read-token pstate))
       ((unless (equal token (token-punctuator punct))) ; implies non-nil
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected (msg "the punctuator ~x0" punct)
                    :found (token-to-msg token))))
    (retok span pstate))

  ///

  (defret parsize-of-read-punctuator-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-read-punctuator-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-keyword ((keywd stringp) (pstate parstatep))
  :returns (mv erp (span spanp) (new-pstate parstatep))
  :short "Read a specific keyword token."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a specific keyword.
     We pass the string for the keyword,
     and we read the next token,
     ensuring it exists and it is that keyword."))
  (b* (((reterr) (irr-span) (irr-parstate))
       ((erp token span pstate) (read-token pstate))
       ((unless (equal token (token-keyword keywd))) ; implies non-nil
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected (msg "the keyword \"~s0\"" keywd)
                    :found (token-to-msg token))))
    (retok span pstate))

  ///

  (defret parsize-of-read-keyword-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-read-keyword-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-stringlit ((pstate parstatep))
  :returns (mv erp (stringlit stringlitp) (span spanp) (new-pstate parstatep))
  :short "Read a string literal token."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a string literal token.
     We read the next token, ensuring it exists and is a string literal.
     We return the string literal if successful."))
  (b* (((reterr) (irr-stringlit) (irr-span) (irr-parstate))
       ((erp token span pstate) (read-token pstate))
       ((unless (and token
                     (token-case token :stringlit)))
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a string literal"
                    :found (token-to-msg token)))
       (stringlit (token-stringlit->unwrap token)))
    (retok stringlit span pstate))

  ///

  (defret parsize-of-read-stringlit-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-read-stringlit-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-identifier ((pstate parstatep))
  :returns (mv erp (ident identp) (span spanp) (new-pstate parstatep))
  :short "Read an identifier token."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect an identifier token.
     We read the next token, ensuring it exists and is an identifier.
     We return the identifier if successful."))
  (b* (((reterr) (irr-ident) (irr-span) (irr-parstate))
       ((erp token span pstate) (read-token pstate))
       ((unless (and token
                     (token-case token :ident)))
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier"
                    :found (token-to-msg token)))
       (ident (token-ident->unwrap token)))
    (retok ident span pstate))

  ///

  (defret parsize-of-read-ident-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-read-ident-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define record-checkpoint ((pstate parstatep))
  :returns (new-pstate parstatep)
  :short "Record a checkpoint for possible backtracking."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee parstate),
     we add (by @(tsee cons)ing) to the list of checkpoints
     the current length of the list of tokens read so far."))
  (b* ((tokens-read (parstate->tokens-read pstate))
       (checkpoints (parstate->checkpoints pstate))
       (new-checkpoints (cons (len tokens-read) checkpoints))
       (new-pstate (change-parstate pstate :checkpoints new-checkpoints)))
    new-pstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define clear-checkpoint ((pstate parstatep))
  :returns (new-pstate parstatep)
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
  (b* ((checkpoints (parstate->checkpoints pstate))
       ((unless checkpoints)
        (raise "Internal error: no checkpoint to clear.")
        (parstate-fix pstate))
       (new-checkpoints (cdr checkpoints))
       (new-pstate (change-parstate pstate :checkpoints new-checkpoints)))
    new-pstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define backtrack-checkpoint ((pstate parstatep))
  :returns (new-pstate parstatep)
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
  (b* ((checkpoints (parstate->checkpoints pstate))
       ((unless (consp checkpoints))
        (raise "Internal error: no checkpoints to backtrack.")
        (parstate-fix pstate))
       (checkpoint (car checkpoints))
       (new-chechpoints (cdr checkpoints))
       (number-tokens-read (len (parstate->tokens-read pstate)))
       (number-tokens-to-unread (- number-tokens-read checkpoint))
       ((unless (> number-tokens-to-unread 0))
        (raise "Internal error: ~
                the checkpoint ~x0 is not less than ~
                the number ~x1 of tokens read so far."
               checkpoint
               number-tokens-read)
        (parstate-fix pstate))
       (pstate (unread-tokens number-tokens-to-unread pstate))
       (new-pstate (change-parstate pstate :checkpoints new-chechpoints)))
    new-pstate)
  :prepwork
  ((defrulel verify-guards-lemma
     (implies (and (natp x)
                   (natp y)
                   (>= y x))
              (natp (+ (- x) y)))
     :enable natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-assignment-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is an assignment operator."
  (or (equal token? (token-punctuator "="))
      (equal token? (token-punctuator "*="))
      (equal token? (token-punctuator "/="))
      (equal token? (token-punctuator "%="))
      (equal token? (token-punctuator "+="))
      (equal token? (token-punctuator "-="))
      (equal token? (token-punctuator "<<="))
      (equal token? (token-punctuator ">>="))
      (equal token? (token-punctuator "&="))
      (equal token? (token-punctuator "^="))
      (equal token? (token-punctuator "|=")))
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
  (cond ((equal token (token-punctuator "=")) (binop-asg))
        ((equal token (token-punctuator "*=")) (binop-asg-mul))
        ((equal token (token-punctuator "/=")) (binop-asg-div))
        ((equal token (token-punctuator "%=")) (binop-asg-rem))
        ((equal token (token-punctuator "+=")) (binop-asg-add))
        ((equal token (token-punctuator "-=")) (binop-asg-sub))
        ((equal token (token-punctuator "<<=")) (binop-asg-shl))
        ((equal token (token-punctuator ">>=")) (binop-asg-shr))
        ((equal token (token-punctuator "&=")) (binop-asg-and))
        ((equal token (token-punctuator "^=")) (binop-asg-xor))
        ((equal token (token-punctuator "|=")) (binop-asg-ior))
        (t (prog2$ (impossible) (irr-binop))))
  :guard-hints (("Goal" :in-theory (enable token-assignment-operator-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-equality-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is an equality operator."
  (or (equal token? (token-punctuator "=="))
      (equal token? (token-punctuator "!=")))
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
  (cond ((equal token (token-punctuator "==")) (binop-eq))
        ((equal token (token-punctuator "!=")) (binop-ne))
        (t (prog2$ (impossible) (irr-binop))))
  :prepwork ((local (in-theory (enable token-equality-operator-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-relational-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is a relational operator."
  (or (equal token? (token-punctuator "<"))
      (equal token? (token-punctuator ">"))
      (equal token? (token-punctuator "<="))
      (equal token? (token-punctuator ">=")))
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
  (cond ((equal token (token-punctuator "<")) (binop-lt))
        ((equal token (token-punctuator ">")) (binop-gt))
        ((equal token (token-punctuator "<=")) (binop-le))
        ((equal token (token-punctuator ">=")) (binop-ge))
        (t (prog2$ (impossible) (irr-binop))))
  :prepwork ((local (in-theory (enable token-relational-operator-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-shift-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is a shift operator."
  (or (equal token? (token-punctuator "<<"))
      (equal token? (token-punctuator ">>")))
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
  (cond ((equal token (token-punctuator "<<")) (binop-shl))
        ((equal token (token-punctuator ">>")) (binop-shr))
        (t (prog2$ (impossible) (irr-binop))))
  :prepwork ((local (in-theory (enable token-shift-operator-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-additive-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is an additive operator."
  (or (equal token? (token-punctuator "+"))
      (equal token? (token-punctuator "-")))
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
  (cond ((equal token (token-punctuator "+")) (binop-add))
        ((equal token (token-punctuator "-")) (binop-sub))
        (t (prog2$ (impossible) (irr-binop))))
  :prepwork ((local (in-theory (enable token-additive-operator-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-expr-cast/add-or-cast/sub-ambig ((token tokenp)
                                              (ident identp)
                                              (expr exprp))
  :guard (token-additive-operator-p token)
  :returns (new-expr exprp)
  :short "Create an ambiguous expression based on
          a token that is an additive operator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is introduced just to avoid case splits in
     the large clique of mutually recursive parsing functions defined below.
     In certain cases, based on a parsed additive operator,
     we need to construct two different kinds of
     syntactically ambiguous expressions in our abstract syntax."))
  (cond ((equal token (token-punctuator "+"))
         (make-expr-cast/add-ambig :type/arg1 ident
                                   :arg/arg2 expr))
        ((equal token (token-punctuator "-"))
         (make-expr-cast/sub-ambig :type/arg1 ident
                                   :arg/arg2 expr))
        (t (prog2$ (impossible) (irr-expr))))
  :guard-hints (("Goal" :in-theory (enable token-additive-operator-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-multiplicative-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is a multiplicative operator."
  (or (equal token? (token-punctuator "*"))
      (equal token? (token-punctuator "/"))
      (equal token? (token-punctuator "%")))
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
  (cond ((equal token (token-punctuator "*")) (binop-mul))
        ((equal token (token-punctuator "/")) (binop-div))
        ((equal token (token-punctuator "%")) (binop-rem))
        (t (prog2$ (impossible) (irr-binop))))
  :prepwork ((local (in-theory (enable token-multiplicative-operator-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-preinc/predec-operator-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is
          a preincrement or predecrement operator."
  (or (equal token? (token-punctuator "++"))
      (equal token? (token-punctuator "--")))
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
  (cond ((equal token (token-punctuator "++")) (unop-preinc))
        ((equal token (token-punctuator "--")) (unop-predec))
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
  (or (equal token? (token-punctuator "&"))
      (equal token? (token-punctuator "*"))
      (equal token? (token-punctuator "+"))
      (equal token? (token-punctuator "-"))
      (equal token? (token-punctuator "~"))
      (equal token? (token-punctuator "!")))
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
  (cond ((equal token (token-punctuator "&")) (unop-address))
        ((equal token (token-punctuator "*")) (unop-indir))
        ((equal token (token-punctuator "+")) (unop-plus))
        ((equal token (token-punctuator "-")) (unop-minus))
        ((equal token (token-punctuator "~")) (unop-bitnot))
        ((equal token (token-punctuator "!")) (unop-lognot))
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
           (token-case token? :stringlit)
           (equal token? (token-punctuator "("))
           (equal token? (token-keyword "_Generic"))))
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
     or a @('_Alignof') keyword."))
  (or (token-primary-expression-start-p token?)
      (equal token? (token-punctuator "++"))
      (equal token? (token-punctuator "--"))
      (equal token? (token-punctuator "&"))
      (equal token? (token-punctuator "*"))
      (equal token? (token-punctuator "+"))
      (equal token? (token-punctuator "-"))
      (equal token? (token-punctuator "~"))
      (equal token? (token-punctuator "!"))
      (equal token? (token-keyword "sizeof"))
      (equal token? (token-keyword "_Alignof")))
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
  (or (equal token? (token-punctuator "["))
      (equal token? (token-punctuator "("))
      (equal token? (token-punctuator "."))
      (equal token? (token-punctuator "->"))
      (equal token? (token-punctuator "++"))
      (equal token? (token-punctuator "--")))
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
  (or (equal token? (token-keyword "typedef"))
      (equal token? (token-keyword "extern"))
      (equal token? (token-keyword "static"))
      (equal token? (token-keyword "_Thread_local"))
      (equal token? (token-keyword "auto"))
      (equal token? (token-keyword "register")))
  ///

  (defrule non-nil-when-token-storage-class-specifier-p
    (implies (token-storage-class-specifier-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-storage-class-specifier ((token tokenp))
  :guard (token-storage-class-specifier-p token)
  :returns (stoclaspec stoclaspecp)
  :short "Map a token that is a storage class specifier
          to the correspoding storage class specifier."
  (cond ((equal token (token-keyword "typedef")) (stoclaspec-tydef))
        ((equal token (token-keyword "extern")) (stoclaspec-extern))
        ((equal token (token-keyword "static")) (stoclaspec-static))
        ((equal token (token-keyword "_Thread_local")) (stoclaspec-threadloc))
        ((equal token (token-keyword "auto")) (stoclaspec-auto))
        ((equal token (token-keyword "register")) (stoclaspec-register))
        (t (prog2$ (impossible) (irr-stoclaspec))))
  :prepwork ((local (in-theory (enable token-storage-class-specifier-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-type-specifier-keyword-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is a type specifier
          that consists of a single keyword."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are a number of type specifiers that consist of single keywords."))
  (or (equal token? (token-keyword "void"))
      (equal token? (token-keyword "char"))
      (equal token? (token-keyword "short"))
      (equal token? (token-keyword "int"))
      (equal token? (token-keyword "long"))
      (equal token? (token-keyword "float"))
      (equal token? (token-keyword "double"))
      (equal token? (token-keyword "signed"))
      (equal token? (token-keyword "unsigned"))
      (equal token? (token-keyword "_Bool"))
      (equal token? (token-keyword "_Complex")))
  ///

  (defrule non-nil-when-token-type-specifier-keyword-p
    (implies (token-type-specifier-keyword-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-type-specifier-keyword ((token tokenp))
  :guard (token-type-specifier-keyword-p token)
  :returns (tyspec tyspecp)
  :short "Map a token that is a type specifier consisting of a single keyword
          to the corresponding type specifier."
  (cond ((equal token (token-keyword "void")) (tyspec-void))
        ((equal token (token-keyword "char")) (tyspec-char))
        ((equal token (token-keyword "short")) (tyspec-short))
        ((equal token (token-keyword "int")) (tyspec-int))
        ((equal token (token-keyword "long")) (tyspec-long))
        ((equal token (token-keyword "float")) (tyspec-float))
        ((equal token (token-keyword "double")) (tyspec-double))
        ((equal token (token-keyword "signed")) (tyspec-signed))
        ((equal token (token-keyword "unsigned")) (tyspec-unsigned))
        ((equal token (token-keyword "_Bool")) (tyspec-bool))
        ((equal token (token-keyword "_Complex")) (tyspec-complex))
        (t (prog2$ (impossible) (irr-tyspec))))
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
      (equal token? (token-keyword "_Atomic"))
      (equal token? (token-keyword "struct"))
      (equal token? (token-keyword "union"))
      (equal token? (token-keyword "enum"))
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
    "All type qualifiers consist of single keywords."))
  (or (equal token? (token-keyword "const"))
      (equal token? (token-keyword "restrict"))
      (equal token? (token-keyword "volatile"))
      (equal token? (token-keyword "_Atomic")))
  ///

  (defrule non-nil-when-token-type-qualifier-p
    (implies (token-type-qualifier-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-type-qualifier ((token tokenp))
  :guard (token-type-qualifier-p token)
  :returns (tyqual tyqualp)
  :short "Map a token that is a type qualifier
          to the correspoding type qualifier."
  (cond ((equal token (token-keyword "const")) (tyqual-const))
        ((equal token (token-keyword "restrict")) (tyqual-restrict))
        ((equal token (token-keyword "volatile")) (tyqual-volatile))
        ((equal token (token-keyword "_Atomic")) (tyqual-atomic))
        (t (prog2$ (impossible) (irr-tyqual))))
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
     the starts of type names."))
  (or (token-type-specifier-start-p token?)
      (token-type-qualifier-p token?)
      (equal token? (token-keyword "_Alignas")))
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
    "All function specifiers consist of single keywords."))
  (or (equal token? (token-keyword "inline"))
      (equal token? (token-keyword "_Noreturn")))
  ///

  (defrule non-nil-when-token-function-specifier-p
    (implies (token-function-specifier-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-function-specifier ((token tokenp))
  :guard (token-function-specifier-p token)
  :returns (funspec funspecp)
  :short "Map a token that is a function specifier
          to the corresponding function specifier."
  (cond ((equal token (token-keyword "inline")) (funspec-inline))
        ((equal token (token-keyword "_Noreturn")) (funspec-noreturn))
        (t (prog2$ (impossible) (irr-funspec))))
  :prepwork ((local (in-theory (enable token-function-specifier-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-declaration-specifier-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a declaration specifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put together the five cases that define declaration specifiers."))
  (or (token-storage-class-specifier-p token?)
      (token-type-specifier-start-p token?)
      (token-type-qualifier-p token?)
      (token-function-specifier-p token?)
      (equal token? (token-keyword "_Alignas")))
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
    "A type name always starts with a (non-empty) sequence of
     type specifiers, type qualifiers, or alignment specifiers.
     So it has the same starts of a specifier or qualifier."))
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
  (or (equal token? (token-punctuator "("))
      (equal token? (token-punctuator "[")))
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
  (or (equal token? (token-punctuator "*"))
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
      (equal token? (token-punctuator "(")))
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
  (or (equal token? (token-punctuator "*"))
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
      (equal token? (token-punctuator ":")))
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
     or with the @('_Static_assert') keyword."))
  (or (token-specifier/qualifier-start-p token?)
      (equal token? (token-keyword "_Static_assert")))
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
  (or (equal token? (token-punctuator "["))
      (equal token? (token-punctuator ".")))
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
      (equal token? (token-punctuator "{")))
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

(fty::deftagsum partys/declor/ambig
  :short "Fixtype of possible classifications of certain constructs."
  :long
  (xdoc::topstring
   (xdoc::p
    "Under certain circumstances,
     the parser needs to figure out whether
     what comes next in the input is a parameter type list or a declarator:
     see the discussion in @(tsee tyspec).
     However, this cannot be always disambiguated,
     and so we need a third outcome for this case.
     This fixtype is the result of @(tsee classify-partys/declor/ambig)."))
  (:partys ())
  (:declor ())
  (:ambig ())
  :pred partys/declor/ambig-p)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-partys/declor/ambig
  :short "An irrelevant possible classifications of certain constructs."
  :type partys/declor/ambig-p
  :body (partys/declor/ambig-ambig))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define classify-partys/declor/ambig ((pstate parstatep))
  :returns (mv erp
               (classification partys/declor/ambig-p)
               (num-tokens natp :rule-classes (:rewrite :type-prescription))
               (new-pstate parstatep))
  :short "Attempt to classify what comes next in the input
          as a parameter type list or a (possibly abstract) declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "See the discussion in @(tsee tyspec) for background,
     specifically the part regarding the @('(I1(I2(...(In)...)))') construction.
     This function is used to explore that construction,
     after having parsed the open parenthesis just before @('I1').
     More precisely,
     this function is called when parsing
     declaration specifier lists or specifier/qualifier lists,
     and specifically just after parsing one of the following:")
   (xdoc::codeblock
    "_Atomic ( I ) ("
    "I (")
   (xdoc::p
    "where @('I') is an identifier.
     If what comes next is an identifier,
     we may be in the @('(I1(I2(...(In)...)))') situation;
     this is why this function is recursive.
     If we are indeed in this situation,
     we return a result indicating ambiguity.
     If instead we are not in that situation,
     we can resolve the ambiguity, and return a non-ambiguous result.
     As explained in @(tsee tyspec),
     the resolution propagates backwards,
     flipping the classifications.
     See the more detailed comments in the code of this function.")
   (xdoc::p
    "If there are no errors,
     besides returning the (possibly ambiguous) classification,
     this function also returns the number of tokens it has read
     so that the caller can put them back into the parsing state.
     The reason why this function does not put back the tokens itself
     is that, after it is recursively called,
     we may need to read more tokens (see code and comments)."))
  (b* (((reterr) (irr-partys/declor/ambig) 0 (irr-parstate))
       ;; When we get here, we have already parsed an open parenthesis
       ;; (
       ;; following _Atomic(ident) or ident.
       ((erp token span pstate) (read-token pstate)))
    (cond
     ;; If token is an identifier,
     ;; things are still ambiguous.
     ((and token (token-case token :ident)) ; ( ident1
      (b* (((erp token2 span2 pstate) (read-token pstate)))
        (cond
         ;; If token2 is an open parenthesis,
         ;; things are still ambiguous.
         ((equal token2 (token-punctuator "(")) ; ( ident1 (
          ;; We recursively call this function to attempt to classify the rest.
          (b* (((erp classification num-tokens pstate)
                (classify-partys/declor/ambig pstate)))
            (partys/declor/ambig-case
             classification
             ;; If the rest is a parameter type list,
             ;; this must be a (function) declarator.
             :partys ; ( ident1 ( partys...
             (retok (partys/declor/ambig-declor) (+ num-tokens 2) pstate)
             ;; If the rest is a (possibly abstract) declarator,
             ;; this must be a type specifier (typedef name),
             ;; and thus a parameter type list.
             :declor ; ( ident1 ( declor/absdeclor...
             (retok (partys/declor/ambig-partys) (+ num-tokens 2) pstate)
             ;; If the rest is ambiguous, it is
             ;; ident2(ident3(...(identN)...))),
             ;; whose last closed parenthesis matches
             ;; the open parenthesis just before ident2.
             ;; So with what we have already parsed
             ;; we have (ident1(ident2(ident3(...(identN)...))),
             ;; where we need a closed parenthesis to match
             ;; the open one just before ident1,
             ;; otherwise we don't quite have the ambiguous pattern
             ;; (see details just below).
             :ambig ; ( ident1 ( ident2 ( ident3 ( ... ( identN ) ... ) ) )
             (b* (((erp token3 span3 pstate) (read-token pstate)))
               (cond
                ;; If token3 is a closed parenthesis,
                ;; which matches the open one before ident1,
                ;; we have the complete ambiguous pattern.
                ((equal token3 (token-punctuator ")"))
                 ;; ( ident1 ( ident2 ( ident3 ( ... ( identN ) ... ) ) ) )
                 (retok (partys/declor/ambig-ambig) (+ num-tokens 3) pstate))
                ;; If token3 is a comma,
                ;; ident1(ident2(ident3(...(identN)...)))
                ;; must be a paramter declaration,
                ;; so we have a parameter type list.
                ((equal token3 (token-punctuator ","))
                 ;; ( ident1 ( ident2 ( ident3 ( ... ( identN ) ... ) ) ) ,
                 (retok (partys/declor/ambig-partys) (+ num-tokens 3) pstate))
                ;; If token3 is
                ;; an open parenthesis or an open square bracket,
                ;; (ident2(ident3(...(identN)...))) must be a declarator,
                ;; and thus ident1 must be a type specifier,
                ;; and we have a parameter type list.
                ((or (equal token3 (token-punctuator "("))
                     (equal token3 (token-punctuator "[")))
                 ;; ( ident1 ( ident2 ( ident3 ( ... ( identN ) ... ) ) ) (
                 ;; ( ident1 ( ident2 ( ident3 ( ... ( identN ) ... ) ) ) [
                 (retok (partys/declor/ambig-partys) (+ num-tokens 3) pstate))
                ;; In all other cases, it is an error.
                (t
                 (reterr-msg :where (position-to-msg (span->start span3))
                             :expected "an open parenthesis ~
                                        or a closed parenthesis ~
                                        or an open square bracket ~
                                        or a comma"
                             :found (token-to-msg token3))))))))
         ;; If token2 is a closed parenthesis,
         ;; we have an ambiguity.
         ;; This is the "base case" of the next of parenthesized identifiers,
         ;; i.e. N = 1.
         ((equal token2 (token-punctuator ")")) ; ( ident1 )
          (retok (partys/declor/ambig-ambig) 2 pstate))
         ;; If token2 may start a declaration specifier,
         ;; which includes the case of a specifier or qualifier,
         ;; we must have a parameter type list.
         ((token-declaration-specifier-start-p token2) ; ( ident declspec...
          (retok (partys/declor/ambig-partys) 2 pstate))
         ;; If token2 is an open square bracket,
         ;; we must have a declarator.
         ((equal token2 (token-punctuator "[")) ; ( ident [
          (retok (partys/declor/ambig-declor) 2 pstate))
         ;; If token2 is a star,
         ;; we must have a parameter type declaration.
         ((equal token2 (token-punctuator "*")) ; ( ident *
          (retok (partys/declor/ambig-partys) 2 pstate))
         ;; In all other cases, we have an error.
         (t ; ( ident other
          (reterr-msg :where (position-to-msg (span->start span2))
                      :expected "an identifier ~
                                 or an open parenthesis ~
                                 or a closed parenthesis ~
                                 or an open square bracket ~
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
                      :found (token-to-msg token2))))))
     ;; If token may start a declaration specifier,
     ;; which includes a specifier or qualifier,
     ;; we must have a parameter type list.
     ((token-declaration-specifier-start-p token) ; ( declspec...
      (retok (partys/declor/ambig-partys) 1 pstate))
     ;; If token may start a declarator or an abstract declarator
     ;; we must have a declarator.
     ((or (token-declarator-start-p token) ; ( declor...
          (token-abstract-declarator-start-p token)) ; ( absdeclor...
      (retok (partys/declor/ambig-declor) 1 pstate))
     ;; If token is a closed parenthesis,
     ;; it is like the case of having a parameter declaration,
     ;; even though there are no actual parameter declarations
     ;; (i.e. we have a function declarator with no arguments).
     ((equal token (token-punctuator ")")) ; ( )
      (retok (partys/declor/ambig-partys) 1 pstate))
     ;; In all other cases, we have an error.
     (t ; ( other
      (reterr-msg :where (position-to-msg (span->start span))
                  :expected "an identifier ~
                             or an open parenthesis ~
                             or a closed parenthesis ~
                             or an open square bracket ~
                             or a star"
                  :found (token-to-msg token)))))
  :measure (parsize pstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns

  ///

  (defret parsize-of-classify-partys/declor/ambig-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-classify-partys/declor/ambig-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (- (parsize pstate) num-tokens)))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-type-qualifier-list ((pstate parstatep))
  :returns (mv erp (tyquals tyqual-listp) (span spanp) (new-pstate parstatep))
  :parents (parser parse-exprs/decls)
  :short "Parse a list of one or more type qualifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "We parse the first one, which must exist.
     Then we check the next token to see if there is be another one,
     in which case we put it back and recursively parse a type qualifier list,
     otherwise we put back it back and return."))
  (b* (((reterr) nil (irr-span) (irr-parstate))
       ((erp token span pstate) (read-token pstate)))
    (cond
     ((token-type-qualifier-p token) ; tyqual
      (b* ((tyqual (token-to-type-qualifier token))
           ((erp token & pstate) (read-token pstate)))
        (cond
         ((token-type-qualifier-p token) ; tyqual tyqual
          (b* ((pstate (unread-token pstate)) ; tyqual
               ((erp tyquals last-span pstate) ; tyqual tyquals
                (parse-type-qualifier-list pstate)))
            (retok (cons tyqual tyquals)
                   (span-join span last-span)
                   pstate)))
         (t ; tyqual other
          (b* ((pstate (if token (unread-token pstate) pstate)))
            (retok (list tyqual) span pstate))))))
     (t ; other
      (reterr-msg :where (position-to-msg (span->start span))
                  :expected "a keyword in {~
                               const, ~
                               restrict, ~
                               volatile, ~
                               _Atomic~
                               }"
                  :found (token-to-msg token)))))
  :measure (parsize pstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-type-qualifier-list-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-parse-type-qualifier-list-cond
    (implies (and (not erp)
                  token?)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-pointer ((pstate parstatep))
  :returns (mv erp
               (tyqualss tyqual-list-listp)
               (span spanp)
               (new-pstate parstatep))
  :parents (parser parse-exprs/decls)
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
  (b* (((reterr) nil (irr-span) (irr-parstate))
       ((erp span pstate) (read-punctuator "*" pstate)) ; *
       ((erp token & pstate) (read-token pstate)))
    (cond
     ((token-type-qualifier-p token) ; * tyqual
      (b* ((pstate (unread-token pstate)) ; *
           ((erp tyquals span2 pstate) ; * tyquals
            (parse-type-qualifier-list pstate))
           ((erp token & pstate) (read-token pstate)))
        (cond
         ((equal token (token-punctuator "*")) ; * tyquals *
          (b* ((pstate (unread-token pstate)) ; * tyquals
               ((erp tyqualss last-span pstate) ; * tyquals * tyquals ...
                (parse-pointer pstate)))
            (retok (cons tyquals tyqualss)
                   (span-join span last-span)
                   pstate)))
         (t ; * tyquals other
          (b* ((pstate (if token (unread-token pstate) pstate))) ; * tyquals
            (retok (list tyquals) (span-join span span2) pstate))))))
     ((equal token (token-punctuator "*")) ; * *
      (b* ((pstate (unread-token pstate)) ; *
           ((erp tyqualss last-span pstate) ; * * [tyquals] ...
            (parse-pointer pstate)))
        (retok (cons nil tyqualss) (span-join span last-span) pstate)))
     (t ; * other
      (b* ((pstate (if token (unread-token pstate) pstate)))
        (retok (list nil) span pstate)))))
  :measure (parsize pstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-pointer-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-parse-pointer-cond
    (implies (and (not erp)
                  token?)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

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

  (define parse-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp expr span pstate) (parse-assignment-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible)))
      (parse-expression-rest expr span pstate))
    :measure (two-nats-measure (parsize pstate) 16))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-expression-rest ((prev-expr exprp)
                                 (prev-span spanp)
                                 (pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ;; prev-expr
         ((erp token & pstate) (read-token pstate))
         ((when (not (equal token (token-punctuator ",")))) ; prev-expr not,
          (b* ((pstate (if token (unread-token pstate) pstate))) ; prev-expr
            (retok (expr-fix prev-expr) (span-fix prev-span) pstate)))
         ;; prev-expr ,
         (psize (parsize pstate))
         ((erp expr expr-span pstate) ; prev-expr , expr
          (parse-assignment-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         (curr-expr (make-expr-comma :first prev-expr :next expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-expression-rest curr-expr curr-span pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-assignment-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp expr span pstate) (parse-conditional-expression pstate)) ; expr
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         ((when (not (expr-unary/postfix/primary-p expr)))
          (retok expr span pstate))
         ((erp token & pstate) (read-token pstate))
         ((when (not (token-assignment-operator-p token))) ; expr not-asgop
          (b* ((pstate (if token (unread-token pstate) pstate))) ; expr
            (retok expr span pstate)))
         ;; expr asgop
         (asgop (token-to-assignment-operator token))
         ((erp expr2 span2 pstate) ; expr asgop expr2
          (parse-assignment-expression pstate)))
      (retok (make-expr-binary :op asgop
                               :arg1 expr
                               :arg2 expr2)
             (span-join span span2)
             pstate))
    :measure (two-nats-measure (parsize pstate) 15))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-conditional-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp expr span pstate) (parse-logical-or-expression pstate)) ; expr
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         ((erp token & pstate) (read-token pstate))
         ((when (not (equal token (token-punctuator "?")))) ; expr not?
          (b* ((pstate (if token (unread-token pstate) pstate))) ; expr
            (retok expr span pstate)))
         ;; expr ?
         (psize (parsize pstate))
         ((erp expr2 & pstate) (parse-expression pstate)) ; expr ? expr2
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         ((erp & pstate) (read-punctuator ":" pstate)) ; expr ? expr2 :
         ((erp expr3 span3 pstate) ; expr ? expr2 : expr3
          (parse-conditional-expression pstate)))
      (retok (make-expr-cond :test expr :then expr2 :else expr3)
             (span-join span span3)
             pstate))
    :measure (two-nats-measure (parsize pstate) 14))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-logical-or-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a logical disjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp expr span pstate) (parse-logical-and-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible)))
      (parse-logical-or-expression-rest expr span pstate))
    :measure (two-nats-measure (parsize pstate) 13))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-logical-or-expression-rest ((prev-expr exprp)
                                            (prev-span spanp)
                                            (pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a logical disjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-logical-or-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ;; prev-expr
         ((erp token & pstate) (read-token pstate))
         ((when (not (equal token (token-punctuator "||")))) ; prev-expr not||
          (b* ((pstate (if token (unread-token pstate) pstate))) ; prev-expr
            (retok (expr-fix prev-expr) (span-fix prev-span) pstate)))
         ;; prev-expr ||
         (psize (parsize pstate))
         ((erp expr expr-span pstate) ; prev-expr || expr
          (parse-logical-and-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         (curr-expr (make-expr-binary :op (binop-logor)
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-logical-or-expression-rest curr-expr curr-span pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-logical-and-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a logical conjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp expr span pstate) (parse-inclusive-or-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible)))
      (parse-logical-and-expression-rest expr span pstate))
    :measure (two-nats-measure (parsize pstate) 12))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-logical-and-expression-rest ((prev-expr exprp)
                                             (prev-span spanp)
                                             (pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a logical conjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-logical-and-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ;; prev-expr
         ((erp token & pstate) (read-token pstate))
         ((when (not (equal token (token-punctuator "&&")))) ; prev-expr not&&
          (b* ((pstate (if token (unread-token pstate) pstate))) ; prev-expr
            (retok (expr-fix prev-expr) (span-fix prev-span) pstate)))
         ;; prev-expr &&
         (psize (parsize pstate))
         ((erp expr expr-span pstate) ; prev-expr && expr
          (parse-inclusive-or-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         (curr-expr (make-expr-binary :op (binop-logand)
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-logical-and-expression-rest curr-expr curr-span pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-inclusive-or-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse an inclusive disjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp expr span pstate) (parse-exclusive-or-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible)))
      (parse-inclusive-or-expression-rest expr span pstate))
    :measure (two-nats-measure (parsize pstate) 11))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-inclusive-or-expression-rest ((prev-expr exprp)
                                              (prev-span spanp)
                                              (pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of an inclusive disjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-inclusive-or-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ;; prev-expr
         ((erp token & pstate) (read-token pstate))
         ((when (not (equal token (token-punctuator "|")))) ; prev-expr not|
          (b* ((pstate (if token (unread-token pstate) pstate))) ; prev-expr
            (retok (expr-fix prev-expr) (span-fix prev-span) pstate)))
         ;; prev-expr |
         (psize (parsize pstate))
         ((erp expr expr-span pstate) ; prev-expr | expr
          (parse-exclusive-or-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         (curr-expr (make-expr-binary :op (binop-bitior)
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-inclusive-or-expression-rest curr-expr curr-span pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-exclusive-or-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse an exclusive disjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp expr span pstate) (parse-and-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible)))
      (parse-exclusive-or-expression-rest expr span pstate))
    :measure (two-nats-measure (parsize pstate) 10))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-exclusive-or-expression-rest ((prev-expr exprp)
                                              (prev-span spanp)
                                              (pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of an exclusive disjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-exclusive-or-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ;; prev-expr
         ((erp token & pstate) (read-token pstate))
         ((when (not (equal token (token-punctuator "^")))) ; prev-expr not^
          (b* ((pstate (if token (unread-token pstate) pstate)))
            (retok (expr-fix prev-expr) (span-fix prev-span) pstate)))
         ;; prev-expr ^
         (psize (parsize pstate))
         ((erp expr expr-span pstate) ; prev-expr ^ expr
          (parse-and-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         (curr-expr (make-expr-binary :op (binop-bitxor)
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-exclusive-or-expression-rest curr-expr curr-span pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-and-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a conjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp expr span pstate) (parse-equality-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible)))
      (parse-and-expression-rest expr span pstate))
    :measure (two-nats-measure (parsize pstate) 9))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-and-expression-rest ((prev-expr exprp)
                                     (prev-span spanp)
                                     (pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a conjunction expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-and-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ;; prev-expr
         ((erp token & pstate) (read-token pstate))
         ((when (not (equal token (token-punctuator "&")))) ; prev-expr not&
          (b* ((pstate (if token (unread-token pstate) pstate))) ; prev-expr
            (retok (expr-fix prev-expr) (span-fix prev-span) pstate)))
         ;; prev-expr &
         (psize (parsize pstate))
         ((erp expr expr-span pstate) ; prev-expr & expr
          (parse-equality-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         (curr-expr (make-expr-binary :op (binop-bitand)
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-and-expression-rest curr-expr curr-span pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-equality-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse an equality expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp expr span pstate) (parse-relational-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible)))
      (parse-equality-expression-rest expr span pstate))
    :measure (two-nats-measure (parsize pstate) 8))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-equality-expression-rest ((prev-expr exprp)
                                          (prev-span spanp)
                                          (pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of an equality expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-equality-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ;; prev-expr
         ((erp token & pstate) (read-token pstate))
         ((when (not (token-equality-operator-p token))) ; prev-expr not-eqop
          (b* ((pstate (if token (unread-token pstate) pstate))) ; prev-expr
            (retok (expr-fix prev-expr) (span-fix prev-span) pstate)))
         ;; prev-expr eqop
         (psize (parsize pstate))
         ((erp expr expr-span pstate) ;; prev-expr eqop expr
          (parse-relational-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         (op (token-to-equality-operator token))
         (curr-expr (make-expr-binary :op op
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-equality-expression-rest curr-expr curr-span pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-relational-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a relational expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp expr span pstate) (parse-shift-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible)))
      (parse-relational-expression-rest expr span pstate))
    :measure (two-nats-measure (parsize pstate) 7))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-relational-expression-rest ((prev-expr exprp)
                                            (prev-span spanp)
                                            (pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a relational expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-relational-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ;; prev-expr
         ((erp token & pstate) (read-token pstate))
         ((when (not (token-relational-operator-p token))) ; prev-expr not-relop
          (b* ((pstate (if token (unread-token pstate) pstate)))
            (retok (expr-fix prev-expr) (span-fix prev-span) pstate)))
         ;; prev-expr relop
         (psize (parsize pstate))
         ((erp expr expr-span pstate) ;; prev-expr relop expr
          (parse-shift-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         (op (token-to-relational-operator token))
         (curr-expr (make-expr-binary :op op
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-relational-expression-rest curr-expr curr-span pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-shift-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a shift expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp expr span pstate) (parse-additive-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible)))
      (parse-shift-expression-rest expr span pstate))
    :measure (two-nats-measure (parsize pstate) 6))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-shift-expression-rest ((prev-expr exprp)
                                       (prev-span spanp)
                                       (pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a shift expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-shift-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ;; prev-expr
         ((erp token & pstate) (read-token pstate))
         ((when (not (token-shift-operator-p token))) ; prev-expr not-shiftop
          (b* ((pstate (if token (unread-token pstate) pstate)))
            (retok (expr-fix prev-expr) (span-fix prev-span) pstate)))
         ;; prev-expr shiftop
         (psize (parsize pstate))
         ((erp expr expr-span pstate) ;; prev-expr shiftop expr
          (parse-additive-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         (op (token-to-shift-operator token))
         (curr-expr (make-expr-binary :op op
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-shift-expression-rest curr-expr curr-span pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-additive-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse an additive expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp expr span pstate) (parse-multiplicative-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible)))
      (parse-additive-expression-rest expr span pstate))
    :measure (two-nats-measure (parsize pstate) 5))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-additive-expression-rest ((prev-expr exprp)
                                          (prev-span spanp)
                                          (pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of an additive expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by @(tsee parse-additive-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ;; prev-expr
         ((erp token & pstate) (read-token pstate))
         ((when (not (token-additive-operator-p token))) ; prev-expr notaddop
          (b* ((pstate (if token (unread-token pstate) pstate)))
            (retok (expr-fix prev-expr) (span-fix prev-span) pstate)))
         ;; prev-expr addop
         (psize (parsize pstate))
         ((erp expr expr-span pstate) ;; prev-expr addop expr
          (parse-multiplicative-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         (op (token-to-additive-operator token))
         (curr-expr (make-expr-binary :op op
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-additive-expression-rest curr-expr curr-span pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-multiplicative-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a multiplicative expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We handle the left recursion in the grammar rule
       in the same way as for expressions:
       see @(tsee parse-expression)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp expr span pstate) (parse-cast-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible)))
      (parse-multiplicative-expression-rest expr span pstate))
    :measure (two-nats-measure (parsize pstate) 4))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-multiplicative-expression-rest ((prev-expr exprp)
                                                (prev-span spanp)
                                                (pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse the rest of a multiplicative expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This completes the job started by
       @(tsee parse-multiplicative-expression);
       it is analogous to @(tsee parse-expression-rest)."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ;; prev-expr
         ((erp token & pstate) (read-token pstate))
         ((when (not
                 (token-multiplicative-operator-p token))) ; prev-exp notmulop
          (b* ((pstate (if token (unread-token pstate) pstate)))
            (retok (expr-fix prev-expr) (span-fix prev-span) pstate)))
         ;; prev-expr mulop
         (psize (parsize pstate))
         ((erp expr expr-span pstate) ; prev-expr mulop expr
          (parse-cast-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize)))) (reterr :impossible))
         (op (token-to-multiplicative-operator token))
         (curr-expr (make-expr-binary :op op
                                      :arg1 prev-expr
                                      :arg2 expr))
         (curr-span (span-join prev-span expr-span)))
      (parse-multiplicative-expression-rest curr-expr curr-span pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-cast-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token is an open parenthesis,
       ;; we may have a cast expression proper or a unary expression,
       ;; and we may also have the ambiguity discussed in :DOC EXPR.
       ((equal token (token-punctuator "(")) ; (
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ;; If token2 is an identifier, things are still ambiguous:
           ;; the identifier could be (part of) an expression,
           ;; or it could be a type name.
           ((and token2 (token-case token2 :ident)) ; ( ident
            (b* (((erp token3 span3 pstate) (read-token pstate)))
              (cond
               ;; If token3 is a closed parenthesis,
               ;; things are still ambiguous:
               ;; we could have a parenthesized identifier expression,
               ;; or the identifier could be a type name.
               ((equal token3 (token-punctuator ")")) ; ( ident )
                (b* ((ident (token-ident->unwrap token2))
                     ((erp token4 & pstate) (read-token pstate)))
                  (cond
                   ;; If token4 is an open curly brace,
                   ;; we have resolved the ambiguity:
                   ;; we must have a compund literal.
                   ((equal token4 (token-punctuator "{")) ; ( ident ) {
                    (b* ((pstate (unread-token pstate)) ; ( ident )
                         (tyname (make-tyname
                                  :specqual (list (specqual-tyspec
                                                   (tyspec-tydef ident)))
                                  :decl? nil)))
                      (parse-compound-literal tyname span pstate)))
                   ;; If token4 is a star, it may be a unary or binary operator:
                   ;; we have a syntactic ambiguity,
                   ;; but what follows must be a cast expression,
                   ;; whether the star is unary or binary.
                   ((equal token4 (token-punctuator "*")) ; ( ident ) *
                    (b* (((erp expr last-span pstate) ; ( ident ) * expr
                          (parse-cast-expression pstate)))
                      (retok (make-expr-cast/mul-ambig
                              :type/arg1 ident
                              :arg/arg2 expr)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 is a plus or minus,
                   ;; it could be a unary or binary operator,
                   ;; similarly to the star case.
                   ;; We have a syntactic ambiguity.
                   ;; We parse a multiplicative expression after that,
                   ;; which is needed in case the plus or minus is binary.
                   ((token-additive-operator-p token4) ; ( ident ) +-
                    (b* (((erp expr last-span pstate) ; ( ident ) +- expr
                          (parse-multiplicative-expression pstate)))
                      (retok (make-expr-cast/add-or-cast/sub-ambig
                              token4 ident expr)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 is an ampersand,
                   ;; it could be a unary or binary operator,
                   ;; analogously to the cases above of start, plus, and minus.
                   ;; We parse a equality expression after that,
                   ;; in case the ampersand is binary.
                   ((or (equal token4 (token-punctuator "&")))
                    (b* (((erp expr last-span pstate) ; ( ident ) & expr
                          (parse-equality-expression pstate)))
                      (retok (make-expr-cast/and-ambig
                              :type/arg1 ident
                              :arg/arg2 expr)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 may start a (cast) expression,
                   ;; we have resolved the ambiguity:
                   ;; the identifier must be a type name,
                   ;; and we were parsing a proper cast expression all along.
                   ((token-unary-expression-start-p token4) ; ( ident ) expr...
                    (b* ((pstate (unread-token pstate)) ; ( ident )
                         ((erp expr last-span pstate) ; ( ident ) expr
                          (parse-cast-expression pstate)))
                      (retok
                       (make-expr-cast
                        :type (make-tyname
                               :specqual (list (specqual-tyspec
                                                (tyspec-tydef ident)))
                               :decl? nil)
                        :arg expr)
                       (span-join span last-span)
                       pstate)))
                   ;; If token4 may not start an expression,
                   ;; we have resolved the ambiguity:
                   ;; we must simply have a parenthesized identifier expression.
                   (t ; ( ident ) other
                    (b* ((pstate
                          (if token (unread-token pstate) pstate))) ; ( ident )
                      (retok (expr-paren (expr-ident ident))
                             (span-join span span3)
                             pstate))))))
               ;; If token3 is not a closed parenthesis,
               ;; the identifier must be the start of an expression,
               ;; so we put back the tokens and we parse an expression,
               ;; and then the closed parenthesis after that.
               (t ; ( ident other
                (b* ((pstate (if token3 (unread-token pstate) pstate)) ; ( ident
                     (pstate (unread-token pstate)) ; (
                     ((erp expr & pstate) ; ( expr
                      (parse-expression pstate))
                     ((erp last-span pstate) ; ( expr )
                      (read-punctuator ")" pstate)))
                  (retok (expr-paren expr)
                         (span-join span last-span)
                         pstate))))))
           ;; If token2 may start an expression,
           ;; it means that the cast expression is in fact a unary expression,
           ;; and so we go back to the beginning,
           ;; unreading the start of the expression and the open parenthesis,
           ;; and we attempt to parse a unary expression.
           ((token-expression-start-p token2) ; ( expr...
            (b* ((pstate (unread-token pstate)) ; (
                 (pstate (unread-token pstate))) ;
              (parse-unary-expression pstate)))
           ((token-type-name-start-p token2) ; ( typename...
            (b* ((pstate (unread-token pstate)) ; (
                 (psize (parsize pstate))
                 ((erp tyname & pstate) ; ( typename
                  (parse-type-name pstate))
                 ((unless (mbt (<= (parsize pstate) (1- psize))))
                  (reterr :impossible))
                 ((erp & pstate) ; ( typename )
                  (read-punctuator ")" pstate))
                 ((erp token3 span3 pstate) (read-token pstate)))
              (cond
               ((equal token3 (token-punctuator "{")) ; ( typename ) {
                (b* ((pstate (unread-token pstate))) ; ( typename )
                  (parse-compound-literal tyname span pstate)))
               ((token-unary-expression-start-p token3) ; ( typename ) expr...
                (b* ((pstate (unread-token pstate)) ; ( typename )
                     ((erp expr last-span pstate) ; ( typename ) expr
                      (parse-cast-expression pstate)))
                  (retok (make-expr-cast :type tyname :arg expr)
                         (span-join span last-span)
                         pstate)))
               (t ; ( typename ) other
                (reterr-msg :where (position-to-msg (span->start span3))
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
                            :found (token-to-msg token3))))))
           (t ; ( other
            (reterr-msg :where (position-to-msg (span->start span2))
                        :expected "an identifier ~
                                   or a constant ~
                                   or a string literal ~
                                   or a keyword in {~
                                   _Alignas, ~
                                   _Alignof, ~
                                   _Atomic, ~
                                   _Bool, ~
                                   _Complex, ~
                                   _Generic, ~
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
                                   sizeof, ~
                                   struct, ~
                                   union, ~
                                   unsigned, ~
                                   void, ~
                                   volatile~
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
                        :found (token-to-msg token2))))))
       (t ; not-(
        (b* ((pstate (if token (unread-token pstate) pstate))) ; put back not-(
          (parse-unary-expression pstate)))))
    :measure (two-nats-measure (parsize pstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-unary-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a unary expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We read a token:")
     (xdoc::ol
      (xdoc::li
       "If the token may start a postfix expression,
        or equivalently if the token may start a primary expression,
        then we put back the token and we parse a postfix expression.
        There is no overlap between postfix expressions
        and unary expressions proper.")
      (xdoc::li
       "If the token is a preincrement or predecrement operator,
        we recursively parse a unary expression after that.
        This is the only possibility, given this token.")
      (xdoc::li
       "If the token is
        one of @('&'), @('*'), @('+') , @('-'), @('~'), and @('!'),
        i.e. what the grammar calls `unary operators'
        (which is more narrow than
        our definition of @(tsee unop) in our abstract syntax),
        we parse a cast expression
        (not a unary one, unlike the previous case).
        This is the only possibility, given this token.")
      (xdoc::li
       "If the token is @('_Alignof'),
        we proceed to parsing
        an open parenthesis, a type name, and a closed parenthesis.
        This is the only possibility, given this token.")
      (xdoc::li
       "If the token is @('sizeof'), there are possible ambiguities.
        We describe this case below, after describing the remaining case,
        which is simpler.")
      (xdoc::li
       "If none of the above cases apply,
        including the case of an absent token due to end of file,
        it is an error: we do not have a unary expression.
        The error message is based on all the possible ways
        in which a unary expression may start."))
     (xdoc::p
      "Now we describe the case of a @('sizeof') token, mentioned above.
       What follows may be a parenthesized type name or a unary expression.
       We read a second token:")
     (xdoc::ol
      (xdoc::li
       "If this second token is an open parenthesis,
        things are still ambiguous.
        We could have a parenthesized expression.
        We describe this case below,
        after describing the remaining cases for this second token,
        which are easier.")
      (xdoc::li
       "If this second token may be the start of a unary expression,
        since the case of an open parenthesis
        has already been handled in the previous case,
        then we parse the unary expression, after putting back the token.")
      (xdoc::li
       "If this second token is none of the above,
        then we do not have a valid @('sizeof') expression."))
     (xdoc::p
      "Now we describe the more complex first case above,
       where we have a @('sizeof') followed by an open parenthesis.
       We read a third token, and proceed by cases:")
     (xdoc::ol
      (xdoc::li
       "If this third token is an identifier,
        things are still ambiguous,
        because expressions and type names overlap in identifiers.
        We describe this case in more detail below,
        after describing the other cases, which are simpler.")
      (xdoc::li
       "If this third token may start an expression,
        since it is not an identifier (which is the case above),
        we have resolved the ambiguity.
        We put back the token,
        we parse an expression,
        and we parse the closing parenthesis.")
      (xdoc::li
       "If this third token may start a type name,
        since it is not an identifier (which is the first case above),
        we have resolved the ambiguity.
        We put back the token, we parse a type name,
        and we parse the closing parenthesis.")
      (xdoc::li
       "If this third token is none of the above,
        including the case in which there is no third token (end of file),
        we have an error.
        The message lists all possible starts of expressions and type names."))
     (xdoc::p
      "Now we describe the more complex first case above,
       where we have a @('sizeof'), an open parenthesis, and an identifier.
       We read a fourth token, and proceed by cases:")
     (xdoc::ol
      (xdoc::li
       "If this fourth token could start
        the rest of a postfix expression starting with an identifier,
        we have resolved the ambiguity in favor of an expression.
        We put back this and the previous token (the identifer),
        we parse a postfix expression,
        and we parse a closing parenthesis.")
      (xdoc::li
       "If this fourth token is a closing parenthesis,
        we have a syntactic ambiguity, because the identifier
        may be an expression or a type name.
        As explained in @(tsee expr),
        during parsing we classify this expression as an ambiguous @('sizeof'),
        to be unambiguously re-classified during semantic analysis.")
      (xdoc::li
       "If this fourth token is none of the above,
        including the case that this token is absent (end of file),
        it is an error.
        The message describes the tokens for the preceding cases.")))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ((token-primary-expression-start-p token) ; expr...
        (b* ((pstate (unread-token pstate)))
          (parse-postfix-expression pstate)))
       ((token-preinc/predec-operator-p token) ; preop
        (b* (((erp expr last-span pstate) ; preop expr
              (parse-unary-expression pstate))
             (unop (token-to-preinc/predec-operator token)))
          (retok (make-expr-unary :op unop :arg expr)
                 (span-join span last-span)
                 pstate)))
       ((token-unary-operator-p token) ; unop
        (b* (((erp expr last-span pstate) ; unop expr
              (parse-cast-expression pstate))
             (unop (token-to-unary-operator token)))
          (retok (make-expr-unary :op unop :arg expr)
                 (span-join span last-span)
                 pstate)))
       ((equal token (token-keyword "_Alignof")) ; _Alignof
        (b* (((erp & pstate) ; _Alignof (
              (read-punctuator "(" pstate))
             ((erp tyname & pstate) ; _Alignof ( typename
              (parse-type-name pstate))
             ((erp last-span pstate) ; _Alignof ( typename )
              (read-punctuator ")" pstate)))
          (retok (expr-alignof tyname)
                 (span-join span last-span)
                 pstate)))
       ((equal token (token-keyword "sizeof")) ; sizeof
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ((equal token2 (token-punctuator "(")) ; sizeof (
            (b* (((erp token3 span3 pstate) (read-token pstate)))
              (cond
               ((and token3
                     (token-case token3 :ident)) ; sizeof ( ident
                (b* (((erp token4 span4 pstate) (read-token pstate)))
                  (cond
                   ((token-postfix-expression-rest-start-p
                     token4) ; sizeof ( ident...
                    (b* ((pstate (unread-token pstate)) ; sizeof ( ident
                         (pstate (unread-token pstate)) ; sizeof (
                         ((erp expr & pstate) ; sizeof ( expr
                          (parse-postfix-expression pstate))
                         ((erp last-span pstate) ; sizeof ( expr )
                          (read-punctuator ")" pstate)))
                      (retok (expr-paren expr)
                             (span-join span last-span)
                             pstate)))
                   ((equal token4 (token-punctuator ")")) ; sizeof ( ident )
                    (b* ((ident (token-ident->unwrap token3)))
                      (retok (expr-sizeof-ambig ident)
                             (span-join span span4)
                             pstate)))
                   (t
                    (reterr-msg :where (position-to-msg (span->start span4))
                                :expected "a parenthesis ~
                                           or an open square bracket ~
                                           or a dot ~
                                           or a plus ~
                                           or a minus"
                                :found (token-to-msg token4))))))
               ((token-expression-start-p token3) ; sizeof ( expr...
                (b* ((pstate (unread-token pstate)) ; sizeof (
                     ((erp expr & pstate) ; sizeof ( expr
                      (parse-expression pstate))
                     ((erp last-span pstate) ; sizeof ( expr )
                      (read-punctuator ")" pstate)))
                  (retok (make-expr-unary
                          :op (unop-sizeof)
                          :arg (expr-paren expr))
                         (span-join span last-span)
                         pstate)))
               ((token-type-name-start-p token3) ; sizeof ( typename...
                (b* ((pstate (unread-token pstate)) ; sizeof (
                     ((erp tyname & pstate) ; sizeof ( typename
                      (parse-type-name pstate))
                     ((erp last-span pstate) ; sizeof ( typename )
                      (read-punctuator ")" pstate)))
                  (retok (expr-sizeof tyname)
                         (span-join span last-span)
                         pstate)))
               (t ; sizeof ( other
                (reterr-msg :where (position-to-msg (span->start span3))
                            :expected "an identifier ~
                                       or a constant ~
                                       or a string literal ~
                                       or a keyword in {~
                                       _Alignas, ~
                                       _Alignof, ~
                                       _Atomic, ~
                                       _Bool, ~
                                       _Complex, ~
                                       _Generic, ~
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
                                       sizeof, ~
                                       struct, ~
                                       union, ~
                                       unsigned, ~
                                       void, ~
                                       volatile~
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
                            :found (token-to-msg token3))))))
           ((token-unary-expression-start-p token2) ; sizeof expr...
            (b* ((pstate (unread-token pstate)) ; sizeof
                 ((erp expr last-span pstate) ; sizeof expr
                  (parse-unary-expression pstate)))
              (retok (make-expr-unary
                      :op (unop-sizeof)
                      :arg expr)
                     (span-join span last-span)
                     pstate)))
           (t ; sizeof other
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
                                       \"(\"~
                                       }"
                        :found (token-to-msg token2))))))
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
    :measure (two-nats-measure (parsize pstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-postfix-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ((equal token (token-punctuator "(")) ; (
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ((and token2 (token-case token2 :ident)) ; ( ident
            (b* (((erp token3 span3 pstate) (read-token pstate)))
              (cond
               ((equal token3 (token-punctuator ")")) ; ( ident )
                (b* (((erp token4 span4 pstate) (read-token pstate)))
                  (cond
                   ((equal token4 (token-punctuator "{")) ; ( ident ) {
                    (b* ((pstate (unread-token pstate)) ; ( ident )
                         (ident (token-ident->unwrap token2))
                         (tyname (make-tyname
                                  :specqual (list (specqual-tyspec
                                                   (tyspec-tydef ident)))
                                  :decl? nil)))
                      (parse-compound-literal tyname span pstate)))
                   ((token-postfix-expression-rest-start-p
                     token4) ; ( ident ) postrest...
                    (b* ((pstate (unread-token pstate)) ; ( ident )
                         (ident (token-ident->unwrap token2))
                         (expr (expr-paren (expr-ident ident))))
                      (parse-postfix-expression-rest expr
                                                     (span-join span span3)
                                                     pstate)))
                   (t ; ( ident ) other
                    (reterr-msg :where (position-to-msg (span->start span4))
                                :expected "an open parenthesis ~
                                           or an open square bracket ~
                                           or an open curly brace ~
                                           or a member access operator ~
                                           (dot or arrow) ~
                                           or a postincrement operator ~
                                           or a postdecrement operator"
                                :found (token-to-msg token4))))))
               ((token-postfix-expression-rest-start-p token3) ; ( expr...
                (b* ((pstate (unread-token pstate)) ; (
                     (psize (parsize pstate))
                     ((erp expr next-span pstate) ; ( expr
                      (parse-expression pstate))
                     ((unless (mbt (<= (parsize pstate) (1- psize))))
                      (reterr :impossible)))
                  (parse-postfix-expression-rest (expr-paren expr)
                                                 (span-join span next-span)
                                                 pstate)))
               (t ; ( ident other
                (reterr-msg :where (position-to-msg (span->start span3))
                            :expected "a parenthesis ~
                                       or an open square bracket ~
                                       or a member access operator ~
                                       (dot or arrow) ~
                                       or a postincrement operator ~
                                       or a postdecrement operator"
                            :found (token-to-msg token3))))))
           ((token-expression-start-p token2) ; ( expr...
            (b* ((pstate (unread-token pstate)) ; (
                 (psize (parsize pstate))
                 ((erp expr & pstate) ; ( expr
                  (parse-expression pstate))
                 ((unless (mbt (<= (parsize pstate) (1- psize))))
                  (reterr :impossible))
                 ((erp next-span pstate) ; ( expr )
                  (read-punctuator ")" pstate)))
              (parse-postfix-expression-rest (expr-paren expr)
                                             (span-join span next-span)
                                             pstate)))
           ((token-type-name-start-p token2) ; ( typename...
            (b* ((pstate (unread-token pstate)) ; (
                 (psize (parsize pstate))
                 ((erp tyname & pstate) ; ( typename
                  (parse-type-name pstate))
                 ((unless (mbt (<= (parsize pstate) (1- psize))))
                  (reterr :impossible))
                 ((erp & pstate) ; ( typename )
                  (read-punctuator ")" pstate)))
              (parse-compound-literal tyname span pstate)))
           (t ; ( other
            (reterr-msg :where (position-to-msg (span->start span2))
                        :expected "an identifier ~
                                   or a constant ~
                                   or a string literal ~
                                   or a keyword in {~
                                   _Alignas, ~
                                   _Alignof, ~
                                   _Atomic, ~
                                   _Bool, ~
                                   _Complex, ~
                                   _Generic, ~
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
                                   sizeof, ~
                                   struct, ~
                                   union, ~
                                   unsigned, ~
                                   void, ~
                                   volatile~
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
                        :found (token-to-msg token2))))))
       (t ; not-(
        (b* ((pstate (if token (unread-token pstate) pstate))
             (psize (parsize pstate))
             ((erp expr span pstate) ; expr
              (parse-primary-expression pstate))
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible)))
          (parse-postfix-expression-rest expr span pstate)))))
    :measure (two-nats-measure (parsize pstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-postfix-expression-rest ((prev-expr exprp)
                                         (prev-span spanp)
                                         (pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ;; prev-expr
         ((erp token span pstate) (read-token pstate)))
      (cond
       ((equal token (token-punctuator "[")) ; prev-expr [
        (b* ((psize (parsize pstate))
             ((erp expr & pstate) ; prev-expr [ expr
              (parse-expression pstate))
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible))
             ((erp last-span pstate) ; prev-expr [ expr ]
              (read-punctuator "]" pstate))
             (curr-expr (make-expr-arrsub :arg1 prev-expr
                                          :arg2 expr))
             (curr-span (span-join prev-span last-span)))
          (parse-postfix-expression-rest curr-expr curr-span pstate)))
       ((equal token (token-punctuator "(")) ; prev-expr (
        (b* ((psize (parsize pstate))
             ((erp exprs & pstate) ; prev-expr ( exprs
              (parse-argument-expressions pstate))
             ((unless (mbt (<= (parsize pstate) psize)))
              (reterr :impossible))
             ((erp last-span pstate) ; prev-expr ( exprs )
              (read-punctuator ")" pstate))
             (curr-expr (make-expr-funcall :fun prev-expr
                                           :args exprs))
             (curr-span (span-join prev-span last-span)))
          (parse-postfix-expression-rest curr-expr curr-span pstate)))
       ((equal token (token-punctuator ".")) ; prev-expr .
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ((and token2 (token-case token2 :ident)) ; prev-expr . ident
            (b* ((curr-expr (make-expr-member
                             :arg prev-expr
                             :name (token-ident->unwrap token2)))
                 (curr-span (span-join prev-span span2)))
              (parse-postfix-expression-rest curr-expr curr-span pstate)))
           (t ; prev-expr . other
            (reterr-msg :where (position-to-msg (span->start span2))
                        :expected "an identifier"
                        :found (token-to-msg token2))))))
       ((equal token (token-punctuator "->")) ; prev-expr ->
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ((and token2 (token-case token2 :ident)) ; prev-expr -> ident
            (b* ((curr-expr (make-expr-memberp
                             :arg prev-expr
                             :name (token-ident->unwrap token2)))
                 (curr-span (span-join prev-span span2)))
              (parse-postfix-expression-rest curr-expr curr-span pstate)))
           (t ; prev-expr -> other
            (reterr-msg :where (position-to-msg (span->start span2))
                        :expected "an identifier"
                        :found (token-to-msg token2))))))
       ((equal token (token-punctuator "++")) ; prev-expr ++
        (b* ((curr-expr (make-expr-unary :op (unop-postinc)
                                         :arg prev-expr))
             (curr-span (span-join prev-span span)))
          (parse-postfix-expression-rest curr-expr curr-span pstate)))
       ((equal token (token-punctuator "--")) ; prev-expr --
        (b* ((curr-expr (make-expr-unary :op (unop-postdec)
                                         :arg prev-expr))
             (curr-span (span-join prev-span span)))
          (parse-postfix-expression-rest curr-expr curr-span pstate)))
       (t ; prev-expr other
        (b* ((pstate (if token (unread-token pstate) pstate))) ; prev-expr
          (retok (expr-fix prev-expr) (span-fix prev-span) pstate)))))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-argument-expressions ((pstate parstatep))
    :returns (mv erp (exprs expr-listp) (span spanp) (new-pstate parstatep))
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
       which we handles as in other left-recursive parts of the grammar.")
     (xdoc::p
      "If the next token may start an expression,
       we parse an assignment expression,
       and then we call a separate function
       to parse any additional arguments.
       Otherwise, we return the empty list of argument expressions."))
    (b* (((reterr) nil (irr-span) (irr-parstate))
         ((erp token & pstate) (read-token pstate)))
      (cond
       ((token-expression-start-p token) ; expr...
        (b* ((pstate (unread-token pstate))
             (psize (parsize pstate))
             ((erp expr span pstate) ; expr
              (parse-assignment-expression pstate))
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible))
             (curr-exprs (list expr))
             (curr-span span))
          (parse-argument-expressions-rest curr-exprs curr-span pstate)))
       (t ; other
        (b* ((pstate (if token (unread-token pstate) pstate)))
          (retok nil (irr-span) pstate)))))
    :measure (two-nats-measure (parsize pstate) 16))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-argument-expressions-rest ((prev-exprs expr-listp)
                                           (prev-span spanp)
                                           (pstate parstatep))
    :returns (mv erp (exprs expr-listp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) nil (irr-span) (irr-parstate))
         ;; prev-exprs
         ((erp token & pstate) (read-token pstate))
         ((when (not (equal token (token-punctuator ","))))
          (b* ((pstate (if token (unread-token pstate) pstate)))
            (retok (expr-list-fix prev-exprs)
                   (span-fix prev-span)
                   pstate)))
         ;; prev-exprs ,
         (psize (parsize pstate))
         ((erp expr span pstate) ; prev-exprs , expr
          (parse-assignment-expression pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize))))
          (reterr :impossible))
         (curr-exprs (append prev-exprs (list expr)))
         (curr-span (span-join prev-span span)))
      (parse-argument-expressions-rest curr-exprs curr-span pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-primary-expression ((pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ((and token (token-case token :ident)) ; ident
        (retok (expr-ident (token-ident->unwrap token)) span pstate))
       ((and token (token-case token :const)) ; const
        (retok (expr-const (token-const->unwrap token)) span pstate))
       ((and token (token-case token :stringlit)) ; stringlit
        (retok (expr-string (token-stringlit->unwrap token)) span pstate))
       ((equal token (token-punctuator "(")) ; (
        (b* (((erp expr & pstate) ; ( expr
              (parse-expression pstate))
             ((erp last-span pstate) ; ( expr )
              (read-punctuator ")" pstate)))
          (retok (expr-paren expr)
                 (span-join span last-span)
                 pstate)))
       ((equal token (token-keyword "_Generic")) ; _Generic
        (b* (((erp & pstate) (read-punctuator "(" pstate)) ; _Generic (
             (psize (parsize pstate))
             ((erp expr & pstate) ; _Generic ( expr
              (parse-assignment-expression pstate))
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible))
             ((erp & pstate) (read-punctuator "," pstate)) ; _Generic ( expr ,
             (psize (parsize pstate))
             ((erp genassoc genassoc-span pstate) ; _Generic ( expr , genassoc
              (parse-generic-association pstate))
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible))
             ((erp genassocs & pstate) ; _Generic ( expr , genassoc ...
              (parse-generic-associations-rest (list genassoc)
                                               genassoc-span
                                               pstate))
             ((erp last-span pstate) ; _Generic ( expr , genassoc ... )
              (read-punctuator ")" pstate)))
          (retok (make-expr-gensel :control expr
                                   :assoc genassocs)
                 (span-join span last-span)
                 pstate)))
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or a constant ~
                               or a string literal ~
                               or an open parenthesis ~
                               or the keyword _Generic"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-generic-associations-rest ((prev-genassocs genassoc-listp)
                                           (prev-span spanp)
                                           (pstate parstatep))
    :returns (mv erp
                 (genassocs genassoc-listp)
                 (span spanp)
                 (new-pstate parstatep))
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
    (b* (((reterr) nil (irr-span) (irr-parstate))
         ((erp token & pstate) (read-token pstate))
         ((when (not (equal token (token-punctuator ","))))
          (b* ((pstate (if token (unread-token pstate) pstate)))
            (retok (genassoc-list-fix prev-genassocs)
                   (span-fix prev-span)
                   pstate)))
         ;; ,
         (psize (parsize pstate))
         ((erp genassoc span pstate) ; , genassoc
          (parse-generic-association pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize))))
          (reterr :impossible))
         (curr-genassocs (append prev-genassocs (list genassoc)))
         (curr-span (span-join prev-span span)))
      (parse-generic-associations-rest curr-genassocs curr-span pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-generic-association ((pstate parstatep))
    :returns (mv erp (genassoc genassocp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-genassoc) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ((token-type-name-start-p token) ; typename...
        (b* ((pstate (unread-token pstate))
             (psize (parsize pstate))
             ((erp tyname & pstate) (parse-type-name pstate)) ; typename
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible))
             ((erp & pstate) (read-punctuator ":" pstate)) ; typename :
             ((erp expr last-span pstate) ; typename : expr
              (parse-assignment-expression pstate)))
          (retok (make-genassoc-type :type tyname
                                     :expr expr)
                 (span-join span last-span)
                 pstate)))
       ((equal token (token-keyword "default")) ; default
        (b* (((erp & pstate) (read-punctuator ":" pstate)) ; default :
             ((erp expr last-span pstate) ; default : expr
              (parse-assignment-expression pstate)))
          (retok (genassoc-default expr)
                 (span-join span last-span)
                 pstate)))
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
    :measure (two-nats-measure (parsize pstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-compound-literal ((tyname tynamep)
                                  (first-span spanp)
                                  (pstate parstatep))
    :returns (mv erp (expr exprp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a compound literal."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after parsing the parenthesized type name.
       So we start by parsing an open curly brace,
       a list of initializers,
       and a closed curly brace."))
    (b* (((reterr) (irr-expr) (irr-span) (irr-parstate))
         ((erp & pstate) (read-punctuator "{" pstate)) ; {
         ((erp desiniters final-comma & pstate) ; { inits [,]
          (parse-initializer-list pstate))
         ((erp last-span pstate) (read-punctuator "}" pstate))) ; { inits [,] }
      (retok (make-expr-complit :type tyname
                                :elems desiniters
                                :final-comma final-comma)
             (span-join first-span last-span)
             pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-constant-expression ((pstate parstatep))
    :returns (mv erp (cexpr const-exprp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-const-expr) (irr-span) (irr-parstate))
         ((erp expr span pstate) (parse-conditional-expression pstate)))
      (retok (const-expr expr) span pstate))
    :measure (two-nats-measure (parsize pstate) 17))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-static-assert-declaration ((first-span spanp)
                                           (pstate parstatep))
    :returns (mv erp
                 (statassert statassertp)
                 (span spanp)
                 (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a static assert declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called when we expect a static assert declaration,
       after having read the @('_Static_assert') keyword.
       We pass the span of that keyword to this function,
       so that we can calculate a span for the whole static assert declaration.")
     (xdoc::p
      "We read the remaining components of the grammar rule,
       one after the other.
       There are no alternatives."))
    (b* (((reterr) (irr-statassert) (irr-span) (irr-parstate))
         ((erp & pstate) (read-punctuator "(" pstate))
         ((erp cexpr & pstate) (parse-constant-expression pstate))
         ((erp & pstate) (read-punctuator "," pstate))
         ((erp stringlit & pstate) (read-stringlit pstate))
         ((erp & pstate) (read-punctuator ")" pstate))
         ((erp last-span pstate) (read-punctuator ";" pstate)))
      (retok (make-statassert :test cexpr :message stringlit)
             (span-join first-span last-span)
             pstate))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-designator ((pstate parstatep))
    :returns (mv erp (designor designorp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a designator."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are two kinds of designators,
       easily distinguished by their first token."))
    (b* (((reterr) (irr-designor) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ((equal token (token-punctuator "[")) ; [
        (b* (((erp cexpr & pstate) (parse-constant-expression pstate)) ; [ cexpr
             ((erp last-span pstate) (read-punctuator "]" pstate))) ; [ cexpr ]
          (retok (designor-sub cexpr) (span-join span last-span) pstate)))
       ((equal token (token-punctuator ".")) ; .
        (b* (((erp ident last-span pstate) (read-identifier pstate))) ; . ident
          (retok (designor-dot ident) (span-join span last-span) pstate)))
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an open square bracket ~
                               or a dot"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-designator-list ((pstate parstatep))
    :returns (mv erp
                 (designors designor-listp)
                 (span spanp)
                 (new-pstate parstatep))
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
    (b* (((reterr) nil (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp designor span pstate) (parse-designator pstate)) ; designor
         ((unless (mbt (<= (parsize pstate) (1- psize))))
          (reterr :impossible))
         ((erp token & pstate) (read-token pstate))
         ((when (not (token-designator-start-p token))) ; designor other
          (b* ((pstate (if token (unread-token pstate) pstate))) ; designor
            (retok (list designor) span pstate)))
         ;; designor [
         ;; designor .
         (pstate (unread-token pstate)) ; designor
         ((erp designors more-span pstate) ; designor designors
          (parse-designator-list pstate)))
      (retok (cons designor designors)
             (span-join span more-span)
             pstate))
    :measure (two-nats-measure (parsize pstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-initializer ((pstate parstatep))
    :returns (mv erp (initer initerp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-initer) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ((token-expression-start-p token) ; expr...
        (b* ((pstate (unread-token pstate)) ;
             ((erp expr span pstate) ; expr
              (parse-assignment-expression pstate)))
          (retok (initer-single expr) span pstate)))
       ((equal token (token-punctuator "{")) ; {
        (b* (((erp desiniters final-comma & pstate) ; { inits [,]
              (parse-initializer-list pstate))
             ((erp last-span pstate) ; { inits [,] }
              (read-punctuator "}" pstate)))
          (retok (make-initer-list :elems desiniters :final-comma final-comma)
                 (span-join span last-span)
                 pstate)))
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
    :measure (two-nats-measure (parsize pstate) 16))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-designation?-initializer ((pstate parstatep))
    :returns (mv erp (desiniter desiniterp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-desiniter) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ((token-designation-start-p token) ; designation...
        (b* ((pstate (unread-token pstate)) ;
             (psize (parsize pstate))
             ((erp designors span pstate) ; designators
              (parse-designator-list pstate))
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible))
             ((erp & pstate) ; designators =
              (read-punctuator "=" pstate))
             ((erp initer last-span pstate) ; designators = initializer
              (parse-initializer pstate)))
          (retok (make-desiniter :design designors :init initer)
                 (span-join span last-span)
                 pstate)))
       ((token-initializer-start-p token) ; initializer...
        (b* ((pstate (unread-token pstate))
             ((erp initer span pstate) ; initializer
              (parse-initializer pstate)))
          (retok (make-desiniter :design nil :init initer)
                 span
                 pstate)))
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
    :measure (two-nats-measure (parsize pstate) 17))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-initializer-list ((pstate parstatep))
    :returns (mv erp
                 (desiniters desiniter-listp)
                 (final-comma booleanp)
                 (span spanp)
                 (new-pstate parstatep))
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
    (b* (((reterr) nil nil (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp desiniter span pstate) ; initializer
          (parse-designation?-initializer pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize))))
          (reterr :impossible))
         ((erp token & pstate) (read-token pstate)))
      (cond
       ((equal token (token-punctuator ",")) ; initializer ,
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ((equal token2 (token-punctuator "}")) ; initializer , }
            (b* ((pstate (unread-token pstate))) ; initializer ,
              (retok (list desiniter)
                     t ; final-comma
                     (span-join span span2)
                     pstate)))
           ((token-designation?-initializer-start-p
             token2) ; initializer , initializer...
            (b* ((pstate (unread-token pstate)) ; initializer ,
                 ((erp desiniters final-comma last-span pstate)
                  (parse-initializer-list pstate))) ; initializer , initializers
              (retok (cons desiniter desiniters)
                     final-comma
                     (span-join span last-span)
                     pstate)))
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
       ((equal token (token-punctuator "}")) ; initializer }
        (b* ((pstate (unread-token pstate))) ; initializer
          (retok (list desiniter)
                 nil ; final-comma
                 span
                 pstate)))
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
    :measure (two-nats-measure (parsize pstate) 18))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-enumerator ((pstate parstatep))
    :returns (mv erp (enumer enumerp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse an enumerator."
    (b* (((reterr) (irr-enumer) (irr-span) (irr-parstate))
         ;; An enumerator always starts with (or is) an identifier.
         ((erp ident span pstate) (read-identifier pstate)) ; ident
         ;; The identifier may be the whole enumerator, or there may be more,
         ;; so we read another token.
         ((erp token & pstate) (read-token pstate)))
      (cond
       ;; If token is an equal sign, the enumerator continues,
       ;; and there must be a constant expression.
       ((equal token (token-punctuator "=")) ; ident =
        (b* (((erp cexpr last-span pstate) ; ident = cexpr
              (parse-constant-expression pstate)))
          (retok (make-enumer :name ident :value cexpr)
                 (span-join span last-span)
                 pstate)))
       ;; If token is not an equal sign, we put it back,
       ;; and the enumerator is just the identifier.
       (t ; ident other
        (b* ((pstate (if token (unread-token pstate) pstate))) ; ident
          (retok (make-enumer :name ident :value nil)
                 span
                 pstate)))))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-enumerator-list ((pstate parstatep))
    :returns (mv erp
                 (enumers enumer-listp)
                 (final-comma booleanp)
                 (span spanp)
                 (new-pstate parstatep))
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
    (b* (((reterr) nil nil (irr-span) (irr-parstate))
         ;; The list must not be empty, so we parse the first enumerator.
         (psize (parsize pstate))
         ((erp enumer enumer-span pstate) (parse-enumerator pstate)) ; enumer
         ((unless (mbt (<= (parsize pstate) (1- psize))))
          (reterr :impossible))
         ;; To see if there are more enumerators,
         ;; we read another token.
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token is a comma,
       ;; there could be another enumerator,
       ;; or it could be just a final comma,
       ;; so we need to read another token.
       ((equal token (token-punctuator ",")) ; enumer ,
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ;; If token2 is an identifier,
           ;; the comma is not a final one,
           ;; and we must have another enumerator.
           ;; We put back the identifier,
           ;; recursively call this function,
           ;; and combine the result with the enumerator parsed above.
           ((and token2 (token-case token2 :ident)) ; enumer , ident
            (b* ((pstate (unread-token pstate)) ; enumer ,
                 ((erp enumers final-comma enumers-span pstate)
                  (parse-enumerator-list pstate))) ; enumer , enumers
              (retok (cons enumer enumers)
                     final-comma
                     (span-join enumer-span enumers-span)
                     pstate)))
           ;; If token2 is a closed curly brace,
           ;; the list ends, and the comma is a final one.
           ;; We put back the curly brace.
           ;; We return the singleton list of the enumerator parsed above.
           ((equal token2 (token-punctuator "}")) ; enumer , }
            (b* ((pstate (unread-token pstate))) ; enumer ,
              (retok (list enumer)
                     t ; final-comma
                     (span-join enumer-span span)
                     pstate)))
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
       ((equal token (token-punctuator "}")) ; enumer }
        (b* ((pstate (unread-token pstate))) ; enumer
          (retok (list enumer)
                 nil ; final-comma
                 enumer-span
                 pstate)))
       ;; If token is neither a comma nor a closed curly brace,
       ;; it is an error, because an enumerator must be always followed by
       ;; a comma or closed curly brace.
       (t ; enumer other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a comma ~
                               or a closed curly brace"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize pstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-specifier/qualifier ((tyspec-seenp booleanp)
                                     (pstate parstatep))
    :returns (mv erp (specqual specqualp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-specqual) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token is a type specifier consisting of a single keyword,
       ;; return that type specifier.
       ((token-type-specifier-keyword-p token) ; void/char/.../_Complex
        (retok (specqual-tyspec (token-to-type-specifier-keyword token))
               span
               pstate))
       ;; If token is the keyword _Atomic,
       ;; it may be either a type specifier or a type qualifier,
       ;; so we examine more tokens.
       ((equal token (token-keyword "_Atomic")) ; _Atomic
        (b* (((erp token2 & pstate) (read-token pstate)))
          (cond
           ;; If token2 is an open parenthesis,
           ;; we check the TYSPEC-SEENP flag,
           ;; as explained in the documentation.
           ((equal token2 (token-punctuator "(")) ; _Atomic (
            (if tyspec-seenp
                ;; If we have already seen a type specifier,
                ;; this must be a type qualifier.
                (b* ((pstate (unread-token pstate))) ; _Atomic
                  (retok (specqual-tyqual (tyqual-atomic))
                         span
                         pstate))
              ;; If we have not already seen a type specifier,
              ;; this must be a type specifier,
              ;; because the open parenthesis cannot be
              ;; another specifier or qualifier.
              (b* (((erp tyname & pstate) ; _Atomic ( typename
                    (parse-type-name pstate))
                   ((erp last-span pstate) ; _Atomic ( typename )
                    (read-punctuator ")" pstate)))
                (retok (specqual-tyspec (tyspec-atomic tyname))
                       (span-join span last-span)
                       pstate))))
           ;; If token2 is not an open parenthesis,
           ;; we must have an atomic type qualifier.
           (t ; _Atomic other
            (b* ((pstate ; _Atomic
                  (if token2 (unread-token pstate) pstate)))
              (retok (specqual-tyqual (tyqual-atomic))
                     span
                     pstate))))))
       ;; If token is the keyword struct,
       ;; we must have a structure type specifier.
       ((equal token (token-keyword "struct")) ; struct
        (b* (((erp strunispec last-span pstate) ; struct strunispec
              (parse-struct-or-union-specifier pstate)))
          (retok (specqual-tyspec (tyspec-struct strunispec))
                 (span-join span last-span)
                 pstate)))
       ;; If token is the keyword union
       ;; we must have a union type specifier.
       ((equal token (token-keyword "union")) ; union
        (b* (((erp strunispec last-span pstate) ; union strunispec
              (parse-struct-or-union-specifier pstate)))
          (retok (specqual-tyspec (tyspec-union strunispec))
                 (span-join span last-span)
                 pstate)))
       ;; If token is the keyword enum,
       ;; we must have an enumeration type specifier.
       ((equal token (token-keyword "enum")) ; enum
        (b* (((erp enumspec last-span pstate) ; enum enumspec
              (parse-enum-specifier span pstate)))
          (retok (specqual-tyspec (tyspec-enum enumspec))
                 (span-join span last-span)
                 pstate)))
       ;; If token is an identifier,
       ;; it is a type specifier, precisely a @('typedef') name.
       ;; It is the responsibility of the caller of this function
       ;; to ensure that this is not (the start of) a declarator:
       ;; when this function is called, it must be the case that
       ;; a specifier or qualifier is expected.
       ((and token (token-case token :ident)) ; ident
        (retok (specqual-tyspec (tyspec-tydef (token-ident->unwrap token)))
               span
               pstate))
       ;; If token is a type qualifier, which is always a single keyword,
       ;; we have that type qualifier.
       ((token-type-qualifier-p token) ; tyqual
        (retok (specqual-tyqual (token-to-type-qualifier token))
               span
               pstate))
       ;; If token is the keyword _Alignas,
       ;; we must have an alignment specifier.
       ((equal token (token-keyword "_Alignas")) ; _Alignas
        (b* (((erp alignspec last-span pstate) ; _Alignas ( ... )
              (parse-alignment-specifier span pstate)))
          (retok (specqual-alignspec alignspec)
                 (span-join span last-span)
                 pstate)))
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
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-specifier-qualifier-list ((tyspec-seenp booleanp)
                                          (pstate parstatep))
    :returns (mv erp
                 (specquals specqual-listp)
                 (span spanp)
                 (new-pstate parstatep))
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
    (b* (((reterr) nil (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp specqual first-span pstate) ; specqual
          (parse-specifier/qualifier tyspec-seenp pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize))))
          (reterr :impossible))
         (tyspec-seenp (or tyspec-seenp
                           (specqual-case specqual :tyspec)))
         ((erp token & pstate) (read-token pstate)))
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
            (b* ((pstate (unread-token pstate))) ; declspec
              (retok (list specqual) first-span pstate))
          ;; If we have not already parsed a type specifier,
          ;; the identifier must be a type specifier,
          ;; so we put it back and we recursively call this function,
          ;; combining its results with
          ;; the specifier or qualifier that we have parsed above.
          (b* ((pstate (unread-token pstate)) ; specqual
               ((erp specquals last-span pstate) ; specqual specquals
                (parse-specifier-qualifier-list tyspec-seenp pstate)))
            (retok (cons specqual specquals)
                   (span-join first-span last-span)
                   pstate))))
       ;; If token may start a specifier or qualifier,
       ;; since it is not an identifier (which we have considered above),
       ;; there must be another type specifier or qualifier.
       ;; We recursively call this function, combining the result
       ;; with the previous parsed specifier or qualifier.
       ((token-specifier/qualifier-start-p token)
        ;; specqual specqual...
        (b* ((pstate (unread-token pstate)) ; specqual
             ((erp specquals last-span pstate) ; specqual specquals
              (parse-specifier-qualifier-list tyspec-seenp pstate)))
          (retok (cons specqual specquals)
                 (span-join first-span last-span)
                 pstate)))
       ;; If token is something else,
       ;; there cannot be another specifier and qualifier,
       ;; so we return the singleton list with
       ;; the previous parsed specifier or qualifier.
       (t ; specqual other
        (b* ((pstate (if token (unread-token pstate) pstate))) ; specqual
          (retok (list specqual) first-span pstate)))))
    :measure (two-nats-measure (parsize pstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-declaration-specifier ((tyspec-seenp booleanp)
                                       (pstate parstatep))
    :returns (mv erp (declspec declspecp) (span spanp) (new-pstate parstatep))
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
       a function specifier, or
       an alignment specifier.")
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
    (b* (((reterr) (irr-declspec) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token is a storage class specifier,
       ;; which always consists of a single keyword,
       ;; return that storage class specifier.
       ((token-storage-class-specifier-p token) ; typedef/.../register
        (retok (declspec-stocla (token-to-storage-class-specifier token))
               span
               pstate))
       ;; If token is a type specifier consisting of a single keyword,
       ;; return that type specifier.
       ((token-type-specifier-keyword-p token) ; void/.../_Complex
        (retok (declspec-tyspec (token-to-type-specifier-keyword token))
               span
               pstate))
       ;; If token is the keyword _Atomic,
       ;; it may be either a type specifier or a type qualifier,
       ;; so we examine more tokens.
       ((equal token (token-keyword "_Atomic")) ; _Atomic
        (b* (((erp token2 & pstate) (read-token pstate)))
          (cond
           ;; If token2 is an open parenthesis,
           ;; we check the TYSPEC-SEENP flag,
           ;; as explained in the documentation.
           ((equal token2 (token-punctuator "(")) ; _Atomic (
            (if tyspec-seenp
                ;; If we have already seen a type specifier,
                ;; this must be a type qualifier.
                (b* ((pstate (unread-token pstate))) ; _Atomic
                  (retok (declspec-tyqual (tyqual-atomic))
                         span
                         pstate))
              ;; If we have not already seen a type specifier,
              ;; this must be a type specifier,
              ;; because the open parenthesis cannot be
              ;; another declaration specifier.
              (b* (((erp tyname & pstate) ; _Atomic ( typename
                    (parse-type-name pstate))
                   ((erp last-span pstate) ; _Atomic ( typename )
                    (read-punctuator ")" pstate)))
                (retok (declspec-tyspec (tyspec-atomic tyname))
                       (span-join span last-span)
                       pstate))))
           ;; If token2 is not an open parenthesis,
           ;; we must have an atomic type qualifier.
           (t ; _Atomic other
            (b* ((pstate ; _Atomic
                  (if token2 (unread-token pstate) pstate)))
              (retok (declspec-tyqual (tyqual-atomic))
                     span
                     pstate))))))
       ;; If token is the keyword struct,
       ;; we must have a structure type specifier.
       ((equal token (token-keyword "struct")) ; struct
        (b* (((erp strunispec last-span pstate) ; struct strunispec
              (parse-struct-or-union-specifier pstate)))
          (retok (declspec-tyspec (tyspec-struct strunispec))
                 (span-join span last-span)
                 pstate)))
       ;; If token is the keyword union
       ;; we must have a union type specifier.
       ((equal token (token-keyword "union")) ; union
        (b* (((erp strunispec last-span pstate) ; union strunispec
              (parse-struct-or-union-specifier pstate)))
          (retok (declspec-tyspec (tyspec-union strunispec))
                 (span-join span last-span)
                 pstate)))
       ;; If token is the keyword enum,
       ;; we must have an enumeration type specifier.
       ((equal token (token-keyword "enum")) ; enum
        (b* (((erp enumspec last-span pstate) ; enum enumspec
              (parse-enum-specifier span pstate)))
          (retok (declspec-tyspec (tyspec-enum enumspec))
                 (span-join span last-span)
                 pstate)))
       ;; If token is an identifier,
       ;; it is a type specifier, precisely a @('typedef') name.
       ;; It is the responsibility of the caller of this function
       ;; to ensure that this is not (the start of) a declarator:
       ;; when this function is called, it must be the case that
       ;; a specifier or qualifier is expected.
       ((and token (token-case token :ident)) ; ident
        (retok (declspec-tyspec (tyspec-tydef (token-ident->unwrap token)))
               span
               pstate))
       ;; If token is a type qualifier, which is always a single keyword,
       ;; we have that type qualifier.
       ((token-type-qualifier-p token) ; tyqual
        (retok (declspec-tyqual (token-to-type-qualifier token))
               span
               pstate))
       ;; If token is a function specifier, which is always a single keyword,
       ;; we have that function specifier.
       ((token-function-specifier-p token) ; inline/_Noreturn
        (retok (declspec-funspec (token-to-function-specifier token))
               span
               pstate))
       ;; If token is the keyword _Alignas,
       ;; we must have an alignment specifier.
       ((equal token (token-keyword "_Alignas")) ; _Alignas
        (b* (((erp alignspec last-span pstate) ; _Alignas ( ... )
              (parse-alignment-specifier span pstate)))
          (retok (declspec-alignspec alignspec)
                 (span-join span last-span)
                 pstate)))
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
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-declaration-specifiers ((tyspec-seenp booleanp)
                                        (pstate parstatep))
    :returns (mv erp
                 (declspecs declspec-listp)
                 (span spanp)
                 (new-pstate parstatep))
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
    (b* (((reterr) nil (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp declspec first-span pstate) ; declspec
          (parse-declaration-specifier tyspec-seenp pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize))))
          (reterr :impossible))
         (tyspec-seenp (or tyspec-seenp
                           (declspec-case declspec :tyspec)))
         ((erp token & pstate) (read-token pstate)))
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
            (b* ((pstate (unread-token pstate))) ; declspec
              (retok (list declspec) first-span pstate))
          ;; If we have not already parsed a type specifier,
          ;; the identifier must be a type specifier,
          ;; so we put it back and we recursively call this function,
          ;; combining its results with
          ;; the declaration specifier that we have parsed above.
          (b* ((pstate (unread-token pstate)) ; declspec
               ((erp declspecs last-span pstate) ; declspec declspecs
                (parse-declaration-specifiers tyspec-seenp pstate)))
            (retok (cons declspec declspecs)
                   (span-join first-span last-span)
                   pstate))))
       ;; If token may start a declaration specifier,
       ;; since it is not an identifier (which we have considered above),
       ;; there must be another declaration specifier.
       ;; We recursively call this function, combining the result
       ;; with the previous parsed specifier or qualifier.
       ((token-declaration-specifier-start-p token) ; declspec declspec...
        (b* ((pstate (unread-token pstate)) ; declspec
             ((erp declspecs last-span pstate) ; declspec declspecs
              (parse-declaration-specifiers tyspec-seenp pstate)))
          (retok (cons declspec declspecs)
                 (span-join first-span last-span)
                 pstate)))
       ;; If token is something else,
       ;; there cannot be another declaration specifier,
       ;; so we return the singleton list with
       ;; the previous parsed declaratio specifier.
       (t ; declspec other
        (b* ((pstate (if token (unread-token pstate) pstate))) ; declspec
          (retok (list declspec) first-span pstate)))))
    :measure (two-nats-measure (parsize pstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-struct-or-union-specifier ((pstate parstatep))
    :returns (mv erp
                 (strunispec strunispecp)
                 (span spanp)
                 (new-pstate parstatep))
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
       which is done in @(tsee tyspec) instead;
       this is how we have factored our abstract syntax."))
    (b* (((reterr) (irr-strunispec) (irr-span) (irr-parstate))
         ;; There must be at least one token (identifier of open curly brace),
         ;; so we read one.
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token is an identifier,
       ;; it may be the whole structure or union specifier,
       ;; or there may be more, so we read another token.
       ((and token (token-case token :ident)) ; ident
        (b* ((ident (token-ident->unwrap token))
             ((erp token2 & pstate) (read-token pstate)))
          (cond
           ;; If token2 is an open curly brace,
           ;; we must have a list of structure declarations
           ;; enclosed in curly braces.
           ;; So we parse those.
           ((equal token2 (token-punctuator "{")) ; ident {
            (b* (((erp structdecls & pstate) ; ident { structdecls
                  (parse-struct-declaration-list pstate))
                 ((erp last-span pstate) ; ident { structdecls }
                  (read-punctuator "}" pstate)))
              (retok (make-strunispec :name ident
                                      :members structdecls)
                     (span-join span last-span)
                     pstate)))
           ;; If token2 is not an open curly brace,
           ;; the identifier was the whole structure or union specifier,
           ;; so we put back token2 and return the specifier.
           (t ; ident other
            (b* ((pstate (if token2 (unread-token pstate) pstate))) ; ident
              (retok (make-strunispec :name ident
                                      :members nil)
                     span
                     pstate))))))
       ;; If token is an open curly brace,
       ;; we must have a structure or union specifier without identifier
       ;; but with a list of structure declarations between curly braces.
       ;; So we parse those.
       ((equal token (token-punctuator "{")) ; {
        (b* (((erp structdecls & pstate) ; { structdecls
              (parse-struct-declaration-list pstate))
             ((erp last-span pstate) ; { structdecls }
              (read-punctuator "}" pstate)))
          (retok (make-strunispec :name nil
                                  :members structdecls)
                 (span-join span last-span)
                 pstate)))
       ;; If token is neither an identifier nor an open curly brace,
       ;; we cannot have a structure or union specifier here.
       (t
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or an open curly brace"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-enum-specifier ((first-span spanp) (pstate parstatep))
    :returns (mv erp (enumspec enumspecp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse an enumeration specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after parsing the initial @('enum') keyword.")
     (xdoc::p
      "The span of the @('enum') keyword is passed as input here."))
    (b* (((reterr) (irr-enumspec) (irr-span) (irr-parstate))
         ;; There must be at least one token (identifier of open curly brace),
         ;; so we read one.
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token is an identifier,
       ;; it may be the whole specifier, or there may be more,
       ;; so we read another token.
       ((and token (token-case token :ident)) ; ident
        (b* ((ident (token-ident->unwrap token))
             ((erp token2 & pstate) (read-token pstate)))
          (cond
           ;; If token2 is an open curly brace,
           ;; there must be a list of enumerators, which we parse.
           ;; Then we read the closed curly brace.
           ((equal token2 (token-punctuator "{")) ; ident {
            (b* (((erp enumers final-comma & pstate)
                  (parse-enumerator-list pstate)) ; ident { enumers [,]
                 ((erp last-span pstate) ; ident { enumers [,] }
                  (read-punctuator "}" pstate)))
              (retok (make-enumspec :name ident
                                    :list enumers
                                    :final-comma final-comma)
                     (span-join first-span last-span)
                     pstate)))
           ;; If token2 is not an open curly brace,
           ;; the identifier must be the whole enumeration specifier.
           (t ; ident other
            (b* ((pstate (if token2 (unread-token pstate) pstate))) ; ident
              (retok (make-enumspec :name ident
                                    :list nil
                                    :final-comma nil)
                     (span-join first-span span)
                     pstate))))))
       ;; If token is an open curly brace,
       ;; we must have an enumeration specifier without identifier.
       ;; We parse the list of enumerators, and the closed curly brace.
       ((equal token (token-punctuator "{")) ; {
        (b* (((erp enumers final-comma & pstate)
              (parse-enumerator-list pstate)) ; { enumers [,]
             ((erp last-span pstate) ; { enumers [,] }
              (read-punctuator "}" pstate)))
          (retok (make-enumspec :name nil
                                :list enumers
                                :final-comma final-comma)
                 (span-join first-span last-span)
                 pstate)))
       ;; If token is neither an identifier nor an open curly brace,
       ;; it is an error, because the 'enum' keyword must be alwways followed by
       ;; an identifier or an open curly brace.
       (t
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or a closed curly brace"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-alignment-specifier ((first-span spanp) (pstate parstatep))
    :returns (mv erp (alignspec alignspecp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse an alignment specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after parsing the initial @('_Alignas') keyword.")
     (xdoc::p
      "The span of the @('_Alignas') keyword is passed as input here."))
    (b* (((reterr) (irr-alignspec) (irr-span) (irr-parstate))
         ;; There must be an open parenthesis.
         ((erp & pstate) (read-punctuator "(" pstate)) ; (
         ;; To decide whether we have a type name or a constant expression,
         ;; we read another token.
         ((erp token & pstate) (read-token pstate)))
      (cond
       ;; If token is an identifier,
       ;; things are still ambiguous, and we need to read more tokens.
       ((and token (token-case token :ident)) ;; ( ident
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ;; If token2 is a closed parenthesis, we have an ambiguity.
           ;; The identifier may be a type name or an expression.
           ;; Note that this should be a constant expression,
           ;; and an identifier expression is a variable,
           ;; which is not a constant expression,
           ;; but grammatically a constant expression is an expression,
           ;; and we defer to later the checks on constant expressions.
           ((equal token2 (token-punctuator ")")) ; ( ident )
            (retok (alignspec-alignas-ambig (token-ident->unwrap token))
                   (span-join first-span span2)
                   pstate))
           ;; If token2 is not a closed parenthesis,
           ;; we unread token2 and the identifier,
           ;; and we attempt to parse a type name.
           ;; This may reject code
           ;; if there is an expression instead of a type name:
           ;; we will improve the parser with
           ;; a more complete treatment.
           (t
            (b* ((pstate (if token2 (unread-token pstate) pstate)) ; ( ident
                 (pstate (unread-token pstate)) ; (
                 ((erp tyname & pstate) (parse-type-name pstate)) ; ( typename
                 ((erp last-span pstate) ; ( typename )
                  (read-punctuator ")" pstate)))
              (retok (alignspec-alignas-type tyname)
                     (span-join first-span last-span)
                     pstate))))))
       ;; If token is not an identifier,
       ;; we unread the token and we attempt to parse a type name.
       ;; This may reject code
       ;; if there is an expression instead of a type name:
       ;; we will improve the parser with
       ;; a more complete treatment.
       (t
        (b* ((pstate (if token (unread-token pstate) pstate)) ; (
             ((erp tyname & pstate) (parse-type-name pstate)) ; ( typename
             ((erp last-span pstate) ; ( typename )
              (read-punctuator ")" pstate)))
          (retok (alignspec-alignas-type tyname)
                 (span-join first-span last-span)
                 pstate)))))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-array/function-abstract-declarator ((pstate parstatep))
    :returns (mv erp
                 (dirabsdeclor dirabsdeclorp)
                 (span spanp)
                 (new-pstate parstatep))
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
    (b* (((reterr) (irr-dirabsdeclor) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token is an open square bracket,
       ;; we must have an array abstract declarator.
       ((equal token (token-punctuator "[")) ; [
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ;; If token2 is a closed square bracket, we have a declarator [].
           ((equal token2 (token-punctuator "]")) ; [ ]
            (retok (make-dirabsdeclor-array :decl? nil
                                            :tyquals nil
                                            :expr? nil)
                   (span-join span span2)
                   pstate))
           ;; If token2 is a star, we must have a declarator [*].
           ((equal token2 (token-punctuator "*")) ; [ *
            (b* (((erp last-span pstate) (read-punctuator "]" pstate))) ; [ * ]
              (retok (dirabsdeclor-array-star nil)
                     (span-join span last-span)
                     pstate)))
           ;; If token2 is the keyword 'static',
           ;; the keyword may be followed by a list of type qualifiers,
           ;; and then must be followed by an assignment expression.
           ((equal token2 (token-keyword "static")) ; [ static
            (b* (((erp token3 & pstate) (read-token pstate)))
              (cond
               ;; If token3 is a type qualifier,
               ;; we must have a list of type qualifiers,
               ;; which we parse,
               ;; and then we parse the assignment expression.
               ((token-type-qualifier-p token3) ; [ static tyqual
                (b* ((pstate (unread-token pstate)) ; [ static
                     ((erp tyquals & pstate) ; [ static tyquals
                      (parse-type-qualifier-list pstate))
                     ((erp expr & pstate) ; [ static tyquals expr
                      (parse-assignment-expression pstate))
                     ((erp last-span pstate) ; [ static tyquals expr ]
                      (read-punctuator "]" pstate)))
                  (retok (make-dirabsdeclor-array-static1
                          :decl? nil
                          :tyquals tyquals
                          :expr expr)
                         (span-join span last-span)
                         pstate)))
               ;; If token3 is not a type qualifier,
               ;; we must have an assignment expression.
               (t ; [ static other
                (b* ((pstate
                      (if token3 (unread-token pstate) pstate)) ; [ static
                     ((erp expr & pstate) ; [ static expr
                      (parse-assignment-expression pstate)) ; [ static expr
                     ((erp last-span pstate) ; [ static expr ]
                      (read-punctuator "]" pstate)))
                  (retok (make-dirabsdeclor-array-static1
                          :decl? nil
                          :tyquals nil
                          :expr expr)
                         (span-join span last-span)
                         pstate))))))
           ;; If token2 is a type qualifier,
           ;; we must have a list of type qualifiers,
           ;; possibly followed by the keyword 'static',
           ;; and necessarily followed by an assignment expression.
           ((token-type-qualifier-p token2) ; [ tyqual
            (b* ((pstate (unread-token pstate)) ; [
                 ((erp tyquals & pstate) ; [ tyquals
                  (parse-type-qualifier-list pstate))
                 ((erp token3 & pstate) (read-token pstate)))
              (cond
               ;; If token3 is the keyword 'static',
               ;; we must have an assignment expression after that.
               ((equal token3 (token-keyword "static")) ; [ tyquals static
                (b* (((erp expr & pstate) ; [ tyquals static expr
                      (parse-assignment-expression pstate))
                     ((erp last-span pstate) ; [ tyquals static expr ]
                      (read-punctuator "]" pstate)))
                  (retok (make-dirabsdeclor-array-static2
                          :decl? nil
                          :tyquals tyquals
                          :expr expr)
                         (span-join span last-span)
                         pstate)))
               ;; If token3 is not the keyword 'static',
               ;; we must have an assignment expression here.
               (t ; [ tyquals other
                (b* ((pstate
                      (if token3 (unread-token pstate) pstate)) ; [ tyquals
                     ((erp expr & pstate) ; [ tyquals expr
                      (parse-assignment-expression pstate))
                     ((erp last-span pstate) ; [ tyquals expr ]
                      (read-punctuator "]" pstate)))
                  (retok (make-dirabsdeclor-array
                          :decl? nil
                          :tyquals tyquals
                          :expr? expr)
                         (span-join span last-span)
                         pstate))))))
           ;; If token2 is anything else,
           ;; we must have just an assignment expression.
           (t ; [ other
            (b* ((pstate (if token2 (unread-token pstate) pstate)) ; [
                 ((erp expr & pstate) ; [ expr
                  (parse-assignment-expression pstate))
                 ((erp last-span pstate) ; [ expr ]
                  (read-punctuator "]" pstate)))
              (retok (make-dirabsdeclor-array :decl? nil
                                              :tyquals nil
                                              :expr? expr)
                     (span-join span last-span)
                     pstate))))))
       ;; If token is an open parenthesis,
       ;; we must have a function abstract declarator.
       ((equal token (token-punctuator "(")) ; (
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ;; If token2 is a closed parenthesis,
           ;; we have no parameters.
           ((equal token2 (token-punctuator ")")) ; ( )
            (retok (make-dirabsdeclor-function :decl? nil
                                               :params nil
                                               :ellipsis nil)
                   (span-join span span2)
                   pstate))
           ;; If token2 is not a closed parenthesis,
           ;; we must have a parameter type list,
           ;; which we parse.
           (t ; ( other
            (b* ((pstate (if token2 (unread-token pstate) pstate)) ; (
                 ((erp paramdecls ellipsis & pstate) ; ( params [, ...]
                  (parse-parameter-declaration-list pstate))
                 ((erp last-span pstate) ; ( params [, ...] )
                  (read-punctuator ")" pstate)))
              (retok (make-dirabsdeclor-function :decl? nil
                                                 :params paramdecls
                                                 :ellipsis ellipsis)
                     (span-join span last-span)
                     pstate))))))
       ;; If token is anything else,
       ;; we cannot have either an array or a function abstract declarator.
       ;; So it is an error, because we were expecting one.
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an open parenthesis ~
                               or an open square bracket"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-direct-abstract-declarator ((pstate parstatep))
    :returns (mv erp
                 (dirabsdeclor dirabsdeclorp)
                 (span spanp)
                 (new-pstate parstatep))
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
    (b* (((reterr) (irr-dirabsdeclor) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token is an open parenthesis,
       ;; we could have a parenthesized abstract declarator,
       ;; or a function abstract declarator.
       ((equal token (token-punctuator "(")) ; (
        (b* (((erp token2 & pstate) (read-token pstate)))
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
            (b* ((pstate (unread-token pstate)) ; (
                 (psize (parsize pstate))
                 ((erp absdeclor & pstate) ; ( absdeclor
                  (parse-abstract-declarator pstate))
                 ((unless (mbt (<= (parsize pstate) (1- psize))))
                  (reterr :impossible))
                 ((erp last-span pstate) ; ( absdeclor )
                  (read-punctuator ")" pstate)))
              (parse-direct-abstract-declarator-rest
               (dirabsdeclor-paren absdeclor)
               (span-join span last-span)
               pstate)))
           ;; If token2 may not start an abstract declarator,
           ;; we must have a function abstract declarator,
           ;; which we read with a separate function,
           ;; and then we call the function to read
           ;; zero or more subsequent array and function abstract declarators,
           ;; combining the one we just read into them.
           (t ; ( other
            (b* ((pstate (if token2 (unread-token pstate) pstate)) ; (
                 (pstate (unread-token pstate)) ;
                 (psize (parsize pstate))
                 ((erp dirabsdeclor span pstate) ; dirabsdeclor
                  (parse-array/function-abstract-declarator pstate))
                 ((unless (mbt (<= (parsize pstate) (1- psize))))
                  (reterr :impossible)))
              (parse-direct-abstract-declarator-rest dirabsdeclor
                                                     span
                                                     pstate))))))
       ;; If token is an open square,
       ;; we must have an array abstract declarator,
       ;; which we parse using a separate function,
       ;; and then we use another function to parse
       ;; zero or more subsequent array and function abstract declarators,
       ;; combining into them the one we just read.
       ((equal token (token-punctuator "[")) ; [
        (b* ((pstate (unread-token pstate)) ;
             (psize (parsize pstate))
             ((erp dirabsdeclor span pstate) ; dirabsdeclor
              (parse-array/function-abstract-declarator pstate))
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible)))
          (parse-direct-abstract-declarator-rest dirabsdeclor
                                                 span
                                                 pstate)))
       ;; If token is anything else,
       ;; we cannot have a direct abstract declarator.
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an open parenthesis ~
                               or an open square bracket"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize pstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-direct-abstract-declarator-rest
    ((prev-dirabsdeclor dirabsdeclorp)
     (prev-span spanp)
     (pstate parstatep))
    :returns (mv erp
                 (dirabsdeclor dirabsdeclorp)
                 (span spanp)
                 (new-pstate parstatep))
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
    (b* (((reterr) (irr-dirabsdeclor) (irr-span) (irr-parstate))
         ;; We read the next token, to determine whether
         ;; there is another array or function abstract declarator.
         ((erp token & pstate) (read-token pstate)))
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
       ((or (equal token (token-punctuator "(")) ; (
            (equal token (token-punctuator "["))) ; [
        (b* ((pstate (unread-token pstate)) ;
             (psize (parsize pstate))
             ((erp next-dirabsdeclor next-span pstate) ; dirabsdeclor
              (parse-array/function-abstract-declarator pstate))
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible))
             ((unless (mbt (dirabsdeclor-decl?-nil-p next-dirabsdeclor)))
              (reterr :impossible))
             (curr-dirabsdeclor
              (combine-dirabsdeclor-into-dirabsdeclor prev-dirabsdeclor
                                                      next-dirabsdeclor))
             (curr-span (span-join prev-span next-span)))
          (parse-direct-abstract-declarator-rest curr-dirabsdeclor
                                                 curr-span
                                                 pstate)))
       ;; If token is not an open parenthesis or an open square bracket,
       ;; we have reached the end of the sequence of zero or more
       ;; array and function abstract declarators.
       (t ; other
        (b* ((pstate (if token (unread-token pstate) pstate))) ;
          (retok (dirabsdeclor-fix prev-dirabsdeclor)
                 (span-fix prev-span)
                 pstate)))))
    :measure (two-nats-measure (parsize pstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-abstract-declarator ((pstate parstatep))
    :returns (mv erp
                 (absdeclor absdeclorp)
                 (span spanp)
                 (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse an abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "An abstract declarator may consist of
       a pointer,
       or a direct abstract declarator,
       or a pointer followed by a direct abstract declarator."))
    (b* (((reterr) (irr-absdeclor) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token is a star, we must have a pointer,
       ;; so we parse it, after putting back the token.
       ;; Then we read another token,
       ;; to see if we have a direct abstract declarator after the pointer.
       ((equal token (token-punctuator "*")) ; *
        (b* ((pstate (unread-token pstate))
             (psize (parsize pstate))
             ((erp tyqualss tyqualss-span pstate) ; pointer
              (parse-pointer pstate))
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible))
             ((erp token2 & pstate) (read-token pstate)))
          (cond
           ;; If token2 may start a direct abstract declarator,
           ;; we put the token back
           ;; and we attempt to parse the direct abstract declarator.
           ((token-direct-abstract-declarator-start-p token2)
            ;; pointer dirabsdeclor...
            (b* ((pstate (unread-token pstate))
                 ((erp dirabsdeclor dirabsdeclor-span pstate)
                  ;; pointer dirabsdeclor
                  (parse-direct-abstract-declarator pstate)))
              (retok (make-absdeclor :pointers tyqualss
                                     :decl? dirabsdeclor)
                     (span-join tyqualss-span dirabsdeclor-span)
                     pstate)))
           ;; If token2 may not start a direct abstract declarator,
           ;; our abstract declarator just consists of the pointer part.
           (t ; pointer other
            (b* ((pstate (if token2 (unread-token pstate) pstate))) ; pointer
              (retok (make-absdeclor :pointers tyqualss
                                     :decl? nil)
                     tyqualss-span
                     pstate))))))
       ;; If token may start a direct abstract declarator,
       ;; our abstract declarator is just that, without the pointer part.
       ((token-direct-abstract-declarator-start-p token) ; dirabsdeclor...
        (b* ((pstate (unread-token pstate)) ;
             ((erp dirabsdeclor span pstate) ; dirabsdeclor
              (parse-direct-abstract-declarator pstate)))
          (retok (make-absdeclor :pointers nil
                                 :decl? dirabsdeclor)
                 span
                 pstate)))
       ;; If token is anything else, it is an error,
       ;; because this function is called when we expect an abstract declarator.
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a star ~
                               or an open parenthesis ~
                               or an open square bracket"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize pstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-direct-declarator ((pstate parstatep))
    :returns (mv erp
                 (dirdeclor dirdeclorp)
                 (span spanp)
                 (new-pstate parstatep))
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
    (b* (((reterr) (irr-dirdeclor) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token is an identifier,
       ;; that must be the start of the direct declarator.
       ((and token (token-case token :ident)) ; ident
        (parse-direct-declarator-rest (dirdeclor-ident
                                       (token-ident->unwrap token))
                                      span
                                      pstate))
       ;; If token is an open parenthesis,
       ;; we must have a parenthesized declarator.
       ((equal token (token-punctuator "(")) ; (
        (b* ((psize (parsize pstate))
             ((erp declor & pstate) (parse-declarator pstate)) ; ( declor
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible))
             ((erp last-span pstate) (read-punctuator ")" pstate))) ; ( declor )
          (parse-direct-declarator-rest (dirdeclor-paren declor)
                                        (span-join span last-span)
                                        pstate)))
       ;; If token is anything else, it is an error:
       ;; we do not have a direct declarator.
       (t
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "an identifier ~
                               or an open parenthesis"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-direct-declarator-rest ((prev-dirdeclor dirdeclorp)
                                        (prev-span spanp)
                                        (pstate parstatep))
    :returns (mv erp (dirdeclor dirdeclorp) (span spanp) (new-pstate parstatep))
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
       along with its span.")
     (xdoc::p
      "Although there are two possible variants for function declarators,
       since an identifier is a type specifier and thus a parameter declaration,
       we cannot disambiguate the @(':function-params') and @(':function-names')
       variants during parsing;
       we always generate @(':function-params') during parsing,
       and potentially re-classify it to @(':function-names')
       during post-parsing semantic analysis."))
    (b* (((reterr) (irr-dirdeclor) (irr-span) (irr-parstate))
         ((erp token & pstate) (read-token pstate)))
      (cond
       ;; If token is an open square bracket,
       ;; we have an array construct, which may be of different variants,
       ;; so we read more tokens.
       ((equal token (token-punctuator "[")) ; [
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ;; If token2 is a type qualifier,
           ;; we put it back and read a list of type qualifiers,
           ;; but the array variant is still not determined,
           ;; so we read more tokens.
           ((token-type-qualifier-p token2) ; [ tyqual
            (b* ((pstate (unread-token pstate)) ; [
                 ((erp tyquals & pstate) ; [ tyquals
                  (parse-type-qualifier-list pstate))
                 ((erp token3 span3 pstate) (read-token pstate)))
              (cond
               ;; If token3 may start an (assignment) expression,
               ;; we parse it, and we have determined the array variant.
               ((token-expression-start-p token3) ; [ tyquals expr...
                (b* ((pstate (unread-token pstate)) ; [ tyquals
                     ((erp expr & pstate) ; [ tyquals expr
                      (parse-assignment-expression pstate))
                     ((erp last-span pstate) ; [ tyquals expr ]
                      (read-punctuator "]" pstate)))
                  (retok (make-dirdeclor-array :decl prev-dirdeclor
                                               :tyquals tyquals
                                               :expr? expr)
                         (span-join prev-span last-span)
                         pstate)))
               ;; If token3 is a closed square bracket,
               ;; we have determined the variant, and we have no expression.
               ((equal token3 (token-punctuator "]")) ; [ tyquals ]
                (retok (make-dirdeclor-array :decl prev-dirdeclor
                                             :tyquals tyquals
                                             :expr? nil)
                       (span-join prev-span span3)
                       pstate))
               ;; If token3 is the 'static' keyword,
               ;; we have determined the variant,
               ;; and we must have an expression.
               ((equal token3 (token-keyword "static")) ; [ tyquals static
                (b* (((erp expr & pstate) ; [ tyquals static expr
                      (parse-assignment-expression pstate))
                     ((erp last-span pstate) ; [ tyquals static expr ]
                      (read-punctuator "]" pstate)))
                  (retok (make-dirdeclor-array-static2 :decl prev-dirdeclor
                                                       :tyquals tyquals
                                                       :expr expr)
                         (span-join prev-span last-span)
                         pstate)))
               ;; If token3 is anything else, it is an error.
               (t ; [ tyquals other
                (reterr-msg :where (position-to-msg (span->start span3))
                            :expected "an expression ~
                                       or the 'static' keyword ~
                                       or a closed square bracket"
                            :found (token-to-msg token3))))))
           ;; If token2 may start an assignment expression,
           ;; we have determined the variant.
           ((token-expression-start-p token2) ; [ expr...
            (b* ((pstate (unread-token pstate)) ; [
                 ((erp expr & pstate) ; [ expr
                  (parse-assignment-expression pstate))
                 ((erp last-span pstate) ; [ expr ]
                  (read-punctuator "]" pstate)))
              (retok (make-dirdeclor-array :decl prev-dirdeclor
                                           :tyquals nil
                                           :expr? expr)
                     (span-join prev-span last-span)
                     pstate)))
           ;; If token2 is the 'static' keyword,
           ;; we may have type qualifiers,
           ;; and we must have an expression;
           ;; we have determined the variant.
           ((equal token2 (token-keyword "static")) ; [ static
            (b* (((erp token3 & pstate) (read-token pstate)))
              (cond
               ;; If token3 is a type qualifier,
               ;; we put it back and parse a list of type qualifiers,
               ;; and then we parse an expression.
               ((token-type-qualifier-p token3) ; [ static tyqual
                (b* ((pstate (unread-token pstate)) ; [ static
                     ((erp tyquals & pstate) ; [ static tyquals
                      (parse-type-qualifier-list pstate))
                     ((erp expr & pstate) ; [ static tyquals expr
                      (parse-assignment-expression pstate))
                     ((erp last-span pstate) ; [ static tyquals expr ]
                      (read-punctuator "]" pstate)))
                  (retok (make-dirdeclor-array-static1 :decl prev-dirdeclor
                                                       :tyquals tyquals
                                                       :expr expr)
                         (span-join prev-span last-span)
                         pstate)))
               ;; If token3 is not a type qualifier,
               ;; we must have an expression.
               (t ; [ static other
                (b* ((pstate (unread-token pstate)) ; [ static
                     ((erp expr & pstate) ; [ static expr
                      (parse-assignment-expression pstate))
                     ((erp last-span pstate) ; [ static expr ]
                      (read-punctuator "]" pstate)))
                  (retok (make-dirdeclor-array-static1 :decl prev-dirdeclor
                                                       :tyquals nil
                                                       :expr expr)
                         (span-join prev-span last-span)
                         pstate))))))
           ;; If token2 is a closed square bracket,
           ;; we have an empty array construct.
           ((equal token2 (token-punctuator "]")) ; [ ]
            (retok (make-dirdeclor-array :decl prev-dirdeclor
                                         :tyquals nil
                                         :expr? nil)
                   (span-join prev-span span2)
                   pstate))
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
       ((equal token (token-punctuator "(")) ; (
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ;; If token2 is a closed parenthesis,
           ;; we have no parameter declarations.
           ((equal token2 (token-punctuator ")")) ; ( )
            (retok (make-dirdeclor-function-params :decl prev-dirdeclor
                                                   :params nil
                                                   :ellipsis nil)
                   (span-join prev-span span2)
                   pstate))
           ;; If token2 is anything else,
           ;; we must have a list of one or more parameter declarations.
           (t ; ( other
            (b* ((pstate (if token2 (unread-token pstate) pstate))
                 ((erp paramdecls ellipsis & pstate) ; ( params [, ...]
                  (parse-parameter-declaration-list pstate))
                 ((erp last-span pstate) ; ( params [, ...] )
                  (read-punctuator ")" pstate)))
              (retok (make-dirdeclor-function-params :decl prev-dirdeclor
                                                     :params paramdecls
                                                     :ellipsis ellipsis)
                     (span-join prev-span last-span)
                     pstate))))))
       ;; If token is anything else,
       ;; we have reached the end of the direct declarator.
       (t ; other
        (b* ((pstate (if token (unread-token pstate) pstate)))
          (retok (dirdeclor-fix prev-dirdeclor)
                 (span-fix prev-span)
                 pstate)))))
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-declarator ((pstate parstatep))
    :returns (mv erp (declor declorp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "A declarator has an optional pointer part
       followed by a mandatory direct declarator."))
    (b* (((reterr) (irr-declor) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token is a star, we must have a pointer,
       ;; so we parse it, and then we parse a direct declarator.
       ((equal token (token-punctuator "*")) ; *
        (b* ((pstate (unread-token pstate)) ;
             ((erp tyqualss & pstate) (parse-pointer pstate)) ; pointer
             ((erp dirdeclor last-span pstate) ; pointer dirdeclor
              (parse-direct-declarator pstate)))
          (retok (make-declor :pointers tyqualss
                              :decl dirdeclor)
                 (span-join span last-span)
                 pstate)))
       ;; If token is not a star, we must have a direct declarator.
       (t ; other
        (b* ((pstate (if token (unread-token pstate) pstate)) ;
             ((erp dirdeclor span pstate) ; dirdeclor
              (parse-direct-declarator pstate)))
          (retok (make-declor :pointers nil
                              :decl dirdeclor)
                 span
                 pstate)))))
    :measure (two-nats-measure (parsize pstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-struct-declarator ((pstate parstatep))
    :returns (mv erp
                 (structdeclor structdeclorp)
                 (span spanp)
                 (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a structure declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "A structure declarator consists of
       a declarator,
       or a declarator followed by colon and a constant expression,
       or a colon and a constant expression."))
    (b* (((reterr) (irr-structdeclor) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token may start a declarator, we parse it,
       ;; and then we see whether there is a colon with an expression.
       ((token-declarator-start-p token) ; declor...
        (b* ((pstate (unread-token pstate)) ;
             (psize (parsize pstate))
             ((erp declor span pstate) (parse-declarator pstate)) ; declor
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible))
             ((erp token2 & pstate) (read-token pstate)))
          (cond
           ;; If token2 is a colon,
           ;; we must have a constant expression after it.
           ((equal token2 (token-punctuator ":")) ; declor :
            (b* (((erp cexpr last-span pstate) ; declor : expr
                  (parse-constant-expression pstate)))
              (retok (make-structdeclor :declor? declor
                                        :expr? cexpr)
                     (span-join span last-span)
                     pstate)))
           ;; If token2 is not a colon,
           ;; the declarator is the whole structure declarator.
           (t ; declor other
            (b* ((pstate (if token2 (unread-token pstate) pstate)))
              (retok (make-structdeclor :declor? declor
                                        :expr? nil)
                     span
                     pstate))))))
       ;; If token is a colon,
       ;; we must be in the case in which there is no declarator
       ;; and there is just the colon and a constant expression.
       ((equal token (token-punctuator ":")) ; :
        (b* (((erp cexpr last-span pstate) ; : expr
              (parse-constant-expression pstate)))
          (retok (make-structdeclor :declor? nil
                                    :expr? cexpr)
                 (span-join span last-span)
                 pstate)))
       ;; If token is anything else, it is an error.
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a declarator or a colon"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize pstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-struct-declarator-list ((pstate parstatep))
    :returns (mv erp
                 (structdeclors structdeclor-listp)
                 (span spanp)
                 (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a list of one or more structure declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "We parse a structure declarator, which must be present.
       Then if we have a comma we recursively call this function
       to parse one or more structure declarators."))
    (b* (((reterr) nil (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp structdeclor span pstate) ; structdeclor
          (parse-struct-declarator pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize))))
          (reterr :impossible))
         ((erp token & pstate) (read-token pstate)))
      (cond
       ;; If token is a comma,
       ;; we must have at least another structure declarator.
       ((equal token (token-punctuator ",")) ; structdeclor ,
        (b* ((pstate (unread-token pstate)) ; structdeclor
             ((erp structdeclors last-span  pstate)
              ;; structdeclor , structdeclors
              (parse-struct-declarator-list pstate)))
          (retok (cons structdeclor structdeclors)
                 (span-join span last-span)
                 pstate)))
       ;; If token is not a comma,
       ;; we have reached the end of the structure declarator list.
       (t ; structdeclor other
        (b* ((pstate (if token (unread-token pstate) pstate)))
          (retok (list structdeclor)
                 span
                 pstate)))))
    :measure (two-nats-measure (parsize pstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-struct-declaration ((pstate parstatep))
    :returns (mv erp
                 (structdecl structdeclp)
                 (span spanp)
                 (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a structure declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "A structure declaration is either an assert declaration,
       which is easily recognized by the starting @('_Static_assert') keyword,
       or a list of one or more specifiers and qualifiers
       optionally followed by a list of one or more structure declarators."))
    (b* (((reterr) (irr-structdecl) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token is the '_Static_assert' keyword,
       ;; we have a static assertion.
       ((equal token (token-keyword "_Static_assert")) ; _Static_assert
        (b* (((erp statassert span pstate) ; staticassertion
              (parse-static-assert-declaration span pstate)))
          (retok (structdecl-statassert statassert)
                 span
                 pstate)))
       ;; Otherwise, we must have a specifier and qualifier list.
       (t ; other
        (b* ((pstate (if token (unread-token pstate) pstate)) ;
             (psize (parsize pstate))
             ((erp specquals span pstate) ; specquals
              (parse-specifier-qualifier-list nil pstate))
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible))
             ((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ;; If token2 may start a structure declarator,
           ;; we must have a list of one or more structure declarators,
           ;; which we parse, and then we parse the final semicolon.
           ((token-struct-declarator-start-p token2) ; specquals structdeclor...
            (b* ((pstate (unread-token pstate)) ; specquals
                 ((erp structdeclors & pstate) ; specquals structdeclors
                  (parse-struct-declarator-list pstate))
                 ((erp last-span pstate) ; specquals structdeclors ;
                  (read-punctuator ";" pstate)))
              (retok (make-structdecl-member :specqual specquals
                                             :declor structdeclors)
                     (span-join span last-span)
                     pstate)))
           ;; If token2 is a semicolon,
           ;; we have reached the end of the structure declaration.
           ((equal token2 (token-punctuator ";")) ; specquals ;
            (retok (make-structdecl-member :specqual specquals
                                           :declor nil)
                   (span-join span span2)
                   pstate))
           ;; If token2 is anything else, it is an error.
           (t ; specquals other
            (reterr-msg :where (position-to-msg (span->start span2))
                        :expected "a structure declarator or a semicolon"
                        :found (token-to-msg token2))))))))
    :measure (two-nats-measure (parsize pstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-struct-declaration-list ((pstate parstatep))
    :returns (mv erp
                 (structdecls structdecl-listp)
                 (span spanp)
                 (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a list of one or more structure declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "We parse the first structure declaration, which must be present.
       Then we recursively call this function if the next token
       may start another structure declaration."))
    (b* (((reterr) nil (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp structdecl span pstate) ; structdecl
          (parse-struct-declaration pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize))))
          (reterr :impossible))
         ((erp token & pstate) (read-token pstate)))
      (cond
       ;; If token may start another structure declaration,
       ;; recursively call this function.
       ((token-struct-declaration-start-p token) ; structdecl structdecl...
        (b* ((pstate (unread-token pstate))
             ((erp structdecls last-span pstate) ; structdecl structdecls
              (parse-struct-declaration-list pstate)))
          (retok (cons structdecl structdecls)
                 (span-join span last-span)
                 pstate)))
       ;; Otherwise, we have reached the end of the structure declarations.
       (t ; structdecl other
        (b* ((pstate (if token (unread-token pstate) pstate)))
          (retok (list structdecl) span pstate)))))
    :measure (two-nats-measure (parsize pstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-parameter-declaration ((pstate parstatep))
    :returns (mv erp
                 (paramdecl paramdeclp)
                 (span spanp)
                 (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a parameter declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "A parameter declaration always starts with
       a list of one or more declaration specifiers, which we parse.
       Then we may have a declarator, an abstract declarator, or nothing.")
     (xdoc::p
      "There is a non-trivial syntactic overlap
       between declarators and abstract declarators.
       For instance, if @('I') is an identifier, @('(I)') could be
       either a direct declarator for the parenthesized identifier
       or a function abstract declarator
       where @('I') is a type specifier for the (one) parameter.
       But this is just a simple example:
       there are infinite overlapping constructs,
       e.g. obtained by adding array and function declarator parts to @('I'),
       but not only those.
       We plan to revisit this issue,
       but for now here we just consider declarators,
       and not abstract declarators.
       This is very crude, so we should improve this soon."))
    (b* (((reterr) (irr-paramdecl) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp declspecs span pstate) ; declspecs
          (parse-declaration-specifiers nil pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize))))
          (reterr :impossible))
         ((erp token & pstate) (read-token pstate)))
      (cond
       ;; If token may start a declarator, we parse it.
       ((token-declarator-start-p token) ; declspecs declor...
        (b* ((pstate (unread-token pstate)) ; declspecs
             ((erp declor last-span pstate) ; declspecs declor
              (parse-declarator pstate)))
          (retok (make-paramdecl-nonabstract :spec declspecs
                                             :decl declor)
                 (span-join span last-span)
                 pstate)))
       ;; Otherwise, the parameter declarator has no declarator.
       (t ; declspecs other
        (b* ((pstate (if token (unread-token pstate) pstate)))
          (retok (make-paramdecl-abstract :spec declspecs
                                          :decl nil)
                 span
                 pstate)))))
    :measure (two-nats-measure (parsize pstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-parameter-declaration-list ((pstate parstatep))
    :returns (mv erp
                 (paramdecls paramdecl-listp)
                 (ellipsis booleanp)
                 (span spanp)
                 (new-pstate parstatep))
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
    (b* (((reterr) nil nil (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp paramdecl span pstate) ; paramdecl
          (parse-parameter-declaration pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize))))
          (reterr :impossible))
         ((erp token & pstate) (read-token pstate)))
      (cond
       ;; If token is a comma, we might have another parameter declaration,
       ;; but we need to check whether we have an ellipsis instead.
       ((equal token (token-punctuator ",")) ; paramdecl ,
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ;; If token2 is an ellipsis,
           ;; we have reached the end of the parameter declaration list.
           ((equal token2 (token-punctuator "...")) ; paramdecl , ...
            (retok (list paramdecl)
                   t
                   (span-join span span2)
                   pstate))
           ;; If token2 is not an ellipsis,
           ;; we must have more parameter declarators.
           (t ; paramdecl , other
            (b* ((pstate ; paramdecl ,
                  (if token2 (unread-token pstate) pstate))
                 ((erp paramdecls ellipsis last-span pstate)
                  ;; paramdecl , paramdecls [, ...]
                  (parse-parameter-declaration-list pstate)))
              (retok (cons paramdecl paramdecls)
                     ellipsis
                     (span-join span last-span)
                     pstate))))))
       ;; If token is not a comma,
       ;; we have reached the end of the parameter declaration list.
       (t ; paramdecl other
        (b* ((pstate (if token (unread-token pstate) pstate)))
          (retok (list paramdecl)
                 nil
                 span
                 pstate)))))
    :measure (two-nats-measure (parsize pstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-type-name ((pstate parstatep))
    :returns (mv erp (tyname tynamep) (span spanp) (new-pstate parstatep))
    :parents (parser parse-exprs/decls)
    :short "Parse a type name."
    :long
    (xdoc::topstring
     (xdoc::p
      "A type name always starts with one or more specifiers and qualifiers,
       which may be followed by an abstract declarator.
       We parse the specifier and qualifier list,
       and then we parse the abstract declarator if present."))
    (b* (((reterr) (irr-tyname) (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp specquals span pstate) ; specquals
          (parse-specifier-qualifier-list nil pstate))
         ((unless (mbt (<= (parsize pstate) (1- psize))))
          (reterr :impossible))
         ((erp token & pstate) (read-token pstate)))
      (cond
       ;; If token may start an abstract declarator, we parse it.
       ((token-abstract-declarator-start-p token) ; specquals absdeclor...
        (b* ((pstate (unread-token pstate)) ; specquals
             ((erp absdeclor last-span pstate) ; specquals absdeclor
              (parse-abstract-declarator pstate)))
          (retok (make-tyname :specqual specquals
                              :decl? absdeclor)
                 (span-join span last-span)
                 pstate)))
       ;; Otherwise, there is no abstract declarator.
       (t ; specquals other
        (b* ((pstate (if token (unread-token pstate) pstate)))
          (retok (make-tyname :specqual specquals
                              :decl? nil)
                 span
                 pstate)))))
    :measure (two-nats-measure (parsize pstate) 2))

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
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-expression)
    (defret parsize-of-parse-expression-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-expression-rest)
    (defret parsize-of-parse-assignment-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-assignment-expression)
    (defret parsize-of-parse-conditional-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-conditional-expression)
    (defret parsize-of-parse-logical-or-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-logical-or-expression)
    (defret parsize-of-parse-logical-or-expression-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-logical-or-expression-rest)
    (defret parsize-of-parse-logical-and-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-logical-and-expression)
    (defret parsize-of-parse-logical-and-expression-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-logical-and-expression-rest)
    (defret parsize-of-parse-inclusive-or-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-inclusive-or-expression)
    (defret parsize-of-parse-inclusive-or-expression-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-inclusive-or-expression-rest)
    (defret parsize-of-parse-exclusive-or-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-exclusive-or-expression)
    (defret parsize-of-parse-exclusive-or-expression-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-exclusive-or-expression-rest)
    (defret parsize-of-parse-and-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-and-expression)
    (defret parsize-of-parse-and-expression-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-and-expression-rest)
    (defret parsize-of-parse-equality-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-equality-expression)
    (defret parsize-of-parse-equality-expression-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-equality-expression-rest)
    (defret parsize-of-parse-relational-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-relational-expression)
    (defret parsize-of-parse-relational-expression-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-relational-expression-rest)
    (defret parsize-of-parse-shift-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-shift-expression)
    (defret parsize-of-parse-shift-expression-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-shift-expression-rest)
    (defret parsize-of-parse-additive-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-additive-expression)
    (defret parsize-of-parse-additive-expression-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-additive-expression-rest)
    (defret parsize-of-parse-multiplicative-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-multiplicative-expression)
    (defret parsize-of-parse-multiplicative-expression-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-multiplicative-expression-rest)
    (defret parsize-of-parse-cast-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-cast-expression)
    (defret parsize-of-parse-unary-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-unary-expression)
    (defret parsize-of-parse-postfix-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-postfix-expression)
    (defret parsize-of-parse-postfix-expression-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-postfix-expression-rest)
    (defret parsize-of-parse-argument-expressions-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-argument-expressions)
    (defret parsize-of-parse-argument-expressions-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-argument-expressions-rest)
    (defret parsize-of-parse-primary-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-primary-expression)
    (defret parsize-of-parse-generic-associations-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-generic-associations-rest)
    (defret parsize-of-parse-generic-association-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-generic-association)
    (defret parsize-of-parse-compound-literal-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-compound-literal)
    (defret parsize-of-parse-constant-expression-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-constant-expression)
    (defret parsize-of-parse-static-assert-declaration-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-static-assert-declaration)
    (defret parsize-of-parse-designator-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-designator)
    (defret parsize-of-parse-designator-list-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-designator-list)
    (defret parsize-of-parse--initializer-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-initializer)
    (defret parsize-of-parse-designation?-initializer-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-designation?-initializer)
    (defret parsize-of-parse-initializer-list-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-initializer-list)
    (defret parsize-of-parse-enumerator-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-enumerator)
    (defret parsize-of-parse-enumerator-list-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-enumerator-list)
    (defret parsize-of-parse-specifier/qualifier-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-specifier/qualifier)
    (defret parsize-of-parse-specifier-qualifier-list-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-specifier-qualifier-list)
    (defret parsize-of-parse-declaration-specifier-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-declaration-specifier)
    (defret parsize-of-parse-declaration-specifiers-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-declaration-specifiers)
    (defret parsize-of-parse-struct-or-union-specifier-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-struct-or-union-specifier)
    (defret parsize-of-parse-enum-specifier-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-enum-specifier)
    (defret parsize-of-parse-alignment-specifier-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-alignment-specifier)
    (defret parsize-of-parse-array/function-abstract-declarator-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-array/function-abstract-declarator)
    (defret parsize-of-parse-direct-abstract-declarator-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-direct-abstract-declarator)
    (defret parsize-of-parse-direct-abstract-declarator-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-direct-abstract-declarator-rest)
    (defret parsize-of-parse-abstract-declarator-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-abstract-declarator)
    (defret parsize-of-parse-direct-declarator-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-direct-declarator)
    (defret parsize-of-parse-direct-declarator-rest-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-direct-declarator-rest)
    (defret parsize-of-parse-declarator-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-declarator)
    (defret parsize-of-parse-struct-declarator-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-struct-declarator)
    (defret parsize-of-parse-struct-declarator-list-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-struct-declarator-list)
    (defret parsize-of-parse-struct-declaration-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-struct-declaration)
    (defret parsize-of-parse-struct-declaration-list-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-struct-declaration-list)
    (defret parsize-of-parse-parameter-declaration-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-parameter-declaration)
    (defret parsize-of-parse-parameter-declaration-list-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-parameter-declaration-list)
    (defret parsize-of-parse-type-name-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-type-name)
    :hints
    (("Goal" :in-theory (enable fix nfix))
     (cond
      ((acl2::occur-lst '(acl2::flag-is 'parse-cast-expression)
                        clause)
       '(:expand (parse-cast-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-postfix-expression)
                        clause)
       '(:expand (parse-postfix-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-generic-association)
                        clause)
       '(:expand (parse-generic-association pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-abstract-declarator)
                        clause)
       '(:expand (parse-direct-abstract-declarator pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-declarator)
                        clause)
       '(:expand (parse-direct-declarator pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-specifier-qualifier-list)
                        clause)
       '(:expand (parse-specifier-qualifier-list tyspec-seenp pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration-specifiers)
                        clause)
       '(:expand (parse-declaration-specifiers tyspec-seenp pstate))))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual parsize-of-parse-exprs/decls-cond
    (defret parsize-of-parse-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-expression)
    (defret parsize-of-parse-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-expression-rest)
    (defret parsize-of-parse-assignment-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-assignment-expression)
    (defret parsize-of-parse-conditional-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-conditional-expression)
    (defret parsize-of-parse-logical-or-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-logical-or-expression)
    (defret parsize-of-parse-logical-or-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-logical-or-expression-rest)
    (defret parsize-of-parse-logical-and-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-logical-and-expression)
    (defret parsize-of-parse-logical-and-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-logical-and-expression-rest)
    (defret parsize-of-parse-inclusive-or-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-inclusive-or-expression)
    (defret parsize-of-parse-inclusive-or-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-inclusive-or-expression-rest)
    (defret parsize-of-parse-exclusive-or-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-exclusive-or-expression)
    (defret parsize-of-parse-exclusive-or-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-exclusive-or-expression-rest)
    (defret parsize-of-parse-and-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-and-expression)
    (defret parsize-of-parse-and-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-and-expression-rest)
    (defret parsize-of-parse-equality-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-equality-expression)
    (defret parsize-of-parse-equality-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-equality-expression-rest)
    (defret parsize-of-parse-relational-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-relational-expression)
    (defret parsize-of-parse-relational-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-relational-expression-rest)
    (defret parsize-of-parse-shift-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-shift-expression)
    (defret parsize-of-parse-shift-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-shift-expression-rest)
    (defret parsize-of-parse-additive-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-additive-expression)
    (defret parsize-of-parse-additive-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-additive-expression-rest)
    (defret parsize-of-parse-multiplicative-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-multiplicative-expression)
    (defret parsize-of-parse-multiplicative-expression-rest-cond
      t
      :rule-classes nil
      :fn parse-multiplicative-expression-rest)
    (defret parsize-of-parse-cast-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-cast-expression)
    (defret parsize-of-parse-unary-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-unary-expression)
    (defret parsize-of-parse-postfix-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
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
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-primary-expression)
    (defret parsize-of-parse-generic-associations-rest-cond
      t
      :rule-classes nil
      :fn parse-generic-associations-rest)
    (defret parsize-of-parse-generic-association-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-generic-association)
    (defret parsize-of-parse-compound-literal-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-compound-literal)
    (defret parsize-of-parse-constant-expression-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-constant-expression)
    (defret parsize-of-parse-static-assert-declaration-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-static-assert-declaration)
    (defret parsize-of-parse-designator-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-designator)
    (defret parsize-of-parse-designator-list-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-designator-list)
    (defret parsize-of-parse-initializer-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-initializer)
    (defret parsize-of-parse-designation?-initializer-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-designation?-initializer)
    (defret parsize-of-parse-initializer-list-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-initializer-list)
    (defret parsize-of-parse-enumerator-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-enumerator)
    (defret parsize-of-parse-enumerator-list-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-enumerator-list)
    (defret parsize-of-parse-specifier/qualifier-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-specifier/qualifier)
    (defret parsize-of-parse-specifier-qualifier-list-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-specifier-qualifier-list)
    (defret parsize-of-parse-declaration-specifier-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-declaration-specifier)
    (defret parsize-of-parse-declaration-specifiers-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-declaration-specifiers)
    (defret parsize-of-parse-struct-or-union-specifier-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-struct-or-union-specifier)
    (defret parsize-of-parse-enum-specifier-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-enum-specifier)
    (defret parsize-of-parse-alignment-specifier-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-alignment-specifier)
    (defret parsize-of-parse-array/function-abstract-declarator-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-array/function-abstract-declarator)
    (defret parsize-of-parse-direct-abstract-declarator-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-direct-abstract-declarator)
    (defret parsize-of-parse-direct-abstract-declarator-rest-cond
      t
      :rule-classes nil
      :fn parse-direct-abstract-declarator-rest)
    (defret parsize-of-parse-abstract-declarator-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-abstract-declarator)
    (defret parsize-of-parse-direct-declarator-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-direct-declarator)
    (defret parsize-of-parse-direct-declarator-rest-cond
      t
      :rule-classes nil
      :fn parse-direct-declarator-rest)
    (defret parsize-of-parse-declarator-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-declarator)
    (defret parsize-of-parse-struct-declarator-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-struct-declarator)
    (defret parsize-of-parse-struct-declarator-list-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-struct-declarator-list)
    (defret parsize-of-parse-struct-declaration-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-struct-declaration)
    (defret parsize-of-parse-struct-declaration-list-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-struct-declaration-list)
    (defret parsize-of-parse-parameter-declaration-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-parameter-declaration)
    (defret parsize-of-parse-parameter-declaration-list-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-parameter-declaration-list)
    (defret parsize-of-parse-type-name-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-type-name)
    :hints
    (("Goal" :in-theory (enable fix nfix))
     (cond
      ((acl2::occur-lst '(acl2::flag-is 'parse-expression)
                        clause)
       '(:expand (parse-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-assignment-expression)
                        clause)
       '(:expand (parse-assignment-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-logical-or-expression)
                        clause)
       '(:expand (parse-logical-or-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-logical-and-expression)
                        clause)
       '(:expand (parse-logical-and-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-inclusive-or-expression)
                        clause)
       '(:expand (parse-inclusive-or-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-exclusive-or-expression)
                        clause)
       '(:expand (parse-exclusive-or-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-and-expression)
                        clause)
       '(:expand (parse-and-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-equality-expression)
                        clause)
       '(:expand (parse-equality-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-relational-expression)
                        clause)
       '(:expand (parse-relational-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-shift-expression)
                        clause)
       '(:expand (parse-shift-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-additive-expression)
                        clause)
       '(:expand (parse-additive-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-multiplicative-expression)
                        clause)
       '(:expand (parse-multiplicative-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-cast-expression)
                        clause)
       '(:expand (parse-cast-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-postfix-expression)
                        clause)
       '(:expand (parse-postfix-expression pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-generic-association)
                        clause)
       '(:expand (parse-generic-association pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-abstract-declarator)
                        clause)
       '(:expand (parse-direct-abstract-declarator pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-declarator)
                        clause)
       '(:expand (parse-direct-declarator pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-specifier-qualifier-list)
                        clause)
       '(:expand (parse-specifier-qualifier-list tyspec-seenp pstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration-specifiers)
                        clause)
       '(:expand (parse-declaration-specifiers tyspec-seenp pstate))))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret dirabsdeclor-decl?-nil-p-of-parse-array/function-abstract-declarator
    (implies (not erp)
             (dirabsdeclor-decl?-nil-p dirabsdeclor))
    :hints (("Goal"
             :in-theory (enable dirabsdeclor-decl?-nil-p)
             :expand (parse-array/function-abstract-declarator pstate)))
    :fn parse-array/function-abstract-declarator)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards parse-expression
    :hints (("Goal" :in-theory (e/d (acl2::member-of-cons)
                                    ((:e tau-system))))))) ; for speed

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-init-declarator ((pstate parstatep))
  :returns (mv erp (initdeclor initdeclorp) (span spanp) (new-pstate parstatep))
  :short "Parse an initializer declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "An initializer declarator consists of a declarator,
     optionally followed by an equal sign and an initializer."))
  (b* (((reterr) (irr-initdeclor) (irr-span) (irr-parstate))
       ((erp declor span pstate) (parse-declarator pstate)) ; declor
       ((erp token & pstate) (read-token pstate)))
    (cond
     ;; If token is an equal sign, there must be an initializer.
     ((equal token (token-punctuator "=")) ; declor =
      (b* (((erp initer last-span pstate) ; declor = initer
            (parse-initializer pstate)))
        (retok (make-initdeclor :declor declor :init? initer)
               (span-join span last-span)
               pstate)))
     ;; Otherwise, there is no initializer.
     (t ; declor other
      (b* ((pstate (if token (unread-token pstate) pstate))) ; declor
        (retok (make-initdeclor :declor declor :init? nil)
               span
               pstate)))))

  ///

  (defret parsize-of-parse-init-declarator-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-parse-init-declarator-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-init-declarator-list ((pstate parstatep))
  :returns (mv erp
               (initdeclors initdeclor-listp)
               (span spanp)
               (new-pstate parstatep))
  :short "Parse a list of one or more initializer declarators."
  :long
  (xdoc::topstring
   (xdoc::p
    "We parse the first one, which must be present.
     If there is a comma after that,
     we recursively parse one or more after the comma."))
  (b* (((reterr) nil (irr-span) (irr-parstate))
       ((erp initdeclor span pstate) ; initdeclor
        (parse-init-declarator pstate))
       ((erp token & pstate) (read-token pstate)))
    (cond
     ;; If token is a comma,
     ;; recursively parse one or more initializer declarators,
     ;; and combine with the one just parsed.
     ((equal token (token-punctuator ",")) ; initdeclor ,
      (b* (((erp initdeclors last-span pstate) ; initdeclor , initdeclors
            (parse-init-declarator-list pstate)))
        (retok (cons initdeclor initdeclors)
               (span-join span last-span)
               pstate)))
     ;; If token is anything else, we have reached the end of the list.
     (t ; initdeclor other
      (b* ((pstate (if token (unread-token pstate) pstate)))
        (retok (list initdeclor) span pstate)))))
  :measure (parsize pstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-init-declarator-list-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-parse-init-declarator-list-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-declaration ((pstate parstatep))
  :returns (mv erp (decl declp) (span spanp) (new-pstate parstatep))
  :short "Parse a declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "A declaration is either an assert declaration,
     recognized by the starting @('_Static_assert') keyword,
     or a list of one or more declaration specifiers
     optionally followed by a list of one or more initializer declarators
     and mandatorily followed by a semicolon."))
  (b* (((reterr) (irr-decl) (irr-span) (irr-parstate))
       ((erp token span pstate) (read-token pstate)))
    (cond
     ;; If token may start a declaration specifier, we put it back and
     ;; we parse a list or one or more declaration specifiers.
     ;; Then we read more tokens to see if we have initializer declarators.
     ((token-declaration-specifier-start-p token) ; decspec...
      (b* ((pstate (unread-token pstate)) ;
           ((erp declspecs span pstate) ; declspecs
            (parse-declaration-specifiers nil pstate))
           ((erp token2 span2 pstate) (read-token pstate)))
        (cond
         ;; If token2 may start a declarator,
         ;; which is equivalent to saying that
         ;; it may start an initializer declarator,
         ;; we parse the list of one or more initializer declarators,
         ;; and then the final semicolon.
         ((token-declarator-start-p token2) ; declspecs declor...
          (b* ((pstate (unread-token pstate)) ; declspecs
               ((erp initdeclors & pstate) ; declspecs initdeclors
                (parse-init-declarator-list pstate))
               ((erp last-span pstate) ; declspecs initdeclors ;
                (read-punctuator ";" pstate)))
            (retok (make-decl-decl :specs declspecs
                                   :init initdeclors)
                   (span-join span last-span)
                   pstate)))
         ;; If token2 is a semicolon,
         ;; we have no initializer declarators.
         ((equal token2 (token-punctuator ";")) ; declspecs ;
          (retok (make-decl-decl :specs declspecs
                                 :init nil)
                 (span-join span span2)
                 pstate))
         ;; If token2 is anything else, it is an error.
         (t ; declspecs other
          (reterr-msg :where (position-to-msg (span->start span2))
                      :expected "a declarator or a semicolon"
                      :found (token-to-msg token2))))))
     ;; If token is the keyword @('_Static_assert'),
     ;; we have an assert declaration.
     ((equal token (token-keyword "_Static_assert")) ; _Static_assert
      (b* (((erp statassert last-span pstate) ; statassert
            (parse-static-assert-declaration span pstate)))
        (retok (decl-statassert statassert)
               (span-join span last-span)
               pstate)))
     ;; If token is anything else, it is an error.
     (t ; other
      (reterr-msg :where (position-to-msg (span->start span))
                  :expected "a declaration specifier ~
                             or the _Static_assert keyword"
                  :found (token-to-msg token)))))

  ///

  (defret parsize-of-parse-declaration-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-parse-declaration-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-declaration-list ((pstate parstatep))
  :returns (mv erp (decls decl-listp) (span spanp) (new-pstate parstatep))
  :short "Parse a list of one or more declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We parse the first one, which must be present.
     Then we stop if the next token is an open curly brace,
     because the only place where we parse declaration lists
     is in function definitions, between declarator and body.
     Otherwise we recursively call this function to parse more."))
  (b* (((reterr) nil (irr-span) (irr-parstate))
       ((erp decl span pstate) (parse-declaration pstate)) ; decl
       ((erp token & pstate) (read-token pstate)))
    (cond
     ;; If token is an open curly brace, we stop.
     ((equal token (token-punctuator "{"))  ; decl {
      (retok (list decl) span pstate))
     ;; If token is anything else, we parse more declarations.
     (t ; decl other
      (b* ((pstate (if token (unread-token pstate) pstate)) ; decl
           ((erp decls last-span pstate) ; decl decls
            (parse-declaration-list pstate)))
        (retok (cons decl decls)
               (span-join span last-span)
               pstate)))))
  :measure (parsize pstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-declaration-list-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-parse-declaration-list-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

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

  (define parse-statement ((pstate parstatep))
    :returns (mv erp (stmt stmtp) (span spanp) (new-pstate parstatep))
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
    (b* (((reterr) (irr-stmt) (irr-span) (irr-parstate))
         ((erp token span pstate) (read-token pstate)))
      (cond
       ;; If token is an identifier,
       ;; we could have a labeled statement or an expression statement.
       ;; So we need to read another token.
       ((and token (token-case token :ident)) ; ident
        (b* ((ident (token-ident->unwrap token))
             ((erp token2 & pstate) (read-token pstate)))
          (cond
           ;; If token2 is a colon,
           ;; we must have a labeled statement.
           ((equal token2 (token-punctuator ":")) ; ident :
            (b* (((erp stmt last-span pstate) ; ident : stmt
                  (parse-statement pstate)))
              (retok (make-stmt-labeled :label (label-name ident)
                                        :stmt stmt)
                     (span-join span last-span)
                     pstate)))
           ;; If token2 is not a colon,
           ;; we put it back along with the previous token,
           ;; and we attempt to parse an expression followed by a semicolon.
           (t ; ident other
            (b* ((pstate (if token2 (unread-token pstate) pstate)) ; ident
                 (pstate (unread-token pstate)) ;
                 ((erp expr span pstate) (parse-expression pstate)) ; expr
                 ((erp last-span pstate) (read-punctuator ";" pstate))) ; expr ;
              (retok (stmt-expr expr)
                     (span-join span last-span)
                     pstate))))))
       ;; If token is an open curly brace,
       ;; we must have a compound statement.
       ((equal token (token-punctuator "{")) ; {
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ;; If token2 is a closed curly brace,
           ;; we have an empty compound statement.
           ((equal token2 (token-punctuator "}")) ; { }
            (retok (stmt-compound nil)
                   (span-join span span2)
                   pstate))
           ;; Otherwise, we parse a list of one or more block items.
           (t ; { other
            (b* ((pstate (if token2 (unread-token pstate) pstate)) ; {
                 ((erp items & pstate) ; { blockitems
                  (parse-block-item-list pstate))
                 ((erp last-span pstate) ; { blockitems }
                  (read-punctuator "}" pstate)))
              (retok (stmt-compound items)
                     (span-join span last-span)
                     pstate))))))
       ;; If token is a semicolon,
       ;; we have an expression statement without expression.
       ((equal token (token-punctuator ";")) ; ;
        (retok (stmt-expr nil) span pstate))
       ;; If token is the 'case' keyword,
       ;; we must have a labeled statement.
       ((equal token (token-keyword "case")) ; case
        (b* (((erp cexpr & pstate) ; case constexpr
              (parse-constant-expression pstate))
             ((erp & pstate) (read-punctuator ":" pstate)) ; case constexpr :
             ((erp stmt last-span pstate) ; case constexpr : stmt
              (parse-statement pstate)))
          (retok (make-stmt-labeled :label (label-const cexpr)
                                    :stmt stmt)
                 (span-join span last-span)
                 pstate)))
       ;; If token is the default keyword,
       ;; we must have a labeled statement.
       ((equal token (token-keyword "default")) ; default
        (b* (((erp & pstate) (read-punctuator ":" pstate)) ; default :
             ((erp stmt last-span pstate) ; default : stmt
              (parse-statement pstate)))
          (retok (make-stmt-labeled :label (label-default)
                                    :stmt stmt)
                 (span-join span last-span)
                 pstate)))
       ;; If token is the 'goto' keyword, we have a jump statement.
       ((equal token (token-keyword "goto")) ; goto
        (b* (((erp ident & pstate) (read-identifier pstate)) ; goto ident
             ((erp last-span pstate) ; goto ident ;
              (read-punctuator ";" pstate)))
          (retok (stmt-goto ident)
                 (span-join span last-span)
                 pstate)))
       ;; If token is the keyword 'continue', we have a jump statement.
       ((equal token (token-keyword "continue")) ; continue
        (b* (((erp last-span pstate) ; continue ;
              (read-punctuator ";" pstate)))
          (retok (stmt-continue)
                 (span-join span last-span)
                 pstate)))
       ;; If token is the keyword 'break', we have a jump statement.
       ((equal token (token-keyword "break")) ; break
        (b* (((erp last-span pstate) ; break ;
              (read-punctuator ";" pstate)))
          (retok (stmt-break)
                 (span-join span last-span)
                 pstate)))
       ;; If token is the keyword 'return', we have a jump statement.
       ;; There may be an expression or not.
       ((equal token (token-keyword "return")) ; return
        (b* (((erp token2 span2 pstate) (read-token pstate)))
          (cond
           ;; If token2 may start an expression, we must have an expression.
           ((token-expression-start-p token2) ; return expr...
            (b* ((pstate (unread-token pstate)) ; return
                 ((erp expr & pstate) (parse-expression pstate)) ; return expr
                 ((erp last-span pstate) ; return expr ;
                  (read-punctuator ";" pstate)))
              (retok (stmt-return expr)
                     (span-join span last-span)
                     pstate)))
           ;; If token2 is a semicolon, there is no expression.
           ((equal token2 (token-punctuator ";")) ; return ;
            (retok (stmt-return nil)
                   (span-join span span2)
                   pstate))
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
       ((equal token (token-keyword "if")) ; if
        (b* (((erp & pstate) (read-punctuator "(" pstate)) ; if (
             ((erp expr & pstate) (parse-expression pstate)) ; if ( expr
             ((erp & pstate) (read-punctuator ")" pstate)) ; if ( expr )
             (psize (parsize pstate))
             ((erp stmt stmt-span pstate) ; if ( expr ) stmt
              (parse-statement pstate))
             ((unless (mbt (<= (parsize pstate) (1- psize))))
              (reterr :impossible))
             ((erp token2 & pstate) (read-token pstate)))
          (cond
           ;; If token2 is the 'else' keyword,
           ;; we continue to parse this selection statement.
           ((equal token2 (token-keyword "else")) ; if ( expr ) stmt else
            (b* (((erp stmt-else last-span pstate) ; if ( expr ) stmt else stmt
                  (parse-statement pstate)))
              (retok (make-stmt-ifelse :test expr
                                       :then stmt
                                       :else stmt-else)
                     (span-join span last-span)
                     pstate)))
           ;; If token is not the 'else' keyword,
           ;; we have an 'if' statement without 'else'.
           (t ; if ( expr ) stmt other
            (b* ((pstate ; if ( expr ) stmt
                  (if token2 (unread-token pstate) pstate)))
              (retok (make-stmt-if :test expr
                                   :then stmt)
                     (span-join span stmt-span)
                     pstate))))))
       ;; If token is the 'switch' keyword, we have a selection statement.
       ((equal token (token-keyword "switch")) ; switch
        (b* (((erp & pstate) (read-punctuator "(" pstate)) ; switch (
             ((erp expr & pstate) (parse-expression pstate)) ; switch ( expr
             ((erp & pstate) (read-punctuator ")" pstate)) ; switch ( expr )
             ((erp stmt last-span pstate) ; switch ( expr ) stmt
              (parse-statement pstate)))
          (retok (make-stmt-switch :target expr
                                   :body stmt)
                 (span-join span last-span)
                 pstate)))
       ;; If token is the 'while' keyword, we have an iteration statement.
       ((equal token (token-keyword "while")) ; while
        (b* (((erp & pstate) (read-punctuator "(" pstate)) ; while (
             ((erp expr & pstate) (parse-expression pstate)) ; while ( expr
             ((erp & pstate) (read-punctuator ")" pstate)) ; while ( expr )
             ((erp stmt last-span pstate) ; while ( expr ) stmt
              (parse-statement pstate)))
          (retok (make-stmt-while :test expr
                                  :body stmt)
                 (span-join span last-span)
                 pstate)))
       ;; If token is the 'do' keyword, we have an iteration statement.
       ((equal token (token-keyword "do")) ; do
        (b* (((erp stmt & pstate) (parse-statement pstate)) ; do stmt
             ((erp & pstate) (read-keyword "while" pstate)) ; do stmt while
             ((erp & pstate) (read-punctuator "(" pstate)) ; do stmt while (
             ((erp expr & pstate) ; do stmt while ( expr
              (parse-expression pstate))
             ((erp & pstate) ; do stmt while ( expr )
              (read-punctuator ")" pstate))
             ((erp last-span pstate) ; do stmt while ( expr ) ;
              (read-punctuator ";" pstate)))
          (retok (make-stmt-dowhile :body stmt
                                    :test expr)
                 (span-join span last-span)
                 pstate)))
       ;; If token is the 'for' keyword, we have an iteration statement.
       ((equal token (token-keyword "for")) ; for
        (b* (((erp & pstate) (read-punctuator "(" pstate)) ; for (
             ((erp token2 & pstate) (read-token pstate)))
          (cond
           ;; If token2 may start an expression,
           ;; we commit to parsing an expression,
           ;; i.e. to the kind of 'for' loop with the expression.
           ;; See th discussion in the documentation of this function above.
           ((token-expression-start-p token2) ; for ( expr...
            (b* ((pstate (unread-token pstate)) ; for (
                 ((erp init-expr & pstate) ; for ( expr
                  (parse-expression pstate))
                 ((erp & pstate) ; for ( expr ;
                  (read-punctuator ";" pstate))
                 ((erp token3 span3 pstate) (read-token pstate)))
              (cond
               ;; If token3 may start an expression,
               ;; there must be a test expression.
               ((token-expression-start-p token3) ; for ( expr ; expr...
                (b* ((pstate (unread-token pstate)) ; for ( expr ;
                     ((erp test-expr & pstate) ; for ( expr ; expr
                      (parse-expression pstate))
                     ((erp & pstate) ; for ( expr ; expr ;
                      (read-punctuator ";" pstate))
                     ((erp token4 span4 pstate) (read-token pstate)))
                  (cond
                   ;; If token4 may start an expression,
                   ;; we must have an update expression.
                   ((token-expression-start-p
                     token4) ; for ( expr ; expr ; expr...
                    (b* ((pstate (unread-token pstate)) ; for ( expr ; expr ;
                         ((erp next-expr & pstate) ; for ( expr ; expr ; expr
                          (parse-expression pstate))
                         ((erp & pstate) ; for ( expr ; expr ; expr )
                          (read-punctuator ")" pstate))
                         ((erp stmt last-span pstate)
                          ;; for ( expr ; expr ; expr ) stmt
                          (parse-statement pstate)))
                      (retok (make-stmt-for :init init-expr
                                            :test test-expr
                                            :next next-expr
                                            :body stmt)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 is a closed parenthesis,
                   ;; we have no update expression.
                   ((equal token4 (token-punctuator ")"))
                    (b* (((erp stmt last-span pstate)
                          ;; for ( expr ; expr ; ) stmt
                          (parse-statement pstate)))
                      (retok (make-stmt-for :init init-expr
                                            :test test-expr
                                            :next nil
                                            :body stmt)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 is anything else, it is an error.
                   (t ; for ( expr ; expr ; other
                    (reterr-msg :where (position-to-msg (span->start span4))
                                :expected "an expression ~
                                           or a closed parenthesis"
                                :found (token-to-msg token4))))))
               ;; If token3 is a semicolon, there is no test expression.
               ((equal token3 (token-punctuator ";")) ; for ( expr ; ;
                (b* (((erp token4 & pstate) (read-token pstate)))
                  (cond
                   ;; If token4 may start an expression,
                   ;; we must have an update expression.
                   ((token-expression-start-p token4) ; for ( expr ; ; expr...
                    (b* ((pstate (unread-token pstate)) ; for ( expr ; ;
                         ((erp next-expr & pstate) ; for ( expr ; ; expr
                          (parse-expression pstate))
                         ((erp & pstate) ; for ( expr ; ; expr )
                          (read-punctuator ")" pstate))
                         ((erp stmt last-span pstate)
                          ;; for ( expr ; ; expr ) stmt
                          (parse-statement pstate)))
                      (retok (make-stmt-for :init init-expr
                                            :test nil
                                            :next next-expr
                                            :body stmt)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 is a closed parenthesis,
                   ;; we have no update expression.
                   ((equal token4 (token-punctuator ")")) ; for ( expr ; ; )
                    (b* (((erp stmt last-span pstate) ; for ( expr ; ; ) stmt
                          (parse-statement pstate)))
                      (retok (make-stmt-for :init init-expr
                                            :test nil
                                            :next nil
                                            :body stmt)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 is anything else, it is an error.
                   (t ; for ( expr ; ; other
                    (reterr-msg :where (position-to-msg (span->start span3))
                                :expected "an expression ~
                                           or a closed parenthesis"
                                :found (token-to-msg token4))))))
               ;; If token3 is anything else, is is an error.
               (t ; for ( expr ; other
                (reterr-msg :where (position-to-msg (span->start span3))
                            :expected "an expression ~
                                       or a semicolon"
                            :found (token-to-msg token3))))))
           ;; If token2 is a semicolon, we have no initializing expression.
           ((equal token2 (token-punctuator ";")) ; for ( ;
            (b* (((erp token3 span3 pstate) (read-token pstate)))
              (cond
               ;; If token3 may start an expression,
               ;; we must have a test expression.
               ((token-expression-start-p token3) ; for ( ; expr...
                (b* ((pstate (unread-token pstate)) ; for ( ;
                     ((erp test-expr & pstate) ; for ( ; expr
                      (parse-expression pstate))
                     ((erp & pstate) ; for ( ; expr ;
                      (read-punctuator ";" pstate))
                     ((erp token4 span4 pstate) (read-token pstate)))
                  (cond
                   ;; If token4 may start an expression,
                   ;; we must have an update expression.
                   ((token-expression-start-p token4) ; for ( ; expr ; expr...
                    (b* ((pstate (unread-token pstate)) ; for ( ; expr ;
                         ((erp next-expr & pstate) ; for ( ; expr ; expr
                          (parse-expression pstate))
                         ((erp & pstate) ; for ( ; expr ; expr )
                          (read-punctuator ")" pstate))
                         ((erp stmt last-span pstate)
                          ;; for ( ; expr ; expr ) stmt
                          (parse-statement pstate)))
                      (retok (make-stmt-for :init nil
                                            :test test-expr
                                            :next next-expr
                                            :body stmt)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 is a closed parenthesis,
                   ;; we have no update expression.
                   ((equal token4 (token-punctuator ")")) ; for ( ; expr ; )
                    (b* (((erp stmt last-span pstate) ; for ( ; expr ; ) stmt
                          (parse-statement pstate)))
                      (retok (make-stmt-for :init nil
                                            :test test-expr
                                            :next nil
                                            :body stmt)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 is anything else, it is an error.
                   (t ; for ( ; expr ; other
                    (reterr-msg :where (position-to-msg (span->start span4))
                                :expected "an expression ~
                                           or a closed parenthesis"
                                :found (token-to-msg token4))))))
               ;; If token3 is a semicolon, we have no test expression.
               ((equal token3 (token-punctuator ";")) ; for ( ; ;
                (b* (((erp token4 span4 pstate) (read-token pstate)))
                  (cond
                   ;; If token4 may start an expression,
                   ;; we must have an update expression.
                   ((token-expression-start-p token4) ; for ( ; ; expr...
                    (b* ((pstate (unread-token pstate)) ; for ( ; ;
                         ((erp next-expr & pstate) ; for ( ; ; expr
                          (parse-expression pstate))
                         ((erp & pstate) ; for ( ; ; expr )
                          (read-punctuator ")" pstate))
                         ((erp stmt last-span pstate) ; for ( ; ; expr ) stmt
                          (parse-statement pstate)))
                      (retok (make-stmt-for :init nil
                                            :test nil
                                            :next next-expr
                                            :body stmt)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 is a closed parenthesis,
                   ;; we have no udpate expression.
                   ((equal token4 (token-punctuator ")")) ; for ( ; ; )
                    (b* (((erp stmt last-span pstate) ; for ( ; ; ) stmt
                          (parse-statement pstate)))
                      (retok (make-stmt-for :init nil
                                            :test nil
                                            :next nil
                                            :body stmt)
                             (span-join span last-span)
                             pstate)))
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
           ;; If token2 is anything else, we commit to parsing a declaration.
           ;; See the documentation of this function above for an explanation.
           (t ; for ( other
            (b* ((pstate (if token2 (unread-token pstate) pstate)) ; for (
                 ((erp decl & pstate) (parse-declaration pstate)) ; for ( decl
                 ((erp token3 span3 pstate) (read-token pstate)))
              (cond
               ;; If token3 may start an expression,
               ;; we must have a test expression.
               ((token-expression-start-p token3) ; for ( decl expr...
                (b* ((pstate (unread-token pstate)) ; for ( decl
                     ((erp test-expr & pstate) ; for ( decl expr
                      (parse-expression pstate))
                     ((erp & pstate) ; for ( decl expr ;
                      (read-punctuator ";" pstate))
                     ((erp token4 span4 pstate) (read-token pstate)))
                  (cond
                   ;; If token4 may start an expression,
                   ;; we must have an update expression.
                   ((token-expression-start-p
                     token4) ; for ( decl expr ; expr...
                    (b* ((pstate (unread-token pstate))
                         ((erp next-expr & pstate) ; for ( decl expr ; expr
                          (parse-expression pstate))
                         ((erp & pstate) ; for ( decl expr ; expr )
                          (read-punctuator ")" pstate))
                         ((erp stmt last-span pstate)
                          ;; for ( decl expr ; expr ) stmt
                          (parse-statement pstate)))
                      (retok (make-stmt-fordecl :init decl
                                                :test test-expr
                                                :next next-expr
                                                :body stmt)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 is a closed parenthesis,
                   ;; we have no update expression.
                   ((equal token4 (token-punctuator ")")) ; for ( decl expr ; )
                    (b* (((erp stmt last-span pstate) ; for ( decl expr ; ) stmt
                          (parse-statement pstate)))
                      (retok (make-stmt-fordecl :init decl
                                                :test test-expr
                                                :next nil
                                                :body stmt)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 is anything else, it is an error.
                   (t ; for ( decl expr ; other
                    (reterr-msg :where (position-to-msg (span->start span4))
                                :expected "an expression ~
                                           or a closed parenthesis"
                                :found (token-to-msg token4))))))
               ;; If token3 is a semicolon, we have no test expression.
               ((equal token3 (token-punctuator ";")) ; for ( decl ;
                (b* (((erp token4 span4 pstate) (read-token pstate)))
                  (cond
                   ;; If token4 may start an expression,
                   ;; we have an update expression.
                   ((token-expression-start-p token4) ; for ( decl ; expr...
                    (b* ((pstate (unread-token pstate)) ; for ( decl ;
                         ((erp next-expr & pstate) ; for ( decl ; expr
                          (parse-expression pstate))
                         ((erp & pstate) ; for ( decl ; expr )
                          (read-punctuator ")" pstate))
                         ((erp stmt last-span pstate) ; for ( decl ; expr ) stmt
                          (parse-statement pstate)))
                      (retok (make-stmt-fordecl :init decl
                                                :test nil
                                                :next next-expr
                                                :body stmt)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 is a closed parenthesis,
                   ;; we have no update expression.
                   ((equal token4 (token-punctuator ")")) ; for ( decl ; )
                    (b* (((erp stmt last-span pstate) ; for ( decl ; ) stmt
                          (parse-statement pstate)))
                      (retok (make-stmt-fordecl :init decl
                                                :test nil
                                                :next nil
                                                :body stmt)
                             (span-join span last-span)
                             pstate)))
                   ;; If token4 is anything else, it is an error.
                   (t ; for ( decl ; other
                    (reterr-msg :where (position-to-msg (span->start span4))
                                :expected "an expression ~
                                           or a closed parenthesis"
                                :found (token-to-msg token4))))))
               ;; If token3 is anything else, it is an error.
               (t ; for ( decl other
                (reterr-msg :where (position-to-msg (span->start span3))
                            :expected "an expression ~
                                       or a semicolon"
                            :found (token-to-msg token3)))))))))
       ;; If token may start an expression,
       ;; we must have an expression statement.
       ((token-expression-start-p token) ; expr...
        (b* ((pstate (unread-token pstate)) ;
             ((erp expr span pstate) (parse-expression pstate)) ; expr
             ((erp last-span pstate) (read-punctuator ";" pstate))) ; expr ;
          (retok (stmt-expr expr)
                 (span-join span last-span)
                 pstate)))
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
    :measure (two-nats-measure (parsize pstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-block-item ((pstate parstatep))
    :returns (mv erp (item block-itemp) (span spanp) (new-pstate parstatep))
    :parents (parser parse-stmts/blocks)
    :short "Parse a block item."
    :long
    (xdoc::topstring
     (xdoc::p
      "There is a syntactic overlap between statements and declarations,
       which are the two kinds of block items;
       the overlap cannot be disambiguated purely syntactically.
       For now we use an approximate strategy:
       if the first token may start a declaration specifier,
       except for an identifier,
       we commit to attempting to parse a declaration;
       otherwise, we attempt to parse a statement.
       We will refine this approach soon."))
    (b* (((reterr) (irr-block-item) (irr-span) (irr-parstate))
         ((erp token & pstate) (read-token pstate)))
      (cond
       ;; If token is an identifier,
       ;; we may have a declaration or an expression statement,
       ;; so we read more tokens.
       ((and token (token-case token :ident)) ; ident
        (b* (((erp token2 & pstate) (read-token pstate)))
          (cond
           ;; If token2 may start a declaration specifier,
           ;; we cannot have an expression (statement).
           ;; Note that identifiers are
           ;; possible starts of declaration specifiers,
           ;; so this check also covers the case of
           ;; a second identifier following the first identifier,
           ;; where the second identifier cannot be a declaration specifier
           ;; (because, as noted in PARSE-DECLARATION-SPECIFIERS,
           ;; there may be at most one type specifier
           ;; in a list of declaration specifiers),
           ;; and thus the second identifier must be
           ;; (the start of) a declarator.
           ((token-declaration-specifier-start-p token2) ; ident declspec...
            (b* ((pstate (unread-token pstate)) ; ident
                 (pstate (unread-token pstate)) ;
                 ((erp decl span pstate) (parse-declaration pstate))) ; decl
              (retok (block-item-decl decl) span pstate)))
           ;; If token2 is an open parenthesis,
           ;; things are still ambiguous,
           ;; because we could have a function call
           ;; or a declaration with a parenthesized declarator.
           ;; For now we commit to a function call,
           ;; which should be much more common,
           ;; but we should revisit this code and handle things properly.
           ;; Note that some situations may be inherently ambiguous,
           ;; which we plan to capture as such,
           ;; deferring the disambiguation to post-parsing semantic analysis.
           ((equal token2 (token-punctuator "(")) ; ident (
            (b* ((pstate (unread-token pstate)) ; ident
                 (pstate (unread-token pstate)) ;
                 ((erp stmt span pstate) (parse-statement pstate))) ; stmt
              (retok (block-item-stmt stmt) span pstate)))
           ;; If token2 is a star,
           ;; things are still ambiguous,
           ;; because we may have a declaration
           ;; with a starred declarator,
           ;; or a multiplication expression.
           ;; The latter situation seems much less common,
           ;; so for now we commit to a declaration,
           ;; but we should revisit this code for more complete treatment.
           ((equal token2 (token-punctuator "*")) ; ident *
            (b* ((pstate (unread-token pstate)) ; ident
                 (pstate (unread-token pstate)) ;
                 ((erp decl span pstate) (parse-declaration pstate))) ; decl
              (retok (block-item-decl decl) span pstate)))
           ;; In all other cases,
           ;; we commit to an expression statement.
           (t ; ident other
            (b* ((pstate (if token2 (unread-token pstate) pstate)) ; ident
                 (pstate (unread-token pstate)) ;
                 ((erp stmt span pstate) (parse-statement pstate))) ; stmt
              (retok (block-item-stmt stmt) span pstate))))))
       ;; If token may start a declaration specifier,
       ;; since we have already considered the case of an identifier above,
       ;; we must have a declaration.
       ((token-declaration-specifier-start-p token) ; declspec...
        (b* ((pstate (unread-token pstate)) ;
             ((erp decl span pstate) ; decl
              (parse-declaration pstate)))
          (retok (block-item-decl decl) span pstate)))
       ;; Otherwise, we must have a statement.
       (t ; other
        (b* ((pstate (if token (unread-token pstate) pstate)) ;
             ((erp stmt span pstate) ; stmt
              (parse-statement pstate)))
          (retok (block-item-stmt stmt) span pstate)))))
    :measure (two-nats-measure (parsize pstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-block-item-list ((pstate parstatep))
    :returns (mv erp
                 (items block-item-listp)
                 (span spanp)
                 (new-pstate parstatep))
    :parents (parser parse-stmts/blocks)
    :short "Parse a list of one or more block items."
    :long
    (xdoc::topstring
     (xdoc::p
      "We parse the first block item, which must be present.
       Then, unless we have a closed curly brace,
       we recursively parse one or more block items."))
    (b* (((reterr) nil (irr-span) (irr-parstate))
         (psize (parsize pstate))
         ((erp item span pstate) (parse-block-item pstate)) ; item
         ((unless (mbt (<= (parsize pstate) (1- psize))))
          (reterr :impossible))
         ((erp token & pstate) (read-token pstate)))
      (cond
       ;; If token is a closed curly brace, we have reached the end of the list.
       ((equal token (token-punctuator "}")) ; item }
        (b* ((pstate (unread-token pstate))) ; item
          (retok (list item) span pstate)))
       ;; Otherwise, we recursively parse more block items,
       ;; and we combine them with the one just parsed.
       (t ; item other
        (b* ((pstate (if token (unread-token pstate) pstate)) ; item
             ((erp items last-span pstate) ; item items
              (parse-block-item-list pstate)))
          (retok (cons item items)
                 (span-join span last-span)
                 pstate)))))
    :measure (two-nats-measure (parsize pstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable nfix fix)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual parsize-of-parse-stmts/blocks-uncond
    (defret parsize-of-parse-statement-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-statement)
    (defret parsize-of-parse-block-item-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-block-item)
    (defret parsize-of-parse-block-item-list-uncond
      (<= (parsize new-pstate)
          (parsize pstate))
      :rule-classes :linear
      :fn parse-block-item-list)
    :hints (("Goal" :expand ((parse-statement pstate)
                             (parse-block-item pstate)
                             (parse-block-item-list pstate)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual parsize-of-parse-stmts/blocks-cond
    (defret parsize-of-parse-statement-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-statement)
    (defret parsize-of-parse-block-item-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-block-item)
    (defret parsize-of-parse-block-item-list-cond
      (implies (not erp)
               (<= (parsize new-pstate)
                   (1- (parsize pstate))))
      :rule-classes :linear
      :fn parse-block-item-list)
    :hints (("Goal"
             :in-theory (enable fix)
             :expand ((parse-statement pstate)
                      (parse-block-item pstate)
                      (parse-block-item-list pstate)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards parse-statement))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-external-declaration ((pstate parstatep))
  :returns (mv erp (extdecl extdeclp) (span spanp) (new-pstate parstatep))
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
     we can decide whether we have a declarator or a function definition")
   (xdoc::p
    "This may need a more refined treatment,
     given that there are certain syntactic ambiguities
     related to declaration specifiers and declarators.
     We will do that soon,
     in the broader context of other parts of the parser."))
  (b* (((reterr) (irr-extdecl) (irr-span) (irr-parstate))
       ((erp token span pstate) (read-token pstate)))
    (cond
     ;; If token is the keyword _Static_assert,
     ;; we have a static assertion declaration.
     ((equal token (token-keyword "_Static_assert")) ; _Static_assert
      (b* (((erp statassert span pstate) ; statassert
            (parse-static-assert-declaration span pstate)))
        (retok (extdecl-decl (decl-statassert statassert)) span pstate)))
     ;; Otherwise, we must have a list of one or more declaration specifiers.
     (t
      (b* ((pstate (if token (unread-token pstate) pstate))
           ((erp declspecs span pstate) ; declspecs
            (parse-declaration-specifiers nil pstate))
           ((erp token2 span2 pstate) (read-token pstate)))
        (cond
         ;; If token2 is a semicolon,
         ;; we must have a declaration without initialization declarators.
         ((equal token2 (token-punctuator ";")) ; declspecs ;
          (retok (extdecl-decl (make-decl-decl :specs declspecs
                                               :init nil))
                 (span-join span span2)
                 pstate))
         ;; If token2 is not a semicolon,
         ;; we must have at least one declarator, which we parse.
         (t ; declspecs other
          (b* ((pstate (if token2 (unread-token pstate) pstate))
               ((erp declor & pstate) ; declspecs declor
                (parse-declarator pstate))
               ((erp token3 span3 pstate) (read-token pstate)))
            (cond
             ;; If token3 is an equal sign,
             ;; we must be parsing an intialization declarator,
             ;; and therefore the external declaration must be a declarator.
             ;; We parse the rest of the initialization declarator,
             ;; then possibly more initialization declarators.
             ((equal token3 (token-punctuator "=")) ; declspecs declor =
              (b* (((erp initer & pstate) ; declspecs declor = initer
                    (parse-initializer pstate))
                   ((erp token4 span4 pstate) (read-token pstate)))
                (cond
                 ;; If token4 is a semicolon,
                 ;; we have reached the end of the declarator.
                 ((equal token4
                         (token-punctuator ";")) ; declspecs declor = initer ;
                  (retok (extdecl-decl
                          (make-decl-decl
                           :specs declspecs
                           :init (list (make-initdeclor
                                        :declor declor
                                        :init? initer))))
                         (span-join span span4)
                         pstate))
                 ;; If token4 is a comma,
                 ;; we must have more initialization declarators.
                 ((equal token4
                         (token-punctuator ",")) ; declspecs declor = initer ,
                  (b* (((erp initdeclors & pstate)
                        ;; declspecs declor = initer , initdeclors
                        (parse-init-declarator-list pstate))
                       ((erp last-span pstate)
                        ;; declspecs declor = initer , initdeclors ;
                        (read-punctuator ";" pstate)))
                    (retok (extdecl-decl
                            (make-decl-decl
                             :specs declspecs
                             :init (cons (make-initdeclor
                                          :declor declor
                                          :init? initer)
                                         initdeclors)))
                           (span-join span last-span)
                           pstate)))
                 ;; If token4 is anything else, it is an error.
                 (t ; declspecs declor = initer other
                  (reterr-msg :where (position-to-msg (span->start span4))
                              :expected "a semicolon or a comma"
                              :found (token-to-msg token4))))))
             ;; If token3 is a semicolon,
             ;; we must be parsing an intialization declarator,
             ;; without initializer,
             ;; and the external declaration must be a declaration,
             ;; which the semicolon concludes.
             ((equal token3 (token-punctuator ";")) ; declspecs declor ;
              (retok (extdecl-decl
                      (make-decl-decl
                       :specs declspecs
                       :init (list (make-initdeclor
                                    :declor declor
                                    :init? nil))))
                     (span-join span span3)
                     pstate))
             ;; If token3 is a comma,
             ;; we must be parsing
             ;; an external declaration that is a declaration.
             ;; There must be more initialization declarations,
             ;; which we parse.
             ((equal token3 (token-punctuator ",")) ; declspecs declor ,
              (b* (((erp initdeclors & pstate) ; declspecs declor , initdeclors
                    (parse-init-declarator-list pstate))
                   ((erp last-span pstate) ; declspecs declor , initdeclors ;
                    (read-punctuator ";" pstate)))
                (retok (extdecl-decl
                        (make-decl-decl
                         :specs declspecs
                         :init (cons (make-initdeclor
                                      :declor declor
                                      :init? nil)
                                     initdeclors)))
                       (span-join span last-span)
                       pstate)))
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
             ((equal token3 (token-punctuator "{")) ; declspecs declor {
              (b* ((pstate (unread-token pstate)) ; declspecs declor
                   ((erp stmt last-span pstate) ; declspecs declor stmt
                    (parse-statement pstate)))
                (retok (extdecl-fundef
                        (make-fundef :spec declspecs
                                     :declor declor
                                     :decls nil
                                     :body stmt))
                       (span-join span last-span)
                       pstate)))
             ;; If token is not an open curly brace,
             ;; we must have one or more declarations, which we parse.
             ;; Then we parse the compound statement.
             (t ; declspecs declor other
              (b* ((pstate ; declspecs declor
                    (if token3 (unread-token pstate) pstate))
                   ((erp decls & pstate) ; declspecs declor decls
                    (parse-declaration-list pstate))
                   ((erp token4 span4 pstate) (read-token pstate))
                   ((unless (equal token4 (token-punctuator "{")))
                    (reterr-msg :where (position-to-msg (span->start span4))
                                :expected "an open curly brace"
                                :found (token-to-msg token4)))
                   ;; declspecs declor decls {
                   (pstate (unread-token pstate)) ; declspecs declor decls
                   ((erp stmt last-span pstate) ; declspecs declor decls stmt
                    (parse-statement pstate)))
                (retok (extdecl-fundef
                        (make-fundef :spec declspecs
                                     :declor declor
                                     :decls decls
                                     :body stmt))
                       (span-join span last-span)
                       pstate)))))))))))

  ///

  (defret parsize-of-parse-external-declaration-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-parse-external-declaration-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-external-declaration-list ((pstate parstatep))
  :returns (mv erp
               (extdecls extdecl-listp)
               (span spanp)
               (eof-pos positionp)
               (new-pstate parstatep))
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
  (b* (((reterr) nil (irr-span) (irr-position) (irr-parstate))
       ((erp extdecl first-span pstate) ; extdecl
        (parse-external-declaration pstate))
       ((erp token span pstate) (read-token pstate))
       ((when (not token)) ; extdecl EOF
        (retok (list extdecl) first-span (span->start span) pstate))
       ;; extdecl other
       (pstate (unread-token pstate)) ; extdecl
       ((erp extdecls last-span eof-pos pstate) ; extdecl extdecls
        (parse-external-declaration-list pstate)))
    (retok (cons extdecl extdecls)
           (span-join first-span last-span)
           eof-pos
           pstate))
  :measure (parsize pstate)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-external-declaration-list-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-parse-external-declaration-list-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-translation-unit ((pstate parstatep))
  :returns (mv erp (tunit transunitp) (new-pstate parstatep))
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
  (b* (((reterr) (irr-transunit) (irr-parstate))
       ((erp extdecls & eof-pos pstate)
        (parse-external-declaration-list pstate))
       ((unless (= (position->column eof-pos) 0))
        (reterr (msg "The file does not end in new-line."))))
    (retok (transunit extdecls) pstate))

  ///

  (defret parsize-of-parse-translation-unit-uncond
    (<= (parsize new-pstate)
        (parsize pstate))
    :rule-classes :linear)

  (defret parsize-of-parse-translation-unit-cond
    (implies (not erp)
             (<= (parsize new-pstate)
                 (1- (parsize pstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-file ((path filepathp) (data byte-listp))
  :returns (mv erp (tunit transunitp))
  :short "Parse (the data bytes of) a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "If successful, the result is a translation unit.
     We initialize the parser state with the data bytes,
     and we attempt to parse them as a translation unit.
     The final parser state is discarded, since it is no longer needed.")
   (xdoc::p
    "If an error occurs, we enhance it with
     information about the file path.
     It is the case that @('erp') is a message,
     but currently we do not have that information statically available,
     so we add a run-time check that should always succeed."))
  (b* (((reterr) (irr-transunit))
       (parstate (init-parstate data))
       ((mv erp tunit &) (parse-translation-unit parstate))
       ((when erp)
        (b* (((unless (msgp erp))
              (raise "Internal error: ~x0 is not a message." erp)
              (reterr t)))
          (reterr (msg "Error in file ~x0: ~@1" (filepath->unwrap path) erp)))))
    (retok tunit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-fileset ((fileset filesetp))
  :returns (mv erp (tunits transunit-ensemblep))
  :short "Parse a file set."
  :long
  (xdoc::topstring
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
       ((erp tunitmap) (parse-fileset-loop filemap)))
    (retok (transunit-ensemble tunitmap)))

  :prepwork
  ((define parse-fileset-loop ((filemap filepath-filedata-mapp))
     :returns (mv erp (tunitmap filepath-transunit-mapp))
     (b* (((reterr) nil)
          ((when (omap::emptyp filemap)) (retok nil))
          ((mv filepath filedata) (omap::head filemap))
          ((erp tunit) (parse-file filepath (filedata->unwrap filedata)))
          ((erp tunitmap) (parse-fileset-loop (omap::tail filemap))))
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
