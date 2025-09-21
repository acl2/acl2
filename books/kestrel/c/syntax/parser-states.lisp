; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-trees")

(include-book "kestrel/fty/byte-list" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (:e tau-system))))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser-states
  :parents (parser)
  :short "States of the parser."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define types, and related operations,
     for the possible states of our C parser."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum token
  :short "Fixtype of tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>token</i> in the grammar in [C17:A.1.1] [C17:6.4].")
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
  :pred token-listp)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod position
  :short "Fixtype of positions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A position within a file is normally specified by
     a combination of a line number and column number.
     We number lines from 1,
     which is consistent with [C17:6.10.4/2]:
     since the characters in the first line
     have 0 preceding new-line characters,
     the number of the first line is 1 plus 0, i.e. 1.
     We number columns from 0,
     but we could change that to 1.
     Numbering lines from 1 and columns from 0
     is also consistent with Emacs."))
  ((line pos)
   (column nat))
  :pred positionp)

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
  :pred char+position-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist char+position-list
  :short "Fixtype of lists of
          pairs each consisting of a character and a position."
  :elt-type char+position
  :true-listp t
  :elementp-of-nil nil
  :pred char+position-listp
  :prepwork ((local (in-theory (enable nfix))))

  ///

  (defruled char+position-listp-of-resize-list
    (implies (and (char+position-listp chars)
                  (char+position-p default))
             (char+position-listp (resize-list chars length default)))
    :induct t
    :enable (resize-list))

  (defruled char+position-listp-of-update-nth-strong
    (implies (char+position-listp chars)
             (equal (char+position-listp (update-nth i char chars))
                    (and (char+position-p char)
                         (<= (nfix i) (len chars)))))
    :induct t
    :enable (update-nth nfix zp len)))

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
  :prepwork ((local (in-theory (enable nfix))))

  ///

  (defruled token+span-listp-of-resize-list
    (implies (and (token+span-listp tokens)
                  (token+span-p default))
             (token+span-listp (resize-list tokens length default)))
    :induct t
    :enable (resize-list))

  (defruled token+span-listp-of-update-nth-strong
    (implies (token+span-listp tokens)
             (equal (token+span-listp (update-nth i token tokens))
                    (and (token+span-p token)
                         (<= (nfix i) (len tokens)))))
    :induct t
    :enable (update-nth nfix zp len)))

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
     and in fact it was defined like that in previous versions of the parser.")
   (xdoc::p
    "The first component of the parser state is
     the input sequence @('bytes') of bytes remaining,
     which initially comes from a file (see @(see files)).
     Bytes are read and removed from this component,
     and turned into characters.")
   (xdoc::p
    "Given the need for look-ahead during lexing,
     we use the common technique of ``unreading'' characters sometimes,
     i.e. putting them back into the parser state.
     But since we have already turned bytes into characters,
     we do not want to put back the bytes:
     thus, we keep, as part of the parser state
     (the exact representation is explained later),
     a sequence of unread characters,
     i.e. characters that have been read and then put back (i.e. unread),
     in character form;
     the form is natural numbers, i.e. Unicode code points.
     The sequence is initially empty.
     When non-empty, it can be thought of
     as preceding the @('bytes') byte list.
     If the sequence of unread characters is not empty,
     the next character will be read directly from that list,
     not from the byte list.")
   (xdoc::p
    "To avoid putting back the wrong character by mistake,
     i.e. a character that was not actually read,
     the parser state also includes a sequence of
     all the characters read so far and that have not been unread
     (the exact representation is explained later),
     to keep track of which characters have been read and could be unread.
     Thus, every time we read a character,
     we add it to the sequence of read characters,
     which can be visualized to the left of
     the sequence of unread characters and the @('bytes') list:")
   (xdoc::codeblock
    "+----------+    read    +--------+-------+"
    "| chars    |   <-----   | chars  | bytes |"
    "| read     |   ----->   | unread |       |"
    "+----------+   unread   +--------+-------+")
   (xdoc::p
    "The reading of a character moves the character from right to left,
     from the sequence of unread characters
     to the sequence of read characters
     if the sequence of unread characters is not empty,
     or from the @('bytes') list to the sequence of read characters
     where one or more bytes are UTF-8-decoded into the character.")
   (xdoc::p
    "When a character is unread, it is moved from left to right,
     i.e. from the sequence of read characters
     to the sequence of unread characters.
     If the sequence of read characters is empty, it is an internal error:
     if the parser code is correct, this must never happen.")
   (xdoc::p
    "The reading and unreading of characters happens at the lexing level.
     A similar look-ahead happens at the proper parsing level,
     where the elements of the read and unread sequences
     are not characters but tokens.
     The parser state includes
     a sequence of read tokens and a sequence of unread tokens
     (the exact representation is explained later),
     whose handling is similar to the ones for characters.
     The sequence can be visualized as follows,
     similarly to characters:")
   (xdoc::codeblock
    "+----------+    read    +--------+"
    "| tokens   |   <-----   | tokens |"
    "| read     |   ----->   | unread |"
    "+----------+   unread   +--------+")
   (xdoc::p
    "When characters are read to form a token,
     the token is added to the sequence of read tokens.
     If the token is unread (i.e. put back),
     it is moved right to the sequence of unread tokens.
     When a token is read, if the sequence of unread tokens is not empty,
     the token is moved from right to left;
     if instead the sequence of unread tokens is empty,
     the token is read by reading characters and forming the token.")
   (xdoc::p
    "At the end of the parsing,
     the sequence of read characters contains all the characters read,
     and the sequence of read tokens contains all the tokens read.
     That is, the sequences are never cleared.
     For tokens, this lets us do some backtracking when needed,
     but without saving and copying the whole parser state:
     we just need to keep track of how many tokens must be put back
     for backtracking.
     For characters, in principle we could clear
     the sequence of read characters once a token is formed,
     but due to the representation of the sequence in the stobj,
     it is more time-efficient to never clear the sequence,
     at the cost of some space inefficiency,
     but we believe the latter not to be significant.")
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
     we store their positions in the sequences of read and unread characters;
     so those sequences contain not just characters,
     but @(tsee char+position) pairs.
     Similarly, for tokens, we also store their spans in the sequences.")
   (xdoc::p
    "The sequences of read and unread characters
     are represented by three stobj components.
     The @('chars') component consists of
     the concatenation of the two sequences,
     read characters then unread characters
     (as shown in the diagrams above),
     with additional elements to the right to extend the sequences.
     The @('chars-read') component is the numbers of characters read,
     which are in the positions 0 (inclusive) to @('chars-read') (exclusive).
     When @('chars-read') is 0, there are no read characters,
     which happens at the beginning.
     The @('chars-unread') component is the number of characters unread,
     which are in the positions @('chars-read') (inclusive)
     to @('chars-read + chars-unread') (exclusive).
     When @('chars-unread') is 0, there are no unread characters,
     which happens at the beginning,
     and every time all the unread characters are read again.
     This organization lets us move characters between the two sequences
     just by changing @('char-read') and @('char-unread'),
     but leaving all the characters stored in the stobj array.
     The position from @('chars-read + chars-unread') (inclusive)
     to the end of the array are not part of the sequences,
     but they are used when extending the sequence of read characters
     when there are no more unread characters:
     in this situation, @('chars-unread') is 0,
     and the next character read from the bytes
     is stored into position @('chars-read'),
     which is the same as @('chars-read + chars-unread')
     since @('chars-unread') is 0.")
   (xdoc::p
    "The sequence of read and unread tokens
     are represented similarly to read and unread characters,
     via the three stobj components
     @('tokens'), @('tokens-read'), and @('tokens-unread').")
   (xdoc::p
    "We include a boolean flag saying whether
     certain GCC extensions should be accepted or not.
     These GCC extensions are limited to the ones
     currently captured in our grammar and abstract syntax.
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
    "The definition of the stobj itself is straightforward,
     but we use a @(tsee make-event) so we can use
     richer terms for initial values.
     The initial @('chars') and @('tokens') arrays have length 1,
     which seems convenient for some fixing theorems,
     but it is irrelevant because it is resized
     at the very beginning of parsing.")
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
     which we define in terms of the generated ones
     (actually, a few readers and writers do not fix their inputs yet,
     because we need to tweak the definition of the fixer for that,
     which we plan to do soon).
     The generated ones are enabled,
     but we do not bother disabling them,
     because we are not going to use them anywhere anyhow.
     We also prove some theorems about how readers and writers interact,
     as needed.")
   (xdoc::p
    "We locally enable @(tsee length) in order for
     the proofs generated by @(tsee defstobj) to go through.
     This is also useful for proofs about our readers and writers;
     for those, we also locally enable the fixer,
     and we prove some local theorems that are used there.")
   (xdoc::p
    "By making the parser state a stobj instead of a @(tsee fty::defprod),
     we cannot use the @(':require') feature of @(tsee fty::defprod)
     to enforce invariants, such as the fact that
     the @('size') component is derived from others.
     But we can probably use @(tsee defabsstobj) for that,
     which may be also overall a better way to
     ``turn'' a stobj into a @(tsee fty::defprod)-like fixtype;
     we will look into that in the future."))

  ;; needed for DEFSTOBJ and reader/writer proofs:

  (local (in-theory (enable length)))

  ;; stobj definition:

  (make-event
   `(defstobj parstate
      (bytes :type (satisfies byte-listp)
             :initially nil)
      (position :type (satisfies positionp)
                :initially ,(irr-position))
      (chars :type (array (satisfies char+position-p) (1))
             :initially ,(make-char+position :char 0
                                             :position (irr-position))
             :resizable t)
      (chars-read :type (integer 0 *)
                  :initially 0)
      (chars-unread :type (integer 0 *)
                    :initially 0)
      (tokens :type (array (satisfies token+span-p) (1))
              :initially ,(make-token+span :token (irr-token)
                                           :span (irr-span))
              :resizable t)
      (tokens-read :type (integer 0 *)
                   :initially 0)
      (tokens-unread :type (integer 0 *)
                     :initially 0)
      (gcc :type (satisfies booleanp)
           :initially nil)
      (size :type (integer 0 *)
            :initially 0)
      :renaming (;; field recognizers:
                 (bytesp raw-parstate->bytes-p)
                 (positionp raw-parstate->position-p)
                 (charsp raw-parstate->chars-p)
                 (chars-readp raw-parstate->chars-read-p)
                 (chars-unreadp raw-parstate->chars-unread-p)
                 (tokensp raw-parstate->tokens-p)
                 (tokens-readp raw-parstate->tokens-read-p)
                 (tokens-unreadp raw-parstate->tokens-unread-p)
                 (gccp raw-parstate->gcc-p)
                 (sizep raw-parstate->size-p)
                 ;; field readers:
                 (bytes raw-parstate->bytes)
                 (position raw-parstate->position)
                 (chars-length raw-parstate->chars-length)
                 (charsi raw-parstate->char)
                 (chars-read raw-parstate->chars-read)
                 (chars-unread raw-parstate->chars-unread)
                 (tokens-length raw-parstate->tokens-length)
                 (tokensi raw-parstate->token)
                 (tokens-read raw-parstate->tokens-read)
                 (tokens-unread raw-parstate->tokens-unread)
                 (gcc raw-parstate->gcc)
                 (size raw-parstate->size)
                 ;; field writers:
                 (update-bytes raw-update-parstate->bytes)
                 (update-position raw-update-parstate->position)
                 (resize-chars raw-update-parstate->chars-length)
                 (update-charsi raw-update-parstate->char)
                 (update-chars-read raw-update-parstate->chars-read)
                 (update-chars-unread raw-update-parstate->chars-unread)
                 (resize-tokens raw-update-parstate->tokens-length)
                 (update-tokensi raw-update-parstate->token)
                 (update-tokens-read raw-update-parstate->tokens-read)
                 (update-tokens-unread raw-update-parstate->tokens-unread)
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

  ;; normalize recognizers:

  (defrule raw-parstate->chars-p-becomes-char+position-listp
    (equal (raw-parstate->chars-p x)
           (char+position-listp x))
    :induct t
    :enable (raw-parstate->chars-p
             char+position-listp))

  (defrule raw-parstate->tokens-p-becomes-token+span-listp
    (equal (raw-parstate->tokens-p x)
           (token+span-listp x))
    :induct t
    :enable (raw-parstate->tokens-p
             token+span-listp))

  ;; needed for reader/writer proofs:

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
                  (irr-position))
         :exec (raw-parstate->position parstate)))

  (define parstate->chars-length (parstate)
    :returns (length natp)
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->chars-length parstate)
                  1)
         :exec (raw-parstate->chars-length parstate))
    :hooks (:fix))

  (define parstate->char ((i natp) parstate)
    :guard (< i (parstate->chars-length parstate))
    :returns (char+pos char+position-p
                       :hints
                       (("Goal" :in-theory (enable parstate->chars-length))))
    (mbe :logic (if (and (parstatep parstate)
                         (< (nfix i) (parstate->chars-length parstate)))
                    (raw-parstate->char (nfix i) parstate)
                  (make-char+position :char 0
                                      :position (irr-position)))
         :exec (raw-parstate->char i parstate))
    :guard-hints (("Goal" :in-theory (enable nfix parstate->chars-length))))

  (define parstate->chars-read (parstate)
    :returns (chars-read natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->chars-read parstate)
                  0)
         :exec (raw-parstate->chars-read parstate))
    :hooks (:fix))

  (define parstate->chars-unread (parstate)
    :returns (chars-unread natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->chars-unread parstate)
                  0)
         :exec (raw-parstate->chars-unread parstate))
    :hooks (:fix))

  (define parstate->tokens-length (parstate)
    :returns (length natp)
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->tokens-length parstate)
                  1)
         :exec (raw-parstate->tokens-length parstate))
    :hooks (:fix))

  (define parstate->token ((i natp) parstate)
    :guard (< i (parstate->tokens-length parstate))
    :returns (token+span token+span-p
                         :hints
                         (("Goal" :in-theory (enable parstate->tokens-length))))
    (mbe :logic (if (and (parstatep parstate)
                         (< (nfix i) (parstate->tokens-length parstate)))
                    (raw-parstate->token (nfix i) parstate)
                  (make-token+span :token (irr-token)
                                   :span (irr-position)))
         :exec (raw-parstate->token i parstate))
    :guard-hints (("Goal" :in-theory (enable nfix parstate->tokens-length))))

  (define parstate->tokens-read (parstate)
    :returns (tokens-read natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->tokens-read parstate)
                  0)
         :exec (raw-parstate->tokens-read parstate))
    :hooks (:fix))

  (define parstate->tokens-unread (parstate)
    :returns (tokens-unread natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (parstatep parstate)
                    (raw-parstate->tokens-unread parstate)
                  0)
         :exec (raw-parstate->tokens-unread parstate))
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

  (define update-parstate->chars-length ((length natp) parstate)
    :returns (parstate parstatep
                       :hints (("Goal"
                                :in-theory (enable nfix
                                                   parstate-fix
                                                   length
                                                   char+position-listp-of-resize-list))))
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->chars-length (nfix length) parstate))
    :hooks (:fix))

  (define update-parstate->char ((i natp)
                                 (char+pos char+position-p)
                                 parstate)
    :guard (< i (parstate->chars-length parstate))
    :returns (parstate parstatep
                       :hints
                       (("Goal"
                         :in-theory
                         (enable update-nth-array
                                 parstate->chars-length
                                 char+position-listp-of-update-nth-strong))))
    (b* ((parstate (parstate-fix parstate)))
      (mbe :logic (if (< (nfix i) (parstate->chars-length parstate))
                      (raw-update-parstate->char (nfix i)
                                                 (char+position-fix char+pos)
                                                 parstate)
                    parstate)
           :exec (raw-update-parstate->char i char+pos parstate)))
    :guard-hints (("Goal" :in-theory (enable parstate->chars-length nfix))))

  (define update-parstate->chars-read ((chars-read natp) parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->chars-read (nfix chars-read) parstate))
    :hooks (:fix))

  (define update-parstate->chars-unread ((chars-unread natp) parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->chars-unread (nfix chars-unread) parstate))
    :hooks (:fix))

  (define update-parstate->tokens-length ((length natp) parstate)
    :returns (parstate parstatep
                       :hints (("Goal"
                                :in-theory (enable nfix
                                                   parstate-fix
                                                   length
                                                   token+span-listp-of-resize-list))))
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->tokens-length (nfix length) parstate))
    :hooks (:fix))

  (define update-parstate->token ((i natp)
                                  (token+span token+span-p)
                                  parstate)
    :guard (< i (parstate->tokens-length parstate))
    :returns (parstate parstatep
                       :hints
                       (("Goal"
                         :in-theory
                         (enable update-nth-array
                                 parstate->tokens-length
                                 token+span-listp-of-update-nth-strong))))
    (b* ((parstate (parstate-fix parstate)))
      (mbe :logic (if (< (nfix i) (parstate->tokens-length parstate))
                      (raw-update-parstate->token (nfix i)
                                                  (token+span-fix token+span)
                                                  parstate)
                    parstate)
           :exec (raw-update-parstate->token i token+span parstate)))
    :guard-hints (("Goal" :in-theory (enable parstate->tokens-length nfix))))

  (define update-parstate->tokens-read ((tokens-read natp) parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->tokens-read (nfix tokens-read) parstate))
    :hooks (:fix))

  (define update-parstate->tokens-unread ((tokens-unread natp) parstate)
    :returns (parstate parstatep)
    (b* ((parstate (parstate-fix parstate)))
      (raw-update-parstate->tokens-unread (nfix tokens-unread) parstate))
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

  (defrule parstate->size-of-update-parstate->bytes
    (equal (parstate->size (update-parstate->bytes bytes parstate))
           (parstate->size parstate))
    :enable (parstate->size
             update-parstate->bytes
             parstatep
             parstate-fix
             length))

  (defrule parstate->size-of-update-parstate->position
    (equal (parstate->size (update-parstate->position position parstate))
           (parstate->size parstate))
    :enable (parstate->size
             update-parstate->position
             parstatep
             parstate-fix
             length))

  (defrule parstate->size-of-update-parstate->chars-read
    (equal (parstate->size (update-parstate->chars-read chars-read parstate))
           (parstate->size parstate))
    :enable (parstate->size
             update-parstate->chars-read
             parstatep
             parstate-fix
             length))

  (defrule parstate->size-of-update-parstate->chars-unread
    (equal (parstate->size (update-parstate->chars-unread chars-unread
                                                          parstate))
           (parstate->size parstate))
    :enable (parstate->size
             update-parstate->chars-unread
             parstatep
             parstate-fix
             length))

  (defrule parstate->size-of-update-parstate->token
    (equal (parstate->size (update-parstate->token i token parstate))
           (parstate->size parstate))
    :enable (parstate->size
             update-parstate->token
             parstatep
             parstate-fix
             length
             update-nth-array
             parstate->tokens-length
             token+span-listp-of-update-nth-strong))

  (defrule parstate->size-of-update-parstate->tokens-read
    (equal (parstate->size (update-parstate->tokens-read tokens-read parstate))
           (parstate->size parstate))
    :enable (parstate->size
             update-parstate->tokens-read
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

  ;; writers over readers:

  (defrule update-parstate->chars-read-of-parstate->chars-read
    (equal (update-parstate->chars-read
            (parstate->chars-read parstate) parstate)
           (parstate-fix parstate))
    :enable (update-parstate->chars-read
             parstate->chars-read
             parstatep
             parstate-fix
             nfix
             length
             acl2::update-nth-of-nth))

  (defrule update-parstate->chars-read-of-parstate->chars-unread
    (equal (update-parstate->chars-unread
            (parstate->chars-unread parstate) parstate)
           (parstate-fix parstate))
    :enable (update-parstate->chars-unread
             parstate->chars-unread
             parstatep
             parstate-fix
             nfix
             length
             acl2::update-nth-of-nth))

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
     no read characters or tokens,
     no unread characters or tokens,
     and the initial file position.
     We also resize the arrays of characters and tokens
     to the number of data bytes,
     which is overkill but certainly sufficient
     (because we will never lex more characters or tokens than bytes);
     if this turns out to be too large,
     we will pick a different size,
     but then we may need to resize the array as needed
     while lexing and parsing."))
  (b* ((parstate (update-parstate->bytes data parstate))
       (parstate (update-parstate->position (position-init) parstate))
       (parstate (update-parstate->chars-length (len data) parstate))
       (parstate (update-parstate->chars-read 0 parstate))
       (parstate (update-parstate->chars-unread 0 parstate))
       (parstate (update-parstate->tokens-length (len data) parstate))
       (parstate (update-parstate->tokens-read 0 parstate))
       (parstate (update-parstate->tokens-unread 0 parstate))
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

; Fixtype version of PARSTATE stobj (useful for debugging and testing).
; This is how the parser state was originally defined,
; before using a stobj and before caching the size.
(fty::defprod parstate$
  ((bytes byte-list)
   (position position)
   (chars-read char+position-list)
   (chars-unread char+position-list)
   (tokens-read token+span-list)
   (tokens-unread token+span-list)
   (gcc bool))
  :prepwork ((local (in-theory (enable nfix)))))

; Convert PARSTATE stobj to fixtype value (useful for debugging and testing).
; To construct the lists of read and unread characters,
; we need to loop through suitable ranges of the character array.
(define to-parstate$ (parstate)
  (make-parstate$
   :bytes (parstate->bytes parstate)
   :position (parstate->position parstate)
   :chars-read (to-parstate$-chars-read (parstate->chars-read parstate)
                                        parstate)
   :chars-unread (to-parstate$-chars-unread (parstate->chars-unread parstate)
                                            parstate)
   :tokens-read (to-parstate$-tokens-read (parstate->tokens-read parstate)
                                          parstate)
   :tokens-unread (to-parstate$-tokens-unread (parstate->tokens-unread parstate)
                                              parstate)
   :gcc (parstate->gcc parstate))

  :prepwork

  ((define to-parstate$-chars-read ((n natp) parstate)
     :returns (chars char+position-listp)
     (b* (((when (zp n)) nil)
          (i (1- n))
          ((unless (< i (parstate->chars-length parstate)))
           (raise "Internal error: chars-read index ~x0 out of bound ~x1."
                  i (parstate->chars-length parstate))))
       (cons (parstate->char i parstate)
             (to-parstate$-chars-read (1- n) parstate))))

   (define to-parstate$-chars-unread ((n natp) parstate)
     :returns (chars char+position-listp)
     (b* (((when (zp n)) nil)
          (i (+ (parstate->chars-read parstate)
                (- (parstate->chars-unread parstate)
                   n)))
          ((unless (>= i 0))
           (raise "Internal error: chars-unread index ~x0 is negative."
                  i))
          ((unless (< i (parstate->chars-length parstate)))
           (raise "Internal error: chars-unread index ~x0 out of bound ~x1."
                  i (parstate->chars-length parstate))))
       (cons (parstate->char i parstate)
             (to-parstate$-chars-unread (1- n) parstate)))
     :guard-hints (("Goal" :in-theory (enable natp zp))))

   (define to-parstate$-tokens-read ((n natp) parstate)
     :returns (tokens token+span-listp)
     (b* (((when (zp n)) nil)
          (i (1- n))
          ((unless (< i (parstate->tokens-length parstate)))
           (raise "Internal error: tokens-read index ~x0 out of bound ~x1."
                  i (parstate->tokens-length parstate))))
       (cons (parstate->token i parstate)
             (to-parstate$-tokens-read (1- n) parstate))))

   (define to-parstate$-tokens-unread ((n natp) parstate)
     :returns (tokens token+span-listp)
     (b* (((when (zp n)) nil)
          (i (+ (parstate->tokens-read parstate)
                (- (parstate->tokens-unread parstate)
                   n)))
          ((unless (>= i 0))
           (raise "Internal error: tokens-unread index ~x0 is negative."
                  i))
          ((unless (< i (parstate->tokens-length parstate)))
           (raise "Internal error: tokens-unread index ~x0 out of bound ~x1."
                  i (parstate->tokens-length parstate))))
       (cons (parstate->token i parstate)
             (to-parstate$-tokens-unread (1- n) parstate)))
     :guard-hints (("Goal" :in-theory (enable natp zp))))))

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
