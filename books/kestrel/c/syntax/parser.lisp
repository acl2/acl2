; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "reader")
(include-book "files")
(include-book "keywords")
(include-book "abstract-syntax-operations")

(include-book "kestrel/fty/nat-option" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/strings/char-code-theorems" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (:e tau-system))))
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

(defruledl update-nth-of-nth
  (implies (< (nfix i) (len l))
           (equal (update-nth i (nth i l) l)
                  l))
  :induct t
  :enable (nth update-nth nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser
  :parents (parsing)
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
    "Our parser uses recursive descent,
     both for lexing and for parsing proper.
     The parser is closely based on the ABNF grammar in @(see grammar),
     which should be consulted alongside the parser code.
     The function names are mostly based on the names of the grammar rules;
     we plan to make all of them based on the names of the grammar rules.
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
  :order-subtopics (parser-states
                    reader
                    t)
  :default-parent t)

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
  (:prepr-directive ())
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
    (if (or (member-equal string c::*keywords*)
            (and (parstate->gcc parstate)
                 (member-equal string *gcc-keywords*)))
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
     ((and (= char (char-code #\%)) ; \ %
           (parstate->gcc parstate))
      (retok (escape-simple (simple-escape-percent)) pos parstate))
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

(define lex-string-literal ((eprefix? eprefix-optionp)
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

  (defret parsize-of-lex-string-literal-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-string-literal-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-*-h-char ((parstate parstatep))
  :returns (mv erp
               (hchars h-char-listp)
               (closing-angle-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex zero or more characters
          in a header name between angle brackets."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, lex a @('*h-char'), in ABNF notation,
     i.e. a repetition of zero or more instances of @('h-char').")
   (xdoc::p
    "This is called when we expect a header name,
     after reading the opening angle bracker of a header name.
     If successful, this reads up to and including the closing angle bracket,
     and returns the position of the latter,
     along with the sequence of characters.")
   (xdoc::p
    "We read the next character;
     it is an error if there is none.
     It is also an error if the character is a new-line.
     If the character is a closing angle bracket,
     we end the recursion and return.
     In all other cases,
     we take the character as is,
     we read zero or more additional characters and escape sequences,
     and we combine them with the character."))
  (b* (((reterr) nil (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate))
       ((unless char)
        (reterr-msg :where (position-to-msg pos)
                    :expected "any character other than ~
                               greater-than or new-line"
                    :found (char-to-msg char)))
       ((when (= char (char-code #\>))) ; >
        (retok nil pos parstate))
       ((when (= char 10)) ; new-line
        (reterr-msg :where (position-to-msg pos)
                    :expected "any character other than ~
                               greater-than or new-line"
                    :found (char-to-msg char)))
       (hchar (h-char char))
       ((erp hchars closing-angle-pos parstate) (lex-*-h-char parstate)))
    (retok (cons hchar hchars) closing-angle-pos parstate))
  :measure (parsize parstate)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-*-h-char-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-lex-*-h-char-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (- (parsize parstate)
                        (len hchars)))))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable fix len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-*-q-char ((parstate parstatep))
  :returns (mv erp
               (qchars q-char-listp)
               (closing-dquote-pos positionp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex zero or more characters
          in a header name between double quotes."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, lex a @('*q-char'), in ABNF notation,
     i.e. a repetition of zero or more instances of @('q-char').")
   (xdoc::p
    "This is called when we expect a header name,
     after reading the opening double quote of a header name.
     If successful, this reads up to and including the closing double quote,
     and returns the position of the latter,
     along with the sequence of characters.")
   (xdoc::p
    "We read the next character;
     it is an error if there is none.
     It is also an error if the character is a new-line.
     If the character is a closing double quote,
     we end the recursion and return.
     In all other cases,
     we take the character as is,
     we read zero or more additional characters and escape sequences,
     and we combine them with the character."))
  (b* (((reterr) nil (irr-position) parstate)
       ((erp char pos parstate) (read-char parstate))
       ((unless char)
        (reterr-msg :where (position-to-msg pos)
                    :expected "any character other than ~
                               greater-than or new-line"
                    :found (char-to-msg char)))
       ((when (= char (char-code #\"))) ; "
        (retok nil pos parstate))
       ((when (= char 10)) ; new-line
        (reterr-msg :where (position-to-msg pos)
                    :expected "any character other than ~
                               greater-than or new-line"
                    :found (char-to-msg char)))
       (qchar (q-char char))
       ((erp qchars closing-dquote-pos parstate) (lex-*-q-char parstate)))
    (retok (cons qchar qchars) closing-dquote-pos parstate))
  :measure (parsize parstate)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-*-q-char-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret parsize-of-lex-*-q-char-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (- (parsize parstate)
                        (len qchars)))))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable fix len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-header-name ((parstate parstatep))
  :returns (mv erp
               (hname header-namep)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a header name."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a header name.
     We read the next character, which must be present.
     Then we read the two kinds of header names,
     based on whether the next character is greater-than or double quote.
     If it is neither, lexing fails."))
  (b* (((reterr) (irr-header-name) (irr-span) parstate)
       ((erp char first-pos parstate) (read-char parstate)))
    (cond
     ((not char)
      (reterr-msg :where (position-to-msg first-pos)
                  :expected "a greater-than ~
                             or a double quote"
                  :found (char-to-msg char)))
     ((= char (char-code #\<)) ; <
      (b* (((erp hchars closing-angle-pos parstate) (lex-*-h-char parstate))
           (span (make-span :start first-pos :end closing-angle-pos))
           ((unless hchars)
            (reterr-msg :where (position-to-msg closing-angle-pos)
                        :expected "one or more characters"
                        :found "none")))
        (retok (header-name-angles hchars)
               span
               parstate)))
     ((= char (char-code #\")) ; "
      (b* (((erp qchars closing-dquote-pos parstate) (lex-*-q-char parstate))
           (span (make-span :start first-pos :end closing-dquote-pos))
           ((unless qchars)
            (reterr-msg :where (position-to-msg closing-dquote-pos)
                        :expected "one or more characters"
                        :found "none")))
        (retok (header-name-quotes qchars)
               span
               parstate)))
     (t ; other
      (reterr-msg :where (position-to-msg first-pos)
                  :expected "a greater-than ~
                             or a double quote"
                  :found (char-to-msg char)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

  (defret parsize-of-lex-header-name-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-header-name-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-?-integer-suffix ((parstate parstatep))
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

  (defret parsize-of-lex-?-integer-suffix-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-?-integer-suffix-cond
    (implies (and (not erp)
                  isuffix?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-?-floating-suffix ((parstate parstatep))
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

  (defret parsize-of-lex-?-floating-suffix-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-?-floating-suffix-cond
    (implies (and (not erp)
                  fsuffix?)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-?-sign ((parstate parstatep))
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

  (defret parsize-of-lex-?-sign-ucond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-?-sign-cond
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
           ((erp sign? sign-pos parstate) (lex-?-sign parstate))
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
            (lex-?-sign parstate))
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
            (lex-?-sign parstate))
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
     according to their grammar rules in [C17].
     First, preprocessing tokens must be recognized,
     defined by <i>preprocessing-token</i> in [C17:6.4] [C17:A.1.1].
     These include preprocessing numbers,
     defined by <i>pp-number</i> in [C17:6.4.8] [C17:A.1.9],
     which start with a digit, optionally preceded by a dot,
     and are followed by identifier characters (including digits and letter),
     as well as plus and minus signs immediately preceded by exponent letters,
     as well as periods
     [C17:6.4.8/2].
     Thus, preprocessing numbers lexically include
     all integer and floating constants [C17:6.4.8/3],
     and much more, e.g. @('638xyyy.e+E-').")
   (xdoc::p
    "As part of translation phase 7 [C17:5.1.1.2],
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
     in that case, according to the grammar rule of <i>pp-number</i> in [C17],
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
                      (lex-?-floating-suffix parstate))
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
                   :suffix? nil
                   :info nil))
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
                    (lex-?-floating-suffix parstate))
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
                    (lex-?-floating-suffix parstate))
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
                (lex-?-floating-suffix parstate))
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
                (lex-?-integer-suffix parstate))
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
                     :suffix? isuffix?
                     :info nil))
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
               :suffix? nil
               :info nil))
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
            (lex-?-floating-suffix parstate))
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
            (lex-?-floating-suffix parstate))
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
            (lex-?-integer-suffix parstate))
           ;; 1-9 [decdigs] [suffix]
           ((erp parstate) (check-full-ppnumber nil parstate)))
        (retok (const-int
                (make-iconst
                 :core (make-dec/oct/hex-const-dec
                        :value (str::dec-digit-chars-value
                                (cons first-digit decdigs)))
                 :suffix? isuffix?
                 :info nil))
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
        (lex-?-floating-suffix parstate))
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
                 :suffix? nil
                 :info nil))
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
            (lex-?-floating-suffix parstate))
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
            (lex-?-floating-suffix parstate))
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
              (lex-?-integer-suffix parstate))
             ;; 0 [octdigs] [suffix]
             ((erp parstate) (check-full-ppnumber nil parstate)))
          (retok (const-int
                  (make-iconst
                   :core (make-dec/oct/hex-const-oct
                          :leading-zeros (1+ (oct-iconst-leading-zeros digits))
                          :value (str::oct-digit-chars-value digits))
                   :suffix? isuffix?
                   :info nil))
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
                   :suffix? nil
                   :info nil))
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

(define lex-prepr-directive ((first-pos positionp) (parstate parstatep))
  :returns (mv erp
               (lexeme lexemep)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Lex a preprocessing directive."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a preprocessing directive,
     after reading the initial @('#').")
   (xdoc::p
    "We read characters in a loop until
     either we find a new-line character (success)
     or we find end of file (failure).
     In case of success, we return
     a lexeme that currently contains no information
     (but that may change in the future),
     and a span calculated from
     the position of the @('#'), which is passed to this function,
     and the position of the closing new-line,
     which is returned by the loop function."))
  (b* (((reterr) (irr-lexeme) (irr-span) parstate)
       ((erp last-pos parstate) (lex-prepr-directive-loop first-pos parstate)))
    (retok (lexeme-prepr-directive)
           (make-span :start first-pos :end last-pos)
           parstate))

  :prepwork

  ((define lex-prepr-directive-loop ((first-pos positionp) (parstate parstatep))
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
                     :extra (msg "The preprocessing directive starting at ~@1 ~
                                  never ends."
                                 (position-to-msg first-pos))))
        ((= char 10) ; new-line
         (retok pos parstate))
        (t ; other
         (lex-prepr-directive-loop first-pos parstate))))
     :measure (parsize parstate)
     :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

     ///

     (defret parsize-of-lex-prepr-directive-loop-uncond
       (<= (parsize new-parstate)
           (parsize parstate))
       :rule-classes :linear
       :hints (("Goal" :induct t)))

     (defret parsize-of-lex-prepr-directive-loop-cond
       (implies (not erp)
                (<= (parsize new-parstate)
                    (1- (parsize parstate))))
       :rule-classes :linear
       :hints (("Goal" :induct t)))))

  ///

  (defret parsize-of-lex-prepr-directive-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-lex-prepr-directive-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define only-whitespace-backward-through-line ((parstate parstatep))
  :returns (only-whitespace booleanp)
  :short "Check that the only preceding characters on the line are whitespace."
  :long
  (xdoc::topstring
   (xdoc::p
    "We begin with the character immediately before the last read character,
     and check that every character is whitespace until we reach either
     a new-line or the start of the file.")
   (xdoc::p
    "Since @(tsee read-char) converts all recognized new-line sequences
     into a single line feed character,
     we detect new-lines by simply checking for a line feed."))
  (b* ((chars-read (parstate->chars-read parstate))
       ((when (= chars-read 1))
        t)
       ((when (or (< chars-read 1)
                  (<= (parstate->chars-length parstate) chars-read)))
        (raise "Internal error: chars-read index ~x0 out of bound ~x1."
               chars-read
               (parstate->chars-length parstate))))
    (only-whitespace-backward-through-line-loop (- chars-read 2) parstate))
  :guard-hints (("Goal" :in-theory (enable natp)))

  :prepwork

  ((define only-whitespace-backward-through-line-loop ((i natp)
                                                       (parstate parstatep))
     :parents nil
     :guard (< i (parstate->chars-length parstate))
     :returns (all-whitespace booleanp)
     (b* ((char+pos (parstate->char i parstate))
          (char (char+position->char char+pos)))
       (cond ((= char 10) ; new-line
              t)
             ((or (= char 32) ; SP
                  (and (<= 9 char) (<= char 12))) ; HT VT FF
              (if (= (mbe :logic (nfix i)
                          :exec (the unsigned-byte i))
                     0)
                  t
                (only-whitespace-backward-through-line-loop (- i 1) parstate)))
             (t nil)))
     :measure (nfix i)
     :hints (("Goal" :in-theory (enable nfix)))
     :guard-hints (("Goal" :in-theory (enable nfix))))))

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
      [C17:6.4/4]:
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
      but at that point the only possibility would be
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
      If the following character is another @('.'),
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
          (lex-string-literal (eprefix-locase-u) first-pos parstate))
         ((= char2 (char-code #\8)) ; u 8
          (b* (((erp char3 & parstate) (read-char parstate)))
            (cond
             ((not char3) ; u 8 EOF
              (retok (lexeme-token (token-ident (ident "u8")))
                     (make-span :start first-pos :end pos2)
                     parstate))
             ((= char3 (char-code #\")) ; u 8 "
              (lex-string-literal (eprefix-locase-u8) first-pos parstate))
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
          (lex-string-literal (eprefix-upcase-u) first-pos parstate))
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
          (lex-string-literal (eprefix-upcase-l) first-pos parstate))
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
      (lex-string-literal nil first-pos parstate))

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

     ((and (= char (char-code #\#))
           (only-whitespace-backward-through-line parstate))
      (lex-prepr-directive first-pos parstate))

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
                                           dec-digit-char-p
                                           natp)))

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
    "If there are unread tokens, we move a token
     from the sequence of unread tokens to the sequence of read tokens.
     We need to check that the index is in range,
     which we may be able to avoid in the future
     by adding invariants via an abstract stobj.")
   (xdoc::p
    "Otherwise, we call the lexer to get the next lexeme,
     until we find a token lexeme or the end of file.
     That is, we discard white space and comments.
     (Future extensions of this parser may instead
     return certain white space and comments under some conditions.)"))
  (b* (((reterr) nil (irr-span) parstate)
       (parstate.tokens-read (parstate->tokens-read parstate))
       (parstate.tokens-unread (parstate->tokens-unread parstate))
       (parstate.size (parstate->size parstate))
       ((when (and (> parstate.tokens-unread 0)
                   (> parstate.size 0)))
        (b* (((unless (< parstate.tokens-read
                         (parstate->tokens-length parstate)))
              (raise "Internal error: index ~x0 out of bound ~x1."
                     parstate.tokens-read
                     (parstate->tokens-length parstate))
              (reterr t))
             (token+span (parstate->token parstate.tokens-read parstate))
             (parstate (update-parstate->tokens-unread
                        (1- parstate.tokens-unread) parstate))
             (parstate (update-parstate->tokens-read
                        (1+ parstate.tokens-read) parstate))
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
          (parstate.tokens-read (parstate->tokens-read parstate))
          ((erp lexeme? span parstate) (lex-lexeme parstate))
          ((when (not lexeme?))
           (retok nil span parstate))
          ((when (lexeme-case lexeme? :token))
           (b* ((token (lexeme-token->unwrap lexeme?))
                ((unless (< parstate.tokens-read
                            (parstate->tokens-length parstate)))
                 (raise "Internal error: index ~x0 out of bound ~x1."
                        parstate.tokens-read
                        (parstate->tokens-length parstate))
                 (reterr t))
                (parstate (update-parstate->token parstate.tokens-read
                                                  (make-token+span
                                                   :token token
                                                   :span span)
                                                  parstate))
                (parstate (update-parstate->tokens-read
                           (1+ parstate.tokens-read) parstate)))
             (retok token span parstate))))
       (read-token-loop parstate))
     :measure (parsize parstate)

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
    "We move the token from the sequence of read tokens
     to the sequence of unread tokens.")
   (xdoc::p
    "It is an internal error if @('tokens-read') is 0.
     It means that the calling code is wrong.
     In this case, after raising the hard error,
     logically we still increment @('tokens-read')
     so that the theorem about @(tsee parsize) holds unconditionally."))
  (b* ((parstate.tokens-read (parstate->tokens-read parstate))
       (parstate.tokens-unread (parstate->tokens-unread parstate))
       (parstate.size (parstate->size parstate))
       ((unless (> parstate.tokens-read 0))
        (raise "Internal error: no token to unread.")
        (b* ((parstate (update-parstate->tokens-unread
                        (1+ parstate.tokens-unread) parstate))
             (parstate (update-parstate->size (1+ parstate.size) parstate)))
          parstate))
       (parstate (update-parstate->tokens-unread
                  (1+ parstate.tokens-unread) parstate))
       (parstate (update-parstate->tokens-read
                  (1- parstate.tokens-read) parstate))
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
    "We move tokens
     from the sequence of read tokens
     to the sequence of unread tokens
     by incrementing the number of unread tokens by @('n')
     and decrementing the number of read tokens by @('n').")
   (xdoc::p
    "It is an internal error if @('n') exceeds
     the number of tokens read so far.
     In this case, besides raising the error,
     we increment @('tokens-unread') so that
     the theorem on the parser state size holds unconditionally."))
  (b* ((n (nfix n))
       (tokens-read (parstate->tokens-read parstate))
       (tokens-unread (parstate->tokens-unread parstate))
       (size (parstate->size parstate))
       ((unless (<= n tokens-read))
        (raise "Internal error: ~
                attempting to unread ~x0 tokens ~
                from ~x1 read tokens."
               n tokens-read)
        (b* ((parstate
              (update-parstate->tokens-unread (+ tokens-unread n) parstate))
             (parstate
              (update-parstate->size (+ size n) parstate)))
          parstate))
       (new-tokens-read (- tokens-read n))
       (new-tokens-unread (+ tokens-unread n))
       (new-size (+ size n))
       (parstate (update-parstate->tokens-read new-tokens-read parstate))
       (parstate (update-parstate->tokens-unread new-tokens-unread parstate))
       (parstate (update-parstate->size new-size parstate)))
    parstate)
  :guard-hints (("Goal" :in-theory (enable natp)))

  ///

  (defret parsize-of-unread-tokens
    (equal (parsize new-parstate)
           (+ (parsize parstate) (nfix n)))
    :hints (("Goal" :in-theory (enable parsize nfix fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-to-token ((token-index natp) (parstate parstatep))
  :returns (new-parstate parstatep :hyp (parstatep parstate))
  :short "Unread tokens down to a specified index."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set @('tokens-read') (and adjust @('tokens-unread') accordingly)
     to the @('token-index') input,
     which must be less than or equal to the current @('tokens-read')
     (otherwise it is an internal error).
     This is used to backtrack during parsing,
     with @('token-index') being a previously saved @('tokens-read')."))
  (b* ((token-index (nfix token-index))
       (tokens-read (parstate->tokens-read parstate))
       ((unless (<= token-index tokens-read))
        (raise "Internal error: ~
                attempting to unread tokens down to index ~x0 ~
                but the currently read tokens are ~x1."
               token-index tokens-read)
        (parstate-fix parstate))
       (parstate (update-parstate->tokens-read token-index parstate))
       (tokens-diff (- tokens-read token-index))
       (parstate (update-parstate->tokens-unread
                  (+ (parstate->tokens-unread parstate) tokens-diff)
                  parstate))
       (parstate (update-parstate->size
                  (+ (parstate->size parstate) tokens-diff)
                  parstate)))
    parstate)
  :guard-hints (("Goal" :in-theory (enable natp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define reread-to-token ((token-index natp) (parstate parstatep))
  :returns (new-parstate parstatep :hyp (parstatep parstate))
  :short "Re-read tokens up to a specified index."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set @('tokens-read') (and adjust @('tokens-unread') accordingly),
     to the @('token-index') input,
     which must be greater than or equal to the current @('tokens-read')
     but not exceed @('tokens-read + tokens-unread')
     (otherwise it is an internal error).
     This is used when parsing fails after backtracking:
     we use this to quickly get back to the situation in which we were
     before backtracking;
     this of course requires us to save @('tokens-read')
     just before backtracking.
     No tokens are returned by this function,
     because we only use it after we have already parsed the tokens,
     and after backtracking."))
  (b* ((token-index (nfix token-index))
       (tokens-read (parstate->tokens-read parstate))
       (tokens-unread (parstate->tokens-unread parstate))
       ((unless (>= token-index tokens-read))
        (raise "Internal error: ~
                attempting to re-read tokens up to index ~x0 ~
                but the currently read tokens are ~x1."
               token-index tokens-read)
        (parstate-fix parstate))
       ((unless (<= token-index (+ tokens-read tokens-unread)))
        (raise "Internal error: ~
                attempting to re-read tokens up to index ~x0 ~
                but the currently available tokens (read and unread) are ~x1."
               token-index (+ tokens-read tokens-unread))
        (parstate-fix parstate))
       (parstate (update-parstate->tokens-read token-index parstate))
       (tokens-diff (- token-index tokens-read))
       (parstate (update-parstate->tokens-unread
                  (- tokens-unread tokens-diff)
                  parstate))
       ((unless (>= (parstate->size parstate) tokens-diff))
        (raise "Internal error: ~
                size ~x0 is less than decrement ~x1."
               (parstate->size parstate) tokens-diff)
        (parstate-fix parstate))
       (parstate (update-parstate->size
                  (- (parstate->size parstate) tokens-diff)
                  parstate)))
    parstate)
  :guard-hints (("Goal" :in-theory (enable natp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     or a generic selection (which starts a certain keyword),
     or a call of a GCC built-in special function,
     or another primary expression preceded by @('__extension__')."))
  (and token?
       (or (token-case token? :ident)
           (token-case token? :const)
           (token-case token? :string)
           (token-punctuatorp token? "(")
           (token-keywordp token? "_Generic")
           (token-keywordp token? "__builtin_offsetof")
           (token-keywordp token? "__builtin_types_compatible_p")
           (token-keywordp token? "__builtin_va_arg")
           (token-keywordp token? "__extension__")))
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
      (token-keywordp token? "__thread")
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
        ((token-keywordp token "_Thread_local") (stor-spec-thread t))
        ((token-keywordp token "__thread") (stor-spec-thread nil))
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
     @('__int128'),
     @('__int128_t'),
     @('_Float32'),
     @('_Float32x'),
     @('_Float64'),
     @('_Float64x'),
     @('_Float128'),
     @('_Float128x'),
     @('__builtin_va_list'), and
     @('__auto_type')."))
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
      (token-keywordp token? "__int128_t")
      (token-keywordp token? "_Float32")
      (token-keywordp token? "_Float32x")
      (token-keywordp token? "_Float64")
      (token-keywordp token? "_Float64x")
      (token-keywordp token? "_Float128")
      (token-keywordp token? "_Float128x")
      (token-keywordp token? "__builtin_va_list")
      (token-keywordp token? "__auto_type"))
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
        ((token-keywordp token "__int128") (type-spec-int128 nil))
        ((token-keywordp token "__int128_t") (type-spec-int128 t))
        ((token-keywordp token "_Float32") (type-spec-float32))
        ((token-keywordp token "_Float32x") (type-spec-float32x))
        ((token-keywordp token "_Float64") (type-spec-float64))
        ((token-keywordp token "_Float64x") (type-spec-float64x))
        ((token-keywordp token "_Float128") (type-spec-float128))
        ((token-keywordp token "_Float128x") (type-spec-float128x))
        ((token-keywordp token "__builtin_va_list") (type-spec-builtin-va-list))
        ((token-keywordp token "__auto_type") (type-spec-auto-type))
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
     would be identifier tokens, not keyword tokens.")
   (xdoc::p
    "We do the same for the @('__volatile') and @('__volatile__')
     variants of @('volatile')."))
  (or (token-keywordp token? "const")
      (token-keywordp token? "restrict")
      (token-keywordp token? "__restrict")
      (token-keywordp token? "__restrict__")
      (token-keywordp token? "volatile")
      (token-keywordp token? "__volatile")
      (token-keywordp token? "__volatile__")
      (token-keywordp token? "_Atomic")
      (token-keywordp token? "__seg_fs")
      (token-keywordp token? "__seg_gs"))
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
        ((token-keywordp token "volatile")
         (type-qual-volatile (keyword-uscores-none)))
        ((token-keywordp token "__volatile")
         (type-qual-volatile (keyword-uscores-start)))
        ((token-keywordp token "__volatile__")
         (type-qual-volatile (keyword-uscores-both)))
        ((token-keywordp token "_Atomic") (type-qual-atomic))
        ((token-keywordp token "__seg_fs") (type-qual-seg-fs))
        ((token-keywordp token "__seg_gs") (type-qual-seg-gs))
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
      (token-keywordp token? "__attribute")
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

(define token-asm-qualifier-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token is an assembler qualifier."
  (or (token-keywordp token? "volatile")
      (token-keywordp token? "__volatile")
      (token-keywordp token? "__volatile__")
      (token-keywordp token? "inline")
      (token-keywordp token? "__inline")
      (token-keywordp token? "__inline__")
      (token-keywordp token? "goto"))
  ///

  (defrule non-nil-when-token-asm-qualifier-p
    (implies (token-asm-qualifier-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-asm-qualifier ((token tokenp))
  :guard (token-asm-qualifier-p token)
  :returns (asmqual asm-qualp)
  :short "Map a token that is an assembler qualifier
          to the corresponding assembler qualifier."
  (cond ((token-keywordp token "volatile")
         (asm-qual-volatile (keyword-uscores-none)))
        ((token-keywordp token "__volatile")
         (asm-qual-volatile (keyword-uscores-start)))
        ((token-keywordp token "__volatile__")
         (asm-qual-volatile (keyword-uscores-both)))
        ((token-keywordp token "inline")
         (asm-qual-inline (keyword-uscores-none)))
        ((token-keywordp token "__inline")
         (asm-qual-inline (keyword-uscores-start)))
        ((token-keywordp token "__inline__")
         (asm-qual-inline (keyword-uscores-both)))
        ((token-keywordp token "goto")
         (asm-qual-goto))
        (t (prog2$ (impossible) (irr-asm-qual))))
  :prepwork ((local (in-theory (enable token-asm-qualifier-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-declaration-specifier-start-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start a declaration specifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put together the five cases that define declaration specifiers,
     plus more cases for GCC attribute specifiers."))
  (or (token-storage-class-specifier-p token?)
      (token-type-specifier-start-p token?)
      (token-type-qualifier-p token?)
      (token-function-specifier-p token?)
      (token-keywordp token? "_Alignas")
      (token-keywordp token? "__attribute")
      (token-keywordp token? "__attribute__")
      (token-keywordp token? "__stdcall")
      (token-keywordp token? "__declspec"))
  ///

  (defrule non-nil-when-token-declaration-specifier-start-p
    (implies (token-declaration-specifier-start-p token?)
             token?)
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-type-qualifier-or-attribute-specifier-start-p
  ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional token may start
          a type qualifier or an attribute specifier."
  (or (token-type-qualifier-p token?)
      (token-keywordp token? "__attribute")
      (token-keywordp token? "__attribute__"))
  ///

  (defrule non-nil-when-token-type-qualifier-or-attribute-specifier-start-p
    (implies (token-type-qualifier-or-attribute-specifier-start-p token?)
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

(define token-struct-declaration-start-p ((token? token-optionp)
                                          (gcc booleanp))
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
     which must be an identifier if GCC extensions are not supported.")
   (xdoc::p
    "If GCC extensions are supported,
     which is indicated by the boolean flag passed as input,
     we also include semicolons, for empty structure declarations."))
  (or (token-specifier/qualifier-start-p token?)
      (token-keywordp token? "_Static_assert")
      (token-keywordp token? "__extension__")
      (and gcc (token-punctuatorp token? ";")))
  ///

  (defrule non-nil-when-token-strut-declaration-start-p
    (implies (token-struct-declaration-start-p token? gcc)
             token?)
    :rule-classes :forward-chaining))

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
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-*-stringlit-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
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
    (make-expr-unary :op preop :arg expr1 :info nil))
  :verify-guards :after-returns
  :hooks (:fix))

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

(define parse-*-asm-qualifier ((parstate parstatep))
  :returns (mv erp
               (quals asm-qual-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse zero or more assembler qualifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, parse a @('*asm-qualifier'), in ABNF notation.")
   (xdoc::p
    "If there are no assembler qualifiers,
     we return an irrelevant span,
     which the caller does not use."))
  (b* (((reterr) nil (irr-span) parstate)
       ((erp token span parstate) (read-token parstate))
       ((unless (token-asm-qualifier-p token))
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok nil (irr-span) parstate)))
       (qual (token-to-asm-qualifier token))
       ((erp quals last-span parstate) (parse-*-asm-qualifier parstate)))
    (retok (cons qual quals)
           (if quals (span-join span last-span) span)
           parstate))
  :measure (parsize parstate)
  :verify-guards :after-returns

  ///

  (defret parsize-of-parse-*-asm-qualifier-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-asm-clobber ((parstate parstatep))
  :returns (mv erp
               (clobber asm-clobberp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse an assembler clobber."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a sequence of one or more juxtaposed string literals."))
  (b* (((reterr) (irr-asm-clobber) (irr-span) parstate)
       ((erp string span parstate) (read-stringlit parstate)) ; string
       ((erp strings last-span parstate) ; string strings
        (parse-*-stringlit parstate)))
    (retok (asm-clobber (cons string strings))
           (if (consp strings) (span-join span last-span) span)
           parstate))

  ///

  (defret parsize-of-parse-asm-clobber-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-asm-clobber-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-asm-clobbers ((parstate parstatep))
  :returns (mv erp
               (clobbers asm-clobber-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse zero or more assembler clobbers, separated by commas."
  (b* (((reterr) nil (irr-span) parstate)
       ((erp token & parstate) (read-token parstate))
       ((unless (and token (token-case token :string))) ; string
        (b* ((parstate (if token (unread-token parstate) parstate))) ;
          (retok nil (irr-span) parstate)))
       (parstate (unread-token parstate))) ;
    (parse-asm-clobbers-loop parstate)) ; clobbers

  :prepwork

  ((define parse-asm-clobbers-loop ((parstate parstatep))
     :returns (mv erp
                  (clobbers asm-clobber-listp)
                  (span spanp)
                  (new-parstate parstatep :hyp (parstatep parstate)))
     :parents nil
     (b* (((reterr) nil (irr-span) parstate)
          ((erp clobber span parstate) ; clobber
           (parse-asm-clobber parstate))
          ((erp token & parstate) (read-token parstate))
          ((unless (token-punctuatorp token ",")) ; clobber ,
           (b* ((parstate (if token (unread-token parstate) parstate)))
             (retok (list clobber) span parstate)))
          ((erp clobbers last-span parstate) ; clobber , clobbers
           (parse-asm-clobbers-loop parstate)))
       (retok (cons clobber clobbers)
              (span-join span last-span)
              parstate))
     :measure (parsize parstate)
     :verify-guards :after-returns

     ///

     (defret parsize-of-parse-asm-clobbers-loop
       (<= (parsize new-parstate)
           (parsize parstate))
       :rule-classes :linear
       :hints (("Goal" :induct t)))))

  ///

  (defret parsize-of-parse-*-asm-clobbers-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-asm-goto-labels ((parstate parstatep))
  :returns (mv erp
               (labels ident-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse zero or more assembler goto labels."
  (b* (((reterr) nil (irr-span) parstate)
       ((erp token & parstate) (read-token parstate))
       ((unless (and token (token-case token :ident)))
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok nil (irr-span) parstate)))
       (parstate (unread-token parstate)))
    (parse-asm-goto-labels-loop parstate))

  :prepwork

  ((define parse-asm-goto-labels-loop ((parstate parstatep))
     :returns (mv erp
                  (labels ident-listp)
                  (span spanp)
                  (new-parstate parstatep :hyp (parstatep parstate)))
     :parents nil
     (b* (((reterr) nil (irr-span) parstate)
          ((erp label span parstate) (read-identifier parstate)) ; ident
          ((erp token & parstate) (read-token parstate))
          ((unless (token-punctuatorp token ",")) ; ident ,
           (b* ((parstate (if token (unread-token parstate) parstate)))
             (retok (list label) span parstate)))
          ((erp labels last-span parstate) ; ident , idents
           (parse-asm-goto-labels-loop parstate)))
       (retok (cons label labels)
              (span-join span last-span)
              parstate))
     :measure (parsize parstate)
     :verify-guards :after-returns

     ///

     (defret parsize-of-parse-asm-goto-labels-loop
       (<= (parsize new-parstate)
           (parsize parstate))
       :rule-classes :linear
       :hints (("Goal" :induct t)))))

  ///

  (defret parsize-of-parse-asm-goto-labels
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-attribute-name ((parstate parstatep))
  :returns (mv erp
               (attrname attrib-namep)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse an attribute name."
  (b* (((reterr) (irr-attrib-name) (irr-span) parstate)
       ((erp token span parstate) (read-token parstate)))
    (cond
     ((and token (token-case token :ident)) ; ident
      (retok (attrib-name-ident (token-ident->unwrap token))
             span
             parstate))
     ((and token (token-case token :keyword)) ; keyword
      (retok (attrib-name-keyword (token-keyword->unwrap token))
             span
             parstate))
     (t
      (reterr-msg :where (position-to-msg (span->start span))
                  :expected "an identifier or keyword"
                  :found (token-to-msg token)))))

  ///

  (defret parsize-of-parse-attribute-name-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-attribute-name-cond
    (implies (not erp)
             (<= (parsize new-parstate)
                 (1- (parsize parstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines parse-exprs/decls/stmts
  :short "Parse expressions, declarations, statements, and related entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "In accordance with the mutual recursion in the C grammar,
     and with the mutual recursion @(tsee exprs/decls/stmts)
     in our abstract syntax,
     the functions to parse
     expressions, declarations, statements, and related entities
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
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
                               :arg2 expr2
                               :info nil)
             (span-join span span2)
             parstate))
    :measure (two-nats-measure (parsize parstate) 15))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-conditional-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
       if there is not, it must be a logical disjunction expression.")
     (xdoc::p
      "If GCC extensions are enabled,
       we also allow the omission of the `then' sub-expression;
       see the ABNF grammar."))
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

         ((erp token2 & parstate) (read-token parstate)))
      (cond
       ;; If token2 is a colon and GCC extensions are enabled,
       ;; we have a conditional with omitted operand.
       ((and (token-punctuatorp token2 ":") ; expr ? :
             (parstate->gcc parstate))
        (b* (((erp expr3 span3 parstate) ; expr ? : expr3
              (parse-conditional-expression parstate)))
          (retok (make-expr-cond :test expr :then nil :else expr3)
                 (span-join span span3)
                 parstate)))
       ;; If token2 is not a colon or GCC extensions are not enabled,
       ;; we put back token2 and parse the two remaining expressions,
       ;; separated by a colon.
       (t ; expr ? other
        (b* ((parstate (if token2 (unread-token parstate) parstate))
             (psize (parsize parstate))
             ((erp expr2 & parstate) (parse-expression parstate)) ; expr ? expr2
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp & parstate) (read-punctuator ":" parstate)) ; expr ? expr2 :
             ((erp expr3 span3 parstate) ; expr ? expr2 : expr3
              (parse-conditional-expression parstate)))
          (retok (make-expr-cond :test expr :then expr2 :else expr3)
                 (span-join span span3)
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 14))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-logical-or-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
                                      :arg2 expr
                                      :info nil))
         (curr-span (span-join prev-span expr-span)))
      (parse-logical-or-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-logical-and-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
                                      :arg2 expr
                                      :info nil))
         (curr-span (span-join prev-span expr-span)))
      (parse-logical-and-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-inclusive-or-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
                                      :arg2 expr
                                      :info nil))
         (curr-span (span-join prev-span expr-span)))
      (parse-inclusive-or-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-exclusive-or-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
                                      :arg2 expr
                                      :info nil))
         (curr-span (span-join prev-span expr-span)))
      (parse-exclusive-or-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-and-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
                                      :arg2 expr
                                      :info nil))
         (curr-span (span-join prev-span expr-span)))
      (parse-and-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-equality-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
                                      :arg2 expr
                                      :info nil))
         (curr-span (span-join prev-span expr-span)))
      (parse-equality-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-relational-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
                                      :arg2 expr
                                      :info nil))
         (curr-span (span-join prev-span expr-span)))
      (parse-relational-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-shift-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
                                      :arg2 expr
                                      :info nil))
         (curr-span (span-join prev-span expr-span)))
      (parse-shift-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-additive-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
                                      :arg2 expr
                                      :info nil))
         (curr-span (span-join prev-span expr-span)))
      (parse-additive-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-multiplicative-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
                                      :arg2 expr
                                      :info nil))
         (curr-span (span-join prev-span expr-span)))
      (parse-multiplicative-expression-rest curr-expr curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-cast-expression ((parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
       ;; If GCC extensions are supported,
       ;; we also need to check whether there is an open curly brace,
       ;; in which case we have a statement expressions.
       ;; In the latter case,
       ;; the cast expression is in fact a postfix expression,
       ;; and so we must parse the rest of it, if any.
       ((token-punctuatorp token "(") ; (
        (b* (;; We read the next token to see if it is an open curly brace,
             ;; but we also need to check that GCC extensions are supported.
             ((erp token2 & parstate) (read-token parstate))
             ((when (and (token-punctuatorp token2 "{") ; ( {
                         (parstate->gcc parstate)))
              (b* (((erp token3 & parstate) (read-token parstate)))
                (cond
                 ;; If token3 is a closed curly brace,
                 ;; we have an empty block.
                 ((token-punctuatorp token3 "}") ; ( { }
                  (b* (((erp last-span parstate) ; ( { } )
                        (read-punctuator ")" parstate))
                       (prev-expr (expr-stmt nil))
                       (prev-span (span-join span last-span)))
                    (parse-postfix-expression-rest prev-expr
                                                   prev-span
                                                   parstate)))
                 ;; If token 3 is not a closed curly brace,
                 ;; we must have a non-empty block.
                 (t ; ( { other
                  (b* ((parstate ; ( {
                        (if token3 (unread-token parstate) parstate))
                       (psize (parsize parstate))
                       ((erp items & parstate) ; ( { items
                        (parse-block-item-list parstate))
                       ((unless (mbt (<= (parsize parstate) (1- psize))))
                        (reterr :impossible))
                       ((erp & parstate) ; ( { items }
                        (read-punctuator "}" parstate))
                       ((erp last-span parstate) ; ( { items } )
                        (read-punctuator ")" parstate))
                       (prev-expr (expr-stmt items))
                       (prev-span (span-join span last-span)))
                    (parse-postfix-expression-rest prev-expr
                                                   prev-span
                                                   parstate))))))
             ;; If we do not have an open curly brace,
             ;; or if GCC extensions are not supported,
             ;; we need to parse a possibly ambiguous expression or type name.
             ;; We first need to puth back token2, if not NIL.
             (parstate (if token2 (unread-token parstate) parstate)) ; (
             (checkpoint (parstate->tokens-read parstate))
             (psize (parsize parstate))
             ((erp expr/tyname & parstate) ; ( expr/tyname
              (parse-expression-or-type-name t parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible)))
          (amb?-expr/tyname-case
           expr/tyname
           ;; If we have an unambiguous type name,
           ;; we may be parsing a proper cast expression
           ;; or a compound literal.
           ;; We parse the closed parenthesis
           ;; and we read another token to disambiguate
           ;; between a cast expression and a compound literal.
           :tyname ; ( tyname
           (b* (((erp & parstate) (read-punctuator ")" parstate)) ; ( tyname )
                ((erp token2 & parstate) (read-token parstate)))
             (cond
              ;; If token2 is an open curly brace,
              ;; we must have a compound literal.
              ;; We put back the open curly brace,
              ;; and we call the function to parse compound literals.
              ;; The compound literal may be
              ;; the start of a longer postfix expression
              ;; so we also attempt to parse that.
              ((token-punctuatorp token2 "{") ; ( tyname ) {
               (b* ((parstate (unread-token parstate))
                    (psize (parsize parstate))
                    ((erp prev-expr prev-span parstate)
                     (parse-compound-literal expr/tyname.unwrap span parstate))
                    ((unless (mbt (<= (parsize parstate) (1- psize))))
                     (reterr :impossible)))
                 (parse-postfix-expression-rest prev-expr prev-span parstate)))
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
           (b* ((parstate (unread-to-token checkpoint parstate)) ; (
                ((unless (<= (parsize parstate) psize))
                 (raise "Internal error: ~
                         size ~x0 after backtracking exceeds ~
                         size ~x1 before backtracking."
                        (parsize parstate) psize)
                 ;; Here we have (> (parsize parstate) psize),
                 ;; but we need to return a parser state
                 ;; no larger than the initial one,
                 ;; so we just return the initial parser state.
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
              ;; it may start a postfix expression,
              ;; in which case we are in an ambiguous situation
              ;; (see the first pattern in :DOC EXPR).
              ;; But if the ambiguous expression or type name is a type name,
              ;; and if there are no increment and decrement operators,
              ;; the open parenthesis may start a cast expression,
              ;; so we parse a cast expression to cover both cases,
              ;; if there are no increment and decrement operators.
              ((token-punctuatorp token2 "(") ; ( expr/tyname ) [ops] (
               (b* ((parstate (unread-token parstate))) ; ( expr/tyname ) [ops]
                 (cond
                  ;; If there are increment and decrement operators,
                  ;; we parse a postfix expression,
                  ;; and we have an ambiguous situation.
                  ((consp incdecops)
                   (b* (((erp expr last-span parstate)
                         ;; ( expr/tyname ) [ops] expr
                         (parse-postfix-expression parstate)))
                     (retok (make-expr-cast/call-ambig
                             :type/fun expr/tyname.unwrap
                             :inc/dec incdecops
                             :arg/rest expr)
                            (span-join span last-span)
                            parstate)))
                  ;; If there are no increment and decrement operators,
                  ;; we must parse a cast expression
                  ;; in case the ambiguous expression or type name
                  ;; is a type name.
                  (t ; ( expr/tyname )
                   (b* (((erp expr last-span parstate)
                         ;; ( expr/tyname ) expr
                         (parse-cast-expression parstate)))
                     (cond
                      ;; If the cast expression just parsed is actually postfix,
                      ;; then we have again the same ambiguity as above.
                      ((expr-postfix/primary-p expr)
                       (retok (make-expr-cast/call-ambig
                               :type/fun expr/tyname.unwrap
                               :inc/dec incdecops
                               :arg/rest expr)
                              (span-join span last-span)
                              parstate))
                      ;; If the cast expression just parsed is not postfix,
                      ;; then it must be a proper cast expression,
                      ;; because we know from above that
                      ;; the expression starts with open parenthesis.
                      ;; In this case we have resolved the ambiguity:
                      ;; the previously parsed ambiguout expression or type name
                      ;; must be a type name,
                      ;; and we have a (nested) cast expression.
                      (t
                       (retok (make-expr-cast
                               :type (amb-expr/tyname->tyname
                                      expr/tyname.unwrap)
                               :arg expr)
                              (span-join span last-span)
                              parstate))))))))
              ;; If token2 is a star, we have an ambiguity.
              ;; We parse a cast expression after the star,
              ;; which is the same kind of expected expression
              ;; whether the star is unary or binary.
              ((token-punctuatorp token2 "*") ; ( expr/tyname ) [ops] *
               (b* (;; ( expr/tyname ) [ops] * expr
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
              ((or (token-punctuatorp token2 "+") ; ( expr/tyname ) [ops] +
                   (token-punctuatorp token2 "-")) ; ( expr/tyname ) [ops] -
               (b* (;; ( expr/tyname ) [ops] +- expr
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
              ((token-punctuatorp token2 "&") ; ( expr/tyname ) [ops] &
               (b* (((erp expr last-span parstate)
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
              ((token-unary-expression-start-p
                token2) ; ( expr/tyname ) [ops] unaryexpr...
               (b* ((parstate (unread-token parstate)) ; ( expr/tyname ) [ops]
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
               (b* ((parstate (unread-to-token checkpoint parstate)) ; (
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
    :parents (parser parse-exprs/decls/stmts)
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
          (retok (make-expr-unary :op unop :arg expr :info nil)
                 (span-join span last-span)
                 parstate)))
       ;; If token is a unay operator as defined in the grammar
       ;; (our abstract syntax has a broader notion),
       ;; then we recursively parse a cast expression as operand.
       ((token-unary-operator-p token) ; unop
        (b* (((erp expr last-span parstate) ; unop expr
              (parse-cast-expression parstate))
             (unop (token-to-unary-operator token)))
          (retok (make-expr-unary :op unop :arg expr :info nil)
                 (span-join span last-span)
                 parstate)))
       ;; If token is 'sizeof', we need to read another token.
       ((token-keywordp token "sizeof") ; sizeof
        (b* (((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is an open parenthesis,
           ;; we are in a potentially ambiguous situation.
           ;; We put back the token and we attempt to parse
           ;; a unary expression or a parenthesized type name.
           ;; Note that PARSE-UNARY-EXPRESSION-OR-PARENTHESIZED-TYPE-NAME
           ;; returns the type name (whether ambiguous or not)
           ;; without parentheses,
           ;; and that the expression, if ambiguous,
           ;; is without the parentheses.
           ((token-punctuatorp token2 "(") ; sizeof expr/parentyname
            (b* ((parstate (unread-token parstate))
                 ((erp expr/tyname last-span parstate)
                  (parse-unary-expression-or-parenthesized-type-name parstate))
                 (expr
                  (amb?-expr/tyname-case
                   expr/tyname
                   :expr (make-expr-unary :op (unop-sizeof)
                                          :arg expr/tyname.unwrap
                                          :info nil)
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
                                      :arg expr
                                      :info nil)
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
    :parents (parser parse-exprs/decls/stmts)
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
       ;; or a (parenthesized) primary expresssion
       ;; or a statement expression (if GCC extensions are enabled).
       ;; We read another token to handle the case of a statement expression
       ;; separately from the other cases.
       ((token-punctuatorp token "(") ; (
        (b* (((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is an open curly brace, and GCC extensions are enabled,
           ;; we must have a statement expression, which we parse,
           ;; and then we parse the rest of the postfix expression if any.
           ((and (token-punctuatorp token2 "{") ; ( {
                 (parstate->gcc parstate))
            (b* (((erp token3 & parstate) (read-token parstate)))
              (cond
               ;; If token3 is a closed curly brace,
               ;; we must have a statement expression with an empty block,
               ;; which seems odd but not syntactically wrong.
               ((token-punctuatorp token3 "}") ; ( { }
                (b* (((erp last-span parstate) ; ( { } )
                      (read-punctuator ")" parstate))
                     (prev-expr (expr-stmt nil))
                     (prev-span (span-join span last-span)))
                  (parse-postfix-expression-rest prev-expr prev-span parstate)))
               ;; If token3 is not a closed curly brace,
               ;; we must have a statement expression with a non-empty block.
               ;; We put back token3 and we parse one or more block items.
               (t ; ( { other
                (b* ((parstate ; ( {
                      (if token3 (unread-token parstate) parstate))
                     (psize (parsize parstate))
                     ((erp items & parstate) ; ( { items
                      (parse-block-item-list parstate))
                     ((unless (mbt (<= (parsize parstate) (1- psize))))
                      (reterr :impossible))
                     ((erp & parstate) ; ( { items }
                      (read-punctuator "}" parstate))
                     ((erp last-span parstate) ; ( { items } )
                      (read-punctuator ")" parstate))
                     (prev-expr (expr-stmt items))
                     (prev-span (span-join span last-span)))
                  (parse-postfix-expression-rest prev-expr
                                                 prev-span
                                                 parstate))))))
           ;; If token2 is not an open curly brace,
           ;; or if GCC extensions are not supported,
           ;; the opening parenthesis may start
           ;; a compound literal or a (parenthesized) primary expression.
           ;; So we put back the token (if any),
           ;; and we parse a possibly ambiguous type name or expression
           ;; and we decide what to do next based on that result
           ;; (we also parse past the closed parenthesis).
           (t ; ( other
            (b* ((parstate (if token2 (unread-token parstate) parstate)) ; (
                 (psize (parsize parstate))
                 ((erp expr/tyname & parstate) ; ( expr/tyname
                  (parse-expression-or-type-name t parstate))
                 ((unless (mbt (<= (parsize parstate) (1- psize))))
                  (reterr :impossible))
                 ((erp close-paren-span parstate) ; ( expr/tyname )
                  (read-punctuator ")" parstate)))
              (amb?-expr/tyname-case
               expr/tyname
               ;; If we just parsed a parenthesized type name,
               ;; the only possibility is to have a compound literal.
               ;; We parse it, and we continue to parse
               ;; the rest of the postfix expression, if any.
               :tyname
               (b* ((psize (parsize parstate))
                    ((erp prev-expr prev-span parstate)
                     (parse-compound-literal expr/tyname.unwrap
                                             (span-join span close-paren-span)
                                             parstate))
                    ((unless (mbt (<= (parsize parstate) (1- psize))))
                     (reterr :impossible)))
                 (parse-postfix-expression-rest prev-expr prev-span parstate))
               ;; If we just parsed a parenthesized expression,
               ;; we cannot have a compound literal,
               ;; and instead we have just parsed the primary expression
               ;; that always starts a non-compound-literal postfix expression.
               ;; So we proceed to parse the rest of the postfix expression.
               ;; Note that, since we have obtained an unambiguous expression,
               ;; it has been already parenthesized,
               ;; because the ADD-PARENS-P flag is T
               ;; in the call above to PARSE-EXPRESSION-OR-TYPE-NAME.
               :expr
               (b* ((prev-expr expr/tyname.unwrap)
                    (prev-span (span-join span close-paren-span)))
                 (parse-postfix-expression-rest prev-expr prev-span parstate))
               ;; If we just parsed an ambiguous type name or expression,
               ;; we can actually disambiguate it by looking at what comes next.
               :ambig
               (b* (((erp token2 & parstate) (read-token parstate)))
                 (cond
                  ;; If token2 is an open curly brace,
                  ;; we must have a compound literal,
                  ;; and the ambiguous expression or type name
                  ;; must be a type name.
                  ;; But the compound literal
                  ;; could start a longer postfix expression,
                  ;; so we also attempt to parser that.
                  ((token-punctuatorp token2 "{") ; ( expr/tyname ) {
                   (b* ((parstate (unread-token parstate)) ; ( expr/tyname )
                        (tyname (amb-expr/tyname->tyname expr/tyname.unwrap))
                        (psize (parsize parstate))
                        ((erp prev-expr prev-span parstate)
                         (parse-compound-literal tyname
                                                 (span-join span
                                                            close-paren-span)
                                                 parstate))
                        ((unless (mbt (<= (parsize parstate) (1- psize))))
                         (reterr :impossible)))
                     (parse-postfix-expression-rest
                      prev-expr prev-span parstate)))
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
                                                    parstate)))))))))))
       ;; If token is not an open parenthesis,
       ;; we cannot have a compound literal,
       ;; and thus we parse the primary expression
       ;; that starts the postfix expression,
       ;; followed by the rest of the postfix expression if any.
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
    :parents (parser parse-exprs/decls/stmts)
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
                                         :arg prev-expr
                                         :info nil))
             (curr-span (span-join prev-span span)))
          (parse-postfix-expression-rest curr-expr curr-span parstate)))
       ((token-punctuatorp token "--") ; prev-expr --
        (b* ((curr-expr (make-expr-unary :op (unop-postdec)
                                         :arg prev-expr
                                         :info nil))
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
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse a primary expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called when we expect an expression.")
     (xdoc::p
      "We read a token.")
     (xdoc::p
      "If the token is an identifier or a constant,
       that is the whole expression.")
     (xdoc::p
      "If the token is a string literal,
       we read zero or more that may follow,
       and we have a string literal expression.
       Recall that C supports
       automatically concatenated adjacent string literals,
       and that our abstract syntax preserves the distinct string literals.")
     (xdoc::p
      "If the token is an open parenthesis,
       we read another token to see whether it is an open curly brace.
       If it is, we have a statement expression (a GCC extension);
       otherwise, we have a parenthesized expression.
       We only allow this if GCC extensions are supported.")
     (xdoc::p
      "If the token is the keyword @('_Generic'),
       we parse an open parenthesis and an assignment expression,
       then a comma and a generic association,
       since there must be at least one.
       Then we call a separate function to parse
       zero or more additional generic associations.
       Finally we parse a closed parenthesis and return a generic selection.")
     (xdoc::p
      "If the token is the GCC keyword @('__builtin_types_compatible_p'),
       we parse a call of this built-in function,
       which has two type names as arguments.")
     (xdoc::p
      "If the token is the GCC keyword @('__builtin_offsetof'),
       we parse a call of this built-in function,
       which has a type name and a member designator as arguments.")
     (xdoc::p
      "If the token is the GCC keyword @('__builtin_va_arg'),
       we parse a call of this built-in function,
       which has an expression and a type name as arguments.")
     (xdoc::p
      "If the token is the GCC keyword @('__extension__'),
       we parse the primary expression after it, recursively.")
     (xdoc::p
      "If the token is none of the above,
       including the token being absent,
       it is an error."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ((and token (token-case token :ident)) ; identifier
        (retok (make-expr-ident :ident (token-ident->unwrap token)
                                :info nil)
               span
               parstate))
       ((and token (token-case token :const)) ; constant
        (retok (expr-const (token-const->unwrap token)) span parstate))
       ((and token (token-case token :string)) ; stringlit
        (b* (((erp strings last-span parstate) ; stringlit stringlits
              (parse-*-stringlit parstate)))
          (retok (expr-string (cons (token-string->unwrap token) strings))
                 (if strings (span-join span last-span) span)
                 parstate)))
       ((token-punctuatorp token "(") ; (
        (b* (((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is an open curly brace, and GCC extensions are enabled,
           ;; we have a statement expression.
           ((and (token-punctuatorp token2 "{") ; ( {
                 (parstate->gcc parstate))
            (b* (((erp token3 & parstate) (read-token parstate)))
              (cond
               ;; If token3 is a closed curly brace,
               ;; we must have a statement expression with an empty block,
               ;; which seems odd but not syntactically wrong.
               ((token-punctuatorp token3 "}") ; ( { }
                (b* (((erp last-span parstate) ; ( { } )
                      (read-punctuator ")" parstate)))
                  (retok (expr-stmt nil)
                         (span-join span last-span)
                         parstate)))
               ;; If token3 is not a closed curly brace,
               ;; we must have a statement expression with a non-empty block.
               ;; We put back token3 and we parse one or more block items.
               (t ; ( { other
                (b* ((parstate ; ( {
                      (if token3 (unread-token parstate) parstate))
                     ((erp items & parstate) ; ( { items
                      (parse-block-item-list parstate))
                     ((erp & parstate) ; ( { items }
                      (read-punctuator "}" parstate))
                     ((erp last-span parstate) ; ( { items } )
                      (read-punctuator ")" parstate)))
                  (retok (expr-stmt items)
                         (span-join span last-span)
                         parstate))))))
           ;; If token2 is not an open curly brace,
           ;; we must have a parenthesized expression.
           ;; We put back token2 and we parse the expression.
           (t ; ( other
            (b* ((parstate (if token2 (unread-token parstate) parstate)) ; (
                 ((erp expr & parstate) ; ( expr
                  (parse-expression parstate))
                 ((erp last-span parstate) ; ( expr )
                  (read-punctuator ")" parstate)))
              (retok (expr-paren expr)
                     (span-join span last-span)
                     parstate))))))
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
       ((token-keywordp token ; __builtin_types_compatible_p
                        "__builtin_types_compatible_p")
        (b* (((erp & parstate) (read-punctuator "(" parstate))
             ;; __builtin_types_compatible_p (
             (psize (parsize parstate))
             ((erp type1 & parstate) (parse-type-name parstate))
             ;; __builtin_types_compatible_p ( type1
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp & parstate) (read-punctuator "," parstate))
             ;; __builtin_types_compatible_p ( type1 ,
             ((erp type2 & parstate) (parse-type-name parstate))
             ;; __builtin_types_compatible_p ( type1 , type2
             ((erp last-span parstate) (read-punctuator ")" parstate)))
          ;; __builtin_types_compatible_p ( type1 , type2 )
          (retok (make-expr-tycompat :type1 type1 :type2 type2)
                 (span-join span last-span)
                 parstate)))
       ((token-keywordp token "__builtin_offsetof") ; __builtin_offsetof
        (b* (((erp & parstate)
              ;; __builtin_offsetof (
              (read-punctuator "(" parstate))
             (psize (parsize parstate))
             ((erp tyname & parstate)
              ;; __builtin_offsetof ( type
              (parse-type-name parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp & parstate)
              ;; __builtin_offset ( type ,
              (read-punctuator "," parstate))
             ((erp memdes & parstate)
              ;; __builtin_offset ( type , memdes
              (parse-member-designor parstate))
             ((erp last-span parstate)
              ;; __builtin_offset ( type , memdes )
              (read-punctuator ")" parstate)))
          (retok (make-expr-offsetof :type tyname :member memdes)
                 (span-join span last-span)
                 parstate)))
       ((token-keywordp token "__builtin_va_arg") ; __builtin_va_arg
        (b* (((erp & parstate)
              ;; __builtin_va_arg (
              (read-punctuator "(" parstate))
             (psize (parsize parstate))
             ((erp list & parstate)
              ;; __builtin_va_arg ( list
              (parse-assignment-expression parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp & parstate)
              ;; __builtin_va_arg ( list ,
              (read-punctuator "," parstate))
             (psize (parsize parstate))
             ((erp type & parstate)
              ;; __builtin_va_arg ( list , type
              (parse-type-name parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp last-span parstate)
              ;; __builtin_va_arg ( list , type )
              (read-punctuator ")" parstate)))
          (retok (make-expr-va-arg :list list :type type)
                 (span-join span last-span)
                 parstate)))
       ((token-keywordp token "__extension__") ; __extension__
        (b* (((erp expr last-span parstate) ; __extension__ expr
              (parse-primary-expression parstate)))
          (retok (expr-extension expr)
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

  (define parse-compound-literal ((tyname tynamep)
                                  (first-span spanp)
                                  (parstate parstatep))
    :returns (mv erp
                 (expr exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse a compound literal."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after parsing the parenthesized type name.
       So we start by parsing an open curly brace,
       a list of initializers,
       and a closed curly brace.")
     (xdoc::p
      "If GCC extensions are enabled,
       we also allow an empty list of initializers;
       see the ABNF grammar."))
    (b* (((reterr) (irr-expr) (irr-span) parstate)
         ((erp & parstate) (read-punctuator "{" parstate)) ; {
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is a closed curly brace and GCC extensions are enabled,
       ;; we have an empty compound literal.
       ((and (token-punctuatorp token "}") ; { }
             (parstate->gcc parstate))
        (retok (make-expr-complit :type tyname
                                  :elems nil
                                  :final-comma nil)
               (span-join first-span span)
               parstate))
       ;; If token is not a closed curly brace
       ;; or GCC extensions are not enabled,
       ;; we put back token (if any),
       ;; and we parse one or more initializers,
       ;; followed by a closed curly braces.
       (t ; { other
        (b* ((parstate (if token (unread-token parstate) parstate)) ; {
             ((erp desiniters final-comma & parstate) ; { inits [,]
              (parse-initializer-list parstate))
             ((erp last-span parstate)
              (read-punctuator "}" parstate))) ; { inits [,] }
          (retok (make-expr-complit :type tyname
                                    :elems desiniters
                                    :final-comma final-comma)
                 (span-join first-span last-span)
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-generic-association ((parstate parstatep))
    :returns (mv erp
                 (genassoc genassocp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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

  (define parse-generic-associations-rest ((prev-genassocs genassoc-listp)
                                           (prev-span spanp)
                                           (parstate parstatep))
    :returns (mv erp
                 (genassocs genassoc-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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

  (define parse-member-designor ((parstate parstatep))
    :returns (mv erp
                 (memdes member-designorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse a member designator."
    :long
    (xdoc::topstring
     (xdoc::p
      "A member designator always starts with an identifier, which we parse.
       Then we parse zero or more dotted or subscript notations,
       using a separate parsing function."))
    (b* (((reterr) (irr-member-designor) (irr-span) parstate)
         ((erp ident span parstate) (read-identifier parstate))
         (curr-memdes (member-designor-ident ident))
         (curr-span span))
      (parse-member-designor-rest curr-memdes curr-span parstate))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-member-designor-rest ((prev-memdes member-designorp)
                                      (prev-span spanp)
                                      (parstate parstatep))
    :returns (mv erp
                 (memdes member-designorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse the rest of a member designator."
    (b* (((reterr) (irr-member-designor) (irr-span) parstate)
         ((erp token & parstate) (read-token parstate)))
      (cond
       ((token-punctuatorp token ".") ; .
        (b* (((erp ident span parstate) (read-identifier parstate)) ; . ident
             (curr-memdes (make-member-designor-dot
                           :member prev-memdes
                           :name ident))
             (curr-span (span-join prev-span span)))
          (parse-member-designor-rest curr-memdes curr-span parstate)))
       ((token-punctuatorp token "[") ; [
        (b* ((psize (parsize parstate))
             ((erp index & parstate) (parse-expression parstate)) ; [ expr
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp span parstate) (read-punctuator "]" parstate)) ; [ expr ]
             (curr-memdes (make-member-designor-sub
                           :member prev-memdes
                           :index index))
             (curr-span (span-join prev-span span)))
          (parse-member-designor-rest curr-memdes curr-span parstate)))
       (t ; other
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok (member-designor-fix prev-memdes)
                 (span-fix prev-span)
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-constant-expression ((parstate parstatep))
    :returns (mv erp
                 (cexpr const-exprp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse a designator."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are two kinds of designators,
       easily distinguished by their first token.")
     (xdoc::p
      "If GCC extensions are enabled, we also allow for range designators.
       See the ABNF grammar."))
    (b* (((reterr) (irr-designor) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ((token-punctuatorp token "[") ; [
        (b* ((psize (parsize parstate))
             ((erp cexpr & parstate) ; [ cexpr
              (parse-constant-expression parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp token2 next-span parstate) (read-token parstate)))
          (cond
           ((token-punctuatorp token2 "]") ; [ cexpr ]
            (retok (make-designor-sub :index cexpr :range? nil)
                   (span-join span next-span)
                   parstate))
           ((and (token-punctuatorp token2 "...") ; [ cexpr ...
                 (parstate->gcc parstate))
            (b* (((erp cexpr2 & parstate) ; [ cexpr ... cexpr
                  (parse-constant-expression parstate))
                 ((erp last-span parstate) ; [ cexpr ... cexpr ]
                  (read-punctuator "]" parstate)))
              (retok (make-designor-sub :index cexpr :range? cexpr2)
                     (span-join span last-span)
                     parstate)))
           (t ; [ cexpr other
            (reterr-msg :where (position-to-msg (span->start next-span))
                        :expected (if (parstate->gcc parstate)
                                      "an ellipsis ~
                                       or a closing square bracket"
                                    "a closing square bracket")
                        :found (token-to-msg token2))))))
       ((token-punctuatorp token ".") ; .
        (b* (((erp ident last-span parstate) ; . ident
              (read-identifier parstate)))
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
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
       There is no overlap between these two cases.")
     (xdoc::p
      "If GCC extensions are enabled,
       a closing brace could immediately follow the open one."))
    (b* (((reterr) (irr-initer) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ((token-expression-start-p token) ; expr...
        (b* ((parstate (unread-token parstate)) ;
             ((erp expr span parstate) ; expr
              (parse-assignment-expression parstate)))
          (retok (initer-single expr) span parstate)))
       ((token-punctuatorp token "{") ; {
        (b* (((erp token2 span2 parstate) (read-token parstate)))
          (cond
           ((and (token-punctuatorp token2 "}") ; { }
                 (parstate->gcc parstate))
            (retok (make-initer-list :elems nil :final-comma nil)
                   (span-join span span2)
                   parstate))
           (t ; { other
            (b* ((parstate (if token2 (unread-token parstate) parstate)) ; {
                 ((erp desiniters final-comma & parstate) ; { inits [,]
                  (parse-initializer-list parstate))
                 ((erp last-span parstate) ; { inits [,] }
                  (read-punctuator "}" parstate)))
              (retok (make-initer-list :elems desiniters :final-comma final-comma)
                     (span-join span last-span)
                     parstate))))))
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
    :parents (parser parse-exprs/decls/stmts)
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
          (retok (make-desiniter :designors designors :initer initer)
                 (span-join span last-span)
                 parstate)))
       ((token-initializer-start-p token) ; initializer...
        (b* ((parstate (unread-token parstate))
             ((erp initer span parstate) ; initializer
              (parse-initializer parstate)))
          (retok (make-desiniter :designors nil :initer initer)
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
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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

  (define parse-specifier/qualifier ((parstate parstatep))
    :returns (mv erp
                 (specqual spec/qual-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse a specifier or qualifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is one of the elements of
       @('specifier-qualifier-list') in the ABNF grammar;
       the grammar does not have a rule name for that.
       But this is like an alternation of
       a type specifier, a type qualifier, or an alignment specifier;
       if GCC extensions are enabled,
       the alternation also includes attribute specifiers.")
     (xdoc::p
      "This function is called when we expect a specifier or qualifier,
       which is the case at the start of a specifier and qualifier list
       (because the list cannot be empty),
       and when the caller @(tsee parse-specifier-qualifier-list)
       determines that there must be another specifier or qualifier.")
     (xdoc::p
      "There is an overlap in the tokens that may start two cases:
       the @('_Atomic') keyword could start a type specifier,
       in which case it must be followed by a parenthesized type name,
       or it could be a type qualifier (as is).
       So we cannot simply look at the next token
       and call separate functions to parse
       a type specifier or a type qualifier or an alignment specifier
       (or an attribute specifier, if GCC extensions are enabled).
       We need to read more tokens if we see @('_Atomic').
       [C17:6.7.2.4/4] says that
       an @('_Atomic') immediately followed by a left parentheses
       is interpreted as a type specifier (not a type qualifier).
       Thus, we read an additional token to decide whether
       we are parsing a type specifier or a type qualifier."))
    (b* (((reterr) (irr-spec/qual) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is a type specifier consisting of a single keyword,
       ;; return that type specifier.
       ((token-type-specifier-keyword-p token) ; void/char/.../_Complex
        (retok (spec/qual-typespec (token-to-type-specifier-keyword token))
               span
               parstate))
       ;; If token is the keyword _Atomic,
       ;; it may be either a type specifier or a type qualifier,
       ;; so we examine an additional token.
       ((token-keywordp token "_Atomic") ; _Atomic
        (b* (((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is an open parenthesis,
           ;; we must be parsing a type specifier.
           ((token-punctuatorp token2 "(") ; _Atomic (
            (b* (((erp tyname & parstate) ; _Atomic ( typename
                  (parse-type-name parstate))
                 ((erp last-span parstate) ; _Atomic ( typename )
                  (read-punctuator ")" parstate)))
              (retok (spec/qual-typespec (type-spec-atomic tyname))
                     (span-join span last-span)
                     parstate)))
           ;; If token 2 is not an open parenthesis,
           ;; we must be parsing a type qualifier.
           (t ; _Atomic other
            (b* ((parstate ; _Atomic
                  (if token2 (unread-token parstate) parstate)))
              (retok (spec/qual-typequal (type-qual-atomic))
                     span
                     parstate))))))
       ;; If token is the keyword struct,
       ;; we must have a structure type specifier.
       ((token-keywordp token "struct") ; struct
        (b* (((erp tyspec last-span parstate) ; struct struni-spec
              (parse-struct-or-union-specifier t span parstate)))
          (retok (spec/qual-typespec tyspec)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword union
       ;; we must have a union type specifier.
       ((token-keywordp token "union") ; union
        (b* (((erp tyspec last-span parstate) ; union struni-spec
              (parse-struct-or-union-specifier nil span parstate)))
          (retok (spec/qual-typespec tyspec)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword enum,
       ;; we must have an enumeration type specifier.
       ((token-keywordp token "enum") ; enum
        (b* (((erp enumspec last-span parstate) ; enum enumspec
              (parse-enum-specifier span parstate)))
          (retok (spec/qual-typespec (type-spec-enum enumspec))
                 (span-join span last-span)
                 parstate)))
       ;; If token is an identifier,
       ;; it is a type specifier, precisely a @('typedef') name.
       ;; It is the responsibility of the caller of this function
       ;; to ensure that this is not (the start of) a declarator:
       ;; when this function is called, it must be the case that
       ;; a specifier or qualifier is expected.
       ((and token (token-case token :ident)) ; ident
        (retok (spec/qual-typespec
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
              (parse-expression-or-type-name nil parstate))
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
          (retok (spec/qual-typespec tyspec)
                 (span-join span last-span)
                 parstate)))
       ;; If token is a type qualifier, which is always a single keyword,
       ;; we have that type qualifier.
       ((token-type-qualifier-p token) ; tyqual
        (retok (spec/qual-typequal (token-to-type-qualifier token))
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
    :parents (parser parse-exprs/decls/stmts)
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
          (parse-specifier/qualifier parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (tyspec-seenp (or tyspec-seenp
                           (spec/qual-case specqual :typespec)))
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

  (define parse-declaration-specifier ((parstate parstatep))
    :returns (mv erp
                 (declspec decl-specp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
       an attribute specifier,
       the @('__stdcall') keyword,
       or the @('__declspec') keyword
       (the last three are GCC extensions).")
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
       is resolved in the same way as in @(tsee parse-specifier/qualifier);
       see that function's documentation."))
    (b* (((reterr) (irr-decl-spec) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is a storage class specifier,
       ;; which always consists of a single keyword,
       ;; return that storage class specifier.
       ((token-storage-class-specifier-p token) ; typedef/.../register
        (retok (decl-spec-stoclass (token-to-storage-class-specifier token))
               span
               parstate))
       ;; If token is a type specifier consisting of a single keyword,
       ;; return that type specifier.
       ((token-type-specifier-keyword-p token) ; void/.../_Complex
        (retok (decl-spec-typespec (token-to-type-specifier-keyword token))
               span
               parstate))
       ;; If token is the keyword _Atomic,
       ;; it may be either a type specifier or a type qualifier,
       ;; so we examine an additional token.
       ((token-keywordp token "_Atomic") ; _Atomic
        (b* (((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is an open parenthesis,
           ;; we must be parsing a type specifier.
           ((token-punctuatorp token2 "(") ; _Atomic (
            (b* (((erp tyname & parstate) ; _Atomic ( typename
                  (parse-type-name parstate))
                 ((erp last-span parstate) ; _Atomic ( typename )
                  (read-punctuator ")" parstate)))
              (retok (decl-spec-typespec (type-spec-atomic tyname))
                     (span-join span last-span)
                     parstate)))
           ;; If token2 is not an open parenthesis,
           ;; we must be parsing a type qualifier.
           (t ; _Atomic other
            (b* ((parstate ; _Atomic
                  (if token2 (unread-token parstate) parstate)))
              (retok (decl-spec-typequal (type-qual-atomic))
                     span
                     parstate))))))
       ;; If token is the keyword struct,
       ;; we must have a structure type specifier.
       ((token-keywordp token "struct") ; struct
        (b* (((erp tyspec last-span parstate) ; struct struni-spec
              (parse-struct-or-union-specifier t span parstate)))
          (retok (decl-spec-typespec tyspec)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword union
       ;; we must have a union type specifier.
       ((token-keywordp token "union") ; union
        (b* (((erp tyspec last-span parstate) ; union struni-spec
              (parse-struct-or-union-specifier nil span parstate)))
          (retok (decl-spec-typespec tyspec)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword enum,
       ;; we must have an enumeration type specifier.
       ((token-keywordp token "enum") ; enum
        (b* (((erp enumspec last-span parstate) ; enum enumspec
              (parse-enum-specifier span parstate)))
          (retok (decl-spec-typespec (type-spec-enum enumspec))
                 (span-join span last-span)
                 parstate)))
       ;; If token is an identifier,
       ;; it is a type specifier, precisely a @('typedef') name.
       ;; It is the responsibility of the caller of this function
       ;; to ensure that this is not (the start of) a declarator:
       ;; when this function is called, it must be the case that
       ;; a specifier or qualifier is expected.
       ((and token (token-case token :ident)) ; ident
        (retok (decl-spec-typespec
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
              (parse-expression-or-type-name nil parstate))
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
          (retok (decl-spec-typespec tyspec)
                 (span-join span last-span)
                 parstate)))
       ;; If token is a type qualifier, which is always a single keyword,
       ;; we have that type qualifier.
       ((token-type-qualifier-p token) ; tyqual
        (retok (decl-spec-typequal (token-to-type-qualifier token))
               span
               parstate))
       ;; If token is a function specifier, which is always a single keyword,
       ;; we have that function specifier.
       ((token-function-specifier-p token) ; inline/_Noreturn
        (retok (decl-spec-function (token-to-function-specifier token))
               span
               parstate))
       ;; If token is the keyword _Alignas,
       ;; we must have an alignment specifier.
       ((token-keywordp token "_Alignas") ; _Alignas
        (b* (((erp alignspec last-span parstate) ; _Alignas ( ... )
              (parse-alignment-specifier span parstate)))
          (retok (decl-spec-align alignspec)
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
          (retok (decl-spec-attrib attrspec)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the keyword '__stdcall',
       ;; which can only happen if GCC extensions are enabled,
       ;; we must have that special GCC construct.
       ((token-keywordp token "__stdcall")
        (retok (decl-spec-stdcall) span parstate))
       ;; If token is the keyword '__declspec',
       ;; which can only happen if GCC extensions are enabled,
       ;; we must have an attribute with that syntax.
       ((token-keywordp token "__declspec")
        (b* (((erp & parstate) (read-punctuator "(" parstate))
             ((erp ident & parstate) (read-identifier parstate))
             ((erp last-span parstate) (read-punctuator ")" parstate)))
          (retok (decl-spec-declspec ident)
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
                 (declspecs decl-spec-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
       at least one type specifier [C17:6.7.2/2]
       and only the multisets listed in [C17:6.7.2/2].
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
          (parse-declaration-specifier parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         (tyspec-seenp (or tyspec-seenp
                           (decl-spec-case declspec :typespec)))
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

  (define parse-type-qualifier-or-attribute-specifier ((parstate parstatep))
    :returns (mv erp
                 (tyqual/attrib typequal/attribspec-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse a type qualifier or attribute specifier."
    (b* (((reterr) (irr-typequal/attribspec) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ((token-type-qualifier-p token) ; tyqual
        (retok (typequal/attribspec-type (token-to-type-qualifier token))
               span
               parstate))
       ((or (token-keywordp token "__attribute") ; __attribute
            (token-keywordp token "__attribute__")) ; __attribute__
        (b* ((uscores (token-keywordp token "__attribute__"))
             ((erp attrspec last-span parstate) ; attrspec
              (parse-attribute-specifier uscores span parstate)))
          (retok (typequal/attribspec-attrib attrspec)
                 (span-join span last-span)
                 parstate)))
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected "a keyword in {~
                               _Atomic, ~
                               const, ~
                               restrict, ~
                               volatile~
                               }"
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-type-qualifier-and-attribute-specifier-list
    ((parstate parstatep))
    :returns (mv erp
                 (tyqualattribs typequal/attribspec-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse a list of one or more
            type qualifiers and attribute specifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "We parse the first one, which must exist.
       Then we check the next token to see if there is be another one,
       in which case we put it back and recursively parse
       a list of type qualifiers and attribute specifiers,
       otherwise we put back it back and return."))
    (b* (((reterr) nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp tyqualattrib span parstate) ; tyqual/attrib
          (parse-type-qualifier-or-attribute-specifier parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ((token-type-qualifier-or-attribute-specifier-start-p
         token) ; tyqualattrib...
        (b* ((parstate (unread-token parstate))
             ((erp tyqualattribs last-span parstate)
              ;; tyqual/attib tyqual/attribs
              (parse-type-qualifier-and-attribute-specifier-list parstate)))
          (retok (cons tyqualattrib tyqualattribs)
                 (span-join span last-span)
                 parstate)))
       (t ; tyqual other
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok (list tyqualattrib) span parstate)))))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-pointer ((parstate parstatep))
    :returns (mv erp
                 (tyqualattribss typequal/attribspec-list-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse a pointer."
    :long
    (xdoc::topstring
     (xdoc::p
      "In the grammar, a `pointer' is a sequence of one or more stars,
       each followed by zero or more type qualifiers and attribute specifiers.
       In our abstract syntax, we model this notion as
       a list of lists of type qualifiers and attribute specifiers,
       one inner list for each star (implicit in our abstract syntax),
       with the outer list corresponding to the sequence of stars.")
     (xdoc::p
      "We read a star, which must be present:
       this function is called when we expect a pointer.
       If the next token is a type qualifier or starts an attribute specifier,
       we put it back and read a list of
       one or more type qualifiers and attribute specifier;
       then we check the next token if there is another star,
       in which case we recursively call this function.
       If instead the initial star is followed by another star,
       we also call this function recursively.
       We stop when there is not a star."))
    (b* (((reterr) nil (irr-span) parstate)
         ((erp span parstate) (read-punctuator "*" parstate)) ; *
         ((erp token & parstate) (read-token parstate)))
      (cond
       ((token-type-qualifier-or-attribute-specifier-start-p
         token) ; * tyqual/attrib...
        (b* ((parstate (unread-token parstate)) ; *
             (psize (parsize parstate))
             ((erp tyqualattribs span2 parstate) ; * tyqual/attribs
              (parse-type-qualifier-and-attribute-specifier-list parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp token & parstate) (read-token parstate)))
          (cond
           ((token-punctuatorp token "*") ; * tyqual/attribs *
            (b* ((parstate (unread-token parstate)) ; * tyqual/attribs
                 ((erp tyqualattribss last-span parstate)
                  ;; * tyqual/attribs * [tyqual/attribs] ...
                  (parse-pointer parstate)))
              (retok (cons tyqualattribs tyqualattribss)
                     (span-join span last-span)
                     parstate)))
           (t ; * tyqual/attribs other
            (b* ((parstate ; * tyqual/attribs
                  (if token (unread-token parstate) parstate)))
              (retok (list tyqualattribs) (span-join span span2) parstate))))))
       ((token-punctuatorp token "*") ; * *
        (b* ((parstate (unread-token parstate)) ; *
             ((erp tyqualattribss last-span parstate) ; * * [tyqual/attribs] ...
              (parse-pointer parstate)))
          (retok (cons nil tyqualattribss)
                 (span-join span last-span)
                 parstate)))
       (t ; * other
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok (list nil) span parstate)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-struct-or-union-specifier ((structp booleanp)
                                           (struct/union-span spanp)
                                           (parstate parstatep))
    :returns (mv erp
                 (tyspec type-specp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse or structure or union specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after parsing
       the initial @('struct') or @('union') keyword:
       we pass a boolean saying whether it was a @('struct') or not.")
     (xdoc::p
      "We return a type specifier that combines
       the parsed structure or union specifier
       with the information from the boolean input.
       The reason why we do that,
       instead of just returning a @(tsee struni-spec)
       and letting the callers build the @(tsee type-spec),
       is that we also accommodate the GCC extension of
       a structure specifier without members (and with optional name);
       this is a separate kind in @(tsee type-spec).")
     (xdoc::p
      "We also pass the span of the @('struct') or @('union') keyword,
       so that we can return a span for the whole type specifier."))
    (b* (((reterr) (irr-type-spec) (irr-span) parstate)
         ;; There must be at least one token (identifier or open curly brace),
         ;; so we read a token.
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is an identifier,
       ;; it may be the whole structure or union specifier,
       ;; or there may be more to it, so we read another token.
       ((and token (token-case token :ident)) ; struct/union ident
        (b* ((ident (token-ident->unwrap token))
             ((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is an open curly brace, there are two cases.
           ((token-punctuatorp token2 "{") ; struct/union ident {
            (if (and structp ; struct ident {
                     (parstate->gcc parstate))
                ;; If we are parsing a structure type specifier
                ;; and GCC extensions are enabled,
                ;; we read another token to see whether
                ;; we have a structure type with no members or not.
                (b* (((erp token3 span3 parstate) (read-token parstate)))
                  (cond
                   ;; If token3 is a closed curly brace,
                   ;; we have a structure type specifier with no members.
                   ((token-punctuatorp token3 "}") ; struct ident { }
                    (retok (type-spec-struct-empty ident)
                           (span-join struct/union-span span3)
                           parstate))
                   ;; If token3 is not a closed curly brace,
                   ;; we put back token3
                   ;; and parse one or more structure declarations,
                   ;; followed by a closed curly brace.
                   ;; In this case we return a (non-empty)
                   ;; structure type specifier.
                   (t ; struct ident { other
                    (b* ((parstate ; struct ident {
                          (if token3 (unread-token parstate) parstate))
                         ((erp structdeclons & parstate)
                          ;; struct ident { structdeclons
                          (parse-struct-declaration-list parstate))
                         ((erp last-span parstate)
                          ;; struct ident { structdeclons }
                          (read-punctuator "}" parstate)))
                      (retok (type-spec-struct
                              (make-struni-spec :name? ident
                                                :members structdeclons))
                             (span-join struct/union-span last-span)
                             parstate)))))
              ;; if we are parsing a union type specifier
              ;; or GCC extensions are not enabled,
              ;; we need to parse one of more structure declarations,
              ;; followed by a closed curly brace.
              (b* (((erp structdeclons & parstate)
                    ;; struct/union ident { structdeclons
                    (parse-struct-declaration-list parstate))
                   ((erp last-span parstate)
                    ;; struct/union ident { structdeclons }
                    (read-punctuator "}" parstate)))
                (retok (if structp
                           (type-spec-struct
                             (make-struni-spec :name? ident
                                               :members structdeclons))
                         (type-spec-union
                             (make-struni-spec :name? ident
                                               :members structdeclons)))
                       (span-join struct/union-span last-span)
                       parstate))))
           ;; If token2 is not an open curly brace,
           ;; the identifier was the whole structure or union specifier,
           ;; so we put back token2 and return the type specifier.
           (t ; struct/union ident other
            (b* ((parstate ; struct/union ident
                  (if token2 (unread-token parstate) parstate)))
              (retok (if structp
                         (type-spec-struct
                          (make-struni-spec :name? ident
                                            :members nil))
                       (type-spec-union
                        (make-struni-spec :name? ident
                                          :members nil)))
                     (span-join struct/union-span span)
                     parstate))))))
       ;; If token is an open curly brace,
       ;; we must have a structure or union specifier without name.
       ((token-punctuatorp token "{") ; struct/union {
        (if (and structp ; struct {
                 (parstate->gcc parstate))
            ;; If we are parsing a structure type specifier
            ;; and GCC extensions are enabled,
            ;; we read another token to see whether
            ;; we have a structure type with no members or not.
            (b* (((erp token3 span3 parstate) (read-token parstate)))
              (cond
               ;; If token3 is a closed curly brace,
               ;; we have a structure type specifier with no members.
               ((token-punctuatorp token3 "}") ; struct { }
                (retok (type-spec-struct-empty nil)
                       (span-join struct/union-span span3)
                       parstate))
               ;; If token3 is not a closed curly brace,
               ;; we put back token3
               ;; and parse one or more structure declarations,
               ;; followed by a closed curly brace.
               ;; In this case we return a (non-empty)
               ;; structure type specifier.
               (t ; struct { other
                (b* ((parstate ; struct {
                      (if token3 (unread-token parstate) parstate))
                     ((erp structdeclons & parstate)
                      ;; struct { structdeclons
                      (parse-struct-declaration-list parstate))
                     ((erp last-span parstate)
                      ;; struct { structdeclons }
                      (read-punctuator "}" parstate)))
                  (retok (type-spec-struct
                          (make-struni-spec :name? nil
                                            :members structdeclons))
                         (span-join struct/union-span last-span)
                         parstate)))))
          ;; If we are parsing a union type specifier
          ;; or GCC extensions are not enabled,
          ;; we must have one or more structure declarations.
          (b* (((erp structdeclons & parstate) ; struct/union { structdeclons
                (parse-struct-declaration-list parstate))
               ((erp last-span parstate) ; struct/union { structdeclons }
                (read-punctuator "}" parstate)))
            (retok (if structp
                       (type-spec-struct
                        (make-struni-spec :name? nil
                                          :members structdeclons))
                     (type-spec-union
                      (make-struni-spec :name? nil
                                        :members structdeclons)))
                   (span-join struct/union-span last-span)
                   parstate))))
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
                 (enumspec enum-specp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse an enumeration specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after parsing the initial @('enum') keyword.")
     (xdoc::p
      "The span of the @('enum') keyword is passed as input here."))
    (b* (((reterr) (irr-enum-spec) (irr-span) parstate)
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
              (retok (make-enum-spec :name ident
                                     :list enumers
                                     :final-comma final-comma)
                     (span-join first-span last-span)
                     parstate)))
           ;; If token2 is not an open curly brace,
           ;; the identifier must be the whole enumeration specifier.
           (t ; ident other
            (b* ((parstate
                  (if token2 (unread-token parstate) parstate))) ; ident
              (retok (make-enum-spec :name ident
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
          (retok (make-enum-spec :name nil
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
    :parents (parser parse-exprs/decls/stmts)
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
          (parse-expression-or-type-name nil parstate))
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
    :parents (parser parse-exprs/decls/stmts)
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
            (retok (make-dirabsdeclor-array :declor? nil
                                            :qualspecs nil
                                            :size? nil)
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
                (retok (make-dirabsdeclor-array-star :declor? nil)
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
                  (retok (make-dirabsdeclor-array :declor? nil
                                                  :qualspecs nil
                                                  :size? expr)
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
                     (psize (parsize parstate))
                     ((erp qualspecs & parstate) ; [ static tyqualattribs
                      (parse-type-qualifier-and-attribute-specifier-list
                       parstate))
                     ((unless (mbt (<= (parsize parstate) (1- psize))))
                      (reterr :impossible))
                     ((erp expr & parstate) ; [ static tyqualattribs expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ static tyqualattribs expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirabsdeclor-array-static1
                          :declor? nil
                          :qualspecs qualspecs
                          :size expr)
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
                          :declor? nil
                          :qualspecs nil
                          :size expr)
                         (span-join span last-span)
                         parstate))))))
           ;; If token2 is a type qualifier,
           ;; we must have a list of type qualifiers,
           ;; possibly followed by the keyword 'static',
           ;; and necessarily followed by an assignment expression.
           ((token-type-qualifier-p token2) ; [ tyqualattrib...
            (b* ((parstate (unread-token parstate)) ; [
                 (psize (parsize parstate))
                 ((erp qualspecs & parstate) ; [ tyqualattribs
                  (parse-type-qualifier-and-attribute-specifier-list parstate))
                 ((unless (mbt (<= (parsize parstate) (1- psize))))
                  (reterr :impossible))
                 ((erp token3 span3 parstate) (read-token parstate)))
              (cond
               ;; If token3 is the keyword 'static',
               ;; we must have an assignment expression after that.
               ((token-keywordp token3 "static") ; [ qualspecs static
                (b* (((erp expr & parstate) ; [ qualspecs static expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ qualspecs static expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirabsdeclor-array-static2
                          :declor? nil
                          :qualspecs qualspecs
                          :size expr)
                         (span-join span last-span)
                         parstate)))
               ;; If token3 is a closed square bracket,
               ;; there is no expression, and we have determined the variant.
               ((token-punctuatorp token3 "]") ; [ qualspecs ]
                (retok (make-dirabsdeclor-array
                        :declor? nil
                        :qualspecs qualspecs
                        :size? nil)
                       (span-join span span3)
                       parstate))
               ;; If token3 is not the keyword 'static'
               ;; and is not a closed square bracket,
               ;; we must have an assignment expression here.
               (t ; [ qualspecs other
                (b* ((parstate
                      (if token3 (unread-token parstate) parstate)) ; [ qualspecs
                     ((erp expr & parstate) ; [ qualspecs expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ qualspecs expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirabsdeclor-array
                          :declor? nil
                          :qualspecs qualspecs
                          :size? expr)
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
              (retok (make-dirabsdeclor-array :declor? nil
                                              :qualspecs nil
                                              :size? expr)
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
            (retok (make-dirabsdeclor-function :declor? nil
                                               :params nil
                                               :ellipsis nil)
                   (span-join span span2)
                   parstate))
           ;; If token2 is not a closed parenthesis,
           ;; we must have a parameter type list,
           ;; which we parse.
           (t ; ( other
            (b* ((parstate (if token2 (unread-token parstate) parstate)) ; (
                 ((erp params ellipsis & parstate) ; ( params [, ...]
                  (parse-parameter-declaration-list parstate))
                 ((erp last-span parstate) ; ( params [, ...] )
                  (read-punctuator ")" parstate)))
              (retok (make-dirabsdeclor-function :declor? nil
                                                 :params params
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
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
       ;; whose DECLOR? component is NIL (as we prove)
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
             ((unless (mbt (dirabsdeclor-declor?-nil-p next-dirabsdeclor)))
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
    :parents (parser parse-exprs/decls/stmts)
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
             ((erp qualspecss qualspecss-span parstate) ; pointer
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
              (retok (make-absdeclor :pointers qualspecss
                                     :direct? dirabsdeclor)
                     (span-join qualspecss-span dirabsdeclor-span)
                     parstate)))
           ;; If token2 may not start a direct abstract declarator,
           ;; our abstract declarator just consists of the pointer part.
           (t ; pointer other
            (b* ((parstate
                  (if token2 (unread-token parstate) parstate))) ; pointer
              (retok (make-absdeclor :pointers qualspecss
                                     :direct? nil)
                     qualspecss-span
                     parstate))))))
       ;; If token may start a direct abstract declarator,
       ;; our abstract declarator is just that, without the pointer part.
       ((token-direct-abstract-declarator-start-p token) ; dirabsdeclor...
        (b* ((parstate (unread-token parstate)) ;
             ((erp dirabsdeclor span parstate) ; dirabsdeclor
              (parse-direct-abstract-declarator parstate)))
          (retok (make-absdeclor :pointers nil
                                 :direct? dirabsdeclor)
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
    :parents (parser parse-exprs/decls/stmts)
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
           ((token-type-qualifier-p token2) ; [ tyqualattrib...
            (b* ((parstate (unread-token parstate)) ; [
                 (psize (parsize parstate))
                 ((erp qualspecs & parstate) ; [ tyqualattribs
                  (parse-type-qualifier-and-attribute-specifier-list parstate))
                 ((unless (mbt (<= (parsize parstate) (1- psize))))
                  (reterr :impossible))
                 ((erp token3 span3 parstate) (read-token parstate)))
              (cond
               ;; If token3 is a star, it may start an expression,
               ;; or it may be just a star for a variable length array.
               ;; So we need to read another token to disambiguate.
               ((token-punctuatorp token3 "*") ; [ qualspecs *
                (b* (((erp token4 span4 parstate) (read-token parstate)))
                  (cond
                   ;; If token4 is a closed square bracket,
                   ;; we have a variable length array declarator.
                   ((token-punctuatorp token4 "]") ; [ qualspecs * ]
                    (retok (make-dirdeclor-array-star :declor prev-dirdeclor
                                                      :qualspecs qualspecs)
                           (span-join prev-span span4)
                           parstate))
                   ;; If token4 is not a square bracket,
                   ;; the star must start an expression,
                   ;; so we put the tokens back
                   ;; and we proceed to parse an assignment expression.
                   ;; We have determined the array variant.
                   (t ; [ qualspecs * other
                    (b* ((parstate ; [ qualspecs *
                          (if token4 (unread-token parstate) parstate))
                         (parstate (unread-token parstate)) ; [ qualspecs
                         ((erp expr & parstate) ; [ qualspecs expr
                          (parse-assignment-expression parstate))
                         ((erp last-span parstate) ; [ qualspecs expr ]
                          (read-punctuator "]" parstate)))
                      (retok (make-dirdeclor-array :declor prev-dirdeclor
                                                   :qualspecs qualspecs
                                                   :size? expr)
                             (span-join prev-span last-span)
                             parstate))))))
               ;; If token3 may start an (assignment) expression,
               ;; we parse it, and we have determined the array variant.
               ;; We have already considered the case of a star above,
               ;; so this can only be an expression at this point.
               ((token-expression-start-p token3) ; [ qualspecs expr...
                (b* ((parstate (unread-token parstate)) ; [ qualspecs
                     ((erp expr & parstate) ; [ qualspecs expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ qualspecs expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirdeclor-array :declor prev-dirdeclor
                                               :qualspecs qualspecs
                                               :size? expr)
                         (span-join prev-span last-span)
                         parstate)))
               ;; If token3 is a closed square bracket,
               ;; we have determined the variant, and we have no expression.
               ((token-punctuatorp token3 "]") ; [ qualspecs ]
                (retok (make-dirdeclor-array :declor prev-dirdeclor
                                             :qualspecs qualspecs
                                             :size? nil)
                       (span-join prev-span span3)
                       parstate))
               ;; If token3 is the 'static' keyword,
               ;; we have determined the variant,
               ;; and we must have an expression.
               ((token-keywordp token3 "static") ; [ qualspecs static
                (b* (((erp expr & parstate) ; [ qualspecs static expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ qualspecs static expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirdeclor-array-static2 :declor prev-dirdeclor
                                                       :qualspecs qualspecs
                                                       :size expr)
                         (span-join prev-span last-span)
                         parstate)))
               ;; If token3 is anything else, it is an error.
               (t ; [ qualspecs other
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
                (retok (make-dirdeclor-array-star :declor prev-dirdeclor
                                                  :qualspecs nil)
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
                  (retok (make-dirdeclor-array :declor prev-dirdeclor
                                               :qualspecs nil
                                               :size? expr)
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
              (retok (make-dirdeclor-array :declor prev-dirdeclor
                                           :qualspecs nil
                                           :size? expr)
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
               ((token-type-qualifier-p token3) ; [ static tyqualattrib...
                (b* ((parstate (unread-token parstate)) ; [ static
                     (psize (parsize parstate))
                     ((erp qualspecs & parstate) ; [ static tyqualattribs
                      (parse-type-qualifier-and-attribute-specifier-list
                       parstate))
                     ((unless (mbt (<= (parsize parstate) (1- psize))))
                      (reterr :impossible))
                     ((erp expr & parstate) ; [ static tyqualattribs expr
                      (parse-assignment-expression parstate))
                     ((erp last-span parstate) ; [ static tyqualattribs expr ]
                      (read-punctuator "]" parstate)))
                  (retok (make-dirdeclor-array-static1 :declor prev-dirdeclor
                                                       :qualspecs qualspecs
                                                       :size expr)
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
                  (retok (make-dirdeclor-array-static1 :declor prev-dirdeclor
                                                       :qualspecs nil
                                                       :size expr)
                         (span-join prev-span last-span)
                         parstate))))))
           ;; If token2 is a closed square bracket,
           ;; we have an empty array construct.
           ((token-punctuatorp token2 "]") ; [ ]
            (retok (make-dirdeclor-array :declor prev-dirdeclor
                                         :qualspecs nil
                                         :size? nil)
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
            (retok (make-dirdeclor-function-params :declor prev-dirdeclor
                                                   :params nil
                                                   :ellipsis nil)
                   (span-join prev-span span2)
                   parstate))
           ;; If token2 is anything else,
           ;; we must have a list of one or more parameter declarations.
           (t ; ( other
            (b* ((parstate (if token2 (unread-token parstate) parstate))
                 ((erp params ellipsis & parstate) ; ( params [, ...]
                  (parse-parameter-declaration-list parstate))
                 ((erp last-span parstate) ; ( params [, ...] )
                  (read-punctuator ")" parstate)))
              (retok (make-dirdeclor-function-params :declor prev-dirdeclor
                                                     :params params
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
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
             (psize (parsize parstate))
             ((erp qualspecss & parstate) (parse-pointer parstate)) ; pointer
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp dirdeclor last-span parstate) ; pointer dirdeclor
              (parse-direct-declarator parstate)))
          (retok (make-declor :pointers qualspecss
                              :direct dirdeclor)
                 (span-join span last-span)
                 parstate)))
       ;; If token is not a star, we must have a direct declarator.
       (t ; other
        (b* ((parstate (if token (unread-token parstate) parstate)) ;
             ((erp dirdeclor span parstate) ; dirdeclor
              (parse-direct-declarator parstate)))
          (retok (make-declor :pointers nil
                              :direct dirdeclor)
                 span
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-struct-declarator ((parstate parstatep))
    :returns (mv erp
                 (structdeclor struct-declorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse a structure declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "A structure declarator consists of
       a declarator,
       or a declarator followed by colon and a constant expression,
       or a colon and a constant expression."))
    (b* (((reterr) (irr-struct-declor) (irr-span) parstate)
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
              (retok (make-struct-declor :declor? declor
                                         :expr? cexpr)
                     (span-join span last-span)
                     parstate)))
           ;; If token2 is not a colon,
           ;; the declarator is the whole structure declarator.
           (t ; declor other
            (b* ((parstate (if token2 (unread-token parstate) parstate)))
              (retok (make-struct-declor :declor? declor
                                         :expr? nil)
                     span
                     parstate))))))
       ;; If token is a colon,
       ;; we must be in the case in which there is no declarator
       ;; and there is just the colon and a constant expression.
       ((token-punctuatorp token ":") ; :
        (b* (((erp cexpr last-span parstate) ; : expr
              (parse-constant-expression parstate)))
          (retok (make-struct-declor :declor? nil
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
                 (structdeclors struct-declor-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
                 (structdeclon struct-declonp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    (b* (((reterr) (irr-struct-declon) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is the '_Static_assert' keyword,
       ;; we have a static assertion.
       ((token-keywordp token "_Static_assert") ; _Static_assert
        (b* (((erp statassert span parstate) ; staticassertion
              (parse-static-assert-declaration span parstate)))
          (retok (struct-declon-statassert statassert)
                 span
                 parstate)))
       ;; If token is a semicolon, and GCC extensions are enabled,
       ;; we have an empty structure declaration.
       ((token-punctuatorp token ";") ; ;
        (retok (struct-declon-empty) span parstate))
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
              (retok (make-struct-declon-member :extension extension
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
              (retok (make-struct-declon-member :extension extension
                                                :specqual specquals
                                                :declor nil
                                                :attrib attrspecs)
                     (span-join span last-span)
                     parstate)))
           ;; If token2 is a semicolon,
           ;; we have reached the end of the structure declaration.
           ((token-punctuatorp token2 ";") ; specquals ;
            (retok (make-struct-declon-member :extension extension
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
                 (structdeclons struct-declon-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse a list of one or more structure declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "We parse the first structure declaration, which must be present.
       Then we recursively call this function if the next token
       may start another structure declaration."))
    (b* (((reterr) nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp structdeclon span parstate) ; structdeclon
          (parse-struct-declaration parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token may start another structure declaration,
       ;; recursively call this function.
       ((token-struct-declaration-start-p
         token (parstate->gcc parstate)) ; structdeclon structdeclon...
        (b* ((parstate (unread-token parstate))
             ((erp structdeclons last-span parstate)
              ;; structdeclon structdeclons
              (parse-struct-declaration-list parstate)))
          (retok (cons structdeclon structdeclons)
                 (span-join span last-span)
                 parstate)))
       ;; Otherwise, we have reached the end of the structure declarations.
       (t ; structdeclon other
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok (list structdeclon) span parstate)))))
    :measure (two-nats-measure (parsize parstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-parameter-declaration ((parstate parstatep))
    :returns (mv erp
                 (param param-declonp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse a parameter declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "A parameter declaration always starts with
       a list of one or more declaration specifiers, which we parse.
       Then we may have a declarator, an abstract declarator, or nothing.
       After that, we may have zero or more attribute specifiers
       (this is a GCC extension).")
     (xdoc::p
      "As explained in @(tsee amb-declor/absdeclor),
       there is a complex syntactic overlap
       between declarators and abstract declarators.
       Thus, unless there is no (abstract or non-abstract) declarator,
       which we recognize by the presence of
       a comma
       or closed parenthesis
       or (if GCC extensions are enabled) an attribute keyword,
       we parse a possibly ambiguous declarator or abstract declarator,
       and generate a parameter declarator accordingly,
       and then a parameter declaration with the declaration specifiers."))
    (b* (((reterr) (irr-param-declon) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp declspecs span parstate) ; declspecs
          (parse-declaration-specifiers nil parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is a comma or a closed parenthesis,
       ;; or an attribute keyword
       ;; (which can only happen when GCC extensions are enabled),
       ;; there is no parameter declarator.
       ((or (token-punctuatorp token ")") ; declspecs )
            (token-punctuatorp token ",") ; declspecs ,
            (token-keywordp token "__attribute") ; declspecs __attribute
            (token-keywordp token "__attribute__")) ; declspecs __attribute__
        (b* ((parstate (unread-token parstate)) ; declspecs
             ((erp attrspecs last-span parstate) ; declspecs attrspecs
              (parse-*-attribute-specifier parstate)))
          (retok (make-param-declon :specs declspecs
                                    :declor (param-declor-none)
                                    :attribs attrspecs)
                 (if attrspecs
                     (span-join span last-span)
                   span)
                 parstate)))
       ;; Otherwise, we parse
       ;; a possibly ambiguous declarator or abstract declarator,
       ;; and return a parameter declaration in accordance.
       ;; We also parse zero or more attribute specifiers
       ;; (which can only occur if GCC extensions are enabled),
       ;; after the possibly ambiguous declarator or abstract declarator.
       (t ; declspecs other
        (b* ((parstate (if token (unread-token parstate) parstate)) ; declspecs
             (psize (parsize parstate))
             ((erp declor/absdeclor
                   declor/absdeclor-span
                   parstate) ; declspecs declor/absdeclor
              (parse-declarator-or-abstract-declarator parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp attrspecs
                   attrs-span
                   parstate) ; declspecs declor/absdeclor attrs
              (parse-*-attribute-specifier parstate)))
          (amb?-declor/absdeclor-case
           declor/absdeclor
           ;; If we parsed an unambiguous declarator,
           ;; we return a parameter declaration with that.
           :declor
           (retok (make-param-declon
                   :specs declspecs
                   :declor (make-param-declor-nonabstract
                            :declor declor/absdeclor.unwrap
                            :info nil)
                   :attribs attrspecs)
                  (if attrspecs
                      (span-join span attrs-span)
                    (span-join span declor/absdeclor-span))
                  parstate)
           ;; If we parsed an unambiguous abstract declarator,
           ;; we return a parameter declaration with that.
           :absdeclor
           (retok (make-param-declon
                   :specs declspecs
                   :declor (param-declor-abstract declor/absdeclor.unwrap)
                   :attribs attrspecs)
                  (if attrspecs
                      (span-join span attrs-span)
                    (span-join span declor/absdeclor-span))
                  parstate)
           ;; If we parsed an ambiguous declarator or abstract declarator,
           ;; we return a parameter declaration with that.
           :ambig
           (retok (make-param-declon
                   :specs declspecs
                   :declor (param-declor-ambig declor/absdeclor.unwrap)
                   :attribs attrspecs)
                  (if attrspecs
                      (span-join span attrs-span)
                    (span-join span declor/absdeclor-span))
                  parstate))))))
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-parameter-declaration-list ((parstate parstatep))
    :returns (mv erp
                 (params param-declon-listp)
                 (ellipsis booleanp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
         ((erp param span parstate) ; paramdeclon
          (parse-parameter-declaration parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is a comma, we might have another parameter declaration,
       ;; but we need to check whether we have an ellipsis instead.
       ((token-punctuatorp token ",") ; paramdeclon ,
        (b* (((erp token2 span2 parstate) (read-token parstate)))
          (cond
           ;; If token2 is an ellipsis,
           ;; we have reached the end of the parameter declaration list.
           ((token-punctuatorp token2 "...") ; paramdeclon , ...
            (retok (list param)
                   t
                   (span-join span span2)
                   parstate))
           ;; If token2 is not an ellipsis,
           ;; we must have more parameter declarators.
           (t ; paramdeclon , other
            (b* ((parstate ; paramdeclon ,
                  (if token2 (unread-token parstate) parstate))
                 ((erp params ellipsis last-span parstate)
                  ;; paramdeclon , paramdeclons [, ...]
                  (parse-parameter-declaration-list parstate)))
              (retok (cons param params)
                     ellipsis
                     (span-join span last-span)
                     parstate))))))
       ;; If token is not a comma,
       ;; we have reached the end of the parameter declaration list.
       (t ; paramdeclon other
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok (list param)
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
    :parents (parser parse-exprs/decls/stmts)
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
          (retok (make-tyname :specquals specquals
                              :declor? absdeclor
                              :info nil)
                 (span-join span last-span)
                 parstate)))
       ;; Otherwise, there is no abstract declarator.
       (t ; specquals other
        (b* ((parstate (if token (unread-token parstate) parstate)))
          (retok (make-tyname :specquals specquals
                              :declor? nil
                              :info nil)
                 span
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-expression-or-type-name ((add-parens-p booleanp)
                                         (parstate parstatep))
    :returns (mv erp
                 (expr/tyname amb?-expr/tyname-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
      "The @('add-parens-p') flag indicates whether,
       if the expression or type name turns out to be an expression,
       such expression should be parenthesized.
       This is needed because, for instance,
       in a @('sizeof(A)') expression where A is
       a possibly ambiguous expression or type name,
       the actual expression would be @('(A)'), not just @('A'),
       because @('sizeof') can be applied to
       an unparenthesized unary expression (e.g. @('sizeof x')).
       In this case, the @('add-parens-p') is set to @('t')
       by the caller of this parsing function.
       On the other hand, in a construct like @('_Alignas(A)'),
       where @('A') is a possibly ambiguous expression or type name,
       the expression is just @('A'),
       because the parentheses are always required:
       they are part of the syntax of @('_Alignas'),
       not part of the expression as in the case of
       @('sizeof') applied to an expression.
       In this case, the @('add-parens-p') flag is set to @('nil')
       by the caller of this parsing function.
       This flag is ignored if the expression or type name
       turns out to be ambiguous at parsing time:
       the disambiguation function @(tsee dimb-amb-expr/tyname)
       has an analogous @('add-parens-p') boolean flag
       to add parentheses to expressions, if needed,
       at disambiguation time.")
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
       are enclosed by the parentheses in the C grammar:
       it is the case that this parsing function is called
       always after an open parenthesis has just been parsed.
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
       but we plan to revisit this to see if we can have an @(tsee mbt).")
     (xdoc::p
      "As an optimization, we check whether the next token is an identifier
       before attempting the parsing of both an expression and a type name:
       identifiers are the only common starts of expressions and type names.
       If the next token is not an identifier,
       then we must have either an expression or a type name,
       which we choose based on the specific token."))
    (b* (((reterr) (irr-amb?-expr/tyname) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is an identifier, we try parsing
       ;; both an expression and a type name.
       ((and token (token-case token :ident)) ; ident
        (b* ((parstate (unread-token parstate)) ;
             (checkpoint (parstate->tokens-read parstate)) ; we will backtrack here
             (psize (parsize parstate))
             ((mv erp-expr expr span-expr parstate) (parse-expression parstate)))
          (if erp-expr
              ;; If the parsing of an expression fails,
              ;; we must have a type name.
              (b* ((parstate (unread-to-token checkpoint parstate)) ; backtrack
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
                  ;; But first, we save the checkpoint just after parsing
                  ;; the closing parenthesis after the expression,
                  ;; so that we can quickly go back here
                  ;; if the parsing of the type name fails.
                  (b* ((checkpoint-after-expr (parstate->tokens-read parstate))
                       (parstate (unread-to-token checkpoint parstate)) ; backtrack
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
                       ((mv erp tyname span-tyname parstate)
                        (parse-type-name parstate)))
                    (if erp
                        ;; If the parsing of a type name fails,
                        ;; we have an unambiguous expression, already parsed.
                        ;; If the ADD-PARENS-P flag is T,
                        ;; we parenthesize the expression
                        ;; (see the documentation of this function).
                        ;; So we re-read the already parsed tokens to get to
                        ;; just past the closing parenthesis after the expression,
                        ;; and we return the expression;
                        ;; that is, we backtrack from the backtracking.
                        ;; We first go back to the opening parenthesis,
                        ;; and then go forward to the closing parenthesis;
                        ;; perhaps it would be equivalent
                        ;; to go directly to the closing parenthesis,
                        ;; but going back and forth does not take much longer,
                        ;; and it would be needed if
                        ;; attempting to parse the type name
                        ;; goes past the closing parenthesis after the expression,
                        ;; which probably cannot, but we need to double-check.
                        (b* ((parstate ; backtrack
                              (unread-to-token checkpoint parstate))
                             (parstate ; backtrack from backtracking
                              (reread-to-token checkpoint-after-expr parstate))
                             ;; Compared to the opening parenthesis,
                             ;; if we go to the closing parenthesis,
                             ;; we must be at least two tokens ahead.
                             ((unless (<= (parsize parstate) (- psize 2)))
                              (raise "Internal error: ~
                                      size ~x0 after backtracking exceeds ~
                                      size ~x1 before backtracking."
                                     (parsize parstate) psize)
                              ;; Here we have (> (parsize parstate) (- psize 2)),
                              ;; but we need to return a parser state
                              ;; no larger than the initial one,
                              ;; so we just return the empty parser state.
                              ;; This is just logical:
                              ;; execution stops at the RAISE above.
                              (b* ((parstate (init-parstate nil nil parstate)))
                                (reterr t)))
                             ;; Put back the closing parenthesis,
                             ;; which is not part of the expression.
                             (parstate (unread-token parstate))
                             (expr (if add-parens-p
                                       (expr-paren expr)
                                     expr)))
                          (retok (amb?-expr/tyname-expr expr)
                                 span-expr
                                 parstate))
                      ;; If the parsing of a type name succeeds,
                      ;; we read a token to see whether
                      ;; a closed parenthesis follows.
                      (b* (((erp token & parstate) (read-token parstate)))
                        (if (token-punctuatorp token ")")
                            ;; If a closed parenthesis follows,
                            ;; we have an ambiguous expression or type name.
                            ;; We double-check that
                            ;; the expression and the type name
                            ;; have the same spans;
                            ;; this is always expected to succeed,
                            ;; because we have checked that in both cases
                            ;; we have reached a closed parenthesis,
                            ;; and the parser reads only balanced parentheses.
                            ;; We put back the closed parenthesis.
                            (b* (((unless (equal span-expr span-tyname))
                                  (raise "Internal error:
                                          span ~x0 of expression ~x1 ~
                                          differs from ~
                                          span ~x2 of type name ~x3."
                                         span-expr expr span-tyname tyname)
                                  (reterr t))
                                 ;; Put back the closing parenthesis,
                                 ;; which is not part of
                                 ;; the expression or type name.
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
                          ;; so we backtrack from the backtracking as before.
                          ;; We parenthesize the expression
                          ;; the ADD-PARENS-P flag is T.
                          (b* ((parstate ; backtrack
                                (unread-to-token checkpoint parstate))
                               (parstate ; backtrack from backtracking
                                (reread-to-token checkpoint-after-expr parstate))
                               ;; Compared to the opening parenthesis,
                               ;; if we go to the closing parenthesis,
                               ;; we must be at least two tokens ahead.
                               ((unless (<= (parsize parstate) (- psize 2)))
                                (raise "Internal error: ~
                                    size ~x0 after backtracking exceeds ~
                                    size ~x1 before backtracking."
                                       (parsize parstate) psize)
                                ;; Here we have (> (parsize parstate) (- psize 2)),
                                ;; but we need to return a parser state
                                ;; no larger than the initial one,
                                ;; so we just return the empty parser state.
                                ;; This is just logical:
                                ;; execution stops at the RAISE above.
                                (b* ((parstate (init-parstate nil nil parstate)))
                                  (reterr t)))
                               ;; Put back the closing parenthesis,
                               ;; which is not part of the expression.
                               (parstate (unread-token parstate))
                               (expr (if add-parens-p
                                         (expr-paren expr)
                                       expr)))
                            (retok (amb?-expr/tyname-expr expr)
                                   span-expr
                                   parstate))))))
                ;; If no closed parenthesis follows the parsed expression,
                ;; we regard the parsing of the expression to have failed,
                ;; perhaps because we have only parsed a prefix of a type name.
                ;; So we must have a type name instead.
                ;; We backtrack, which also puts back any tokens just read,
                ;; and we attempt to parse a type name.
                (b* ((parstate (unread-to-token checkpoint parstate)) ; backtrack
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
                  (retok (amb?-expr/tyname-tyname tyname) span parstate)))))))
       ;; If token may start an expression, we must have an expression,
       ;; because we have already handled the case of an identifier above.
       ;; We parenthesize the expression if ADD-PARENS-P is T.
       ((token-expression-start-p token) ; expr...
        (b* ((parstate (unread-token parstate)) ;
             ((erp expr span parstate) (parse-expression parstate)) ; expr
             (expr (if add-parens-p
                       (expr-paren expr)
                     expr)))
          (retok (amb?-expr/tyname-expr expr) span parstate)))
       ;; If token may start a type name, we must have a type name,
       ;; because we have already handled the case of an identifier above.
       ((token-type-name-start-p token) ; tyname...
        (b* ((parstate (unread-token parstate)) ;
             ((erp tyname span parstate) (parse-type-name parstate))) ; tyname
          (retok (amb?-expr/tyname-tyname tyname) span parstate)))
       ;; If token is anything else, including absent, it is an error:
       ;; we have neither an expression nor a type name.
       (t ; other
        (reterr-msg :where (position-to-msg (span->start span))
                    :expected (msg "the start of an expression or type name")
                    :found (token-to-msg token)))))
    :measure (two-nats-measure (parsize parstate) 17))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-unary-expression-or-parenthesized-type-name ((parstate
                                                              parstatep))
    :returns (mv erp
                 (expr/tyname amb?-expr/tyname-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse a unary expression or a parenthesized type name."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is, in a way, a specialized form of
       @(tsee parse-expression-or-type-name).
       It is used just after a @('sizeof') followed by an open parenthesis,
       which could be ambiguous, e.g. @('sizeof(x)').
       In the grammar, @('sizeof') may be followed
       by a unary expression or by a parenthesized type name.
       Note that the (unary) expression does not have to be parenthesized.
       So, for example, @('sizeof(x).m') is not ambiguous:
       it consists of @('sizeof') followed by
       the postfix (hence unary) expression @('(x).m').
       This means that, after parsing @('sizeof') and @('('),
       we cannot just parse a possibly ambiguous expression or type name
       and then the closing @(')'):
       we would be missing the @('.m') part, in this example.
       Indeed, based on the grammar,
       it makes sense that, after parsing a @('sizeof'),
       we need to try parsing a unary expression or a parenthesized type name.")
     (xdoc::p
      "This parsing function is called just after parsing the @('sizeof');
       the caller unreads the @('(') after reading it;
       the caller only calls this function
       if the @('sizeof') is followed by @('(').")
     (xdoc::p
      "Note that here we should parse a unary expression,
       but we know that it starts with an open parenthesis.
       So the unary expression must be in fact a postfix expression,
       and we use directly the parsing function for that.")
     (xdoc::p
      "We return the span of the whole
       unary expression or parenthesized type name,
       so that the caller can combine it with the span of @('sizeof')
       to obtain a span for the whole @('sizeof') expression."))
    (b* (((reterr) (irr-amb?-expr/tyname) (irr-span) parstate)
         (checkpoint (parstate->tokens-read parstate)) ; we will backtrack here
         (psize (parsize parstate))
         ((mv erp-expr expr span-expr parstate) ; expr
          (parse-postfix-expression parstate)) ; unary must be postfix
         ((when erp-expr)
          ;; If the parsing of a unary (postfix) expression fails,
          ;; we must have a parenthesized type name.
          (b* ((parstate (unread-to-token checkpoint parstate)) ; backtrack
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
               ((erp first-span parstate) ; (
                (read-punctuator "(" parstate))
               ((erp tyname & parstate) ; ( tyname
                (parse-type-name parstate))
               ((erp last-span parstate) ; ( tyname )
                (read-punctuator ")" parstate)))
            (retok (amb?-expr/tyname-tyname tyname)
                   (span-join first-span last-span)
                   parstate)))
         ;; If the parsing of the unary (postfix) expression succeeds,
         ;; we must see whether we can also parse a parenthesized type name,
         ;; after backtracking.
         ;; So we backtrack, but first we save the checkpoint
         ;; just after parsing the expression,
         ;; so that we can quickly go back here
         ;; if the parsing of the parenthesized type name fails.
         (checkpoint-after-expr (parstate->tokens-read parstate))
         (parstate (unread-to-token checkpoint parstate)) ; backtrack
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
         ;; If the parsing of any part of the parenthesized type name fails,
         ;; we have an unambiguous expression, already parsed.
         ;; So we re-read the already parsed tokens to get to
         ;; just past the expression,
         ;; and we return the expression;
         ;; that is, we backtrack from the backtracking.
         ;; We first go back to the start of the expression,
         ;; and then go forward to the end;
         ;; perhaps it would be equivalent
         ;; to go directly to the end of the expression,
         ;; but going back and forth does not take much longer,
         ;; and it would be needed if
         ;; attempting to parse the parenthesized tyoe name
         ;; goes past the end of the expression,
         ;; which probably cannot, but we need to double-check.
         ((mv erp-open-paren & parstate) ; (
          (read-punctuator "(" parstate))
         ((when erp-open-paren)
          (b* ((parstate ; backtrack
                (unread-to-token checkpoint parstate))
               (parstate ; backtrack from backtracking
                (reread-to-token checkpoint-after-expr parstate))
               ;; Compared to the start of the expression,
               ;; if we go to the end of the expression,
               ;; we must be at least one token ahead.
               ((unless (<= (parsize parstate) (1- psize)))
                (raise "Internal error: ~
                        size ~x0 after backtracking exceeds ~
                        size ~x1 before backtracking."
                       (parsize parstate) psize)
                ;; Here we have (> (parsize parstate) (1- psize)),
                ;; but we need to return a parser state
                ;; no larger than the initial one,
                ;; so we just return the empty parser state.
                ;; This is just logical:
                ;; execution stops at the RAISE above.
                (b* ((parstate (init-parstate nil nil parstate)))
                  (reterr t))))
            (retok (amb?-expr/tyname-expr expr) span-expr parstate)))
         ((mv erp-tyname tyname & parstate) ; ( tyname
          (parse-type-name parstate))
         ((when erp-tyname)
          (b* ((parstate ; backtrack
                (unread-to-token checkpoint parstate))
               (parstate ; backtrack from backtracking
                (reread-to-token checkpoint-after-expr parstate))
               ;; Compared to the start of the expression,
               ;; if we go to the end of the expression,
               ;; we must be at least one token ahead.
               ((unless (<= (parsize parstate) (1- psize)))
                (raise "Internal error: ~
                        size ~x0 after backtracking exceeds ~
                        size ~x1 before backtracking."
                       (parsize parstate) psize)
                ;; Here we have (> (parsize parstate) (1- psize)),
                ;; but we need to return a parser state
                ;; no larger than the initial one,
                ;; so we just return the empty parser state.
                ;; This is just logical:
                ;; execution stops at the RAISE above.
                (b* ((parstate (init-parstate nil nil parstate)))
                  (reterr t))))
            (retok (amb?-expr/tyname-expr expr) span-expr parstate)))
         ((mv erp-close-paren & parstate) ; ( tyname )
          (read-punctuator ")" parstate))
         ((when erp-close-paren)
          (b* ((parstate ; backtrack
                (unread-to-token checkpoint parstate))
               (parstate ; backtrack from backtracking
                (reread-to-token checkpoint-after-expr parstate))
               ;; Compared to the start of the expression,
               ;; if we go to the end of the expression,
               ;; we must be at least one token ahead.
               ((unless (<= (parsize parstate) (1- psize)))
                (raise "Internal error: ~
                        size ~x0 after backtracking exceeds ~
                        size ~x1 before backtracking."
                       (parsize parstate) psize)
                ;; Here we have (> (parsize parstate) (1- psize)),
                ;; but we need to return a parser state
                ;; no larger than the initial one,
                ;; so we just return the empty parser state.
                ;; This is just logical:
                ;; execution stops at the RAISE above.
                (b* ((parstate (init-parstate nil nil parstate)))
                  (reterr t))))
            (retok (amb?-expr/tyname-expr expr) span-expr parstate)))
         ;; If the parsing of the parenthesized type name succeeds,
         ;; we could have an ambiguity,
         ;; unless we have only parsed the first part of a postfix expression,
         ;; as in the sizeof(x).m example in the documentation of this function.
         ;; We can tell that by looking at the previously parsed expression:
         ;; unless it is a parenthesized expression,
         ;; we are in an umambiguous situation in which
         ;; the sizeof is in fact followed by a (proper) postfix expression.
         ((unless (expr-case expr :paren))
          (b* ((parstate ; backtrack
                (unread-to-token checkpoint parstate))
               (parstate ; backtrack from backtracking
                (reread-to-token checkpoint-after-expr parstate))
               ;; Compared to the start of the expression,
               ;; if we go to the end of the expression,
               ;; we must be at least one token ahead.
               ((unless (<= (parsize parstate) (1- psize)))
                (raise "Internal error: ~
                        size ~x0 after backtracking exceeds ~
                        size ~x1 before backtracking."
                       (parsize parstate) psize)
                ;; Here we have (> (parsize parstate) (1- psize)),
                ;; but we need to return a parser state
                ;; no larger than the initial one,
                ;; so we just return the empty parser state.
                ;; This is just logical:
                ;; execution stops at the RAISE above.
                (b* ((parstate (init-parstate nil nil parstate)))
                  (reterr t))))
            (retok (amb?-expr/tyname-expr expr) span-expr parstate))))
      ;; If the expression is a parenthesized one,
      ;; we have an ambiguous situation.
      ;; We return an ambiguous expression or type name,
      ;; where the expression is the one without the parentheses.
      (retok (amb?-expr/tyname-ambig
              (make-amb-expr/tyname :expr (expr-paren->inner expr)
                                    :tyname tyname))
             span-expr
             parstate))
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-declarator-or-abstract-declarator ((parstate parstatep))
    :returns (mv erp
                 (declor/absdeclor amb?-declor/absdeclor-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
       which is always followed by a comma or closed parenthesis,
       or by an attribute if GCC extensions are enabled.
       So, if we successfully parse an abstract declarator,
       we also ensure that the next token is
       a comma or closed parenthesis or attribute keyword,
       otherwise we regard the parsing of the abstract declarator
       to have failed."))
    (b* (((reterr) (irr-amb?-declor/absdeclor) (irr-span) parstate)
         (checkpoint (parstate->tokens-read parstate)) ; we will backtrack here
         (psize (parsize parstate))
         ((mv erp-declor declor span-declor parstate)
          (parse-declarator parstate)))
      (if erp-declor
          ;; If the parsing of a declarator fails,
          ;; we must have an abstract declarator.
          (b* ((parstate (unread-to-token checkpoint parstate)) ; backtrack
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
        ;; So we backtrack, but first we save the checkpoint
        ;; just after parsing the declarator,
        ;; so that we can quickly go back here
        ;; if the parsing of the abstract declarator fails.
        (b* ((checkpoint-after-declor (parstate->tokens-read parstate))
             (parstate (unread-to-token checkpoint parstate)) ; backtrack
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
             ((mv erp absdeclor span-absdeclor parstate)
              (parse-abstract-declarator parstate)))
          (if erp
              ;; If the parsing of an abstract declarator fails,
              ;; we have an unambiguous declarator, already parsed.
              ;; So we re-read the already parsed tokens to get to
              ;; just past the declarator,
              ;; and we return the declarator;
              ;; that is, we backtrack from the backtracking.
              ;; We first go back to the start of the declarator,
              ;; and then go forward to the end;
              ;; perhaps it would be equivalent
              ;; to go directly to the end of the declarator,
              ;; but going back and forth does not take much longer,
              ;; and it would be needed if
              ;; attempting to parse the abstract declarator
              ;; goes past the end of the declarator,
              ;; which probably cannot, but we need to double-check.
              (b* ((parstate ; backtrack
                    (unread-to-token checkpoint parstate))
                   (parstate ; backtrack from backtracking
                    (reread-to-token checkpoint-after-declor parstate))
                   ;; Compared to the start of the declarator,
                   ;; if we go to the end of the declarator,
                   ;; we must be at least one token ahead.
                   ((unless (<= (parsize parstate) (1- psize)))
                    (raise "Internal error: ~
                            size ~x0 after backtracking exceeds ~
                            size ~x1 before backtracking."
                           (parsize parstate) psize)
                    ;; Here we have (> (parsize parstate) (1- psize)),
                    ;; but we need to return a parser state
                    ;; no larger than the initial one,
                    ;; so we just return the empty parser state.
                    ;; This is just logical:
                    ;; execution stops at the RAISE above.
                    (b* ((parstate (init-parstate nil nil parstate)))
                      (reterr t))))
                (retok (amb?-declor/absdeclor-declor declor)
                       span-declor
                       parstate))
            ;; If the parsing of an abstract declarator succeeds,
            ;; we still need to check whether
            ;; it is followed by a comma or closed parenthesis
            ;; (or an attribute, if GCC extensions are enabled),
            ;; as explained in the documentation of the function above.
            ;; So we read a token.
            (b* (((erp token & parstate) (read-token parstate)))
              (if (or (token-punctuatorp token ",")
                      (token-punctuatorp token ")")
                      (token-keywordp token "__attribute")
                      (token-keywordp token "__attribute__"))
                  ;; If a comma or closed parenthesis follows,
                  ;; the parsing of the abstract declarator has succeeded,
                  ;; we have an ambiguous declarator or abstract declarator.
                  ;; We double-check that the two spans are the same;
                  ;; we have not yet analyzed in detail
                  ;; whether this check should always succeed,
                  ;; but we will revisit the issue if we observe failures
                  ;; (in which case we can handle things similarly to
                  ;; our handling in PARSE-EXPRESSION-OR-TYPE-NAME).
                  (b* (((unless (equal span-absdeclor span-declor))
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
                ;; So we must have a declarator instead,
                ;; which we have already parsed,
                ;; so we backtrack from the backtracking as before.
                (b* ((parstate ; backtrack
                      (unread-to-token checkpoint parstate))
                     (parstate ; backtrack from backtracking
                      (reread-to-token checkpoint-after-declor parstate))
                     ;; Compared to the start of the declarator,
                     ;; if we go to the end of the declarator,
                     ;; we must be at least one token ahead.
                     ((unless (<= (parsize parstate) (1- psize)))
                      (raise "Internal error: ~
                              size ~x0 after backtracking exceeds ~
                              size ~x1 before backtracking."
                             (parsize parstate) psize)
                      ;; Here we have (> (parsize parstate) (1- psize)),
                      ;; but we need to return a parser state
                      ;; no larger than the initial one,
                      ;; so we just return the empty parser state.
                      ;; This is just logical:
                      ;; execution stops at the RAISE above.
                      (b* ((parstate (init-parstate nil nil parstate)))
                        (reterr t))))
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
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse an attribute."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is only used if GCC extensions are supported.
       See the ABNF grammar rule for @('attribute')."))
    (b* (((reterr) (irr-attrib) (irr-span) parstate)
         ((erp name name-span parstate) (parse-attribute-name parstate)) ; name
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is an open parenthesis, the attribute has parameters.
       ((token-punctuatorp token "(") ; name (
        (b* ((parstate (unread-token parstate)) ; name
             ((erp exprs span parstate) ; name ( exprs )
              (parse-attribute-parameters parstate)))
          (retok (make-attrib-name-param :name name :param exprs)
                 (span-join name-span span)
                 parstate)))
       ;; If token is anything else, the attribute is just a name.
       (t ; name other
        (b* ((parstate (if token (unread-token parstate) parstate))) ; name
          (retok (attrib-name-only name) name-span parstate)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-attribute-list ((parstate parstatep))
    :returns (mv erp
                 (attrs attrib-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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
    :parents (parser parse-exprs/decls/stmts)
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

  (define parse-init-declarator ((parstate parstatep))
    :returns (mv erp
                 (initdeclor initdeclorp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse an initializer declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "An initializer declarator consists of a declarator,
       optionally followed by an assembler name specifier,
       optionally followed by an equal sign and an initializer."))
    (b* (((reterr) (irr-initdeclor) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp declor span parstate) (parse-declarator parstate)) ; declor
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp asmspec? asmspec?-span parstate) ; declor [asmspec]
          (parse-?-asm-name-specifier parstate))
         (psize (parsize parstate))
         ((erp attrspecs attrspecs-span parstate) ; declor [asmspec] [attrspecs]
          (parse-*-attribute-specifier parstate))
         ((unless (mbt (<= (parsize parstate) psize)))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate)))
      (cond
       ;; If token is an equal sign, there must be an initializer.
       ((token-punctuatorp token "=") ; declor [asmspec] =
        (b* (((erp initer last-span parstate) ; declor [asmspec] = initer
              (parse-initializer parstate)))
          (retok (make-initdeclor :declor declor
                                  :asm? asmspec?
                                  :attribs attrspecs
                                  :init? initer
                                  :info nil)
                 (span-join span last-span)
                 parstate)))
       ;; Otherwise, there is no initializer.
       (t ; declor [asmspec] other
        (b* ((parstate (if token (unread-token parstate) parstate)))
          ;; declor [asmspec]
          (retok (make-initdeclor :declor declor
                                  :asm? asmspec?
                                  :attribs attrspecs
                                  :init? nil
                                  :info nil)
                 (cond (attrspecs (span-join span attrspecs-span))
                       (asmspec? (span-join span asmspec?-span))
                       (t span))
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-init-declarator-list ((parstate parstatep))
    :returns (mv erp
                 (initdeclors initdeclor-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse a list of one or more initializer declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "We parse the first one, which must be present.
       If there is a comma after that,
       we recursively parse one or more after the comma."))
    (b* (((reterr) nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp initdeclor span parstate) ; initdeclor
          (parse-init-declarator parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
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
    :measure (two-nats-measure (parsize parstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-declaration ((parstate parstatep))
    :returns (mv erp
                 (decl declp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
      "If GCC extensions are supported,
       we must allow for an @('__extension__') keyword at the beginning.
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
             (psize (parsize parstate))
             ((erp declspecs span parstate) ; [__extension__] declspecs
              (parse-declaration-specifiers nil parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp token2 span2 parstate) (read-token parstate)))
          (cond
           ;; If token2 may start a declarator,
           ;; which is equivalent to saying that
           ;; it may start an initializer declarator,
           ;; we parse the list of one or more initializer declarators,
           ;; and then the final semicolon.
           ((token-declarator-start-p token2)
            ;; [__extension__] declspecs declor...
            (b* ((parstate (unread-token parstate))
                 ;; [__extension__] declspecs
                 ((erp initdeclors & parstate)
                  ;; [__extension__] declspecs initdeclors
                  (parse-init-declarator-list parstate))
                 ((erp last-span parstate)
                  ;; [__extension__] declspecs initdeclors ;
                  (read-punctuator ";" parstate)))
              (retok (make-decl-decl :extension extension
                                     :specs declspecs
                                     :init initdeclors)
                     (span-join span last-span)
                     parstate)))
           ;; If token2 is a semicolon,
           ;; we have no initializer declarators.
           ;; If GCC extensions are supported,
           ;; this also means that we have no attribute specifiers.
           ((token-punctuatorp token2 ";") ; [__extension__] declspecs ;
            (retok (make-decl-decl :extension extension
                                   :specs declspecs
                                   :init nil)
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
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-declaration-list ((parstate parstatep))
    :returns (mv erp
                 (decls decl-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
         (psize (parsize parstate))
         ((erp decl span parstate) (parse-declaration parstate)) ; decl
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
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
    :measure (two-nats-measure (parsize parstate) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-declaration-or-statement ((parstate parstatep))
    :returns (mv erp
                 (decl/stmt amb?-decl/stmt-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
         (checkpoint (parstate->tokens-read parstate)) ; we will backtrack here
         (psize (parsize parstate))
         ((mv erp expr span-expr parstate) (parse-expression parstate)))
      (if erp
          ;; If the parsing of an expression fails,
          ;; we must have a declaration.
          (b* ((parstate (unread-to-token checkpoint parstate)) ; backtrack
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
              ;; So we backtrack (which will also put back the semicolon)
              ;; and we attempt to parse a declaration.
              ;; But first, we save the checkpoint just after parsing
              ;; the semicolon after the expression,
              ;; so that we can quickly go back here
              ;; if the parsing of the declartion fails.
              (b* ((checkpoint-after-expr (parstate->tokens-read parstate))
                   (parstate (unread-to-token checkpoint parstate)) ; backtrack
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
                   ((mv erp decl span-decl parstate)
                    (parse-declaration parstate)))
                (if erp
                    ;; If the parsing of a declaration fails,
                    ;; we have an expression statement.
                    ;; So we re-read the already parsed tokens to get to
                    ;; just past the semicolon after the expression,
                    ;; and we return the expression;
                    ;; that is, we backtrack from the backtracking.
                    ;; We first go back to the start of the expression,
                    ;; and then go forward to the semicolon;
                    ;; perhaps it would be equivalent
                    ;; to go directly to the semicolon,
                    ;; but going back and forth does not take much longer,
                    ;; and it would be needed if
                    ;; attempting to parse the type name
                    ;; goes past the semicolon after the expression,
                    ;; which probably cannot, but we need to double-check.
                    (b* ((parstate ; backtrack
                          (unread-to-token checkpoint parstate))
                         (parstate ; backtrack from backtracking
                          (reread-to-token checkpoint-after-expr parstate))
                         ;; Compared to the start of the expression,
                         ;; if we go to the semicolon,
                         ;; we must be at least two tokens ahead.
                         ((unless (<= (parsize parstate) (- psize 2)))
                          (raise "Internal error: ~
                                  size ~x0 after backtracking exceeds ~
                                  size ~x1 before backtracking."
                                 (parsize parstate) psize)
                          ;; Here we have (> (parsize parstate) (- psize 2)),
                          ;; but we need to return a parser state
                          ;; no larger than the initial one,
                          ;; so we just return the empty parser state.
                          ;; This is just logical:
                          ;; execution stops at the RAISE above.
                          (b* ((parstate (init-parstate nil nil parstate)))
                            (reterr t))))
                      (retok (amb?-decl/stmt-stmt expr)
                             (span-join span-expr span-semicolon)
                             parstate))
                  ;; If the parsing of a declaration succeeds,
                  ;; we return an ambiguous declaration or statement.
                  ;; We double-check that the spans are the same,
                  ;; which is always expected to succeed.
                  (b* (((unless (equal span-stmt span-decl))
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
            (b* ((parstate (unread-to-token checkpoint parstate)) ; backtrack
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
    :measure (two-nats-measure (parsize parstate) 17))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-asm-output-operand ((parstate parstatep))
    :returns (mv erp
                 (output asm-outputp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse an assembler output operand."
    (b* (((reterr) (irr-asm-output) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is an open square bracket, we have a name to parse,
       ;; followed by one or more string literals,
       ;; followed by a parenthesized expression.
       ((token-punctuatorp token "[") ; [
        (b* (((erp name & parstate) (read-identifier parstate)) ; [ name
             ((erp & parstate) (read-punctuator "]" parstate)) ; [ name ]
             ((erp token2 span2 parstate) (read-token parstate))
             ((unless (and token2 (token-case token2 :string)))
              (reterr-msg :where (position-to-msg (span->start span2))
                          :expected "a string literal"
                          :found (token-to-msg token2)))
             ;; [ name ] string
             (string (token-string->unwrap token2))
             ((erp strings & parstate) ; [ name ] string strings
              (parse-*-stringlit parstate))
             (constraint (cons string strings)) ; [ name ] constraint
             ((erp & parstate) ; [ name ] constraint (
              (read-punctuator "(" parstate))
             ((erp lvalue & parstate) ; [ name ] constraint ( expr
              (parse-expression parstate))
             ((erp last-span parstate) ; [ name ] constraint ( expr )
              (read-punctuator ")" parstate)))
          (retok (make-asm-output :name name
                                  :constraint constraint
                                  :lvalue lvalue)
                 (span-join span last-span)
                 parstate)))
       ;; Otherwise, we must have one or more string literals,
       ;; followed by a parenthesized expression.
       (t ; other
        (b* ((parstate (if token (unread-token parstate) parstate)) ;
             ((erp token2 span2 parstate) (read-token parstate))
             ((unless (and token2 (token-case token2 :string)))
              (reterr-msg :where (position-to-msg (span->start span2))
                          :expected "a string literal"
                          :found (token-to-msg token2)))
             ;; string
             (string (token-string->unwrap token2))
             ((erp strings & parstate) ; string strings
              (parse-*-stringlit parstate))
             (constraint (cons string strings)) ; constraint
             ((erp & parstate) ; constraint (
              (read-punctuator "(" parstate))
             ((erp lvalue & parstate) ; constraint ( expr
              (parse-expression parstate))
             ((erp last-span parstate) ; constraint ( expr )
              (read-punctuator ")" parstate)))
          (retok (make-asm-output :name nil
                                  :constraint constraint
                                  :lvalue lvalue)
                 (span-join span last-span)
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-asm-output-operands ((parstate parstatep))
    :returns (mv erp
                 (outputs asm-output-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse one or more assembler output operands, separated by commas."
    :long
    (xdoc::topstring
     (xdoc::p
      "After parsing an assembler output operand,
       we check whether the following token is a comma,
       in which case there must be at least another assembler output operand,
       so we recursively parse one or more assembler output operands."))
    (b* (((reterr) nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp output span parstate) ; output
          (parse-asm-output-operand parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate))
         ((unless (token-punctuatorp token ",")) ; output ,
          (b* ((parstate (if token (unread-token parstate) parstate)))
            (retok (list output) span parstate)))
         ((erp outputs last-span parstate) ; output , outputs
          (parse-asm-output-operands parstate)))
      (retok (cons output outputs)
             (span-join span last-span)
             parstate))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-?-asm-output-operands ((parstate parstatep))
    :returns (mv erp
                 (outputs asm-output-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse zero or more assembler output operands, separated by commas."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the next token is an open square bracket or a string literal,
       there must be at least one assembler output operand,
       so we call the function that parses
       one or more assembler output operands.
       If the next token is not an open square bracket or a string literal,
       then there are no assembler output operands;
       we return an irrelevant span in this case,
       which callers do not use."))
    (b* (((reterr) nil (irr-span) parstate)
         ((erp token & parstate) (read-token parstate))
         ((when (and (not (token-punctuatorp token "["))
                     (not (and token (token-case token :string)))))
          (b* ((parstate (if token (unread-token parstate) parstate)))
            (retok nil (irr-span) parstate)))
       ; [ or string
         (parstate (unread-token parstate))) ;
      (parse-asm-output-operands parstate))
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-asm-input-operand ((parstate parstatep))
    :returns (mv erp
                 (input asm-inputp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse an assembler input operand."
    (b* (((reterr) (irr-asm-input) (irr-span) parstate)
         ((erp token span parstate) (read-token parstate)))
      (cond
       ;; If token is an open square bracket, we have a name to parse,
       ;; followed by one or more string literals,
       ;; followed by a parenthesized expression.
       ((token-punctuatorp token "[") ; [
        (b* (((erp name & parstate) (read-identifier parstate)) ; [ name
             ((erp & parstate) (read-punctuator "]" parstate)) ; [ name ]
             ((erp token2 span2 parstate) (read-token parstate))
             ((unless (and token2 (token-case token2 :string)))
              (reterr-msg :where (position-to-msg (span->start span2))
                          :expected "a string literal"
                          :found (token-to-msg token2)))
             ;; [ name ] string
             (string (token-string->unwrap token2))
             ((erp strings & parstate) ; [ name ] string strings
              (parse-*-stringlit parstate))
             (constraint (cons string strings)) ; [ name ] constraint
             ((erp & parstate) ; [ name ] constraint (
              (read-punctuator "(" parstate))
             ((erp rvalue & parstate) ; [ name ] constraint ( expr
              (parse-expression parstate))
             ((erp last-span parstate) ; [ name ] constraint ( expr )
              (read-punctuator ")" parstate)))
          (retok (make-asm-input :name name
                                 :constraint constraint
                                 :rvalue rvalue)
                 (span-join span last-span)
                 parstate)))
       ;; Otherwise, we must have one or more string literals,
       ;; followed by a parenthesized expression.
       (t ; other
        (b* ((parstate (if token (unread-token parstate) parstate)) ;
             ((erp token2 span2 parstate) (read-token parstate))
             ((unless (and token2 (token-case token2 :string)))
              (reterr-msg :where (position-to-msg (span->start span2))
                          :expected "a string literal"
                          :found (token-to-msg token2)))
             ;; string
             (string (token-string->unwrap token2))
             ((erp strings & parstate) ; string strings
              (parse-*-stringlit parstate))
             (constraint (cons string strings)) ; constraint
             ((erp & parstate) ; constraint (
              (read-punctuator "(" parstate))
             ((erp rvalue & parstate) ; constraint ( expr
              (parse-expression parstate))
             ((erp last-span parstate) ; constraint ( expr )
              (read-punctuator ")" parstate)))
          (retok (make-asm-input :name nil
                                 :constraint constraint
                                 :rvalue rvalue)
                 (span-join span last-span)
                 parstate)))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-asm-input-operands ((parstate parstatep))
    :returns (mv erp
                 (inputs asm-input-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse one or more assembler input operands, separated by commas."
    :long
    (xdoc::topstring
     (xdoc::p
      "After parsing an assembler input operand,
       we check whether the following token is a comma,
       in which case there must be at least another assembler input operand,
       so we recursively parse one or more assembler input operands."))
    (b* (((reterr) nil (irr-span) parstate)
         (psize (parsize parstate))
         ((erp input span parstate) ; input
          (parse-asm-input-operand parstate))
         ((unless (mbt (<= (parsize parstate) (1- psize))))
          (reterr :impossible))
         ((erp token & parstate) (read-token parstate))
         ((unless (token-punctuatorp token ",")) ; input ,
          (b* ((parstate (if token (unread-token parstate) parstate)))
            (retok (list input) span parstate)))
         ((erp inputs last-span parstate) ; input , inputs
          (parse-asm-input-operands parstate)))
      (retok (cons input inputs)
             (span-join span last-span)
             parstate))
    :measure (two-nats-measure (parsize parstate) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-?-asm-input-operands ((parstate parstatep))
    :returns (mv erp
                 (inputs asm-input-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse zero or more assembler input operands, separated by commas."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the next token is an open square bracket or a string literal,
       there must be at least one assembler input operand,
       so we call the function that parses
       one or more assembler input operands.
       If the next token is not an open square bracket or a string literal,
       then there are no assembler input operands;
       we return an irrelevant span in this case,
       which callers do not use."))
    (b* (((reterr) nil (irr-span) parstate)
         ((erp token & parstate) (read-token parstate))
         ((when (and (not (token-punctuatorp token "["))
                     (not (and token (token-case token :string)))))
          (b* ((parstate (if token (unread-token parstate) parstate)))
            (retok nil (irr-span) parstate)))
       ; [ or string
         (parstate (unread-token parstate))) ;
      (parse-asm-input-operands parstate))
    :measure (two-nats-measure (parsize parstate) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-asm-statement ((first-span spanp)
                               (uscores keyword-uscores-p)
                               (parstate parstatep))
    :returns (mv erp
                 (asm asm-stmtp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
    :short "Parse an assembler statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called just after parsing the @('asm') (or variant) keyword.
       We pass its span to this function as @('first-span').
       We also pass information about the variant keyword."))
    (b* (((reterr) (irr-asm-stmt) (irr-span) parstate)
         ;; asm
         ((erp quals & parstate) ; asm [asmquals]
          (parse-*-asm-qualifier parstate))
         ((erp & parstate) ; asm [asmquals] (
          (read-punctuator "(" parstate))
         ((erp template & parstate) ; asm [asmquals] ( template
          (parse-*-stringlit parstate))
         ((erp token2 span2 parstate) (read-token parstate)))
      (cond
       ;; If token2 is a closed parenthesis,
       ;; we have reached the end of the assembler statement.
       ((token-punctuatorp token2 ")") ; asm [asmquals] ( template )
        (b* (((erp last-span parstate) (read-punctuator ";" parstate)))
          ;; asm [asmquals] ( template ) ;
          (retok (make-asm-stmt :uscores uscores
                                :quals quals
                                :template template
                                :num-colons 0
                                :outputs nil
                                :inputs nil
                                :clobbers nil
                                :labels nil)
                 (span-join first-span last-span)
                 parstate)))
       ;; If token2 is not a closed parenthesis,
       ;; it must be a colon, and we continue parsing.
       (t ; asm [asmquals] ( template other
        (b* (((unless (token-punctuatorp token2 ":"))
              (reterr-msg :where (position-to-msg (span->start span2))
                          :expected "a colon or a closed parenthesis"
                          :found (token-to-msg token2)))
             (psize (parsize parstate))
             ;; asm [asmquals] ( template :
             ((erp outputs & parstate)
              ;; asm [asmquals] ( template : [outputs]
              (parse-?-asm-output-operands parstate))
             ((unless (mbt (<= (parsize parstate) psize)))
              (reterr :impossible))
             ((erp token3 span3 parstate) (read-token parstate)))
          (cond
           ;; If token3 is a closed parenthesis,
           ;; we have reached the end of the assembler statement.
           ((token-punctuatorp token3 ")")
            ;; asm [asmquals] ( template : [outputs] )
            (b* (((erp last-span parstate)
                  ;; asm [asmquals] ( template : [outputs] ) ;
                  (read-punctuator ";" parstate)))
              (retok (make-asm-stmt :uscores uscores
                                    :quals quals
                                    :template template
                                    :num-colons 1
                                    :outputs outputs
                                    :inputs nil
                                    :clobbers nil
                                    :labels nil)
                     (span-join first-span last-span)
                     parstate)))
           ;; If token3 is not a closed parenthesis,
           ;; it must be a colon, and we continue parsing.
           (t ; asm [asmquals] ( template : [outputs] other
            (b* (((unless (token-punctuatorp token3 ":"))
                  (reterr-msg :where (position-to-msg (span->start span3))
                              :expected "a colon or a closed parenthesis"
                              :found (token-to-msg token3)))
                 ;; asm [asmquals] ( template : [outputs] :
                 ((erp inputs & parstate)
                  ;; asm [asmquals] ( template : [outputs] : [inputs]
                  (parse-?-asm-input-operands parstate))
                 ((erp token4 span4 parstate) (read-token parstate)))
              (cond
               ;; If token4 is a closed parenthesis,
               ;; we have reached the end of the assembler statement.
               ((token-punctuatorp token4 ")")
                ;; asm [asmquals] ( template : [outputs] : [inputs] )
                (b* (((erp last-span parstate)
                      ;; asm [asmquals] ( template : [outputs] : [inputs] ) ;
                      (read-punctuator ";" parstate)))
                  (retok (make-asm-stmt :uscores uscores
                                        :quals quals
                                        :template template
                                        :num-colons 2
                                        :outputs outputs
                                        :inputs inputs
                                        :clobbers nil
                                        :labels nil)
                         (span-join first-span last-span)
                         parstate)))
               ;; If token4 is not a closed parenthesis,
               ;; it must be a colon, and we continue parsing.
               (t ; asm [asmquals] ( template : [outputs] : [inputs] other
                (b* (((unless (token-punctuatorp token4 ":"))
                      (reterr-msg
                       :where (position-to-msg (span->start span4))
                       :expected "a colon or a closed parenthesis"
                       :found (token-to-msg token4)))
                     ;; asm [asmquals] ( template : [outputs] : [inputs] :
                     ((erp clobbers & parstate)
                      ;; asm [asmquals] ( template
                      ;; : [outputs] : [inputs] : [clobbers]
                      (parse-asm-clobbers parstate))
                     ((erp token5 span5 parstate) (read-token parstate)))
                  (cond
                   ;; If token5 is a closed parenthesis,
                   ;; we have reached the end of the assembler statement.
                   ((token-punctuatorp token5 ")")
                    ;; asm [asmquals] ( template
                    ;; : [outputs] : [inputs] : [clobbers] )
                    (b* (((erp last-span parstate)
                          ;; asm [asmquals] ( template
                          ;; : [outputs] : [inputs] : [clobbers] ) ;
                          (read-punctuator ";" parstate)))
                      (retok (make-asm-stmt :uscores uscores
                                            :quals quals
                                            :template template
                                            :num-colons 3
                                            :outputs outputs
                                            :inputs inputs
                                            :clobbers clobbers
                                            :labels nil)
                             (span-join first-span last-span)
                             parstate)))
                   ;; If token5 is not a closed parenthesis,
                   ;; it must be a colon, and we continue parsing.
                   (t
                    ;; asm [asmquals] ( template
                    ;; : [outputs] : [inputs] : [clobbers] other
                    (b* (((unless (token-punctuatorp token5 ":"))
                          (reterr-msg
                           :where (position-to-msg (span->start span5))
                           :expected "a colon or a closed parenthesis"
                           :found (token-to-msg token5)))
                         ;; asm [asmquals] ( template
                         ;; : [outputs] : [inputs] : [clobbers] :
                         ((erp labels & parstate)
                          ;; asm [asmquals] ( template
                          ;; : [outputs] : [inputs] : [clobbers] : [labels]
                          (parse-asm-goto-labels parstate))
                         ((erp & parstate)
                          ;; asm [asmquals] ( template
                          ;; : [outputs]
                          ;; : [inputs]
                          ;; : [clobbers]
                          ;; : [labels] )
                          (read-punctuator ")" parstate))
                         ((erp last-span parstate)
                          ;; asm [asmquals] ( template
                          ;; : [outputs]
                          ;; : [inputs]
                          ;; : [clobbers]
                          ;; : [labels] ) ;
                          (read-punctuator ";" parstate)))
                      (retok (make-asm-stmt :uscores uscores
                                            :quals quals
                                            :template template
                                            :num-colons 4
                                            :outputs outputs
                                            :inputs inputs
                                            :clobbers clobbers
                                            :labels labels)
                             (span-join first-span last-span)
                             parstate))))))))))))))
    :measure (two-nats-measure (parsize parstate) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-statement ((parstate parstatep))
    :returns (mv erp
                 (stmt stmtp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
       as required in [C17:6.8.4/3].")
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
              (retok (make-stmt-expr :expr? expr :info nil)
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
        (retok (make-stmt-expr :expr? nil :info nil) span parstate))
       ;; If token is the 'case' keyword,
       ;; we must have a labeled statement.
       ((token-keywordp token "case") ; case
        (b* ((psize (parsize parstate))
             ((erp cexpr & parstate) ; case cexpr
              (parse-constant-expression parstate))
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp token2 & parstate) (read-token parstate)))
          (cond
           ;; If token2 is '...', and GCC extensions are supported,
           ;; we have a range 'case' label.
           ((and (token-punctuatorp token2 "...") ; case cexpr ...
                 (parstate->gcc parstate))
            (b* ((psize (parsize parstate))
                 ((erp cexpr2 & parstate) ; case cexpr ... cexpr2
                  (parse-constant-expression parstate))
                 ((unless (mbt (<= (parsize parstate) (1- psize))))
                  (reterr :impossible))
                 ((erp & parstate)
                  (read-punctuator ":" parstate)) ; case cexpr ... cexpr2 :
                 ((erp stmt last-span parstate) ; case constexpr : stmt
                  (parse-statement parstate)))
              (retok (make-stmt-labeled :label (make-label-casexpr
                                                :expr cexpr
                                                :range? cexpr2)
                                        :stmt stmt)
                     (span-join span last-span)
                     parstate)))
           (t ; case cexpr other
            (b* ((parstate ; case cexpr
                  (if token2 (unread-token parstate) parstate))
                 ((erp & parstate)
                  (read-punctuator ":" parstate)) ; case cexpr :
                 ((erp stmt last-span parstate) ; case cexpr : stmt
                  (parse-statement parstate)))
              (retok (make-stmt-labeled :label (make-label-casexpr
                                                :expr cexpr
                                                :range? nil)
                                        :stmt stmt)
                     (span-join span last-span)
                     parstate))))))
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
              (retok (make-stmt-return :expr? expr :info nil)
                     (span-join span last-span)
                     parstate)))
           ;; If token2 is a semicolon, there is no expression.
           ((token-punctuatorp token2 ";") ; return ;
            (retok (make-stmt-return :expr? nil :info nil)
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
             (psize (parsize parstate))
             ((erp expr & parstate) (parse-expression parstate)) ; if ( expr
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
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
             (psize (parsize parstate))
             ((erp expr & parstate) (parse-expression parstate)) ; switch ( expr
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
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
             (psize (parsize parstate))
             ((erp expr & parstate) (parse-expression parstate)) ; while ( expr
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
             ((erp & parstate) (read-punctuator ")" parstate)) ; while ( expr )
             ((erp stmt last-span parstate) ; while ( expr ) stmt
              (parse-statement parstate)))
          (retok (make-stmt-while :test expr
                                  :body stmt)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the 'do' keyword, we have an iteration statement.
       ((token-keywordp token "do") ; do
        (b* ((psize (parsize parstate))
             ((erp stmt & parstate) (parse-statement parstate)) ; do stmt
             ((unless (mbt (<= (parsize parstate) (1- psize))))
              (reterr :impossible))
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
                     (psize (parsize parstate))
                     ((erp test-expr & parstate) ; for ( ; expr
                      (parse-expression parstate))
                     ((unless (mbt (<= (parsize parstate) (1- psize))))
                      (reterr :impossible))
                     ((erp & parstate) ; for ( ; expr ;
                      (read-punctuator ";" parstate))
                     ((erp token4 span4 parstate) (read-token parstate)))
                  (cond
                   ;; If token4 may start an expression,
                   ;; we must have an update expression.
                   ((token-expression-start-p token4) ; for ( ; expr ; expr...
                    (b* ((parstate (unread-token parstate)) ; for ( ; expr ;
                         (psize (parsize parstate))
                         ((erp next-expr & parstate) ; for ( ; expr ; expr
                          (parse-expression parstate))
                         ((unless (mbt (<= (parsize parstate) (1- psize))))
                          (reterr :impossible))
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
                         (psize (parsize parstate))
                         ((erp next-expr & parstate) ; for ( ; ; expr
                          (parse-expression parstate))
                         ((unless (mbt (<= (parsize parstate) (1- psize))))
                          (reterr :impossible))
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
                 (psize (parsize parstate))
                 ((erp decl/stmt & parstate) ; for ( decl/stmt
                  (parse-declaration-or-statement parstate))
                 ((unless (mbt (<= (parsize parstate) (1- psize))))
                  (reterr :impossible)))
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
                        (psize (parsize parstate))
                        ((erp test-expr & parstate) ; for ( ; expr
                         (parse-expression parstate))
                        ((unless (mbt (<= (parsize parstate) (1- psize))))
                         (reterr :impossible))
                        ((erp & parstate) ; for ( ; expr ;
                         (read-punctuator ";" parstate))
                        ((erp token4 span4 parstate) (read-token parstate)))
                     (cond
                      ;; If token4 may start an expression,
                      ;; we must have an update expression.
                      ((token-expression-start-p token4)
                       ;; for ( ; expr ; expr...
                       (b* ((parstate (unread-token parstate)) ; for ( ; expr ;
                            (psize (parsize parstate))
                            ((erp next-expr & parstate) ; for ( ; expr ; expr
                             (parse-expression parstate))
                            ((unless (mbt (<= (parsize parstate) (1- psize))))
                             (reterr :impossible))
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
                            (psize (parsize parstate))
                            ((erp next-expr & parstate) ; for ( ; ; expr
                             (parse-expression parstate))
                            ((unless (mbt (<= (parsize parstate) (1- psize))))
                             (reterr :impossible))
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
                        (psize (parsize parstate))
                        ((erp test-expr & parstate) ; for ( ; expr
                         (parse-expression parstate))
                        ((unless (mbt (<= (parsize parstate) (1- psize))))
                         (reterr :impossible))
                        ((erp & parstate) ; for ( ; expr ;
                         (read-punctuator ";" parstate))
                        ((erp token4 span4 parstate) (read-token parstate)))
                     (cond
                      ;; If token4 may start an expression,
                      ;; we must have an update expression.
                      ((token-expression-start-p token4)
                       ;; for ( ; expr ; expr...
                       (b* ((parstate (unread-token parstate)) ; for ( ; expr ;
                            (psize (parsize parstate))
                            ((erp next-expr & parstate) ; for ( ; expr ; expr
                             (parse-expression parstate))
                            ((unless (mbt (<= (parsize parstate) (1- psize))))
                             (reterr :impossible))
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
                            (psize (parsize parstate))
                            ((erp next-expr & parstate) ; for ( ; ; expr
                             (parse-expression parstate))
                            ((unless (mbt (<= (parsize parstate) (1- psize))))
                             (reterr :impossible))
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
                        (psize (parsize parstate))
                        ((erp test-expr & parstate) ; for ( ; expr
                         (parse-expression parstate))
                        ((unless (mbt (<= (parsize parstate) (1- psize))))
                         (reterr :impossible))
                        ((erp & parstate) ; for ( ; expr ;
                         (read-punctuator ";" parstate))
                        ((erp token4 span4 parstate) (read-token parstate)))
                     (cond
                      ;; If token4 may start an expression,
                      ;; we must have an update expression.
                      ((token-expression-start-p token4)
                       ;; for ( ; expr ; expr...
                       (b* ((parstate (unread-token parstate)) ; for ( ; expr ;
                            (psize (parsize parstate))
                            ((erp next-expr & parstate) ; for ( ; expr ; expr
                             (parse-expression parstate))
                            ((unless (mbt (<= (parsize parstate) (1- psize))))
                             (reterr :impossible))
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
                            (psize (parsize parstate))
                            ((erp next-expr & parstate) ; for ( ; ; expr
                             (parse-expression parstate))
                            ((unless (mbt (<= (parsize parstate) (1- psize))))
                             (reterr :impossible))
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
          (retok (make-stmt-expr :expr? expr :info nil)
                 (span-join span last-span)
                 parstate)))
       ;; If token is the 'asm' (or variant) keyword,
       ;; which can only happen if GCC extensions are supported,
       ;; we parse an assembler statement.
       ((or (token-keywordp token "asm") ; asm
            (token-keywordp token "__asm") ; __asm
            (token-keywordp token "__asm__")) ; __asm__
        (b* ((uscores
              (cond ((token-keywordp token "asm") (keyword-uscores-none))
                    ((token-keywordp token "__asm") (keyword-uscores-start))
                    ((token-keywordp token "__asm__") (keyword-uscores-both))))
             ((erp asm span parstate)
              (parse-asm-statement span uscores parstate)))
          (retok (stmt-asm asm) span parstate)))
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
    :measure (two-nats-measure (parsize parstate) 17))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-block-item ((parstate parstatep))
    :returns (mv erp
                 (item block-itemp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
              (retok (make-block-item-stmt :stmt stmt :info nil)
                     span
                     parstate)))
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
               (retok (make-block-item-decl :decl decl/stmt.unwrap :info nil)
                      span
                      parstate)
               ;; If we parse an unambiguous statement,
               ;; we return a block item that is a statement.
               :stmt
               (retok (make-block-item-stmt
                       :stmt (make-stmt-expr :expr? decl/stmt.unwrap :info nil)
                       :info nil)
                      span
                      parstate)
               ;; If we parse an ambiguous declaration or statement,
               ;; we return an ambiguous block item.
               :ambig
               (retok (block-item-ambig decl/stmt.unwrap)
                      span
                      parstate)))))))
       ;; If token may start a declaration specifier,
       ;; or token is the '_Static_assert' keyword,
       ;; we must have a declaration,
       ;; because we have already considered the case of an identifier above.
       ((or (token-declaration-specifier-start-p token) ; declspec...
            (token-keywordp token "_Static_assert")) ; _Static_assert
        (b* ((parstate (unread-token parstate)) ;
             ((erp decl span parstate) ; decl
              (parse-declaration parstate)))
          (retok (make-block-item-decl :decl decl :info nil) span parstate)))
       ;; Otherwise, we must have a statement.
       (t ; other
        (b* ((parstate (if token (unread-token parstate) parstate)) ;
             ((erp stmt span parstate) ; stmt
              (parse-statement parstate)))
          (retok (make-block-item-stmt :stmt stmt :info nil) span parstate)))))
    :measure (two-nats-measure (parsize parstate) 18))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define parse-block-item-list ((parstate parstatep))
    :returns (mv erp
                 (items block-item-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :parents (parser parse-exprs/decls/stmts)
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
    :measure (two-nats-measure (parsize parstate) 19))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :prepwork ((local (in-theory (disable acl2::member-of-cons)))) ; for speed

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable nfix fix)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual parsize-of-parse-exprs/decls/stmts-uncond
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
    (defret parsize-of-parse-member-designor-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-member-designor)
    (defret parsize-of-parse-member-designor-rest-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-member-designor-rest)
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
    (defret parsize-of-parse-type-qualifier-or-attribute-specifier-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-type-qualifier-or-attribute-specifier)
    (defret parsize-of-parse-type-qualifier-and-attribute-specifier-list-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-type-qualifier-and-attribute-specifier-list)
    (defret parsize-of-parse-pointer-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-pointer)
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
    (defret parsize-of-parse-unary-expression-or-parenthesized-type-name-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-unary-expression-or-parenthesized-type-name)
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
    (defret parsize-of-parse-init-declarator-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-init-declarator)
    (defret parsize-of-parse-init-declarator-list-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-init-declarator-list)
    (defret parsize-of-parse-declaration-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-declaration)
    (defret parsize-of-parse-declaration-list-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-declaration-list)
    (defret parsize-of-parse-declaration-or-statement-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-declaration-or-statement)
    (defret parsize-of-parse-asm-output-operand-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-asm-output-operand)
    (defret parsize-of-parse-asm-output-operands
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-asm-output-operands)
    (defret parsize-of-parse-?-asm-output-operands-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-?-asm-output-operands)
    (defret parsize-of-parse-asm-input-operand-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-asm-input-operand)
    (defret parsize-of-parse-asm-input-operands
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-asm-input-operands)
    (defret parsize-of-parse-?-asm-input-operands-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-?-asm-input-operands)
    (defret parsize-of-parse-asm-statement-uncond
      (<= (parsize new-parstate)
          (parsize parstate))
      :rule-classes :linear
      :fn parse-asm-statement)
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
    :hints
    (("Goal" :in-theory (enable fix nfix))
     (cond
      ((acl2::occur-lst '(acl2::flag-is 'parse-expression)
                        clause)
       '(:expand (parse-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-expression-rest)
                        clause)
       '(:expand (parse-expression-rest prev-expr prev-span parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-assignment-expression)
                        clause)
       '(:expand (parse-assignment-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-conditional-expression)
                        clause)
       '(:expand (parse-conditional-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-logical-or-expression)
                        clause)
       '(:expand (parse-logical-or-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-logical-or-expression-rest)
                        clause)
       '(:expand (parse-logical-or-expression-rest prev-expr
                                                   prev-span
                                                   parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-logical-and-expression)
                        clause)
       '(:expand (parse-logical-and-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-logical-and-expression-rest)
                        clause)
       '(:expand (parse-logical-and-expression-rest prev-expr
                                                    prev-span
                                                    parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-inclusive-or-expression)
                        clause)
       '(:expand (parse-inclusive-or-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-inclusive-or-expression-rest)
                        clause)
       '(:expand (parse-inclusive-or-expression-rest prev-expr
                                                     prev-span
                                                     parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-exclusive-or-expression)
                        clause)
       '(:expand (parse-exclusive-or-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-exclusive-or-expression-rest)
                        clause)
       '(:expand (parse-exclusive-or-expression-rest prev-expr
                                                     prev-span
                                                     parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-and-expression)
                        clause)
       '(:expand (parse-and-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-and-expression-rest)
                        clause)
       '(:expand (parse-and-expression-rest prev-expr
                                            prev-span
                                            parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-equality-expression)
                        clause)
       '(:expand (parse-equality-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-equality-expression-rest)
                        clause)
       '(:expand (parse-equality-expression-rest prev-expr
                                                 prev-span
                                                 parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-relational-expression)
                        clause)
       '(:expand (parse-relational-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-relational-expression-rest)
                        clause)
       '(:expand (parse-relational-expression-rest prev-expr
                                                   prev-span
                                                   parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-shift-expression)
                        clause)
       '(:expand (parse-shift-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-shift-expression-rest)
                        clause)
       '(:expand (parse-shift-expression-rest prev-expr
                                              prev-span
                                              parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-additive-expression)
                        clause)
       '(:expand (parse-additive-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-additive-expression-rest)
                        clause)
       '(:expand (parse-additive-expression-rest prev-expr
                                                 prev-span
                                                 parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-multiplicative-expression)
                        clause)
       '(:expand (parse-multiplicative-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-multiplicative-expression-rest)
                        clause)
       '(:expand (parse-multiplicative-expression-rest prev-expr
                                                       prev-span
                                                       parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-cast-expression)
                        clause)
       '(:expand (parse-cast-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-unary-expression)
                        clause)
       '(:expand (parse-unary-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-postfix-expression)
                        clause)
       '(:expand (parse-postfix-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-postfix-expression-rest)
                        clause)
       '(:expand (parse-postfix-expression-rest prev-expr
                                                prev-span
                                                parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-argument-expressions)
                        clause)
       '(:expand (parse-argument-expressions parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-argument-expressions-rest)
                        clause)
       '(:expand (parse-argument-expressions-rest prev-exprs
                                                  prev-span
                                                  parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-primary-expression)
                        clause)
       '(:expand (parse-primary-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-compound-literal)
                        clause)
       '(:expand (parse-compound-literal tyname first-span parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-generic-association)
                        clause)
       '(:expand (parse-generic-association parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-generic-associations-rest)
                        clause)
       '(:expand (parse-generic-associations-rest prev-genassocs
                                                  prev-span
                                                  parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-constant-expression)
                        clause)
       '(:expand (parse-constant-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-static-assert-declaration)
                        clause)
       '(:expand (parse-static-assert-declaration first-span parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-designator)
                        clause)
       '(:expand (parse-designator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-designator-list)
                        clause)
       '(:expand (parse-designator-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-initializer)
                        clause)
       '(:expand (parse-initializer parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-designation?-initializer)
                        clause)
       '(:expand (parse-designation?-initializer parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-initializer-list)
                        clause)
       '(:expand (parse-initializer-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-enumerator)
                        clause)
       '(:expand (parse-enumerator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-enumerator-list)
                        clause)
       '(:expand (parse-enumerator-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-specifier/qualifier)
                        clause)
       '(:expand (parse-specifier/qualifier parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-specifier-qualifier-list)
                        clause)
       '(:expand ((parse-specifier-qualifier-list tyspec-seenp parstate)
                  (parse-specifier-qualifier-list nil parstate))))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration-specifier)
                        clause)
       '(:expand (parse-declaration-specifier parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration-specifiers)
                        clause)
       '(:expand ((parse-declaration-specifiers tyspec-seenp parstate)
                  (parse-declaration-specifiers nil parstate))))
      ((acl2::occur-lst '(acl2::flag-is 'parse-struct-or-union-specifier)
                        clause)
       '(:expand (parse-struct-or-union-specifier structp
                                                  struct/union-span
                                                  parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-enum-specifier)
                        clause)
       '(:expand (parse-enum-specifier first-span parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-alignment-specifier)
                        clause)
       '(:expand (parse-alignment-specifier first-span parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-abstract-declarator)
                        clause)
       '(:expand (parse-abstract-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-abstract-declarator-rest)
                        clause)
       '(:expand (parse-direct-abstract-declarator-rest prev-dirabsdeclor
                                                        prev-span
                                                        parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-array/function-abstract-declarator)
                        clause)
       '(:expand (parse-array/function-abstract-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-array/function-declarator)
                        clause)
       '(:expand (parse-array/function-declarator prev-dirdeclor
                                                  prev-span
                                                  parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-abstract-declarator)
                        clause)
       '(:expand (parse-direct-abstract-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-declarator)
                        clause)
       '(:expand (parse-direct-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-declarator-rest)
                        clause)
       '(:expand (parse-direct-declarator-rest prev-dirdeclor
                                               prev-span
                                               parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declarator)
                        clause)
       '(:expand (parse-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-struct-declarator)
                        clause)
       '(:expand (parse-struct-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-struct-declarator-list)
                        clause)
       '(:expand (parse-struct-declarator-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-struct-declaration)
                        clause)
       '(:expand (parse-struct-declaration parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-struct-declaration-list)
                        clause)
       '(:expand (parse-struct-declaration-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-parameter-declaration)
                        clause)
       '(:expand (parse-parameter-declaration parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-parameter-declaration-list)
                        clause)
       '(:expand (parse-parameter-declaration-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-type-name)
                        clause)
       '(:expand (parse-type-name parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-expression-or-type-name)
                        clause)
       '(:expand (parse-expression-or-type-name add-parens-p parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declarator-or-abstract-declarator)
                        clause)
       '(:expand (parse-declarator-or-abstract-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-attribute-parameters)
                        clause)
       '(:expand (parse-attribute-parameters parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-attribute)
                        clause)
       '(:expand (parse-attribute parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-attribute-list)
                        clause)
       '(:expand (parse-attribute-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-attribute-specifier)
                        clause)
       '(:expand (parse-attribute-specifier uscores first-span parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-*-attribute-specifier)
                        clause)
       '(:expand (parse-*-attribute-specifier parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-init-declarator)
                        clause)
       '(:expand (parse-init-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-init-declarator-list)
                        clause)
       '(:expand (parse-init-declarator-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration)
                        clause)
       '(:expand (parse-declaration parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration-list)
                        clause)
       '(:expand (parse-declaration-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration-or-statement)
                        clause)
       '(:expand (parse-declaration-or-statement parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-asm-output-operand)
                        clause)
       '(:expand (parse-asm-output-operand parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-asm-output-operands)
                        clause)
       '(:expand (parse-asm-output-operands parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-?-asm-output-operands)
                        clause)
       '(:expand (parse-?-asm-output-operands parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-asm-input-operand)
                        clause)
       '(:expand (parse-asm-input-operand parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-asm-input-operands)
                        clause)
       '(:expand (parse-asm-input-operands parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-?-asm-input-operands)
                        clause)
       '(:expand (parse-?-asm-input-operands parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-statement)
                        clause)
       '(:expand (parse-statement parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-block-item)
                        clause)
       '(:expand (parse-block-item parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-block-item-list)
                        clause)
       '(:expand (parse-block-item-list parstate))))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual parsize-of-parse-exprs/decls/stmts-cond
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
    (defret parsize-of-parse-member-designor-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-member-designor)
    (defret parsize-of-parse-member-designor-rest-cond
      t
      :rule-classes nil
      :fn parse-member-designor-rest)
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
    (defret parsize-of-parse-type-qualifier-or-attribute-specifier-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-type-qualifier-or-attribute-specifier)
    (defret parsize-of-parse-type-qualifier-and-attribute-specifier-list-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-type-qualifier-and-attribute-specifier-list)
    (defret parsize-of-parse-pointer-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-pointer)
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
    (defret parsize-of-parse-unary-expression-or-parenthesized-type-name-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-unary-expression-or-parenthesized-type-name)
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
    (defret parsize-of-parse-init-declarator-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-init-declarator)
    (defret parsize-of-parse-init-declarator-list-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-init-declarator-list)
    (defret parsize-of-parse-declaration-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-declaration)
    (defret parsize-of-parse-declaration-list-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-declaration-list)
    (defret parsize-of-parse-declaration-or-statement-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-declaration-or-statement)
    (defret parsize-of-parse-asm-output-operand-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-asm-output-operand)
    (defret parsize-of-parse-asm-output-operands-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-asm-output-operands)
    (defret parsize-of-parse-?-asm-output-operands-cond
      t
      :rule-classes nil
      :fn parse-?-asm-output-operands)
    (defret parsize-of-parse-asm-input-operand-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-asm-input-operand)
    (defret parsize-of-parse-asm-input-operands-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-asm-input-operands)
    (defret parsize-of-parse-?-asm-input-operands-cond
      t
      :rule-classes nil
      :fn parse-?-asm-input-operands)
    (defret parsize-of-parse-statement-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-statement)
    (defret parsize-of-parse-asm-statement-cond
      (implies (not erp)
               (<= (parsize new-parstate)
                   (1- (parsize parstate))))
      :rule-classes :linear
      :fn parse-asm-statement)
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
    :hints
    (("Goal" :in-theory (enable fix nfix))
     (cond
      ((acl2::occur-lst '(acl2::flag-is 'parse-expression)
                        clause)
       '(:expand (parse-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-assignment-expression)
                        clause)
       '(:expand (parse-assignment-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-conditional-expression)
                        clause)
       '(:expand (parse-conditional-expression parstate)))
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
      ((acl2::occur-lst '(acl2::flag-is 'parse-unary-expression)
                        clause)
       '(:expand (parse-unary-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-primary-expression)
                        clause)
       '(:expand (parse-primary-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-generic-association)
                        clause)
       '(:expand (parse-generic-association parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-member-designor)
                        clause)
       '(:expand (parse-member-designor parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-compound-literal)
                        clause)
       '(:expand (parse-compound-literal tyname first-span parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-constant-expression)
                        clause)
       '(:expand (parse-constant-expression parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-static-assert-declaration)
                        clause)
       '(:expand (parse-static-assert-declaration first-span parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-abstract-declarator)
                        clause)
       '(:expand (parse-abstract-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-abstract-declarator)
                        clause)
       '(:expand (parse-direct-abstract-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-direct-declarator)
                        clause)
       '(:expand (parse-direct-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-designator)
                        clause)
       '(:expand (parse-designator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-designator-list)
                        clause)
       '(:expand (parse-designator-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-initializer)
                        clause)
       '(:expand (parse-initializer parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-designation?-initializer)
                        clause)
       '(:expand (parse-designation?-initializer parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-initializer-list)
                        clause)
       '(:expand (parse-initializer-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-enumerator)
                        clause)
       '(:expand (parse-enumerator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-enumerator-list)
                        clause)
       '(:expand (parse-enumerator-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-specifier/qualifier)
                        clause)
       '(:expand (parse-specifier/qualifier parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-specifier-qualifier-list)
                        clause)
       '(:expand ((parse-specifier-qualifier-list tyspec-seenp parstate)
                  (parse-specifier-qualifier-list nil parstate))))
      ((acl2::occur-lst '(acl2::flag-is 'parse-statement)
                        clause)
       '(:expand (parse-statement parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration-specifier)
                        clause)
       '(:expand (parse-declaration-specifier parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration-specifiers)
                        clause)
       '(:expand ((parse-declaration-specifiers tyspec-seenp parstate)
                  (parse-declaration-specifiers nil parstate))))
      ((acl2::occur-lst '(acl2::flag-is 'parse-struct-or-union-specifier)
                        clause)
       '(:expand (parse-struct-or-union-specifier structp
                                                  struct/union-span
                                                  parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-attribute-specifier)
                        clause)
       '(:expand (parse-attribute-specifier uscores first-span parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-enum-specifier)
                        clause)
       '(:expand (parse-enum-specifier first-span parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-alignment-specifier)
                        clause)
       '(:expand (parse-alignment-specifier first-span parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-array/function-abstract-declarator)
                        clause)
       '(:expand (parse-array/function-abstract-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-array/function-declarator)
                        clause)
       '(:expand (parse-array/function-declarator prev-dirdeclor
                                                  prev-span
                                                  parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declarator)
                        clause)
       '(:expand (parse-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-struct-declarator)
                        clause)
       '(:expand (parse-struct-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-struct-declarator-list)
                        clause)
       '(:expand (parse-struct-declarator-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-struct-declaration)
                        clause)
       '(:expand (parse-struct-declaration parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-struct-declaration-list)
                        clause)
       '(:expand (parse-struct-declaration-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-parameter-declaration)
                        clause)
       '(:expand (parse-parameter-declaration parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-parameter-declaration-list)
                        clause)
       '(:expand (parse-parameter-declaration-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-type-name)
                        clause)
       '(:expand (parse-type-name parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-expression-or-type-name)
                        clause)
       '(:expand (parse-expression-or-type-name add-parens-p parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declarator-or-abstract-declarator)
                        clause)
       '(:expand (parse-declarator-or-abstract-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-attribute-parameters)
                        clause)
       '(:expand (parse-attribute-parameters parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-attribute)
                        clause)
       '(:expand (parse-attribute parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-attribute-list)
                        clause)
       '(:expand (parse-attribute-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-attribute-specifier)
                        clause)
       '(:expand (parse-attribute-specifier uscores first-span parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-init-declarator)
                        clause)
       '(:expand (parse-init-declarator parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-init-declarator-list)
                        clause)
       '(:expand (parse-init-declarator-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration)
                        clause)
       '(:expand (parse-declaration parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration-list)
                        clause)
       '(:expand (parse-declaration-list parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-declaration-or-statement)
                        clause)
       '(:expand (parse-declaration-or-statement parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-asm-output-operand)
                        clause)
       '(:expand (parse-asm-output-operand parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-asm-output-operands)
                        clause)
       '(:expand (parse-asm-output-operands parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-asm-input-operand)
                        clause)
       '(:expand (parse-asm-input-operand parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-asm-input-operands)
                        clause)
       '(:expand (parse-asm-input-operands parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-block-item)
                        clause)
       '(:expand (parse-block-item parstate)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-block-item-list)
                        clause)
       '(:expand (parse-block-item-list parstate))))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret dirabsdeclor-declor?-nil-p-of-parse-array/function-abstract-declarator
    (implies (not erp)
             (dirabsdeclor-declor?-nil-p dirabsdeclor))
    :hints (("Goal"
             :in-theory (enable dirabsdeclor-declor?-nil-p)
             :expand (parse-array/function-abstract-declarator parstate)))
    :fn parse-array/function-abstract-declarator)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards parse-expression
    :hints (("Goal" :in-theory (e/d (acl2::member-of-cons
                                     token-additive-operator-p)
                                    ((:e tau-system))))))) ; for speed

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
     either an empty one (a lone semicolon),
     or a function definition,
     which starts with a non-empty sequence of declaration specifiers,
     or a declaration,
     which also starts with a non-empty sequence of declaration specifiers,
     unless it is a static assert declaration,
     which starts with the keyword @('_Static_assert').")
   (xdoc::p
    "The case of an empty external declaration is easy,
     because it starts (and ends) with a semicolon.
     This is only allowed if GCC extensions are supported.")
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
    "If GCC extensions are supported, we must also take into account
     the possible presence of attributes and assembler name specifiers,
     as well as of an @('__external__') keyword.")
   (xdoc::p
    "We also handle the GCC extension of allowing assembler statements
     as external declarations, which are easy to recognize."))
  (b* (((reterr) (irr-extdecl) (irr-span) parstate)
       ((erp token span parstate) (read-token parstate)))
    (cond
     ;; If token is a semicolon,
     ;; we have an empty external declaration.
     ((and (token-punctuatorp token ";") ; ;
           (parstate->gcc parstate))
      (retok (extdecl-empty) span parstate))
     ;; If token is the keyword '_Static_assert',
     ;; we have a static assertion declaration.
     ((token-keywordp token "_Static_assert") ; _Static_assert
      (b* (((erp statassert span parstate) ; statassert
            (parse-static-assert-declaration span parstate)))
        (retok (extdecl-decl (decl-statassert statassert)) span parstate)))
     ;; If token is the 'asm' or variant keyword
     ;; (which can only happen if GCC extensions are enabled),
     ;; we have an assembler statement.
     ((or (token-keywordp token "asm") ; asm
          (token-keywordp token "__asm") ; __asm
          (token-keywordp token "__asm__")) ; __asm__
      (b* ((uscores
            (cond ((token-keywordp token "asm") (keyword-uscores-none))
                  ((token-keywordp token "__asm") (keyword-uscores-start))
                  ((token-keywordp token "__asm__") (keyword-uscores-both))))
           ((erp asm span parstate)
            (parse-asm-statement span uscores parstate)))
        (retok (extdecl-asm asm) span parstate)))
     ;; Otherwise, we must have a list of one or more declaration specifiers,
     ;; possibly preceded by an '__extension__' keyword
     ;; if GCC extensions are supported.
     (t
      (b* (((mv extension parstate)
            (if (token-keywordp token "__extension__")
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
                                               :init nil))
                 (span-join span span2)
                 parstate))
         ;; If token2 is anything else,
         ;; we put it back and parse a declarator, which must be there.
         ;; We also parse, if present, an assembler name specifier
         ;; and a sequence of zero or more attribute specifiers.
         (t ; [__extension__] declspecs other
          (b* ((parstate ; [__extension__] declspecs
                (if token2 (unread-token parstate) parstate))
               ((erp declor & parstate) ; [__extension__] declspecs declor
                (parse-declarator parstate))
               ((erp asmspec? & parstate)
                ;; [__extension__] declspecs declor [asmspec]
                (parse-?-asm-name-specifier parstate))
               ((erp attrspecs & parstate)
                ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                (parse-*-attribute-specifier parstate))
               ((erp token3 span3 parstate) (read-token parstate)))
            (cond
             ;; If token3 is a semicolon,
             ;; we have a declaration with one declarator without initializer.
             ((token-punctuatorp token3 ";")
              ;; [__extension__] declspecs declor [asmspec] [attrspecs] ;
              (retok (extdecl-decl (make-decl-decl
                                    :extension extension
                                    :specs declspecs
                                    :init (list (make-initdeclor
                                                 :declor declor
                                                 :asm? asmspec?
                                                 :attribs attrspecs
                                                 :init? nil
                                                 :info nil))))
                     (span-join span span3)
                     parstate))
             ;; If token3 is an equal sign,
             ;; we have a declaration with at least one initializer declarator.
             ;; We parse the initializer for the initializer declarator.
             ((token-punctuatorp token3 "=")
              ;; [__extension__] declspecs declor [asmspec] [attrspecs] =
              (b* (((erp initer & parstate)
                    ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                    ;;   = initer
                    (parse-initializer parstate))
                   (initdeclor (make-initdeclor :declor declor
                                                :asm? asmspec?
                                                :attribs attrspecs
                                                :init? initer
                                                :info nil))
                   ((erp token4 span4 parstate) (read-token parstate)))
                (cond
                 ;; If token4 is a semicolon,
                 ;; we have reached the end of the declaration.
                 ((token-punctuatorp token4 ";")
                  ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                  ;;   = initer ;
                  (retok (extdecl-decl (make-decl-decl
                                        :extension extension
                                        :specs declspecs
                                        :init (list initdeclor)))
                         (span-join span span4)
                         parstate))
                 ;; If token4 is a comma,
                 ;; we must have additiona initializer declarators.
                 ((token-punctuatorp token4 ",")
                  ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                  ;;   = initer ,
                  (b* (((erp initdeclors & parstate)
                        ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                        ;;   = initer , initdeclors
                        (parse-init-declarator-list parstate))
                       ((erp last-span parstate)
                        ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                        ;;   = initer , initdeclors ;
                        (read-punctuator ";" parstate)))
                    (retok (extdecl-decl (make-decl-decl
                                          :extension extension
                                          :specs declspecs
                                          :init (cons initdeclor initdeclors)))
                           (span-join span last-span)
                           parstate)))
                 ;; If token4 is anything else, it is an error.
                 (t
                  ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                  ;;   = initer other
                  (reterr-msg :where (position-to-msg (span->start span4))
                              :expected "a semicolon or a comma"
                              :found (token-to-msg token4))))))
             ;; If token3 is a comma,
             ;; we must have a declaration
             ;; with two or more initializer declarators.
             ((token-punctuatorp token3 ",")
              ;; [__extension__] declspecs declor [asmspec] [attrspecs] ,
              (b* ((initdeclor (make-initdeclor :declor declor
                                                :asm? asmspec?
                                                :attribs attrspecs
                                                :init? nil
                                                :info nil))
                   ((erp initdeclors & parstate)
                    ;; [__extension__] declspecs declor [asmspec] [attrspecs] ,
                    ;;   initdeclors
                    (parse-init-declarator-list parstate))
                   ((erp last-span parstate)
                    ;; [__extension__] declspecs declor [asmspec] [attrspecs] ,
                    ;;   initdeclors ;
                    (read-punctuator ";" parstate)))
                (retok (extdecl-decl (make-decl-decl
                                      :extension extension
                                      :specs declspecs
                                      :init (cons initdeclor initdeclors)))
                       (span-join span last-span)
                       parstate)))
             ;; If token3 is an open curly brace,
             ;; we must have a function definition,
             ;; where the curly brace starts the body, which we parse.
             ((token-punctuatorp token3 "{")
              ;; [__extension__] declspecs declor [asmspec] [attrspecs] {
              (b* (((erp token4 span4 parstate) (read-token parstate)))
                (cond
                 ;; If token4 is a closed curly brace,
                 ;; we have an empty compound statement as the body.
                 ((token-punctuatorp token4 "}")
                  ;; [__extension__] declspecs declor [asmspec] [attrspecs] { }
                  (retok (extdecl-fundef
                          (make-fundef :extension extension
                                       :spec declspecs
                                       :declor declor
                                       :asm? asmspec?
                                       :attribs attrspecs
                                       :decls nil
                                       :body nil
                                       :info nil))
                         (span-join span span4)
                         parstate))
                 ;; If token4 is anything else,
                 ;; we put it back (if any) and we parse block items,
                 ;; followed by a closed curly brace.
                 (t
                  ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                  ;;   { other
                  (b* ((parstate (if token4 (unread-token parstate) parstate))
                       ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                       ;;   {
                       ((erp items & parstate)
                        ;; [__extension__] declspecs declor
                        ;;   [asmspec] [attrspecs]
                        ;;   { items
                        (parse-block-item-list parstate))
                       ((erp last-span parstate)
                        ;; [__extension__] declspecs declor
                        ;;   [asmspec] [attrspecs]
                        ;;   { items }
                        (read-punctuator "}" parstate)))
                    (retok (extdecl-fundef
                            (make-fundef :extension extension
                                         :spec declspecs
                                         :declor declor
                                         :asm? asmspec?
                                         :attribs attrspecs
                                         :decls nil
                                         :body items
                                         :info nil))
                           (span-join span last-span)
                           parstate))))))
             ;; If token3 is anything else,
             ;; we must have one or more declarations, which we parse.
             ;; Then we parse the compound statement.
             (t ; [__extension__] declspecs declor [asmspec] [attrspecs] other
              (b* ((parstate
                    ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                    (if token3 (unread-token parstate) parstate))
                   ((erp decls & parstate)
                    ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                    ;;   decls
                    (parse-declaration-list parstate))
                   ((erp & parstate)
                    ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                    ;;   decls {
                    (read-punctuator "{" parstate))
                   ((erp items & parstate)
                    ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                    ;;   decls { items
                    (parse-block-item-list parstate))
                   ((erp last-span parstate)
                    ;; [__extension__] declspecs declor [asmspec] [attrspecs]
                    ;;   decls { items }
                    (read-punctuator "}" parstate)))
                (retok (extdecl-fundef
                        (make-fundef :extension extension
                                     :spec declspecs
                                     :declor declor
                                     :asm? asmspec?
                                     :attribs attrspecs
                                     :decls decls
                                     :body items
                                     :info nil))
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
     as prescribed in [C17:5.1.1.2/2].
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
    (retok (make-transunit :decls extdecls :info nil) parstate))

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
