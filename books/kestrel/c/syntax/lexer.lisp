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
(include-book "keywords")
(include-book "abstract-syntax-irrelevants")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (:e tau-system))))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Library extensions.

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

(defxdoc+ lexer
  :parents (parser)
  :short "Lexer component of the parser."
  :long
  (xdoc::topstring
   (xdoc::p
    "This builds on the @(see reader):
     it turns read characters into lexemes.
     It provides a layer upon which the (rest of) the parser is built."))
  :order-subtopics t
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
