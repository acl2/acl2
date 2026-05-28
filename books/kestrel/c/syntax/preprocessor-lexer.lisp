; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocessor-states")
(include-book "preprocessor-messages")
(include-book "preprocessor-reader")
(include-book "abstract-syntax-irrelevants")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Library extensions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defxdoc+ preprocessor-lexer
  :parents (preprocessor)
  :short "Lexer component of the preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to the parser's @(see lexer),
     but for the preprocessor."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Macros to concisely express theorems saying that
; the lexing functions do not modify some PPSTATE stobj components.

(local ; for non-recursive FN
 (defmacro defret-same-lexemes (fn)
   `(defret ,(packn-pos (list 'ppstate->lexemes-of- fn) fn)
      (equal (ppstate->lexemes new-ppstate)
             (ppstate->lexemes ppstate)))))

(local ; for singly recursive FN
 (defmacro defret-rec-same-lexemes (fn)
   `(defret ,(packn-pos (list 'ppstate->lexemes-of- fn) fn)
      (equal (ppstate->lexemes new-ppstate)
             (ppstate->lexemes ppstate))
      :hints (("Goal" :induct t)))))

(local ; used by the macro below
 (defun defret-mut-same-lexemes-fn (fns)
   (b* (((when (endp fns)) nil)
        (fn (car fns))
        (event `(defret ,(packn-pos (list 'ppstate->lexemes-of- fn) fn)
                  (equal (ppstate->lexemes new-ppstate)
                         (ppstate->lexemes ppstate))
                  :fn ,fn))
        (events (defret-mut-same-lexemes-fn (cdr fns))))
     (cons event events))))

(local ; for mutually recursive FNS
 (defmacro defret-mut-same-lexemes (name fns &key hints)
   `(defret-mutual ,name
      ,@(defret-mut-same-lexemes-fn fns)
      ,@(and hints (list :hints hints)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-identifier ((first-char (unsigned-byte-p 8 first-char))
                         (first-pos positionp)
                         (ppstate ppstatep))
  :guard (or (and (utf8-<= (char-code #\A) first-char)
                  (utf8-<= first-char (char-code #\Z)))
             (and (utf8-<= (char-code #\a) first-char)
                  (utf8-<= first-char (char-code #\z)))
             (utf8-= first-char (char-code #\_)))
  :returns (mv erp
               (lexeme plexemep)
               (span spanp)
               (new-ppstate ppstatep))
  :short "Lex an identifier during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called after the first character of the identifier
     has been already read;
     that character is passed to this function,
     along with its position.")
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
     (more precisely, lists of that).")
   (xdoc::p
    "Although the ABNF grammar rules for C17 and C23 identifiers vary slightly,
     they are equivalent:
     an identifier consists of a letter or underscore
     followed by zero or more letters, digits, and underscores.")
   (xdoc::p
    "We return an identifier lexeme.
     The provenance list of the identifier is set to @('nil'),
     because the identifier is lexed directly from the file;
     it is not generated by any macro expansion."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) (irr-plexeme) (irr-span) ppstate)
       ((erp rest-chars last-pos ppstate)
        (plex-identifier-loop first-pos ppstate))
       (span (make-span :start first-pos :end last-pos))
       (chars (cons first-char rest-chars))
       (string (acl2::nats=>string chars)))
    (retok (make-plexeme-ident :ident string :provenance nil) span ppstate))

  :prepwork

  ((define plex-identifier-loop ((pos-so-far positionp) (ppstate ppstatep))
     :returns (mv erp
                  (chars (unsigned-byte-listp 8 chars)
                         :hints (("Goal"
                                  :induct t
                                  :in-theory (enable unsigned-byte-p
                                                     integer-range-p))))
                  (last-pos positionp)
                  (new-ppstate ppstatep))
     :parents nil
     (b* ((ppstate (ppstate-fix ppstate))
          ((reterr) nil (irr-position) ppstate)
          ((erp char pos ppstate) (read-pchar ppstate))
          ((when (not char))
           (retok nil (position-fix pos-so-far) ppstate))
          ((unless ; A-Z a-z 0-9 _
               (or (and (utf8-<= (char-code #\A) char)
                        (utf8-<= char (char-code #\Z)))
                   (and (utf8-<= (char-code #\a) char)
                        (utf8-<= char (char-code #\z)))
                   (and (utf8-<= (char-code #\0) char)
                        (utf8-<= char (char-code #\9)))
                   (utf8-= char (char-code #\_))))
           (b* ((ppstate (unread-pchar ppstate)))
             (retok nil (position-fix pos-so-far) ppstate)))
          ((erp chars last-pos ppstate)
           (plex-identifier-loop pos ppstate)))
       (retok (cons char chars) last-pos ppstate))
     :measure (ppstate->size ppstate)
     :verify-guards nil ; done below

     ///

     (verify-guards plex-identifier-loop)

     (defret-rec-same-lexemes plex-identifier-loop)

     (defret ppstate->size-of-plex-identifier-loop-uncond
       (<= (ppstate->size new-ppstate)
           (ppstate->size ppstate))
       :rule-classes :linear
       :hints (("Goal" :induct t :in-theory (enable fix))))))

  ///

  (defret-same-lexemes plex-identifier)

  (defret ppstate->size-of-plex-identifier-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-pp-number ((dot booleanp)
                        (digit dec-digit-char-p)
                        (first-pos positionp)
                        ppstate)
  :returns (mv erp
               (lexeme plexemep)
               (span spanp)
               (new-ppstate ppstatep))
  :short "Lex a preprocessing number during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called after the initial digit, or dot followed by digit,
     has been read; see the grammar rule for @('pp-number').
     The @('dot') input says whether the preprocessing number starts with a dot,
     and the @('digit') input is the first digit (preceded by @('.') or not).")
   (xdoc::p
    "The initial digit, or dot followed by digit,
     already forms a preprocessing number.
     We keep reading characters
     so long as we can ``extend'' the preprocessing number,
     according to the grammar rule.
     Eventually we return the full preprocessing number and the full span.")
   (xdoc::p
    "If we are in a C23 dialect,
     we accept single quotes, according to the ABNF grammar.
     We handle that via the @('squotep') flag the is carried through the loop:
     it is @('t') iff a single quote was just read before the next character;
     it is @('nil') otherwise."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) (irr-plexeme) (irr-span) ppstate)
       (digit (str::dec-digit-char-fix digit))
       (initial-pnumber (if dot
                            (pnumber-dot-digit digit)
                          (pnumber-digit digit)))
       ((erp final-pnumber last-pos ppstate)
        (plex-pp-number-loop initial-pnumber first-pos nil ppstate)))
    (retok (plexeme-number final-pnumber)
           (make-span :start first-pos :end last-pos)
           ppstate))

  :prepwork

  ((define plex-pp-number-loop ((current-pnumber pnumberp)
                                (current-pos positionp)
                                (squotep booleanp)
                                ppstate)
     :returns (mv erp
                  (final-pnumber pnumberp)
                  (last-pos positionp)
                  (new-ppstate ppstatep))
     :parents nil
     (b* ((ppstate (ppstate-fix ppstate))
          ((reterr) (irr-pnumber) (irr-position) ppstate)
          ((erp char pos ppstate) (read-pchar ppstate)))
       (cond
        ((not char) ; pp-number ['] EOF
         (cond
          (squotep ; pp-number ' EOF
           (reterr-msg :where pos
                       :expected "a letter or digit or underscore"
                       :found "end of file"))
          (t ; pp-number EOF
           (retok (pnumber-fix current-pnumber)
                  (position-fix current-pos)
                  ppstate))))
        ((utf8-= char (char-code #\')) ; pp-number ['] '
         (if (c::standard-case
              (c::dialect->std (ienv->dialect (ppstate->ienv ppstate)))
              :c23)
             (cond (squotep ; pp-number ' '
                    (reterr-msg :where pos
                                :expected "a letter or digit or underscore"
                                :found "a single quote ~
                                        immediately following ~
                                        a single quote"))
                   (t ; pp-number '
                    (plex-pp-number-loop current-pnumber pos t ppstate)))
           (reterr-msg :where pos
                       :expected "a letter or digit or underscore"
                       :found "a single quote")))
        ((and (utf8-<= (char-code #\0) char)
              (utf8-<= char (char-code #\9))) ; pp-number ['] digit
         (plex-pp-number-loop (make-pnumber-number-digit
                               :number current-pnumber
                               :squotep squotep
                               :digit (code-char char))
                              pos
                              nil
                              ppstate))
        ((utf8-= char (char-code #\e)) ; pp-number ['] e
         (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
           (cond
            ((and char2 (utf8-= char2 (char-code #\+))) ; pp-number ['] e +
             (cond
              (squotep ; pp-number ' e +
               (reterr-msg :where pos
                           :expected "a letter or digit or underscore ~
                                      or single quote"
                           :found "a plus after an 'e' after a single quote"))
              (t ; pp-number e +
               (plex-pp-number-loop (make-pnumber-number-locase-e-sign
                                     :number current-pnumber
                                     :sign (sign-plus))
                                    pos2
                                    nil
                                    ppstate))))
            ((and char2 (utf8-= char2 (char-code #\-))) ; pp-number ['] e -
             (cond
              (squotep ; pp-number ' e -
               (reterr-msg :where pos
                           :expected "a letter or digit or underscore ~
                                      or single quote"
                           :found "a minus after an 'e' after a single quote"))
              (t ; pp-number e -
               (plex-pp-number-loop (make-pnumber-number-locase-e-sign
                                     :number current-pnumber
                                     :sign (sign-minus))
                                    pos2
                                    nil
                                    ppstate))))
            (t ; pp-number ['] e other
             (b* ((ppstate ; pp-number ['] e
                   (if char2 (unread-pchar ppstate) ppstate)))
               (plex-pp-number-loop (make-pnumber-number-nondigit
                                     :number current-pnumber
                                     :squotep squotep
                                     :nondigit #\e)
                                    pos
                                    nil
                                    ppstate))))))
        ((utf8-= char (char-code #\E)) ; pp-number ['] E
         (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
           (cond
            ((and char2 (utf8-= char2 (char-code #\+))) ; pp-number ['] E +
             (cond
              (squotep ; pp-number ' E +
               (reterr-msg :where pos
                           :expected "a letter or digit or underscore ~
                                      or single quote"
                           :found "a plus after an 'E' after a single quote"))
              (t ; pp-number E +
               (plex-pp-number-loop (make-pnumber-number-upcase-e-sign
                                     :number current-pnumber
                                     :sign (sign-plus))
                                    pos2
                                    nil
                                    ppstate))))
            ((and char2 (utf8-= char2 (char-code #\-))) ; pp-number ['] E -
             (cond
              (squotep ; pp-number ' E -
               (reterr-msg :where pos
                           :expected "a letter or digit or underscore ~
                                      or single quote"
                           :found "a minus after an 'E' after a single quote"))
              (t ; pp-number E -
               (plex-pp-number-loop (make-pnumber-number-upcase-e-sign
                                     :number current-pnumber
                                     :sign (sign-minus))
                                    pos2
                                    nil
                                    ppstate))))
            (t ; pp-number ['] E other
             (b* ((ppstate ; pp-number ['] E
                   (if char2 (unread-pchar ppstate) ppstate)))
               (plex-pp-number-loop (make-pnumber-number-nondigit
                                     :number current-pnumber
                                     :squotep squotep
                                     :nondigit #\E)
                                    pos
                                    nil
                                    ppstate))))))
        ((utf8-= char (char-code #\p)) ; pp-number ['] p
         (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
           (cond
            ((and char2 (utf8-= char2 (char-code #\+))) ; pp-number ['] p +
             (cond
              (squotep ; pp-number ' p +
               (reterr-msg :where pos
                           :expected "a letter or digit or underscore ~
                                      or single quote"
                           :found "a plus after a 'p' after a single quote"))
              (t ; pp-number p +
               (plex-pp-number-loop (make-pnumber-number-locase-p-sign
                                     :number current-pnumber
                                     :sign (sign-plus))
                                    pos2
                                    nil
                                    ppstate))))
            ((and char2 (utf8-= char2 (char-code #\-))) ; pp-number ['] p -
             (cond
              (squotep ; pp-number ' p -
               (reterr-msg :where pos
                           :expected "a letter or digit or underscore ~
                                      or single quote"
                           :found "a minus after a 'p' after a single quote"))
              (t ; pp-number p -
               (plex-pp-number-loop (make-pnumber-number-locase-p-sign
                                     :number current-pnumber
                                     :sign (sign-minus))
                                    pos2
                                    nil
                                    ppstate))))
            (t ; pp-number ['] p other
             (b* ((ppstate ; pp-number ['] p
                   (if char2 (unread-pchar ppstate) ppstate)))
               (plex-pp-number-loop (make-pnumber-number-nondigit
                                     :number current-pnumber
                                     :squotep squotep
                                     :nondigit #\p)
                                    pos
                                    nil
                                    ppstate))))))
        ((utf8-= char (char-code #\P)) ; pp-number ['] P
         (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
           (cond
            ((and char2 (utf8-= char2 (char-code #\+))) ; pp-number ['] P +
             (cond
              (squotep ; pp-number ' P +
               (reterr-msg :where pos
                           :expected "a letter or digit or underscore ~
                                      or single quote"
                           :found "a plus after a 'P' after a single quote"))
              (t ; pp-number P +
               (plex-pp-number-loop (make-pnumber-number-upcase-p-sign
                                     :number current-pnumber
                                     :sign (sign-plus))
                                    pos2
                                    nil
                                    ppstate))))
            ((and char2 (utf8-= char2 (char-code #\-))) ; pp-number ['] P -
             (cond
              (squotep ; pp-number ' P -
               (reterr-msg :where pos
                           :expected "a letter or digit or underscore ~
                                      or single quote"
                           :found "a minus after a 'P' after a single quote"))
              (t ; pp-number P -
               (plex-pp-number-loop (make-pnumber-number-upcase-p-sign
                                     :number current-pnumber
                                     :sign (sign-minus))
                                    pos2
                                    nil
                                    ppstate))))
            (t ; pp-number ['] P other
             (b* ((ppstate ; pp-number ['] P
                   (if char2 (unread-pchar ppstate) ppstate)))
               (plex-pp-number-loop (make-pnumber-number-nondigit
                                     :number current-pnumber
                                     :squotep squotep
                                     :nondigit #\P)
                                    pos
                                    nil
                                    ppstate))))))
        ((or (and (utf8-<= (char-code #\A) char)
                  (utf8-<= char (char-code #\Z)))
             (and (utf8-<= (char-code #\a) char)
                  (utf8-<= char (char-code #\z)))
             (utf8-= char (char-code #\_))) ; pp-number ['] nondigit
         (plex-pp-number-loop (make-pnumber-number-nondigit
                               :number current-pnumber
                               :squotep squotep
                               :nondigit (code-char char))
                              pos
                              nil
                              ppstate))
        ((utf8-= char (char-code #\.)) ; pp-number ['] .
         (cond
          (squotep ; pp-number ' .
           (reterr-msg :where pos
                       :expected "a letter or digit or underscore"
                       :found "a dot after a single quote"))
          (t ; pp-number .
           (plex-pp-number-loop (make-pnumber-number-dot
                                 :number current-pnumber)
                                pos
                                nil
                                ppstate))))
        (t ; pp-number ['] other
         (b* ((ppstate ; pp-number [']
               (if char (unread-pchar ppstate) ppstate)))
           (cond
            (squotep ; pp-number '
             (reterr-msg :where pos
                         :expected "a letter or digit or underscore"
                         :found (char-to-msg char)))
            (t ; pp-number
             (retok (pnumber-fix current-pnumber)
                    (position-fix current-pos)
                    ppstate)))))))
     :no-function nil
     :measure (ppstate->size ppstate)
     :guard-hints (("Goal" :in-theory (enable dec-digit-char-p
                                              str::letter/uscore-char-p)))

     ///

     (defret-rec-same-lexemes plex-pp-number-loop)

     (defret ppstate->size-of-plex-pp-number-loop-uncond
       (<= (ppstate->size new-ppstate)
           (ppstate->size ppstate))
       :rule-classes :linear
       :hints (("Goal" :induct t :in-theory (enable fix))))))

  ///

  (defret-same-lexemes plex-pp-number)

  (defret ppstate->size-of-plex-pp-number-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-hexadecimal-digit ((ppstate ppstatep))
  :returns (mv erp
               (hexdig hex-digit-char-p
                       :hints
                       (("Goal" :in-theory (enable hex-digit-char-p
                                                   unsigned-byte-p
                                                   integer-range-p))))
               (pos positionp)
               (new-ppstate ppstatep))
  :short "Lex a hexadecimal digit during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a hexadecimal digit:
     if the character is not a hexadecimal digit, it is an error.
     If the next character is present and is a hexadecimal digit,
     we return the corresponding ACL2 character,
     along with its position in the file."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) #\0 (irr-position) ppstate)
       ((erp char pos ppstate) (read-pchar ppstate))
       ((when (not char))
        (reterr-msg :where pos
                    :expected "a hexadecimal digit"
                    :found (char-to-msg char)))
       ((unless (or (and (utf8-<= (char-code #\0) char) ; 0
                         (utf8-<= char (char-code #\9))) ; 9
                    (and (utf8-<= (char-code #\A) char) ; A
                         (utf8-<= char (char-code #\F))) ; F
                    (and (utf8-<= (char-code #\a) char) ; a
                         (utf8-<= char (char-code #\f))))) ; f
        (reterr-msg :where pos
                    :expected "a hexadecimal digit"
                    :found (char-to-msg char))))
    (retok (code-char char) pos ppstate))
  :no-function nil

  ///

  (defret-same-lexemes plex-hexadecimal-digit)

  (defret ppstate->size-of-plex-hexadecimal-digit-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear)

  (defret ppstate->size-of-plex-hexadecimal-digit-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-hex-quad ((ppstate ppstatep))
  :returns (mv erp
               (quad hex-quad-p)
               (last-pos positionp)
               (new-ppstate ppstatep))
  :short "Lex a quadruple of hexadecimal digits during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect four hexadecimal digits,
     so we call @(tsee plex-hexadecimal-digit) four times.
     We return the position of the last one."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) (irr-hex-quad) (irr-position) ppstate)
       ((erp hexdig1 & ppstate) (plex-hexadecimal-digit ppstate))
       ((erp hexdig2 & ppstate) (plex-hexadecimal-digit ppstate))
       ((erp hexdig3 & ppstate) (plex-hexadecimal-digit ppstate))
       ((erp hexdig4 pos ppstate) (plex-hexadecimal-digit ppstate)))
    (retok (make-hex-quad :1st hexdig1
                          :2nd hexdig2
                          :3rd hexdig3
                          :4th hexdig4)
           pos
           ppstate))

  ///

  (defret-same-lexemes plex-hex-quad)

  (defret ppstate->size-of-plex-hex-quad-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear)

  (defret ppstate->size-of-plex-hex-quad-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-*-hexadecimal-digit ((pos-so-far positionp) (ppstate ppstatep))
  :returns (mv erp
               (hexdigs hex-digit-char-listp
                        :hints
                        (("Goal"
                          :induct t
                          :in-theory (enable plex-*-hexadecimal-digit
                                             hex-digit-char-p
                                             unsigned-byte-p
                                             integer-range-p))))
               (last-pos positionp)
               (next-pos positionp)
               (new-ppstate ppstatep))
  :short "Lex zero or more hexadecimal digits, as many as available,
          during preprocessing."
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
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil (irr-position) (irr-position) ppstate)
       ((erp char pos ppstate) (read-pchar ppstate))
       ((when (not char))
        (retok nil (position-fix pos-so-far) pos ppstate))
       ((unless (or (and (utf8-<= (char-code #\0) char) ; 0
                         (utf8-<= char (char-code #\9))) ; 9
                    (and (utf8-<= (char-code #\A) char) ; A
                         (utf8-<= char (char-code #\F))) ; F
                    (and (utf8-<= (char-code #\a) char) ; a
                         (utf8-<= char (char-code #\f))))) ; f
        (b* ((ppstate (unread-pchar ppstate)))
          (retok nil (position-fix pos-so-far) pos ppstate)))
       (hexdig (code-char char))
       ((erp hexdigs last-pos next-pos ppstate)
        (plex-*-hexadecimal-digit pos ppstate)))
    (retok (cons hexdig hexdigs) last-pos next-pos ppstate))
  :measure (ppstate->size ppstate)
  :verify-guards :after-returns

  ///

  (more-returns
   (hexdigs true-listp
            :rule-classes :type-prescription))

  (defret-rec-same-lexemes plex-*-hexadecimal-digit)

  (defret ppstate->size-of-plex-*-hexadecimal-digit-uncond
    (<= (ppstate->size new-ppstate)
        (- (ppstate->size ppstate)
           (len hexdigs)))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable fix len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-escape-sequence ((ppstate ppstatep))
  :returns (mv erp
               (escape escapep)
               (last-pos positionp)
               (new-ppstate ppstatep))
  :short "Lex an escape sequence during preprocessing."
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
     we return the simple escape.
     If GCC or Clang extensions are enabled,
     we also allow the @('\\%') escape;
     see the ABNF grammar for an explanation of it.")
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
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) (irr-escape) (irr-position) ppstate)
       ((erp char pos ppstate) (read-pchar ppstate)))
    (cond
     ((not char)
      (reterr-msg :where pos
                  :expected "a single quote ~
                             or a double quote ~
                             or a question mark ~
                             or a backslash ~
                             or a letter in {a, b, f, n, r, t, v, u, U, x} ~
                             or an octal digit"
                  :found (char-to-msg char)))
     ((utf8-= char (char-code #\')) ; \ '
      (retok (escape-simple (simple-escape-squote)) pos ppstate))
     ((utf8-= char (char-code #\")) ; \ "
      (retok (escape-simple (simple-escape-dquote)) pos ppstate))
     ((utf8-= char (char-code #\?)) ; \ ?
      (retok (escape-simple (simple-escape-qmark)) pos ppstate))
     ((utf8-= char (char-code #\\)) ; \ \
      (retok (escape-simple (simple-escape-bslash)) pos ppstate))
     ((utf8-= char (char-code #\a)) ; \ a
      (retok (escape-simple (simple-escape-a)) pos ppstate))
     ((utf8-= char (char-code #\b)) ; \ b
      (retok (escape-simple (simple-escape-b)) pos ppstate))
     ((utf8-= char (char-code #\f)) ; \ f
      (retok (escape-simple (simple-escape-f)) pos ppstate))
     ((utf8-= char (char-code #\n)) ; \ n
      (retok (escape-simple (simple-escape-n)) pos ppstate))
     ((utf8-= char (char-code #\r)) ; \ r
      (retok (escape-simple (simple-escape-r)) pos ppstate))
     ((utf8-= char (char-code #\t)) ; \ t
      (retok (escape-simple (simple-escape-t)) pos ppstate))
     ((utf8-= char (char-code #\v)) ; \ v
      (retok (escape-simple (simple-escape-v)) pos ppstate))
     ((and (utf8-= char (char-code #\%)) ; \ %
           (ppstate->gcc/clang ppstate))
      (retok (escape-simple (simple-escape-percent)) pos ppstate))
     ((and (utf8-<= (char-code #\0) char)
           (utf8-<= char (char-code #\7))) ; \ octdig
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((and char2
               (utf8-<= (char-code #\0) char2)
               (utf8-<= char2 (char-code #\7))) ; \ octdig octdig
          (b* (((erp char3 pos3 ppstate) (read-pchar ppstate)))
            (cond
             ((and char3
                   (utf8-<= (char-code #\0) char3)
                   (utf8-<= char3 (char-code #\7))) ; \ octdig octdig octdig
              (retok (escape-oct (oct-escape-three (code-char char)
                                                   (code-char char2)
                                                   (code-char char3)))
                     pos3
                     ppstate))
             (t ; \ octdig \octdig other
              (b* ((ppstate
                    ;; \ octdig octdig
                    (if char3 (unread-pchar ppstate) ppstate)))
                (retok (escape-oct (oct-escape-two (code-char char)
                                                   (code-char char2)))
                       pos2
                       ppstate))))))
         (t ; \ octdig other
          (b* ((ppstate (if char2 (unread-pchar ppstate) ppstate))) ; \octdig
            (retok (escape-oct (oct-escape-one (code-char char)))
                   pos
                   ppstate))))))
     ((utf8-= char (char-code #\x))
      (b* (((erp hexdigs last-pos next-pos ppstate)
            (plex-*-hexadecimal-digit pos ppstate)))
        (if hexdigs
            (retok (escape-hex hexdigs) last-pos ppstate)
          (reterr-msg :where next-pos
                      :expected "one or more hexadecimal digits"
                      :found "none"))))
     ((utf8-= char (char-code #\u))
      (b* (((erp quad pos ppstate) (plex-hex-quad ppstate)))
        (retok (escape-univ (univ-char-name-locase-u quad)) pos ppstate)))
     ((utf8-= char (char-code #\U))
      (b* (((erp quad1 & ppstate) (plex-hex-quad ppstate))
           ((erp quad2 pos ppstate) (plex-hex-quad ppstate)))
        (retok (escape-univ (make-univ-char-name-upcase-u :quad1 quad1
                                                          :quad2 quad2))
               pos
               ppstate)))
     (t
      (reterr-msg :where pos
                  :expected "a single quote ~
                             or a double quote ~
                             or a question mark ~
                             or a backslash ~
                             or a letter in {a, b, f, n, r, t, v, u, U, x} ~
                             or an octal digit"
                  :found (char-to-msg char)))))
  :guard-hints (("Goal" :in-theory (enable oct-digit-char-p
                                           unsigned-byte-p
                                           integer-range-p)))
  :no-function nil

  ///

  (defret-same-lexemes plex-escape-sequence)

  (defret ppstate->size-of-plex-escape-sequence-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear)

  (defret ppstate->size-of-plex-escape-sequence-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-*-c-char ((ppstate ppstatep))
  :returns (mv erp
               (cchars c-char-listp)
               (closing-squote-pos positionp)
               (new-ppstate ppstatep))
  :short "Lex zero or more characters and escape sequences
          in a character constant,
          during preprocessing."
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
     It is also an error if the character is a LF or CR (new line).
     If the character is a single quote, we end the recursion and return.
     If the character is a backslah,
     we attempt to read an escape sequence,
     then we read zero or more additional characters and escape sequences,
     and we combine them with the escape sequence.
     In all other cases,
     we take the character as is,
     we read zero or more additional characters and escape sequences,
     and we combine them with the character."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil (irr-position) ppstate)
       ((erp char pos ppstate) (read-pchar ppstate))
       ((unless char)
        (reterr-msg :where pos
                    :expected "an escape sequence or ~
                               any character other than ~
                               single quote or backslash or new-line"
                    :found (char-to-msg char)))
       ((when (utf8-= char (char-code #\'))) ; '
        (retok nil pos ppstate))
       ((when (or (utf8-= char 10) (utf8-= char 13))) ; new line
        (reterr-msg :where pos
                    :expected "an escape sequence or ~
                               any character other than ~
                               single quote or backslash or new-line"
                    :found (char-to-msg char)))
       ((erp cchar & ppstate)
        (if (utf8-= char (char-code #\\)) ; \
            (b* (((erp escape pos ppstate) (plex-escape-sequence ppstate))
                 (cchar (c-char-escape escape)))
              (retok cchar pos ppstate))
          (b* ((cchar (c-char-char char)))
            (retok cchar pos ppstate))))
       ((erp cchars closing-squote-pos ppstate) (plex-*-c-char ppstate)))
    (retok (cons cchar cchars) closing-squote-pos ppstate))
  :measure (ppstate->size ppstate)
  :verify-guards :after-returns
  :no-function nil

  ///

  (defret-rec-same-lexemes plex-*-c-char)

  (defret ppstate->size-of-plex-*-c-char-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-plex-*-c-char-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (- (ppstate->size ppstate)
                        (len cchars)))))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable fix len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-*-s-char ((ppstate ppstatep))
  :returns (mv erp
               (schars s-char-listp)
               (closing-dquote-pos positionp)
               (new-ppstate ppstatep))
  :short "Lex zero or more characters and escape sequences
          in a string literal,
          during preprocessing."
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
     It is also an error if the character is a LF or CR (new line).
     If the character is a double quote, we end the recursion and return.
     If the character is a backslah,
     we attempt to read an escape sequence,
     then we read zero or more additional characters and escape sequences,
     and we combine them with the escape sequence.
     In all other cases,
     we take the character as is,
     we read zero or more additional characters and escape sequences,
     and we combine them with the character."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil (irr-position) ppstate)
       ((erp char pos ppstate) (read-pchar ppstate))
       ((unless char)
        (reterr-msg :where pos
                    :expected "an escape sequence or ~
                               any character other than ~
                               double quote or backslash"
                    :found (char-to-msg char)))
       ((when (utf8-= char (char-code #\"))) ; "
        (retok nil pos ppstate))
       ((when (or (utf8-= char 10) (utf8-= char 13))) ; new line
        (reterr-msg :where pos
                    :expected "an escape sequence or ~
                               any character other than ~
                               double quote or backslash"
                    :found (char-to-msg char)))
       ((erp schar & ppstate)
        (if (utf8-= char (char-code #\\)) ; \
            (b* (((erp escape pos ppstate) (plex-escape-sequence ppstate))
                 (schar (s-char-escape escape)))
              (retok schar pos ppstate))
          (b* ((schar (s-char-char char)))
            (retok schar pos ppstate))))
       ((erp schars closing-dquote-pos ppstate) (plex-*-s-char ppstate)))
    (retok (cons schar schars) closing-dquote-pos ppstate))
  :measure (ppstate->size ppstate)
  :verify-guards :after-returns
  :no-function nil

  ///

  (defret-rec-same-lexemes plex-*-s-char)

  (defret ppstate->size-of-plex-*-s-char-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-plex-*-s-char-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (- (ppstate->size ppstate)
                        (len schars)))))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable len fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-*-h-char ((ppstate ppstatep))
  :returns (mv erp
               (hchars h-char-listp)
               (closing-angle-pos positionp)
               (new-ppstate ppstatep))
  :short "Lex zero or more characters
          in a header name between angle brackets,
          during preprocessing."
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
     It is also an error if the character is a LF or CR (new line).
     If the character is a closing angle bracket,
     we end the recursion and return.
     In all other cases,
     we take the character as is,
     we read zero or more additional characters and escape sequences,
     and we combine them with the character."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil (irr-position) ppstate)
       ((erp char pos ppstate) (read-pchar ppstate))
       ((unless char)
        (reterr-msg :where pos
                    :expected "any character other than ~
                               greater-than or new-line"
                    :found (char-to-msg char)))
       ((when (utf8-= char (char-code #\>))) ; >
        (retok nil pos ppstate))
       ((when (or (utf8-= char 10) (utf8-= char 13))) ; new line
        (reterr-msg :where pos
                    :expected "any character other than ~
                               greater-than or new-line"
                    :found (char-to-msg char)))
       (hchar (h-char char))
       ((erp hchars closing-angle-pos ppstate) (plex-*-h-char ppstate)))
    (retok (cons hchar hchars) closing-angle-pos ppstate))
  :measure (ppstate->size ppstate)
  :verify-guards :after-returns
  :no-function nil

  ///

  (defret-rec-same-lexemes plex-*-h-char)

  (defret ppstate->size-of-plex-*-h-char-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-plex-*-h-char-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (- (ppstate->size ppstate)
                        (len hchars)))))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable fix len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-*-q-char ((ppstate ppstatep))
  :returns (mv erp
               (qchars q-char-listp)
               (closing-dquote-pos positionp)
               (new-ppstate ppstatep))
  :short "Lex zero or more characters
          in a header name between double quotes,
          during preprocessing."
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
     It is also an error if the character is a LF or CR (new line).
     If the character is a closing double quote,
     we end the recursion and return.
     In all other cases,
     we take the character as is,
     we read zero or more additional characters and escape sequences,
     and we combine them with the character."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil (irr-position) ppstate)
       ((erp char pos ppstate) (read-pchar ppstate))
       ((unless char)
        (reterr-msg :where pos
                    :expected "any character other than ~
                               greater-than or new-line"
                    :found (char-to-msg char)))
       ((when (utf8-= char (char-code #\"))) ; "
        (retok nil pos ppstate))
       ((when (or (utf8-= char 10) (utf8-= char 13))) ; new line
        (reterr-msg :where pos
                    :expected "any character other than ~
                               greater-than or new-line"
                    :found (char-to-msg char)))
       (qchar (q-char char))
       ((erp qchars closing-dquote-pos ppstate) (plex-*-q-char ppstate)))
    (retok (cons qchar qchars) closing-dquote-pos ppstate))
  :measure (ppstate->size ppstate)
  :verify-guards :after-returns
  :no-function nil

  ///

  (defret-rec-same-lexemes plex-*-q-char)

  (defret ppstate->size-of-plex-*-q-char-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-plex-*-q-char-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (- (ppstate->size ppstate)
                        (len qchars)))))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable fix len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-character-constant ((eprefix? eprefix-optionp)
                                 (first-pos positionp)
                                 (ppstate ppstatep))
  :returns (mv erp
               (lexeme plexemep)
               (span spanp)
               (new-ppstate ppstatep))
  :short "Lex a character constant during preprocessing."
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
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) (irr-plexeme) (irr-span) ppstate)
       ((erp cchars closing-squote-pos ppstate) (plex-*-c-char ppstate))
       (span (make-span :start first-pos :end closing-squote-pos))
       ((unless cchars)
        (reterr-msg :where closing-squote-pos
                    :expected "one or more characters and escape sequences"
                    :found "none")))
    (retok (plexeme-char (cconst eprefix? cchars)) span ppstate))
  :no-function nil

  ///

  (defret-same-lexemes plex-character-constant)

  (defret ppstate->size-of-plex-character-constant-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear)

  (defret ppstate->size-of-plex-character-constant-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-string-literal ((eprefix? eprefix-optionp)
                             (first-pos positionp)
                             (ppstate ppstatep))
  :returns (mv erp
               (lexeme plexemep)
               (span spanp)
               (new-ppstate ppstatep))
  :short "Lex a string literal during preprocessing."
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
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) (irr-plexeme) (irr-span) ppstate)
       ((erp schars closing-dquote-pos ppstate) (plex-*-s-char ppstate))
       (span (make-span :start first-pos :end closing-dquote-pos)))
    (retok (plexeme-string (stringlit eprefix? schars)) span ppstate))

  ///

  (defret-same-lexemes plex-string-literal)

  (defret ppstate->size-of-plex-string-literal-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear)

  (defret ppstate->size-of-plex-string-literal-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-header-name ((ppstate ppstatep))
  :returns (mv erp
               (lexeme plexemep)
               (span spanp)
               (new-ppstate ppstatep))
  :short "Lex a header name during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a header name.
     We read the next character, which must be present.
     Then we read the two kinds of header names,
     based on whether the next character is greater-than or double quote.
     If it is neither, lexing fails."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) (irr-plexeme) (irr-span) ppstate)
       ((erp char first-pos ppstate) (read-pchar ppstate)))
    (cond
     ((not char)
      (reterr-msg :where first-pos
                  :expected "a greater-than ~
                             or a double quote"
                  :found (char-to-msg char)))
     ((utf8-= char (char-code #\<)) ; <
      (b* (((erp hchars closing-angle-pos ppstate) (plex-*-h-char ppstate))
           (span (make-span :start first-pos :end closing-angle-pos))
           ((unless hchars)
            (reterr-msg :where closing-angle-pos
                        :expected "one or more characters"
                        :found "none")))
        (retok (plexeme-header (header-name-angles hchars)) span ppstate)))
     ((utf8-= char (char-code #\")) ; "
      (b* (((erp qchars closing-dquote-pos ppstate) (plex-*-q-char ppstate))
           (span (make-span :start first-pos :end closing-dquote-pos))
           ((unless qchars)
            (reterr-msg :where closing-dquote-pos
                        :expected "one or more characters"
                        :found "none")))
        (retok (plexeme-header (header-name-quotes qchars)) span ppstate)))
     (t ; other
      (reterr-msg :where first-pos
                  :expected "a greater-than ~
                             or a double quote"
                  :found (char-to-msg char)))))
  :no-function nil

  ///

  (defret-same-lexemes plex-header-name)

  (defret ppstate->size-of-plex-header-name-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear)

  (defret ppstate->size-of-plex-header-name-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-block-comment ((first-pos positionp) (ppstate ppstatep))
  :returns (mv erp
               (lexeme plexemep)
               (span spanp)
               (new-ppstate ppstatep))
  :short "Lex a block comment during preprocessing."
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
     In case of success, we return a comment lexeme.
     The span of the comment is calculated from
     the first position (of the @('/') in @('/*')),
     passed to this function,
     and the last position (of the @('/') in the closing @('*/')),
     returned by the loop function.")
   (xdoc::p
    "We collect the content of the comment,
     i.e. the characters between @('/*') and @('*/') (excluding both);
     this content goes into the lexeme.
     @('plex-rest-of-block-comment-after-star') is always called
     just after a @('*') has been read;
     the addition of that @('*') to the content is deferred
     until it is established that the @('*') is not part of
     the closing @('*/');
     see the comments interspersed with the code."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) (irr-plexeme) (irr-span) ppstate)
       ((erp content last-pos ppstate)
        (plex-rest-of-block-comment first-pos ppstate)))
    (retok (plexeme-block-comment content)
           (make-span :start first-pos :end last-pos)
           ppstate))

  :prepwork

  ((defines plex-block-comment-loops

     (define plex-rest-of-block-comment ((first-pos positionp)
                                         (ppstate ppstatep))
       :returns (mv erp
                    (content uchar-listp)
                    (last-pos positionp)
                    (new-ppstate ppstatep))
       :parents nil
       (b* ((ppstate (ppstate-fix ppstate))
            ((reterr) nil (irr-position) ppstate)
            ((erp char pos ppstate) (read-pchar ppstate)))
         (cond
          ((not char) ; EOF
           (reterr-msg :where pos
                       :expected "a character"
                       :found (char-to-msg char)
                       :extra (msg "The block comment starting at (~@1) ~
                                    never ends."
                                   (position-to-msg first-pos))))
          ((utf8-= char (char-code #\*)) ; *
           ;; The function PLEX-REST-OF-BLOCK-COMMENT-AFTER-STAR that we call
           ;; takes care of including the * just read into the content
           ;; if that is not immediately followed by /.
           ;; So here we do not need to handle the inclusion of the *,
           ;; and instead we just relay the content from the call.
           (plex-rest-of-block-comment-after-star first-pos ppstate))
          (t ; other
           ;; We add the character just read to
           ;; the content returned by the recursive call.
           (b* (((erp content last-pos ppstate)
                 (plex-rest-of-block-comment first-pos ppstate)))
             (retok (cons char content) last-pos ppstate)))))
       :measure (ppstate->size ppstate)
       :no-function nil)

     (define plex-rest-of-block-comment-after-star ((first-pos positionp)
                                                    (ppstate ppstatep))
       :returns (mv erp
                    (content uchar-listp)
                    (last-pos positionp)
                    (new-ppstate ppstatep))
       :parents nil
       (b* ((ppstate (ppstate-fix ppstate))
            ((reterr) nil (irr-position) ppstate)
            ((erp char pos ppstate) (read-pchar ppstate)))
         (cond
          ((not char) ; EOF
           (reterr-msg :where pos
                       :expected "a character"
                       :found (char-to-msg char)
                       :extra (msg "The block comment starting at (~@1) ~
                                    never ends."
                                   (position-to-msg first-pos))))
          ((utf8-= char (char-code #\/)) ; /
           ;; We have reached the end of the comment,
           ;; and the * read just before this call must be
           ;; part of  closing */ of the comment.
           ;; So we just return the empty content here;
           ;; recall that the content of a comment lexeme
           ;; does not include the opening /* and closing */.
           (retok nil pos ppstate))
          ((utf8-= char (char-code #\*)) ; *
           ;; Here we are reading another * after having read a *
           ;; just before this call, either called by this function
           ;; or called by PLEX-REST-OF-BLOCK-COMMENT.
           ;; Thus that previous * cannot be part of the closing */
           ;; and thus we add a * to the content that is
           ;; recursively returned by the call just below.
           ;; The * just read may or may not be added to the content,
           ;; based on what follows, but this is handled
           ;; in the recursive call of PLEX-REST-OF-BLOCK-COMMENT-AFTER-STAR.
           (b* (((erp content last-pos ppstate)
                 (plex-rest-of-block-comment-after-star first-pos ppstate)))
             (retok (cons (char-code #\*) content) last-pos ppstate)))
          (t ; other
           ;; Besides adding to the recursively obtained content
           ;; the character just read, we also need to add
           ;; the * that was read before this call.
           (b* (((erp content last-pos ppstate)
                 (plex-rest-of-block-comment first-pos ppstate)))
             (retok (list* (char-code #\*) char content) last-pos ppstate)))))
       :measure (ppstate->size ppstate)
       :no-function nil)

     ///

     (fty::deffixequiv-mutual plex-block-comment-loops)

     (defret-mut-same-lexemes plex-block-comment-loops
       (plex-rest-of-block-comment
        plex-rest-of-block-comment-after-star))

     (std::defret-mutual ppstate->size-of-plex-block-comment-loops-uncond
       (defret ppstate->size-of-plex-rest-of-block-comment-uncond
         (<= (ppstate->size new-ppstate)
             (ppstate->size ppstate))
         :rule-classes :linear
         :fn plex-rest-of-block-comment)
       (defret ppstate->size-of-plex-resto-of-block-comment-after-star-uncond
         (<= (ppstate->size new-ppstate)
             (ppstate->size ppstate))
         :rule-classes :linear
         :fn plex-rest-of-block-comment-after-star))

     (std::defret-mutual ppstate->size-of-plex-block-comment-loops-cond
       (defret ppstate->size-of-plex-rest-of-block-comment-cond
         (implies (not erp)
                  (<= (ppstate->size new-ppstate)
                      (1- (ppstate->size ppstate))))
         :rule-classes :linear
         :fn plex-rest-of-block-comment)
       (defret ppstate->size-of-plex-resto-of-block-comment-after-star-cond
         (implies (not erp)
                  (<= (ppstate->size new-ppstate)
                      (1- (ppstate->size ppstate))))
         :rule-classes :linear
         :fn plex-rest-of-block-comment-after-star))))

  ///

  (defret-same-lexemes plex-block-comment)

  (defret ppstate->size-of-plex-block-comment-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear)

  (defret ppstate->size-of-plex-block-comment-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-line-comment ((first-pos positionp)
                           (current-pos positionp)
                           (ppstate ppstatep))
  :returns (mv erp
               (lexeme plexemep)
               (span spanp)
               (new-ppstate ppstatep))
  :short "Lex a line comment during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when we expect a line comment,
     after reading the initial @('//').")
   (xdoc::p
    "We read characters in a loop until
     either we find a new-line character or the end of file.
     In case of success, we return
     a lexeme that contains the content of the comment,
     i.e. the characters between @('//') and new line if present
     (excluding both).")
   (xdoc::p
    "The span is calculated from
     the position of the first @('/') in the opening @('//'),
     which is passed to this function,
     and the position of the closing new-line or end of file,
     which is returned by the loop function.")
   (xdoc::p
    "When encountering the end of file,
     we succeed and return the line comment,
     even though [C17] prohibits a non-empty file to end without a new line.
     However, this condition can be enforced elsewhere,
     and GCC actually relaxes this condition.
     So it is more flexible for this lexing function
     to handle end of file as successfully ending the line comment."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) (irr-plexeme) (irr-span) ppstate)
       ((erp content last-pos ppstate)
        (plex-line-comment-loop first-pos current-pos ppstate)))
    (retok (plexeme-line-comment content)
           (make-span :start first-pos :end last-pos)
           ppstate))

  :prepwork

  ((define plex-line-comment-loop ((first-pos positionp)
                                   (current-pos positionp)
                                   (ppstate ppstatep))
     :returns (mv erp
                  (content uchar-listp)
                  (last-pos positionp)
                  (new-ppstate ppstatep))
     :parents nil
     (b* ((ppstate (ppstate-fix ppstate))
          ((reterr) nil (irr-position) ppstate)
          ((erp char pos ppstate) (read-pchar ppstate)))
       (cond
        ((not char) ; EOF
         (retok nil (position-fix current-pos) ppstate))
        ((utf8-= char 10) ; LF
         (b* ((ppstate (unread-pchar ppstate))) ;
           (retok nil (position-fix current-pos) ppstate)))
        ((utf8-= char 13) ; CR
         (b* ((ppstate (unread-pchar ppstate))) ;
           (retok nil (position-fix current-pos) ppstate)))
        (t ; other
         (b* (((erp content last-pos ppstate)
               (plex-line-comment-loop first-pos pos ppstate)))
           (retok (cons char content) last-pos ppstate)))))
     :measure (ppstate->size ppstate)
     :no-function nil

     ///

     (defret-rec-same-lexemes plex-line-comment-loop)

     (defret ppstate->size-of-plex-line-comment-loop-uncond
       (<= (ppstate->size new-ppstate)
           (ppstate->size ppstate))
       :rule-classes :linear
       :hints (("Goal" :induct t :in-theory (enable fix))))))

  ///

  (defret-same-lexemes plex-line-comment)

  (defret ppstate->size-of-plex-line-comment-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-spaces ((first-pos positionp) (ppstate ppstatep))
  :returns (mv erp
               (lexeme plexemep)
               (span spanp)
               (new-ppstate ppstatep))
  :short "Lex consecutive spaces during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called just after a space character (code 32) has been read;
     the position of that space character is passed as input here.")
   (xdoc::p
    "We read zero or more additional spaces,
     and we return a lexeme for spaces,
     with the count incremented by one to account for the first space."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) (irr-plexeme) (irr-span) ppstate)
       ((erp nspaces last-pos ppstate) (plex-spaces-loop first-pos ppstate)))
    (retok (plexeme-spaces (1+ nspaces))
           (make-span :start first-pos :end last-pos)
           ppstate))

  :prepwork

  ((define plex-spaces-loop ((prev-pos positionp) (ppstate ppstatep))
     :returns (mv erp
                  (nspaces natp :rule-classes (:rewrite :type-prescription))
                  (last-pos positionp)
                  (new-ppstate ppstatep))
     :parents nil
     (b* ((ppstate (ppstate-fix ppstate))
          ((reterr) 0 (irr-position) ppstate)
          ((erp char pos ppstate) (read-pchar ppstate)))
       (cond
        ((not char) ; end of file
         (retok 0 (position-fix prev-pos) ppstate))
        ((utf8-= char 32) ; SP
         (b* (((erp nspaces last-pos ppstate)
               (plex-spaces-loop pos ppstate)))
           (retok (1+ nspaces) last-pos ppstate)))
        (t ; other
         (b* ((ppstate (unread-pchar ppstate)))
           (retok 0 (position-fix prev-pos) ppstate)))))
     :measure (ppstate->size ppstate)
     :verify-guards :after-returns

     ///

     (defret-rec-same-lexemes plex-spaces-loop)

     (defret ppstate->size-of-plex-spaces-loop-uncond
       (<= (ppstate->size new-ppstate)
           (ppstate->size ppstate))
       :rule-classes :linear
       :hints (("Goal" :induct t :in-theory (enable fix))))))

  ///

  (defret-same-lexemes plex-spaces)

  (defret ppstate->size-of-plex-spaces-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-lexeme ((headerp booleanp) (ppstate ppstatep))
  :returns (mv erp
               (lexeme? plexeme-optionp)
               (span spanp)
               (new-ppstate ppstatep))
  :short "Lex a lexeme during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level lexing function for the preprocessor.")
   (xdoc::p
    "This function returns the next lexeme from the input,
     or @('nil') if we reached the end of the file;
     an error is returned if lexing fails.")
   (xdoc::p
    "Lexing in the preprocessor is context-dependent
     [C17:5.1.1.2/1, footnote 7] [C23:5.2.1.2, footnote 4]:
     when expecting a header name,
     a @('\"') or a @('<') are interpreted differently
     (i.e. as starting a header name)
     than usual
     (i.e. as starting a string literal or a punctuator).
     (Note that header names surrounded with double quotes
     are not the same as string literals,
     because the latter allow escapes while the former do not.)
     Thus, this lexing function takes a boolean flag
     indicating whether we are expecting a header name or not.")
   (xdoc::p
    "We read the next character.
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
     "If the next character is a digit,
      it must start a preprocessing number;
      it is the only possibility.")
    (xdoc::li
     "If the next character is @('.'),
      it may start a preprocessing number,
      or it could be the punctuator @('.'),
      or it could start the punctuator @('...').
      So we examine the following characters.
      If there is none, we have the punctuator @('.').
      If the following character is a digit,
      this must start a preprocessing number.
      If the following character is another @('.'),
      and there is a further @('.') after it,
      we have the punctuator @('...').
      In all other cases, we just have the punctuator @('.'),
      and we put back the additional character(s) read,
      since they may be starting a different lexeme.")
    (xdoc::li
     "If the next character is a letter,
      it could start an identifier,
      but it could also start a character constant or a string literal.
      Specifically, if the letter is @('u'), @('U'), or @('L'),
      it could be a prefix of a character constant or string literal.
      We must try this possibility before trying an identifier,
      because we always need to lex the longest possible sequence of characters
      [C17:6.4/4]:
      if we tried identifiers first,
      for example
      we would erroneously lex the character constant @('u\'a\'')
      as the identifier @('u') followed by
      the unprefixed character constant @('\'a\'').")
    (xdoc::li
     "If the next character is @('u'), and there are no subsequent characters,
      we lex it as an identifier.
      If the following character is a single quote,
      we attempt to lex a character constant with the appropriate prefix;
      if the following character is a double quote,
      we attempt to lex a string literal with the appropriate prefix.
      These are the only two possibilities in these two cases.
      Strictly speaking,
      if the lexing of the character constant or string literal fails,
      we should lex @('u') as an identifier and then continue lexing,
      but at that point the only possibility would be
      an unprefixed character constant or string literal,
      which would fail again; so we can fail sooner without loss.
      If the character immediately following @('u') is @('8'),
      then we need to look at the character after that.
      If there is none, we lex the identifier @('u8').
      If there is a single quote, and the standard is C23,
      we attempt to lex a character constant with the appropriate prefix.
      If there is a double quote,
      then we attempt to lex a string literal with the appropriate prefix.
      If the character after @('u8') is not a single or double quote,
      we put back that character and @('8'),
      and we lex @('u...') as an identifier.
      Also, if the character after @('u') was not
      any of the ones mentioned above,
      we put it back and we lex @('u...') as an identifier.")
    (xdoc::li
     "If the next character is @('U') or @('L'),
      we proceed similarly to the case of @('u'),
      but things are simpler because there is no @('8') to handle.")
    (xdoc::li
     "If the next character is any other letter or an underscore,
      it must start an identifier.
      This is the only possibility,
      since we have already tried
      a prefixed character constant or string literal.")
    (xdoc::li
     "If the next character is a single quote,
      it must start an unprefixed character constant.")
    (xdoc::li
     "If the next character is a double quote,
      and the @('header?') flag is @('nil'),
      it must start an unprefixed string literal;
      if instead the @('header?') flag is @('t'),
      it must start a header name.")
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
      and so they can be immediately decided.")
    (xdoc::li
     "If we encounter the @('<') punctuator,
      and the @('header?') flag is @('nil'),
      it must be or start a punctuator;
      if instead the @('header?') flag is @('t'),
      it must start a header name."))
   (xdoc::p
    "The provenance lists of the identifiers created here is @('nil'),
     because the identifiers are lexed directly from the file,
     not generated by macro expansion."))

  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil (irr-span) ppstate)
       ((erp char pos ppstate) (read-pchar ppstate))
       ((unless char) ; EOF
        (retok nil ; no lexeme
               (make-span :start pos :end pos)
               ppstate)))

    (cond

     ((utf8-= char 32) ; SP
      (plex-spaces pos ppstate))

     ((utf8-= char 9) ; HT
      (retok (plexeme-horizontal-tab)
             (make-span :start pos :end pos)
             ppstate))

     ((utf8-= char 11) ; VT
      (retok (plexeme-vertical-tab)
             (make-span :start pos :end pos)
             ppstate))

     ((utf8-= char 12) ; FF
      (retok (plexeme-form-feed)
             (make-span :start pos :end pos)
             ppstate))

     ((utf8-= char 10) ; LF
      (retok (plexeme-newline (newline-lf))
             (make-span :start pos :end pos)
             ppstate))

     ((utf8-= char 13) ; CR
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; CR EOF
          (retok (plexeme-newline (newline-cr))
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 10) ; CR LF
          (retok (plexeme-newline (newline-crlf))
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; CR other
          (b* ((ppstate (unread-pchar ppstate))) ; CR
            (retok (plexeme-newline (newline-cr))
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((and (utf8-<= (char-code #\0) char)
           (utf8-<= char (char-code #\9))) ; 0-9
      (plex-pp-number nil (code-char char) pos ppstate))

     ((utf8-= char (char-code #\.)) ; .
      (b* (((erp char2 & ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; . EOF
          (retok (plexeme-punctuator ".")
                 (make-span :start pos :end pos)
                 ppstate))
         ((and (utf8-<= (char-code #\0) char2)
               (utf8-<= char2 (char-code #\9))) ; . 0-9
          (plex-pp-number t (code-char char2) pos ppstate))
         ((utf8-= char2 (char-code #\.)) ; . .
          (b* (((erp char3 pos3 ppstate) (read-pchar ppstate)))
            (cond
             ((not char3) ; . . EOF
              (b* ((ppstate (unread-pchar ppstate))) ; .
                (retok (plexeme-punctuator ".")
                       (make-span :start pos :end pos)
                       ppstate)))
             ((utf8-= char3 (char-code #\.)) ; . . .
              (retok (plexeme-punctuator "...")
                     (make-span :start pos :end pos3)
                     ppstate))
             (t ; . . other
              (b* ((ppstate (unread-pchar ppstate)) ; . .
                   (ppstate (unread-pchar ppstate))) ; .
                (retok (plexeme-punctuator ".")
                       (make-span :start pos :end pos)
                       ppstate))))))
         (t ; . other
          (b* ((ppstate (unread-pchar ppstate))) ; .
            (retok (plexeme-punctuator ".")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\u)) ; u
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; u EOF
          (retok (make-plexeme-ident :ident "u" :provenance nil)
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\')) ; u '
          (plex-character-constant (eprefix-locase-u) pos ppstate))
         ((utf8-= char2 (char-code #\")) ; u "
          (plex-string-literal (eprefix-locase-u) pos ppstate))
         ((utf8-= char2 (char-code #\8)) ; u 8
          (b* (((erp char3 & ppstate) (read-pchar ppstate)))
            (cond
             ((not char3) ; u 8 EOF
              (retok (make-plexeme-ident :ident "u8" :provenance nil)
                     (make-span :start pos :end pos2)
                     ppstate))
             ((and (utf8-= char3 (char-code #\')) ; u 8 '
                   (c::standard-case
                    (c::dialect->std (ienv->dialect (ppstate->ienv ppstate)))
                    :c23))
              (plex-character-constant (eprefix-locase-u8) pos ppstate))
             ((utf8-= char3 (char-code #\")) ; u 8 "
              (plex-string-literal (eprefix-locase-u8) pos ppstate))
             (t ; u 8 other
              (b* ((ppstate (unread-pchar ppstate)) ; u 8
                   (ppstate (unread-pchar ppstate))) ; u
                (plex-identifier char pos ppstate))))))
         (t ; u other
          (b* ((ppstate (unread-pchar ppstate))) ; u
            (plex-identifier char pos ppstate))))))

     ((utf8-= char (char-code #\U)) ; U
      (b* (((erp char2 & ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; U EOF
          (retok (make-plexeme-ident :ident "U" :provenance nil)
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\')) ; U '
          (plex-character-constant (eprefix-upcase-u) pos ppstate))
         ((utf8-= char2 (char-code #\")) ; U "
          (plex-string-literal (eprefix-upcase-u) pos ppstate))
         (t ; U other
          (b* ((ppstate (unread-pchar ppstate))) ; U
            (plex-identifier char pos ppstate))))))

     ((utf8-= char (char-code #\L)) ; L
      (b* (((erp char2 & ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; L EOF
          (retok (make-plexeme-ident :ident "L" :provenance nil)
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\')) ; L '
          (plex-character-constant (eprefix-upcase-l) pos ppstate))
         ((utf8-= char2 (char-code #\")) ; L "
          (plex-string-literal (eprefix-upcase-l) pos ppstate))
         (t ; L other
          (b* ((ppstate (unread-pchar ppstate))) ; L
            (plex-identifier char pos ppstate))))))

     ((or (and (utf8-<= (char-code #\A) char)
               (utf8-<= char (char-code #\Z))) ; A-Z
          (and (utf8-<= (char-code #\a) char)
               (utf8-<= char (char-code #\z))) ; a-z
          (= char (char-code #\_))) ; _
      (plex-identifier char pos ppstate))

     ((utf8-= char (char-code #\')) ; '
      (plex-character-constant nil pos ppstate))

     ((utf8-= char (char-code #\")) ; "
      (if headerp
          (b* ((ppstate (unread-pchar ppstate))) ;
            (plex-header-name ppstate))
        (plex-string-literal nil pos ppstate)))

     ((utf8-= char (char-code #\/)) ; /
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; / EOF
          (retok (plexeme-punctuator "/")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\*)) ; / *
          (plex-block-comment pos ppstate))
         ((utf8-= char2 (char-code #\/)) ; / /
          (plex-line-comment pos pos2 ppstate))
         ((utf8-= char2 (char-code #\=)) ; / =
          (retok (plexeme-punctuator "/=")
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; / other
          (b* ((ppstate (unread-pchar ppstate))) ; /
            (retok (plexeme-punctuator "/")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\#)) ; #
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; # EOF
          (retok (plexeme-punctuator "#")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\#)) ; # #
          (retok (plexeme-punctuator "##")
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; # other
          (b* ((ppstate (unread-pchar ppstate)))
            (retok (plexeme-punctuator "#")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((or (utf8-= char (char-code #\[)) ; [
          (utf8-= char (char-code #\])) ; ]
          (utf8-= char (char-code #\()) ; (
          (utf8-= char (char-code #\))) ; )
          (utf8-= char (char-code #\{)) ; {
          (utf8-= char (char-code #\})) ; }
          (utf8-= char (char-code #\~)) ; ~
          (utf8-= char (char-code #\?)) ; ?
          (utf8-= char (char-code #\,)) ; ,
          (utf8-= char (char-code #\;))) ; ;
      (retok (plexeme-punctuator (str::implode (list (code-char char))))
             (make-span :start pos :end pos)
             ppstate))

     ((utf8-= char (char-code #\*)) ; *
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; * EOF
          (retok (plexeme-punctuator "*")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\=)) ; * =
          (retok (plexeme-punctuator "*=")
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; * other
          (b* ((ppstate (unread-pchar ppstate)))
            (retok (plexeme-punctuator "*")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\^)) ; ^
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; ^ EOF
          (retok (plexeme-punctuator "^")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\=)) ; ^ =
          (retok (plexeme-punctuator "^=")
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; ^ other
          (b* ((ppstate (unread-pchar ppstate)))
            (retok (plexeme-punctuator "^")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\!)) ; !
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; ! EOF
          (retok (plexeme-punctuator "!")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\=)) ; ! =
          (retok (plexeme-punctuator "!=")
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; ! other
          (b* ((ppstate (unread-pchar ppstate)))
            (retok (plexeme-punctuator "!")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\=)) ; =
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; = EOF
          (retok (plexeme-punctuator "=")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\=)) ; = =
          (retok (plexeme-punctuator "==")
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; = other
          (b* ((ppstate (unread-pchar ppstate)))
            (retok (plexeme-punctuator "=")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\:)) ; :
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; : EOF
          (retok (plexeme-punctuator ":")
                 (make-span :start pos :end pos)
                 ppstate))
         ((and (utf8-= char2 (char-code #\:)) ; : :
               (c::standard-case
                (c::dialect->std (ienv->dialect (ppstate->ienv ppstate)))
                :c23))
          (retok (plexeme-punctuator "::")
                 (make-span :start pos :end pos2)
                 ppstate))
         ((utf8-= char2 (char-code #\>)) ; : >
          (retok (plexeme-punctuator ":>")
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; : other
          (b* ((ppstate (unread-pchar ppstate)))
            (retok (plexeme-punctuator ":")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\&)) ; &
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; & EOF
          (retok (plexeme-punctuator "&")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\&)) ; & &
          (retok (plexeme-punctuator "&&")
                 (make-span :start pos :end pos2)
                 ppstate))
         ((utf8-= char2 (char-code #\=)) ; & =
          (retok (plexeme-punctuator "&=")
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; & other
          (b* ((ppstate (unread-pchar ppstate)))
            (retok (plexeme-punctuator "&")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\|)) ; |
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; | EOF
          (retok (plexeme-punctuator "|")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\|)) ; | |
          (retok (plexeme-punctuator "||")
                 (make-span :start pos :end pos2)
                 ppstate))
         ((utf8-= char2 (char-code #\=)) ; | =
          (retok (plexeme-punctuator "|=")
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; | other
          (b* ((ppstate (unread-pchar ppstate)))
            (retok (plexeme-punctuator "|")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\+)) ; +
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; + EOF
          (retok (plexeme-punctuator "+")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\+)) ; + +
          (retok (plexeme-punctuator "++")
                 (make-span :start pos :end pos2)
                 ppstate))
         ((utf8-= char2 (char-code #\=)) ; + =
          (retok (plexeme-punctuator "+=")
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; + other
          (b* ((ppstate (unread-pchar ppstate)))
            (retok (plexeme-punctuator "+")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\-)) ; -
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; - EOF
          (retok (plexeme-punctuator "-")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\>)) ; - >
          (retok (plexeme-punctuator "->")
                 (make-span :start pos :end pos2)
                 ppstate))
         ((utf8-= char2 (char-code #\-)) ; - -
          (retok (plexeme-punctuator "--")
                 (make-span :start pos :end pos2)
                 ppstate))
         ((utf8-= char2 (char-code #\=)) ; - =
          (retok (plexeme-punctuator "-=")
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; - other
          (b* ((ppstate (unread-pchar ppstate)))
            (retok (plexeme-punctuator "-")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\>)) ; >
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; > EOF
          (retok (plexeme-punctuator ">")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\>)) ; > >
          (b* (((erp char3 pos3 ppstate) (read-pchar ppstate)))
            (cond
             ((not char3) ; > > EOF
              (retok (plexeme-punctuator ">>")
                     (make-span :start pos :end pos2)
                     ppstate))
             ((utf8-= char3 (char-code #\=))
              (retok (plexeme-punctuator ">>=")
                     (make-span :start pos :end pos3)
                     ppstate))
             (t ; > > other
              (b* ((ppstate (unread-pchar ppstate))) ; > >
                (retok (plexeme-punctuator ">>")
                       (make-span :start pos :end pos2)
                       ppstate))))))
         ((utf8-= char2 (char-code #\=)) ; > =
          (retok (plexeme-punctuator ">=")
                 (make-span :start pos :end pos)
                 ppstate))
         (t ; > other
          (b* ((ppstate (unread-pchar ppstate))) ; >
            (retok (plexeme-punctuator ">")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\%)) ; %
      (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
        (cond
         ((not char2) ; % EOF
          (retok (plexeme-punctuator "%")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\=)) ; % =
          (retok (plexeme-punctuator "%=")
                 (make-span :start pos :end pos2)
                 ppstate))
         ((utf8-= char2 (char-code #\>)) ; % >
          (retok (plexeme-punctuator "%>")
                 (make-span :start pos :end pos2)
                 ppstate))
         ((utf8-= char2 (char-code #\:)) ; % :
          (b* (((erp char3 & ppstate) (read-pchar ppstate)))
            (cond
             ((not char3) ; % : EOF
              (retok (plexeme-punctuator "%:")
                     (make-span :start pos :end pos2)
                     ppstate))
             ((utf8-= char3 (char-code #\%)) ; % : %
              (b* (((erp char4 pos4 ppstate) (read-pchar ppstate)))
                (cond
                 ((not char4) ; % : % EOF
                  (b* ((ppstate (unread-pchar ppstate))) ; % :
                    (retok (plexeme-punctuator "%:")
                           (make-span :start pos :end pos2)
                           ppstate)))
                 ((utf8-= char4 (char-code #\:)) ; % : % :
                  (retok (plexeme-punctuator "%:%:")
                         (make-span :start pos :end pos4)
                         ppstate))
                 (t ; % : % other
                  (b* ((ppstate (unread-pchar ppstate)) ; % : %
                       (ppstate (unread-pchar ppstate))) ; % :
                    (retok (plexeme-punctuator "%:")
                           (make-span :start pos :end pos2)
                           ppstate))))))
             (t ; % : other
              (b* ((ppstate (unread-pchar ppstate))) ; % :
                (retok (plexeme-punctuator "%:")
                       (make-span :start pos :end pos2)
                       ppstate))))))
         (t ; % other
          (b* ((ppstate (unread-pchar ppstate))) ; %
            (retok (plexeme-punctuator "%")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\<)) ; <
      (if headerp
          (b* ((ppstate (unread-pchar ppstate))) ;
            (plex-header-name ppstate))
        (b* (((erp char2 pos2 ppstate) (read-pchar ppstate)))
          (cond
           ((not char2) ; < EOF
            (retok (plexeme-punctuator "<")
                   (make-span :start pos :end pos)
                   ppstate))
           ((utf8-= char2 (char-code #\<)) ; < <
            (b* (((erp char3 pos3 ppstate) (read-pchar ppstate)))
              (cond
               ((not char3) ; < < EOF
                (retok (plexeme-punctuator "<<")
                       (make-span :start pos :end pos2)
                       ppstate))
               ((utf8-= char3 (char-code #\=)) ; < < =
                (retok (plexeme-punctuator "<<=")
                       (make-span :start pos :end pos3)
                       ppstate))
               (t ; < < other
                (b* ((ppstate (unread-pchar ppstate))) ; < <
                  (retok (plexeme-punctuator "<<")
                         (make-span :start pos :end pos2)
                         ppstate))))))
           ((utf8-= char2 (char-code #\=)) ; < =
            (retok (plexeme-punctuator "<=")
                   (make-span :start pos :end pos2)
                   ppstate))
           ((utf8-= char2 (char-code #\:)) ; < :
            (retok (plexeme-punctuator "<:")
                   (make-span :start pos :end pos2)
                   ppstate))
           ((utf8-= char2 (char-code #\%)) ; < %
            (retok (plexeme-punctuator "<%")
                   (make-span :start pos :end pos2)
                   ppstate))
           (t ; < other
            (b* ((ppstate (unread-pchar ppstate))) ; <
              (retok (plexeme-punctuator "<")
                     (make-span :start pos :end pos)
                     ppstate)))))))

     (t ; other
      (retok (plexeme-other char)
             (make-span :start pos :end pos)
             ppstate))))

  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p
                                           integer-range-p
                                           dec-digit-char-p)))

  ///

  (defret-same-lexemes plex-lexeme)

  (defret ppstate->size-of-plex-lexeme-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear)

  (defret ppstate->size-of-plex-lexeme-cond
    (implies (and (not erp)
                  lexeme?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear))
