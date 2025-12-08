; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
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
(include-book "files")
(include-book "implementation-environments")

(include-book "kestrel/fty/character-list" :dir :system)
(include-book "kestrel/fty/nat-option" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (:e tau-system))))
(set-induction-depth-limit 0)

; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Library extensions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl integerp-when-bytep
  (implies (bytep x)
           (integerp x)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl car-of-byte-list-geq-0
  (implies (byte-listp x)
           (>= (car x) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor
  :parents (preprocessing)
  :short "A preprocessor for C."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide a preprocessor for C that, unlike typical preprocessors,
     preserves the information about the @('#include') directives.
     That is, it does not replace such directives
     with the (preprocessed) contents of the referenced files,
     but it otherwise performs the rest of the preprocessing.")
   (xdoc::p
    "Our preprocessor maps a file set to a file set (see @(see files)).
     It reads characters and lexes them into lexemes,
     while executing the preprocessing directives.
     The resulting sequence of lexemes is then turned into characters
     that are written into files.
     The resulting file set is amenable to our parser
     (more precisely, it will be, once we have extended our parser
     to accept @('#include') directives in certain places,
     which we plan to do).
     Our preprocessor preserves white space, in order to preserve the layout
     (modulo the inherent layout changes caused by preprocessing).
     Our preprocessor also preserves comments,
     although some comments may no longer apply to preprocessed code
     (e.g. comments talking about macros).")
   (xdoc::p
    "Currently some of this preprocessor's code duplicates, at some level,
     some of the code in the @(see parser)
     (including the @(see lexer) and the @(see reader)).
     At some point we should integrate the preprocessor into the parser.")
   (xdoc::p
    "This preprocessor is very much work in progress."))
  :order-subtopics (preprocessor-states
                    preprocessor-messages
                    preprocessor-reader
                    t)
  :default-parent t)

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
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex an identifier during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is quite similar to @(tsee lex-identifier/keyword),
     except that there are no keywords to consider during preprocessing,
     just identifiers.")
   (xdoc::p
    "Like @(tsee lex-identifier/keyword),
     this is called after the first character of the identifier
     has been already read;
     that character is passed to this function.
     The position of that character is also passed as input."))
  (b* (((reterr) (irr-plexeme) (irr-span) ppstate)
       ((erp rest-chars last-pos ppstate)
        (plex-identifier-loop first-pos ppstate))
       (span (make-span :start first-pos :end last-pos))
       (chars (cons first-char rest-chars))
       (string (acl2::nats=>string chars)))
    (retok (plexeme-ident (ident string)) span ppstate))

  :prepwork

  ((define plex-identifier-loop ((pos-so-far positionp) (ppstate ppstatep))
     :returns (mv erp
                  (chars (unsigned-byte-listp 8 chars)
                         :hints (("Goal"
                                  :induct t
                                  :in-theory (enable unsigned-byte-p
                                                     integer-range-p))))
                  (last-pos positionp)
                  (new-ppstate ppstatep :hyp (ppstatep ppstate)))
     :parents nil
     (b* (((reterr) nil (irr-position) ppstate)
          ((erp char pos ppstate) (pread-char ppstate))
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
           (b* ((ppstate (punread-char ppstate)))
             (retok nil (position-fix pos-so-far) ppstate)))
          ((erp chars last-pos ppstate)
           (plex-identifier-loop pos ppstate)))
       (retok (cons char chars) last-pos ppstate))
     :measure (ppstate->size ppstate)
     :verify-guards nil ; done below

     ///

     (verify-guards plex-identifier-loop
       :hints (("Goal" :in-theory (enable rationalp-when-natp
                                          acl2-numberp-when-natp))))

     (defret ppstate->size-of-plex-identifier-loop-uncond
       (<= (ppstate->size new-ppstate)
           (ppstate->size ppstate))
       :rule-classes :linear
       :hints (("Goal" :induct t)))))

  ///

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
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
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
     Eventually we return the full preprocessing number and the full span."))
  (b* (((reterr) (irr-plexeme) (irr-span) ppstate)
       (initial-pnumber (if dot
                            (pnumber-dot-digit digit)
                          (pnumber-digit digit)))
       ((erp final-pnumber last-pos ppstate)
        (plex-pp-number-loop initial-pnumber first-pos ppstate)))
    (retok (plexeme-number final-pnumber)
           (make-span :start first-pos :end last-pos)
           ppstate))

  :prepwork

  ((define plex-pp-number-loop ((current-pnumber pnumberp)
                                (current-pos positionp)
                                ppstate)
     :returns (mv erp
                  (final-pnumber pnumberp)
                  (last-pos positionp)
                  (new-ppstate ppstatep :hyp (ppstatep ppstate)))
     :parents nil
     (b* (((reterr) (irr-pnumber) (irr-position) ppstate)
          ((erp char pos ppstate) (pread-char ppstate)))
       (cond
        ((not char) ; pp-number EOF
         (retok (pnumber-fix current-pnumber)
                (position-fix current-pos)
                ppstate))
        ((and (utf8-<= (char-code #\0) char)
              (utf8-<= char (char-code #\9))) ; pp-number digit
         (plex-pp-number-loop (make-pnumber-number-digit
                               :number current-pnumber
                               :digit (code-char char))
                              pos
                              ppstate))
        ((utf8-= char (char-code #\e)) ; pp-number e
         (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
           (cond
            ((and char2 (utf8-= char2 (char-code #\+))) ; pp-number e +
             (plex-pp-number-loop (make-pnumber-number-locase-e-sign
                                   :number current-pnumber
                                   :sign (sign-plus))
                                  pos2
                                  ppstate))
            ((and char2 (utf8-= char2 (char-code #\-))) ; pp-number e -
             (plex-pp-number-loop (make-pnumber-number-locase-e-sign
                                   :number current-pnumber
                                   :sign (sign-minus))
                                  pos2
                                  ppstate))
            (t ; pp-number e other
             (b* ((ppstate ; pp-number e
                   (if char2 (punread-char ppstate) ppstate)))
               (plex-pp-number-loop (make-pnumber-number-nondigit
                                     :number current-pnumber
                                     :nondigit #\e)
                                    pos
                                    ppstate))))))
        ((utf8-= char (char-code #\E)) ; pp-number E
         (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
           (cond
            ((and char2 (utf8-= char2 (char-code #\+))) ; pp-number E +
             (plex-pp-number-loop (make-pnumber-number-upcase-e-sign
                                   :number current-pnumber
                                   :sign (sign-plus))
                                  pos2
                                  ppstate))
            ((and char2 (utf8-= char2 (char-code #\-))) ; pp-number E -
             (plex-pp-number-loop (make-pnumber-number-upcase-e-sign
                                   :number current-pnumber
                                   :sign (sign-minus))
                                  pos2
                                  ppstate))
            (t ; pp-number E other
             (b* ((ppstate ; pp-number E
                   (if char2 (punread-char ppstate) ppstate)))
               (plex-pp-number-loop (make-pnumber-number-nondigit
                                     :number current-pnumber
                                     :nondigit #\E)
                                    pos
                                    ppstate))))))
        ((utf8-= char (char-code #\p)) ; pp-number p
         (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
           (cond
            ((and char2 (utf8-= char2 (char-code #\+))) ; pp-number p +
             (plex-pp-number-loop (make-pnumber-number-locase-p-sign
                                   :number current-pnumber
                                   :sign (sign-plus))
                                  pos2
                                  ppstate))
            ((and char2 (utf8-= char2 (char-code #\-))) ; pp-number p -
             (plex-pp-number-loop (make-pnumber-number-locase-p-sign
                                   :number current-pnumber
                                   :sign (sign-minus))
                                  pos2
                                  ppstate))
            (t ; pp-number p other
             (b* ((ppstate ; pp-number p
                   (if char2 (punread-char ppstate) ppstate)))
               (plex-pp-number-loop (make-pnumber-number-nondigit
                                     :number current-pnumber
                                     :nondigit #\p)
                                    pos
                                    ppstate))))))
        ((utf8-= char (char-code #\P)) ; pp-number P
         (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
           (cond
            ((and char2 (utf8-= char2 (char-code #\+))) ; pp-number P +
             (plex-pp-number-loop (make-pnumber-number-upcase-p-sign
                                   :number current-pnumber
                                   :sign (sign-plus))
                                  pos2
                                  ppstate))
            ((and char2 (utf8-= char2 (char-code #\-))) ; pp-number P -
             (plex-pp-number-loop (make-pnumber-number-upcase-p-sign
                                   :number current-pnumber
                                   :sign (sign-minus))
                                  pos2
                                  ppstate))
            (t ; pp-number P other
             (b* ((ppstate ; pp-number P
                   (if char2 (punread-char ppstate) ppstate)))
               (plex-pp-number-loop (make-pnumber-number-nondigit
                                     :number current-pnumber
                                     :nondigit #\P)
                                    pos
                                    ppstate))))))
        ((or (and (utf8-<= (char-code #\A) char)
                  (utf8-<= char (char-code #\Z)))
             (and (utf8-<= (char-code #\a) char)
                  (utf8-<= char (char-code #\z)))
             (utf8-= char (char-code #\_))) ; pp-number identifier-nondigit
         (plex-pp-number-loop (make-pnumber-number-nondigit
                               :number current-pnumber
                               :nondigit (code-char char))
                              pos
                              ppstate))
        ((utf8-= char (char-code #\.)) ; pp-number .
         (plex-pp-number-loop (make-pnumber-number-dot
                               :number current-pnumber)
                              pos ppstate))
        (t ; pp-number other
         (b* ((ppstate ; pp-number
               (if char (punread-char ppstate) ppstate)))
           (retok (pnumber-fix current-pnumber)
                  (position-fix current-pos)
                  ppstate)))))
     :measure (ppstate->size ppstate)
     :guard-hints (("Goal" :in-theory (enable integerp-when-natp
                                              rationalp-when-natp
                                              acl2-numberp-when-natp
                                              dec-digit-char-p
                                              str::letter/uscore-char-p)))

     ///

     (defret ppstate->size-of-plex-pp-number-loop-uncond
       (<= (ppstate->size new-ppstate)
           (ppstate->size ppstate))
       :rule-classes :linear
       :hints (("Goal" :induct t)))))

  ///

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
                                                   integer-range-p
                                                   integerp-when-natp))))
               (pos positionp)
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex a hexadecimal digit during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as @(tsee lex-hexadecimal-digit),
     but it operates on preprocessor states instead of parser states."))
  (b* (((reterr) #\0 (irr-position) ppstate)
       ((erp char pos ppstate) (pread-char ppstate))
       ((when (not char))
        (reterr-msg :where (position-to-msg pos)
                    :expected "a hexadecimal digit"
                    :found (char-to-msg char)))
       ((unless (or (and (utf8-<= (char-code #\0) char) ; 0
                         (utf8-<= char (char-code #\9))) ; 9
                    (and (utf8-<= (char-code #\A) char) ; A
                         (utf8-<= char (char-code #\F))) ; F
                    (and (utf8-<= (char-code #\a) char) ; a
                         (utf8-<= char (char-code #\f))))) ; f
        (reterr-msg :where (position-to-msg pos)
                    :expected "a hexadecimal digit"
                    :found (char-to-msg char))))
    (retok (code-char char) pos ppstate))
  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp
                                           integerp-when-natp)))

  ///

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
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex a quadruple of hexadecimal digits during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as @(tsee lex-hex-quad),
     but it operates on preprocessor states instead of parser states."))
  (b* (((reterr) (irr-hex-quad) (irr-position) ppstate)
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
                                             integer-range-p
                                             integerp-when-natp))))
               (last-pos positionp)
               (next-pos positionp)
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex zero or more hexadecimal digits, as many as available,
          during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as @(tsee lex-*-hexadecimal-digit),
     but it operates on preprocessor states instead of parser states."))
  (b* (((reterr) nil (irr-position) (irr-position) ppstate)
       ((erp char pos ppstate) (pread-char ppstate))
       ((when (not char))
        (retok nil (position-fix pos-so-far) pos ppstate))
       ((unless (or (and (utf8-<= (char-code #\0) char) ; 0
                         (utf8-<= char (char-code #\9))) ; 9
                    (and (utf8-<= (char-code #\A) char) ; A
                         (utf8-<= char (char-code #\F))) ; F
                    (and (utf8-<= (char-code #\a) char) ; a
                         (utf8-<= char (char-code #\f))))) ; f
        (b* ((ppstate (punread-char ppstate)))
          (retok nil (position-fix pos-so-far) pos ppstate)))
       (hexdig (code-char char))
       ((erp hexdigs last-pos next-pos ppstate)
        (plex-*-hexadecimal-digit pos ppstate)))
    (retok (cons hexdig hexdigs) last-pos next-pos ppstate))
  :measure (ppstate->size ppstate)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp
                                           integerp-when-natp)))

  ///

  (more-returns
   (hexdigs true-listp
            :rule-classes :type-prescription))

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
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex an escape sequence during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as @(tsee lex-escape-sequence),
     but it operates on preprocessor states instead of parser states."))
  (b* (((reterr) (irr-escape) (irr-position) ppstate)
       ((erp char pos ppstate) (pread-char ppstate)))
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
           (ppstate->gcc ppstate))
      (retok (escape-simple (simple-escape-percent)) pos ppstate))
     ((and (utf8-<= (char-code #\0) char)
           (utf8-<= char (char-code #\7))) ; \ octdig
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
        (cond
         ((and char2
               (utf8-<= (char-code #\0) char2)
               (utf8-<= char2 (char-code #\7))) ; \ octdig octdig
          (b* (((erp char3 pos3 ppstate) (pread-char ppstate)))
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
                    (if char3 (punread-char ppstate) ppstate)))
                (retok (escape-oct (oct-escape-two (code-char char)
                                                   (code-char char2)))
                       pos2
                       ppstate))))))
         (t ; \ octdig other
          (b* ((ppstate (if char2 (punread-char ppstate) ppstate))) ; \octdig
            (retok (escape-oct (oct-escape-one (code-char char)))
                   pos
                   ppstate))))))
     ((utf8-= char (char-code #\x))
      (b* (((erp hexdigs last-pos next-pos ppstate)
            (plex-*-hexadecimal-digit pos ppstate)))
        (if hexdigs
            (retok (escape-hex hexdigs) last-pos ppstate)
          (reterr-msg :where (position-to-msg next-pos)
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
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex zero or more characters and escape sequences
          in a character constant,
          during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as @(tsee lex-*-c-char),
     but it operates on preprocessor states instead of parser states,
     and we exclude CR besides LF."))
  (b* (((reterr) nil (irr-position) ppstate)
       ((erp char pos ppstate) (pread-char ppstate))
       ((unless char)
        (reterr-msg :where (position-to-msg pos)
                    :expected "an escape sequence or ~
                               any character other than ~
                               single quote or backslash or new-line"
                    :found (char-to-msg char)))
       ((when (utf8-= char (char-code #\'))) ; '
        (retok nil pos ppstate))
       ((when (or (utf8-= char 10) (utf8-= char 13))) ; new-line
        (reterr-msg :where (position-to-msg pos)
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
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

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
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex zero or more characters and escape sequences
          in a string literal,
          during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as @(tsee lex-*-s-char),
     but it operates on preprocessor states instead of parser states,
     and we exclude CR besides LF."))
  (b* (((reterr) nil (irr-position) ppstate)
       ((erp char pos ppstate) (pread-char ppstate))
       ((unless char)
        (reterr-msg :where (position-to-msg pos)
                    :expected "an escape sequence or ~
                               any character other than ~
                               double quote or backslash"
                    :found (char-to-msg char)))
       ((when (utf8-= char (char-code #\"))) ; "
        (retok nil pos ppstate))
       ((when (or (utf8-= char 10) (utf8-= char 13))) ; new-line
        (reterr-msg :where (position-to-msg pos)
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
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

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
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex zero or more characters
          in a header name between angle brackets,
          during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as @(tsee lex-*-h-char),
     but it operates on preprocessor states instead of parser states."))
  (b* (((reterr) nil (irr-position) ppstate)
       ((erp char pos ppstate) (pread-char ppstate))
       ((unless char)
        (reterr-msg :where (position-to-msg pos)
                    :expected "any character other than ~
                               greater-than or new-line"
                    :found (char-to-msg char)))
       ((when (utf8-= char (char-code #\>))) ; >
        (retok nil pos ppstate))
       ((when (or (utf8-= char 10) (utf8-= char 13))) ; new-line
        (reterr-msg :where (position-to-msg pos)
                    :expected "any character other than ~
                               greater-than or new-line"
                    :found (char-to-msg char)))
       (hchar (h-char char))
       ((erp hchars closing-angle-pos ppstate) (plex-*-h-char ppstate)))
    (retok (cons hchar hchars) closing-angle-pos ppstate))
  :measure (ppstate->size ppstate)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

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
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex zero or more characters
          in a header name between double quotes,
          during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as @(tsee lex-*-q-char),
     but it operates on preprocessor states instead of parser states."))
  (b* (((reterr) nil (irr-position) ppstate)
       ((erp char pos ppstate) (pread-char ppstate))
       ((unless char)
        (reterr-msg :where (position-to-msg pos)
                    :expected "any character other than ~
                               greater-than or new-line"
                    :found (char-to-msg char)))
       ((when (utf8-= char (char-code #\"))) ; "
        (retok nil pos ppstate))
       ((when (or (utf8-= char 10) (utf8-= char 13))) ; new-line
        (reterr-msg :where (position-to-msg pos)
                    :expected "any character other than ~
                               greater-than or new-line"
                    :found (char-to-msg char)))
       (qchar (q-char char))
       ((erp qchars closing-dquote-pos ppstate) (plex-*-q-char ppstate)))
    (retok (cons qchar qchars) closing-dquote-pos ppstate))
  :measure (ppstate->size ppstate)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

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

(define plex-character-constant ((cprefix? cprefix-optionp)
                                 (first-pos positionp)
                                 (ppstate ppstatep))
  :returns (mv erp
               (lexeme plexemep)
               (span spanp)
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex a character constant during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as @(tsee lex-character-constant),
     but it operates on preprocessor states instead of parser states."))
  (b* (((reterr) (irr-plexeme) (irr-span) ppstate)
       ((erp cchars closing-squote-pos ppstate) (plex-*-c-char ppstate))
       (span (make-span :start first-pos :end closing-squote-pos))
       ((unless cchars)
        (reterr-msg :where (position-to-msg closing-squote-pos)
                    :expected "one or more characters and escape sequences"
                    :found "none")))
    (retok (plexeme-char (cconst cprefix? cchars)) span ppstate))

  ///

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
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex a string literal during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as @(tsee lex-string-literal),
     but it operates on preprocessor states instead of parser states."))
  (b* (((reterr) (irr-plexeme) (irr-span) ppstate)
       ((erp schars closing-dquote-pos ppstate) (plex-*-s-char ppstate))
       (span (make-span :start first-pos :end closing-dquote-pos)))
    (retok (plexeme-string (stringlit eprefix? schars)) span ppstate))

  ///

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
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex a header name during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as @(tsee lex-header-name),
     but it operates on preprocessor states instead of parser states,
     and it returns a lexeme instead of a header name."))
  (b* (((reterr) (irr-plexeme) (irr-span) ppstate)
       ((erp char first-pos ppstate) (pread-char ppstate)))
    (cond
     ((not char)
      (reterr-msg :where (position-to-msg first-pos)
                  :expected "a greater-than ~
                             or a double quote"
                  :found (char-to-msg char)))
     ((utf8-= char (char-code #\<)) ; <
      (b* (((erp hchars closing-angle-pos ppstate) (plex-*-h-char ppstate))
           (span (make-span :start first-pos :end closing-angle-pos))
           ((unless hchars)
            (reterr-msg :where (position-to-msg closing-angle-pos)
                        :expected "one or more characters"
                        :found "none")))
        (retok (plexeme-header (header-name-angles hchars)) span ppstate)))
     ((utf8-= char (char-code #\")) ; "
      (b* (((erp qchars closing-dquote-pos ppstate) (plex-*-q-char ppstate))
           (span (make-span :start first-pos :end closing-dquote-pos))
           ((unless qchars)
            (reterr-msg :where (position-to-msg closing-dquote-pos)
                        :expected "one or more characters"
                        :found "none")))
        (retok (plexeme-header (header-name-quotes qchars)) span ppstate)))
     (t ; other
      (reterr-msg :where (position-to-msg first-pos)
                  :expected "a greater-than ~
                             or a double quote"
                  :found (char-to-msg char)))))
  :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

  ///

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
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex a block comment during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as @(tsee lex-block-comment),
     but it operates on preprocessor states instead of parser states,
     and it returns the content of the comment as part of the lexeme.")
   (xdoc::p
    "Collecting the content of the comment,
     i.e. the characters between @('/*') and @('*/') (excluding both),
     requires some additional code here.
     Note that @('plex-rest-of-block-comment-after-star') is always called
     just after a @('*') has been read;
     the addition of that @('*') to the content is deferred
     until it is established that the @('*') is not part of
     the closing @('*/');
     see the comments interspersed with the code."))
  (b* (((reterr) (irr-plexeme) (irr-span) ppstate)
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
                    (content nat-listp)
                    (last-pos positionp)
                    (new-ppstate ppstatep :hyp (ppstatep ppstate)))
       :parents nil
       (b* (((reterr) nil (irr-position) ppstate)
            ((erp char pos ppstate) (pread-char ppstate)))
         (cond
          ((not char) ; EOF
           (reterr-msg :where (position-to-msg pos)
                       :expected "a character"
                       :found (char-to-msg char)
                       :extra (msg "The block comment starting at ~@1 ~
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
       :measure (ppstate->size ppstate))

     (define plex-rest-of-block-comment-after-star ((first-pos positionp)
                                                    (ppstate ppstatep))
       :returns (mv erp
                    (content nat-listp)
                    (last-pos positionp)
                    (new-ppstate ppstatep :hyp (ppstatep ppstate)))
       :parents nil
       (b* (((reterr) nil (irr-position) ppstate)
            ((erp char pos ppstate) (pread-char ppstate)))
         (cond
          ((not char) ; EOF
           (reterr-msg :where (position-to-msg pos)
                       :expected "a character"
                       :found (char-to-msg char)
                       :extra (msg "The block comment starting at ~@1 ~
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
       :measure (ppstate->size ppstate))

     :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

     ///

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

(define plex-line-comment ((first-pos positionp) (ppstate ppstatep))
  :returns (mv erp
               (lexeme plexemep)
               (span spanp)
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex a line comment during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as @(tsee lex-line-comment),
     but it operates on preprocessor states instead of parser states,
     and it returns the content of the comment as part of the lexeme.")
   (xdoc::p
    "Collecting the content of the comment,
     i.e. the characters between @('//') and newline (excluding both),
     requires some additional code here."))
  (b* (((reterr) (irr-plexeme) (irr-span) ppstate)
       ((erp content last-pos ppstate)
        (plex-line-comment-loop first-pos ppstate)))
    (retok (plexeme-line-comment content)
           (make-span :start first-pos :end last-pos)
           ppstate))

  :prepwork

  ((define plex-line-comment-loop ((first-pos positionp) (ppstate ppstatep))
     :returns (mv erp
                  (content nat-listp)
                  (last-pos positionp)
                  (new-ppstate ppstatep :hyp (ppstatep ppstate)))
     :parents nil
     (b* (((reterr) nil (irr-position) ppstate)
          ((erp char pos ppstate) (pread-char ppstate)))
       (cond
        ((not char) ; EOF
         (reterr-msg :where (position-to-msg pos)
                     :expected "a character"
                     :found (char-to-msg char)
                     :extra (msg "The line comment starting at ~@1 ~
                                  never ends."
                                 (position-to-msg first-pos))))
        ((utf8-= char 10) ; LF
         (retok nil pos ppstate))
        ((utf8-= char 13) ; CR
         (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
           (cond
            ((not char2) ; CR EOF
             (retok nil pos ppstate))
            ((utf8-= char2 10) ; CR LF
             (retok nil pos2 ppstate))
            (t ; LF other
             (b* ((ppstate (punread-char ppstate))) ; LF
               (retok nil pos ppstate))))))
        (t ; other
         (b* (((erp content last-pos ppstate)
               (plex-line-comment-loop first-pos ppstate)))
           (retok (cons char content) last-pos ppstate)))))
     :measure (ppstate->size ppstate)
     :guard-hints (("Goal" :in-theory (enable acl2-numberp-when-natp)))

     ///

     (defret ppstate->size-of-plex-line-comment-loop-uncond
       (<= (ppstate->size new-ppstate)
           (ppstate->size ppstate))
       :rule-classes :linear
       :hints (("Goal" :induct t)))

     (defret ppstate->size-of-plex-line-comment-loop-cond
       (implies (not erp)
                (<= (ppstate->size new-ppstate)
                    (1- (ppstate->size ppstate))))
       :rule-classes :linear
       :hints (("Goal" :induct t)))))

  ///

  (defret ppstate->size-of-plex-line-comment-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear)

  (defret ppstate->size-of-plex-line-comment-cond
    (implies (not erp)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-spaces ((first-pos positionp) (ppstate ppstatep))
  :returns (mv erp
               (lexeme plexemep)
               (span spanp)
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
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
  (b* (((reterr) (irr-plexeme) (irr-span) ppstate)
       ((erp nspaces last-pos ppstate) (plex-spaces-loop first-pos ppstate)))
    (retok (plexeme-spaces (1+ nspaces))
           (make-span :start first-pos :end last-pos)
           ppstate))

  :prepwork

  ((define plex-spaces-loop ((prev-pos positionp) (ppstate ppstatep))
     :returns (mv erp
                  (nspaces natp :rule-classes (:rewrite :type-prescription))
                  (last-pos positionp)
                  (new-ppstate ppstatep :hyp (ppstatep ppstate)))
     :parents nil
     (b* (((reterr) 0 (irr-position) ppstate)
          ((erp char pos ppstate) (pread-char ppstate)))
       (cond
        ((not char) ; end of file
         (retok 0 (position-fix prev-pos) ppstate))
        ((utf8-= char 32) ; SP
         (b* (((erp nspaces last-pos ppstate)
               (plex-spaces-loop pos ppstate)))
           (retok (1+ nspaces) last-pos ppstate)))
        (t ; other
         (b* ((ppstate (punread-char ppstate)))
           (retok 0 (position-fix prev-pos) ppstate)))))
     :measure (ppstate->size ppstate)
     :verify-guards :after-returns

     ///

     (defret ppstate->size-of-plex-spaces-loop-uncond
       (<= (ppstate->size new-ppstate)
           (ppstate->size ppstate))
       :rule-classes :linear
       :hints (("Goal" :induct t)))))

  ///

  (defret ppstate->size-of-plex-spaces-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-lexeme ((headerp booleanp) (ppstate ppstatep))
  :returns (mv erp
               (lexeme? plexeme-optionp)
               (span spanp)
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex a lexeme during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level lexing function for the preprocessor.
     It returns the next lexeme found in the parser state,
     or @('nil') if we reached the end of the file;
     an error is returned if lexing fails.")
   (xdoc::p
    "Lexing in the preprocessor is context-dependent
     [C17:5.1.1.2/1, footnote 7]:
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
    "This lexing function is similar to @(tsee lex-lexeme),
     with the necessary differences,
     including the handling of the context header flag."))

  (b* (((reterr) nil (irr-span) ppstate)
       ((erp char pos ppstate) (pread-char ppstate))
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
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
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
          (b* ((ppstate (punread-char ppstate))) ; CR
            (retok (plexeme-newline (newline-cr))
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((and (utf8-<= (char-code #\0) char)
           (utf8-<= char (char-code #\9))) ; 0-9
      (plex-pp-number nil (code-char char) pos ppstate))

     ((utf8-= char (char-code #\.)) ; .
      (b* (((erp char2 & ppstate) (pread-char ppstate)))
        (cond
         ((not char2) ; . EOF
          (retok (plexeme-punctuator ".")
                 (make-span :start pos :end pos)
                 ppstate))
         ((and (utf8-<= (char-code #\0) char2)
               (utf8-<= char2 (char-code #\9))) ; . 0-9
          (plex-pp-number t (code-char char2) pos ppstate))
         ((utf8-= char2 (char-code #\.)) ; . .
          (b* (((erp char3 pos3 ppstate) (pread-char ppstate)))
            (cond
             ((not char3) ; . . EOF
              (b* ((ppstate (punread-char ppstate))) ; .
                (retok (plexeme-punctuator ".")
                       (make-span :start pos :end pos)
                       ppstate)))
             ((utf8-= char3 (char-code #\.)) ; . . .
              (retok (plexeme-punctuator "...")
                     (make-span :start pos :end pos3)
                     ppstate))
             (t ; . . other
              (b* ((ppstate (punread-char ppstate)) ; . .
                   (ppstate (punread-char ppstate))) ; .
                (retok (plexeme-punctuator ".")
                       (make-span :start pos :end pos)
                       ppstate))))))
         (t ; . other
          (b* ((ppstate (punread-char ppstate))) ; .
            (retok (plexeme-punctuator ".")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\u)) ; u
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
        (cond
         ((not char2) ; u EOF
          (retok (plexeme-ident (ident "u"))
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\')) ; u '
          (plex-character-constant (cprefix-locase-u) pos ppstate))
         ((utf8-= char2 (char-code #\")) ; u "
          (plex-string-literal (eprefix-locase-u) pos ppstate))
         ((utf8-= char2 (char-code #\8)) ; u 8
          (b* (((erp char3 & ppstate) (pread-char ppstate)))
            (cond
             ((not char3) ; u 8 EOF
              (retok (plexeme-ident (ident "u8"))
                     (make-span :start pos :end pos2)
                     ppstate))
             ((utf8-= char3 (char-code #\")) ; u 8 "
              (plex-string-literal (eprefix-locase-u8) pos ppstate))
             (t ; u 8 other
              (b* ((ppstate (punread-char ppstate)) ; u 8
                   (ppstate (punread-char ppstate))) ; u
                (plex-identifier char pos ppstate))))))
         (t ; u other
          (b* ((ppstate (punread-char ppstate))) ; u
            (plex-identifier char pos ppstate))))))

     ((utf8-= char (char-code #\U)) ; U
      (b* (((erp char2 & ppstate) (pread-char ppstate)))
        (cond
         ((not char2) ; U EOF
          (retok (plexeme-ident (ident "U"))
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\')) ; U '
          (plex-character-constant (cprefix-upcase-u) pos ppstate))
         ((utf8-= char2 (char-code #\")) ; U "
          (plex-string-literal (eprefix-upcase-u) pos ppstate))
         (t ; U other
          (b* ((ppstate (punread-char ppstate))) ; U
            (plex-identifier char pos ppstate))))))

     ((utf8-= char (char-code #\L)) ; L
      (b* (((erp char2 & ppstate) (pread-char ppstate)))
        (cond
         ((not char2) ; L EOF
          (retok (plexeme-ident (ident "L"))
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\')) ; L '
          (plex-character-constant (cprefix-upcase-l) pos ppstate))
         ((utf8-= char2 (char-code #\")) ; L "
          (plex-string-literal (eprefix-upcase-l) pos ppstate))
         (t ; L other
          (b* ((ppstate (punread-char ppstate))) ; L
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
          (b* ((ppstate (punread-char ppstate))) ;
            (plex-header-name ppstate))
        (plex-string-literal nil pos ppstate)))

     ((utf8-= char (char-code #\/)) ; /
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
        (cond
         ((not char2) ; / EOF
          (retok (plexeme-punctuator "/")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\*)) ; / *
          (plex-block-comment pos ppstate))
         ((utf8-= char2 (char-code #\/)) ; / /
          (plex-line-comment pos ppstate))
         ((utf8-= char2 (char-code #\=)) ; / =
          (retok (plexeme-punctuator "/=")
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; / other
          (b* ((ppstate (punread-char ppstate))) ; /
            (retok (plexeme-punctuator "/")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\#)) ; #
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
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
          (b* ((ppstate (punread-char ppstate)))
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
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
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
          (b* ((ppstate (punread-char ppstate)))
            (retok (plexeme-punctuator "*")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\^)) ; ^
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
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
          (b* ((ppstate (punread-char ppstate)))
            (retok (plexeme-punctuator "^")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\!)) ; !
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
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
          (b* ((ppstate (punread-char ppstate)))
            (retok (plexeme-punctuator "!")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\=)) ; =
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
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
          (b* ((ppstate (punread-char ppstate)))
            (retok (plexeme-punctuator "=")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\:)) ; :
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
        (cond
         ((not char2) ; : EOF
          (retok (plexeme-punctuator ":")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\>)) ; : >
          (retok (plexeme-punctuator ":>")
                 (make-span :start pos :end pos2)
                 ppstate))
         (t ; : other
          (b* ((ppstate (punread-char ppstate)))
            (retok (plexeme-punctuator ":")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\&)) ; &
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
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
          (b* ((ppstate (punread-char ppstate)))
            (retok (plexeme-punctuator "&")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\|)) ; |
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
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
          (b* ((ppstate (punread-char ppstate)))
            (retok (plexeme-punctuator "|")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\+)) ; +
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
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
          (b* ((ppstate (punread-char ppstate)))
            (retok (plexeme-punctuator "+")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\-)) ; -
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
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
          (b* ((ppstate (punread-char ppstate)))
            (retok (plexeme-punctuator "-")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\>)) ; >
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
        (cond
         ((not char2) ; > EOF
          (retok (plexeme-punctuator ">")
                 (make-span :start pos :end pos)
                 ppstate))
         ((utf8-= char2 (char-code #\>)) ; > >
          (b* (((erp char3 pos3 ppstate) (pread-char ppstate)))
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
              (b* ((ppstate (punread-char ppstate))) ; > >
                (retok (plexeme-punctuator ">>")
                       (make-span :start pos :end pos2)
                       ppstate))))))
         ((utf8-= char2 (char-code #\=)) ; > =
          (retok (plexeme-punctuator ">=")
                 (make-span :start pos :end pos)
                 ppstate))
         (t ; > other
          (b* ((ppstate (punread-char ppstate))) ; >
            (retok (plexeme-punctuator ">")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\%)) ; %
      (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
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
          (b* (((erp char3 & ppstate) (pread-char ppstate)))
            (cond
             ((not char3) ; % : EOF
              (retok (plexeme-punctuator "%:")
                     (make-span :start pos :end pos2)
                     ppstate))
             ((utf8-= char3 (char-code #\%)) ; % : %
              (b* (((erp char4 pos4 ppstate) (pread-char ppstate)))
                (cond
                 ((not char4) ; % : % EOF
                  (b* ((ppstate (punread-char ppstate))) ; % :
                    (retok (plexeme-punctuator "%:")
                           (make-span :start pos :end pos2)
                           ppstate)))
                 ((utf8-= char4 (char-code #\:)) ; % : % :
                  (retok (plexeme-punctuator "%:%:")
                         (make-span :start pos :end pos4)
                         ppstate))
                 (t ; % : % other
                  (b* ((ppstate (punread-char ppstate)) ; % : %
                       (ppstate (punread-char ppstate))) ; % :
                    (retok (plexeme-punctuator "%:")
                           (make-span :start pos :end pos2)
                           ppstate))))))
             (t ; % : other
              (b* ((ppstate (punread-char ppstate))) ; % :
                (retok (plexeme-punctuator "%:")
                       (make-span :start pos :end pos2)
                       ppstate))))))
         (t ; % other
          (b* ((ppstate (punread-char ppstate))) ; %
            (retok (plexeme-punctuator "%")
                   (make-span :start pos :end pos)
                   ppstate))))))

     ((utf8-= char (char-code #\<)) ; <
      (if headerp
          (b* ((ppstate (punread-char ppstate))) ;
            (plex-header-name ppstate))
        (b* (((erp char2 pos2 ppstate) (pread-char ppstate)))
          (cond
           ((not char2) ; < EOF
            (retok (plexeme-punctuator "<")
                   (make-span :start pos :end pos)
                   ppstate))
           ((utf8-= char2 (char-code #\<)) ; < <
            (b* (((erp char3 pos3 ppstate) (pread-char ppstate)))
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
                (b* ((ppstate (punread-char ppstate))) ; < <
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
            (b* ((ppstate (punread-char ppstate))) ; <
              (retok (plexeme-punctuator "<")
                     (make-span :start pos :end pos)
                     ppstate)))))))

     (t ; other
      (retok (plexeme-other char)
             (make-span :start pos :end pos)
             ppstate))))

  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p
                                           integer-range-p
                                           dec-digit-char-p
                                           the-check)))

  ///

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plex-token ((headerp booleanp) (ppstate ppstatep))
  :returns (mv erp
               (nontokens plexeme-listp)
               (token? plexeme-optionp)
               (token-span spanp)
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Lex a token during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "We lex zero or more non-tokens, until we find a token.
     We return the list of non-tokens, and the token with its span.
     If we reach the end of file, we return @('nil') as the token,
     and an span consisting of just the current position.")
   (xdoc::p
    "The @('headerp') flag has the same meaning as in @(tsee plex-lexeme):
     see that function's documentation."))
  (b* (((reterr) nil nil (irr-span) ppstate)
       ((erp lexeme span ppstate) (plex-lexeme headerp ppstate))
       ((when (not lexeme)) (retok nil nil span ppstate))
       ((when (plexeme-tokenp lexeme)) (retok nil lexeme span ppstate))
       ((erp nontokens token token-span ppstate) (plex-token headerp ppstate)))
    (retok (cons lexeme nontokens) token token-span ppstate))
  :measure (ppstate->size ppstate)

  ///

  (defret plexeme-list-nontokenp-of-plex-token
    (plexeme-list-nontokenp nontokens)
    :hints (("Goal" :induct t)))

  (defret plexeme-tokenp-of-plex-token
    (implies token?
             (plexeme-tokenp token?))
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-plex-token-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-plexr-token-cond
    (implies (and (not erp)
                  token?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: continue
