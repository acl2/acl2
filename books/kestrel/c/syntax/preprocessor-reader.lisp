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

(local (include-book "kestrel/bv/logand" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cdr-of-byte-list-fix
  (equal (cdr (byte-list-fix x))
         (byte-list-fix (cdr x)))
  :induct t
  :enable byte-list-fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption byte-option
  acl2::byte
  :pred byte-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor-reader
  :parents (preprocessor)
  :short "Reader component of the preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "This realizes translation phases 1 and 2 [C17:5.1.1.2/1] [C23:5.2.1.2],
     i.e. how files, which consist of bytes (see @(see files)),
     are read into the source character set, which for us is Unicode,
     and how lines ending in backslash are spliced.
     The mapping of bytes to characters is UTF-8 decoding,
     but if the C version is C17,
     we also map trigraph sequences to the single characters they represent;
     although our tools aim at preserving concrete syntax information,
     trigraph sequences are a legacy feature that no longer seems useful
     (in fact, it is no longer present in [C23]).
     Line splicing also loses some of the original layout information,
     but we favor simplicity for now (we may revisit this later).")
   (xdoc::p
    "Since UTF-8 decoding is context-free,
     given all the bytes of a file,
     we can map them to a sequence of Unicode characters:
     this is how we initialize the character array in @(tsee ppstate).
     Trigraph sequences, if applicable, are handled as part of this.
     As we obtain the characters, we also obtain their positions in the file:
     thus, we can also initialize the array of positions in @(tsee ppstate).")
   (xdoc::p
    "Besides the code to map bytes to characters and positions,
     we provide code to initialize the preprocessor state from a file,
     and code to read and unread characters from the preprocessor state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-next-char ((pos positionp) (bytes byte-listp) (ienv ienvp))
  :returns (mv erp
               (char? uchar-optionp
                      :hints (("Goal"
                               :induct t
                               :in-theory (e/d (uchar-optionp)
                                               (acl2::commutativity-of-logand
                                                acl2::commutativity-2-of-+
                                                commutativity-of-+)))))
               (char-pos positionp)
               (next-pos positionp)
               (new-bytes byte-listp))
  :short "Read the next character from the remaining bytes,
          and calculate its position and the next position."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is repeatedly used to read characters
     by UTF-8-decoding the bytes of a file,
     at the same time calculating the position of each character in the file.
     The input position is the one at which
     the remaining bytes of the file are at.
     The output @('char-pos') is often the same as @('pos'),
     but not when the next character is a backslash followed by new line,
     because in that case the next character
     is not found at the position of the backslash,
     which is eliminated along with the new line to splice the line.
     The output @('next-pos') is the next position just after @('char?'),
     i.e. the position where the next character may be.
     If there is not character at @('pos'),
     we are at the end of the file:
     we return @('nil') as the character,
     and both @('char-pos') and @('next-pos') are equal to @('pos').
     If we read a character, we also return the remaining bytes;
     if there is no character, we retun @('nil') as the @('new-bytes') output.")
   (xdoc::p
    "A character can take one, two, three, or four bytes,
     according to the UTF8-decoding.
     Additionally, if the C version is C17,
     we turn three bytes that form three ASCII characters
     that form a trigraph sequence [C17:5.2.1.1]
     into the single ASCII character that they represent.
     This is not done if the C version is C23.")
   (xdoc::p
    "For most characters, the position is incremented by one column.
     For trigraph sequences, by three columns,
     because positions refer to the original file.
     For new lines, the line number is incremented
     and the column is reset to 0;
     if a new line consists of both a carriage return and a line feed,
     we do not change the position at the carriage return,
     but we do that at the line feed,
     as if carriage return and line feed were at the same position,
     which makes sense from a point of view.
     Currently a horizontal tab increments the column by one,
     but we should probably increment it to the next tab column,
     based on some additional information passed to this function;
     this would be consistent with the position information
     provided by Emacs and VS Code, for example.
     Currently a vertical tab or a form feed just increment the column by one,
     as if they were regular character;
     we could consider changing that
     (presumably based on additional information passed to this function),
     but the current behavior is consistent
     with Emacs and VS Code, for example
     (more precisely, Emacs increments the column by two,
     displaying vertical tab a @('^K') and form feed as @('^L'),
     each of which looks like formed by two regular characters.
     We treat all the non-ASCII Unicode characters
     as incrementing the column by one,
     which we might need to revise in some cases,
     but those seem unlikely to occur in practical C code.")
   (xdoc::p
    "When encountering a backslash followed by a new line,
     we skip both and we attempt to read a character after them.
     Since another backslash and new line may follow,
     this function is recursive, because there is no bound.
     Although the backslah and new line are not preserved,
     we increment the line number, and reset the column number,
     every time we find one,
     because the positions refer to the original file.
     Note that the backslash could derive from a trigraph sequence:
     trigraph sequences are processed in phase 1,
     while line splicing is processed in phase 2.")
   (xdoc::p
    "Looking at the rules in the ABNF grammar for basic and extended characters,
     we see that the codes of the three ASCII non-new-line extended characters
     (namely dollar, at sign, and backquote)
     fill gaps in the ASCII codes of the basic characters,
     so that the codes 9, 11, 12, and 32-126 are all valid ASCII characters.
     Note that, by the time we reach the case of normal ASCII characters,
     we have skipped the case for carriage return (13) and line feed (10).")
   (xdoc::p
    "We exclude most ASCII control characters,
     except for the basic ones and for the new-line ones,
     since there should be little need to use those in C code.
     Furthermore, some are dangerous, particularly backspace,
     since it may make the code look different from what it is,
     similarly to "
    (xdoc::ahref "https://en.wikipedia.org/wiki/Trojan_Source" "Trojan Source")
    " in Unicode.
     See our ABNF @(see grammar).")
   (xdoc::p
    "If the first byte we read is 128 or more,
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
     see the @('safe-nonascii') rule in our ABNF grammar.
     We also return an error if the character is a surrogate,
     i.e. from @('U+D800') to @('U+DFFF');
     note that this cannot happen
     in the first case above and in the third case below,
     because of their ranges and other checks.")
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
     We return an error in this case."))
  (b* (((reterr) nil (irr-position) (irr-position) nil)
       (bytes (byte-list-fix bytes))
       (pos (position-fix pos))
       ((when (endp bytes)) (retok nil pos pos nil))
       ((cons byte bytes) bytes)
       (pos+1 (position-inc-column 1 pos))
       ;; new lines:
       ((when (utf8-= byte 13)) ; CR
        (if (and (consp bytes)
                 (utf8-= (car bytes) 10)) ; CR LF
            (retok 13 pos pos bytes)
          (retok 13 pos (position-inc-line 1 pos) bytes)))
       ((when (utf8-= byte 10)) ; LF
        (retok 10 pos (position-inc-line 1 pos) bytes))
       ;; trigraph sequences, or just '?':
       ((when (utf8-= byte (char-code #\?))) ; ?
        (if (c::version-std-c23p (ienv->version ienv)) ; C23
            (retok (char-code #\?) pos pos+1 bytes) ; ?
          ;; consider trigraph sequences:
          (if (and (consp bytes)
                   (utf8-= (car bytes) (char-code #\?)) ; ? ?
                   (consp (cdr bytes)))
              (b* ((byte3 (cadr bytes)) ; ? ? byte3
                   (pos+3 (position-inc-column 3 pos)))
                (cond
                 ((utf8-= byte3 (char-code #\=)) ; ? ? =
                  (retok (char-code #\#) pos pos+3 (cddr bytes))) ; #
                 ((utf8-= byte3 (char-code #\()) ; ? ? (
                  (retok (char-code #\[) pos pos+3 (cddr bytes))) ; [
                 ((utf8-= byte3 (char-code #\/)) ; ? ? /
                  ;; line splicing, or just '\':
                  (b* ((bytes (cddr bytes)) ; consume ? /
                       ((unless (consp bytes)) ; \ EOF
                        (retok (char-code #\\) pos pos+3 bytes)) ; \
                       (byte (car bytes)) ; \ byte
                       ((when (utf8-= byte 13)) ; \ CR
                        (cond
                         ((and (consp (cdr bytes))
                               (utf8-= (cadr bytes) 10)) ; \ CR LF
                          (read-next-char (position-inc-line 1 pos+3)
                                          (cddr bytes) ; consume CR LF
                                          ienv))
                         (t ; \ CR other
                          (read-next-char (position-inc-line 1 pos+3)
                                          (cdr bytes) ; consume CR
                                          ienv))))
                       ((when (utf8-= byte 10)) ; \ LF
                        (read-next-char (position-inc-line 1 pos+3)
                                        (cdr bytes) ; consume LF
                                        ienv)))
                    (retok (char-code #\\) pos pos+3 bytes))) ; \
                 ((utf8-= byte3 (char-code #\))) ; ? ? )
                  (retok (char-code #\]) pos pos+3 (cddr bytes))) ; ]
                 ((utf8-= byte3 (char-code #\')) ; ? ? '
                  (retok (char-code #\^) pos pos+3 (cddr bytes))) ; ^
                 ((utf8-= byte3 (char-code #\<)) ; ? ? <
                  (retok (char-code #\{) pos pos+3 (cddr bytes))) ; {
                 ((utf8-= byte3 (char-code #\!)) ; ? ? !
                  (retok (char-code #\|) pos pos+3 (cddr bytes))) ; |
                 ((utf8-= byte3 (char-code #\>)) ; ? ? >
                  (retok (char-code #\}) pos pos+3 (cddr bytes))) ; }
                 ((utf8-= byte3 (char-code #\-)) ; ? ? -
                  (retok (char-code #\~) pos pos+3 (cddr bytes))) ; ~
                 (t ; ? ? other
                  (retok (char-code #\?) pos pos+1 bytes))))
            (retok (char-code #\?) pos pos+1 bytes)))) ; ? other
       ;; line splicing, or just '\':
       ((when (utf8-= byte (char-code #\\))) ; \
        (b* (((unless (consp bytes)) ; \ EOF
              (retok (char-code #\\) pos pos+1 bytes))
             (byte (car bytes))
             ((when (utf8-= byte 13)) ; \ CR
              (cond
               ((and (consp (cdr bytes))
                     (utf8-= (cadr bytes) 10)) ; \ CR LF
                (read-next-char (position-inc-line 1 pos+1)
                                (cddr bytes) ; consume CR LF
                                ienv))
               (t ; \ CR other
                (read-next-char (position-inc-line 1 pos+1)
                                (cdr bytes) ; consume CR
                                ienv))))
             ((when (utf8-= byte 10)) ; \ LF
              (read-next-char (position-inc-line 1 pos+1)
                              (cdr bytes) ; consume LF
                              ienv)))
          (retok (char-code #\\) pos pos+1 bytes))) ; \
       ;; other ASCII:
       ((when (or (utf8-= byte 9) ; HT
                  (utf8-= byte 11) ; VT
                  (utf8-= byte 12) ; FF
                  (and (utf8-<= 32 byte) (utf8-<= byte 126))))
        (retok byte pos pos+1 bytes))
       ;; 2-byte UTF-8:
       ((when (utf8-= (logand byte #b11100000) #b11000000)) ; 110xxxyy
        (b* (((unless (consp bytes))
              (reterr-msg :where pos
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 110... ~
                                          (i.e. between 192 and 223) ~
                                          of a two-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
             ((cons byte2 bytes) bytes)
             ((unless (utf8-= (logand byte2 #b11000000) #b10000000)) ; 10yyzzzz
              (reterr-msg :where pos
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 110... ~
                                          (i.e. between 192 and 223) ~
                                          of a two-byte UTF-8 encoding"
                                         byte)
                          :found (msg "the byte ~x0" byte2)))
             (char (+ (ash (logand byte #b00011111) 6)
                      (logand byte2 #b00111111)))
             ((when (< char #x80))
              (reterr-msg :where pos
                          :expected (msg "a value between 80h and 7FFh ~
                                          UTF-8-encoded in the two bytes ~
                                          (~x0 ~x1)"
                                         byte byte2)
                          :found (msg "the value ~x0" char))))
          (retok char pos pos+1 bytes)))
       ;; 3-byte UTF-8:
       ((when (utf8-= (logand byte #b11110000) #b11100000)) ; 1110xxxx
        (b* (((unless (consp bytes))
              (reterr-msg :where pos
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 1110... ~
                                          (i.e. between 224 to 239) ~
                                          of a three-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
             ((cons byte2 bytes) bytes)
             ((unless (utf8-= (logand byte2 #b11000000) #b10000000)) ; 10yyyyzz
              (reterr-msg :where pos
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 1110... ~
                                          (i.e. between 224 and 239) ~
                                          of a three-byte UTF-8 encoding"
                                         byte)
                          :found (msg "the byte ~x0" byte2)))
             ((unless (consp bytes))
              (reterr-msg :where pos
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
             ((cons byte3 bytes) bytes)
             ((unless (utf8-= (logand byte3 #b11000000) #b10000000)) ; 10zzwwww
              (reterr-msg :where pos
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
             (char (+ (ash (logand byte #b00001111) 12)
                      (ash (logand byte2 #b00111111) 6)
                      (logand byte3 #b00111111)))
             ((when (< char #x800))
              (reterr-msg :where pos
                          :expected (msg "a value between 800h and FFFFh ~
                                          UTF-8-encoded in the three bytes ~
                                          (~x0 ~x1 ~x2)"
                                         byte byte2 byte3)
                          :found (msg "the value ~x0" char)))
             ((when (or (and (utf8-<= #x202a char)
                             (utf8-<= char #x202e))
                        (and (utf8-<= #x2066 char)
                             (utf8-<= char #x2069))
                        (and (utf8-<= #xd800 char)
                             (utf8-<= char #xdfff))))
              (reterr-msg :where pos
                          :expected "a Unicode character with code ~
                                     in the range 9-13 or 32-126 ~
                                     or 128-8233 or 8239-8293 or ~
                                     or 8298-55295 or 57344-1114111"
                          :found (char-to-msg char))))
          (retok char pos pos+1 bytes)))
       ;; 4-byte UTF-8:
       ((when (utf8-= (logand #b11111000 byte) #b11110000)) ; 11110xyy
        (b* (((unless (consp bytes))
              (reterr-msg :where pos
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 to 247) ~
                                          of a four-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
             ((cons byte2 bytes) bytes)
             ((unless (utf8-= (logand byte2 #b11000000) #b10000000)) ; 10yyzzzz
              (reterr-msg :where pos
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 and 247) ~
                                          of a four-byte UTF-8 encoding"
                                         byte)
                          :found (msg "the byte ~x0" byte2)))
             ((unless bytes)
              (reterr-msg :where pos
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
             ((cons byte3 bytes) bytes)
             ((unless (utf8-= (logand byte3 #b11000000) #b10000000)) ; 10wwwwuu
              (reterr-msg :where pos
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
             ((unless (consp bytes))
              (reterr-msg :where pos
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
             ((cons byte4 bytes) bytes)
             ((unless (utf8-= (logand byte4 #b11000000) #b10000000)) ; 10uuvvvv
              (reterr-msg :where pos
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
             (char (+ (ash (logand byte #b00000111) 18)
                      (ash (logand byte2 #b00111111) 12)
                      (ash (logand byte3 #b00111111) 6)
                      (logand byte4 #b00111111)))
             ((when (or (< char #x10000)
                        (> char #x10ffff)))
              (reterr-msg :where pos
                          :expected (msg "a value between 10000h and 10FFFFh ~
                                          UTF-8-encoded in the four bytes ~
                                          (~x0 ~x1 ~x2 ~x3)"
                                         byte byte2 byte3 byte4)
                          :found (msg "the value ~x0" char))))
          (retok char pos pos+1 bytes))))
    (reterr-msg :where pos
                :expected "a byte in the range 9-13 or 32-126 or 192-223"
                :found (msg "the byte ~x0" byte)))
  :no-function nil
  :measure (len bytes)
  :hints (("Goal" :in-theory (enable cdr-of-byte-list-fix)))

  :prepwork

  ((defrulel returns-lemma1 ; ASCII
     (implies (and (bytep byte)
                   (or (utf8-= byte 9) ; HT
                       (utf8-= byte 11) ; VT
                       (utf8-= byte 12) ; FF
                       (and (utf8-<= 32 byte) (utf8-<= byte 126))))
              (ucharp byte))
     :enable (ucharp the-check))

   (defrulel returns-lemma2 ; 2-byte UTF-8
     (implies (and (bytep byte)
                   (bytep byte2)
                   (utf8-= (logand byte #b11100000) #b11000000)
                   (utf8-= (logand byte2 #b11000000) #b10000000))
              (ucharp (+ (ash (logand byte #b00011111) 6)
                         (logand byte2 #b00111111))))
     :enable ucharp
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))

   (defrulel returns-lemma3 ; 3-byte UTF-8
     (implies (and (bytep byte)
                   (bytep byte2)
                   (bytep byte3)
                   (utf8-= (logand byte #b11110000) #b11100000)
                   (utf8-= (logand byte2 #b11000000) #b10000000)
                   (utf8-= (logand byte3 #b11000000) #b10000000))
              (b* ((char (+ (ash (logand byte #b00001111) 12)
                            (ash (logand byte2 #b00111111) 6)
                            (logand byte3 #b00111111))))
                (implies (not (and (utf8-<= #xd800 char)
                                   (utf8-<= char #xdfff)))
                         (ucharp char))))
     :enable (ucharp the-check)
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))

   (defrulel returns-lemma4 ; 4-byte UTF-8
     (implies (and (bytep byte)
                   (bytep byte2)
                   (bytep byte3)
                   (bytep byte4)
                   (utf8-= (logand #b11111000 byte) #b11110000)
                   (utf8-= (logand byte2 #b11000000) #b10000000)
                   (utf8-= (logand byte3 #b11000000) #b10000000)
                   (utf8-= (logand byte4 #b11000000) #b10000000))
              (b* ((char (+ (ash (logand byte #b00000111) 18)
                            (ash (logand byte2 #b00111111) 12)
                            (ash (logand byte3 #b00111111) 6)
                            (logand byte4 #b00111111))))
                (implies (not (or (< char #x10000)
                                  (> char #x10ffff)))
                         (ucharp char))))
     :enable ucharp))

  ///

  (defret len-of-read-next-char-uncond
    (<= (len new-bytes)
        (len bytes))
    :rule-classes :linear
    :hints (("Goal"
             :induct t
             :in-theory (enable cdr-of-byte-list-fix))))

  (defret len-of-read-next-char-cond
    (implies (and (not erp)
                  char?)
             (<= (len new-bytes)
                 (1- (len bytes))))
    :rule-classes :linear
    :hints (("Goal"
             :induct t
             :in-theory (enable len endp fix cdr-of-byte-list-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-chars+positions ((file stringp) (bytes byte-listp) (ienv ienvp))
  :returns (mv erp (chars uchar-listp) (poss position-listp))
  :short "Read all the characters from a list of bytes,
          obtaining the list of characters and the corresponding positions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also pass the path of the file, to put into the positions.")
   (xdoc::p
    "We repeatedly call @(tsee read-next-char)
     so long as it returns characters.
     We start with the initial position.
     The final position is the one just past the end of the file.
     There is one more position than characters."))
  (read-chars+positions-loop (position-init file) bytes ienv)

  :prepwork
  ((define read-chars+positions-loop ((pos positionp)
                                      (bytes byte-listp)
                                      (ienv ienvp))
     :returns (mv erp (chars uchar-listp) (poss position-listp))
     :parents nil
     (b* (((reterr) nil (list (irr-position)))
          ((erp char? pos pos-next bytes) (read-next-char pos bytes ienv))
          ((unless char?) (retok nil (list pos)))
          ((erp chars poss) (read-chars+positions-loop pos-next bytes ienv)))
       (retok (cons char? chars) (cons pos poss)))
     :measure (len bytes)

     ///

     (defret len-of-read-chars+positions-loop-1+
       (equal (len poss) (1+ (len chars)))
       :hints (("Goal" :induct t)))))

  ///

  (defret len-of-read-chars+positions-1+
    (equal (len poss) (1+ (len chars))))

  (in-theory (disable len-of-read-chars+positions-1+
                      len-of-read-chars+positions-loop-1+)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ppstate-for-file ((file-name stringp)
                          (bytes byte-listp)
                          (macros macro-tablep)
                          (options ppoptionsp)
                          (ienv ienvp)
                          (ppstate ppstatep))
  :returns (mv erp (new-ppstate ppstatep))
  :short "Initialize a preprocessor for a file with given name and bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This operation is in a way a wrapper of @(tsee init-ppstate)
     that takes the bytes as input,
     turns them into a list of characters and a list of positions,
     and uses those to initialize the stobj with @(tsee init-ppstate)."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) ppstate)
       ((erp chars poss) (read-chars+positions file-name bytes ienv))
       (ppstate
        (init-ppstate chars poss macros options ienv ppstate)))
    (retok ppstate))
  :guard-hints (("Goal" :in-theory (enable len-of-read-chars+positions-1+))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-pchar ((ppstate ppstatep))
  :returns (mv erp
               (char? uchar-optionp)
               (pos positionp)
               (new-ppstate ppstatep))
  :short "Read a character during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since all the characters and their positions are already in the stobj,
     this function reads and returns the current character and position,
     advances the index by one,
     and updates the size component of the stobj.
     If the index is already one past the end of the characters array,
     @('nil') is returned as character,
     the index is not incremented,
     and the last position in the position array is returned,
     which indicates the position just past the end of the file.")
   (xdoc::p
    "We should avoid the checks and the internal errors
     by explicating and verifying some invariants,
     via an abstract stobj and/or guards."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil (irr-position) ppstate)
       (index (ppstate->char-index ppstate))
       ((unless (< index (ppstate->positions-length ppstate)))
        (raise "Internal error: ~
                the index ~x0 is not below ~
                the length ~x1 of the positions array."
               index
               (ppstate->positions-length ppstate))
        (reterr :should-not-happen))
       (pos (ppstate->position index ppstate)))
    (if (< index (ppstate->chars-length ppstate))
        (b* ((char (ppstate->char index ppstate))
             (ppstate (update-ppstate->char-index (1+ index) ppstate))
             (size (ppstate->size ppstate))
             ((unless (> size 0))
              (raise "Internal error: ~
                      there is a character at index ~x0 but the size is 0."
                     index)
              (reterr :should-not-happen))
             (ppstate (update-ppstate->size (1- size) ppstate)))
          (retok char pos ppstate))
      (retok nil pos ppstate)))
  :no-function nil

  ///

  (defret read-pchar-natp-or-null
    (or (natp char?)
        (not char?))
   :rule-classes :type-prescription)

  (defret ppstate->size-of-read-pchar-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear)

  (defret ppstate->size-of-read-pchar-cond
    (implies (and (not erp)
                  char?)
             (equal (ppstate->size new-ppstate)
                    (1- (ppstate->size ppstate))))
    :rule-classes (:rewrite :linear))

  (defret ppstate->lexmarks-of-read-pchar
    (equal (ppstate->lexmarks new-ppstate)
           (ppstate->lexmarks ppstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-pchar ((ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Unread a character during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "We decrement the character index and increment the size, both by one.")
   (xdoc::p
    "We should avoid the checks and the internal errors
     by explicating and verifying some invariants,
     via an abstract stobj and/or guards.
     Note that, in case of error, we increment the size anyways,
     so that we can have an unconditional theorem about the size."))
  (b* ((size (ppstate->size ppstate))
       (ppstate (update-ppstate->size (1+ size) ppstate))
       (index (ppstate->char-index ppstate))
       ((unless (> index 0))
        (raise "Internal error: no character to unread.")
        ppstate)
       (ppstate (update-ppstate->char-index (1- index) ppstate)))
    ppstate)
  :no-function nil

  ///

  (defret ppstate->size-of-unread-pchar
    (equal (ppstate->size new-ppstate)
           (1+ (ppstate->size ppstate))))

  (defret ppstate->lexmarks-of-unread-pchar
    (equal (ppstate->lexmarks new-ppstate)
           (ppstate->lexmarks ppstate)))

  (defrule unread-pchar-of-read-pchar
    (b* (((mv erp char? & new-ppstate) (read-pchar ppstate)))
      (implies (and (not erp)
                    char?)
               (equal (unread-pchar new-ppstate)
                      (ppstate-fix ppstate))))
    :enable (read-pchar
             nfix
             fix
             update-ppstate->size-of-update-ppstate->char-index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-pchars ((n natp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Unread a specified number of characters during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "We decrement the character index and increment the size, both by @('n').")
   (xdoc::p
    "We should avoid the checks and the internal errors
     by explicating and verifying some invariants,
     via an abstract stobj and/or guards.
     Note that, in case of error, we increment the size anyways,
     so that we can have an unconditional theorem about the size."))
  (b* ((n (nfix n))
       (size (ppstate->size ppstate))
       (ppstate (update-ppstate->size (+ n size) ppstate))
       (index (ppstate->char-index ppstate))
       ((unless (> index n))
        (raise "Internal error: ~
                cannot unread ~x0 characters, ~
                because only ~x1 have been read so far."
               n index)
        ppstate)
       (ppstate (update-ppstate->char-index (- index n) ppstate)))
    ppstate)
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable natp)))

  ///

  (defret ppstate->size-of-unread-pchars
    (equal (ppstate->size new-ppstate)
           (+ (ppstate->size ppstate) (nfix n)))))
