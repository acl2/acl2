; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "parser-states")

(include-book "kestrel/fty/nat-option" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ reader
  :parents (parser)
  :short "Reader component of the parser."
  :long
  (xdoc::topstring
   (xdoc::p
    "This reads Unicode characters from bytes.
     It provides a layer upon which the @(see lexer) is built."))
  :order-subtopics t
  :default-parent t)

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
    "First we check whether the sequence of unread characters is not empty.
     If it is not empty, we move a character from that sequence
     to the sequence of read characters,
     which amounts to incrementing @('chars-read')
     and decrementing @('chars-unread'),
     with no change to the array;
     see @(tsee parstate).
     We also need to check that the @('size') stobj component is not 0,
     which should be an invariant but it is not explicated in the stobj,
     because we also decrement that stobj component,
     to maintain the invariant.
     We read the character (and its position)
     from the array so we can return it,
     but we need to check that the index (i.e. @('chars-read'))
     is within the bounds of the array.
     Maybe we could optimize this check away with suitable invariants,
     presumably via abstract stobjs;
     this could also let us optimize away
     the extra check on @('size') mentioned above.")
   (xdoc::p
    "If the sequence of unread characters is empty,
     we need to read the next character from the bytes.
     If there are no more bytes, we have reached the end of file.
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
     (also in line with [C17:5.2.1/3]);
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
       ((when (and (> parstate.chars-unread 0)
                   (> parstate.size 0)))
        (b* (((unless (< parstate.chars-read
                         (parstate->chars-length parstate)))
              (raise "Internal error: index ~x0 out of bound ~x1."
                     parstate.chars-read
                     (parstate->chars-length parstate))
              (reterr t))
             (char+pos (parstate->char parstate.chars-read parstate))
             (parstate (update-parstate->chars-unread (1- parstate.chars-unread)
                                                      parstate))
             (parstate (update-parstate->chars-read (1+ parstate.chars-read)
                                                    parstate))
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
             ((unless (< parstate.chars-read
                         (parstate->chars-length parstate)))
              (raise "Internal error: index ~x0 out of bound ~x1."
                     parstate.chars-read
                     (parstate->chars-length parstate))
              (reterr t))
             (parstate (update-parstate->char parstate.chars-read
                                              (make-char+position
                                               :char byte
                                               :position parstate.position)
                                              parstate))
             (parstate (update-parstate->chars-read (1+ parstate.chars-read)
                                                    parstate))
             (parstate (update-parstate->size (1- parstate.size) parstate)))
          (retok byte parstate.position parstate)))
       ;; line feed:
       ((when (= byte 10))
        (b* ((parstate (update-parstate->bytes bytes parstate))
             (parstate (update-parstate->position
                        (position-inc-line 1 parstate.position) parstate))
             ((unless (< parstate.chars-read
                         (parstate->chars-length parstate)))
              (raise "Internal error: index ~x0 out of bound ~x1."
                     parstate.chars-read
                     (parstate->chars-length parstate))
              (reterr t))
             (parstate (update-parstate->char parstate.chars-read
                                              (make-char+position
                                               :char 10
                                               :position parstate.position)
                                              parstate))
             (parstate (update-parstate->chars-read (1+ parstate.chars-read)
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
             ((unless (< parstate.chars-read
                         (parstate->chars-length parstate)))
              (raise "Internal error: index ~x0 out of bound ~x1."
                     parstate.chars-read
                     (parstate->chars-length parstate))
              (reterr t))
             (parstate (update-parstate->char parstate.chars-read
                                              (make-char+position
                                               :char 10
                                               :position parstate.position)
                                              parstate))
             (parstate (update-parstate->chars-read (1+ parstate.chars-read)
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
             ((unless (< parstate.chars-read
                         (parstate->chars-length parstate)))
              (raise "Internal error: index ~x0 out of bound ~x1."
                     parstate.chars-read
                     (parstate->chars-length parstate))
              (reterr t))
             (parstate (update-parstate->char parstate.chars-read
                                              (make-char+position
                                               :char code
                                               :position parstate.position)
                                              parstate))
             (parstate (update-parstate->chars-read (1+ parstate.chars-read)
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
             ((unless (< parstate.chars-read
                         (parstate->chars-length parstate)))
              (raise "Internal error: index ~x0 out of bound ~x1."
                     parstate.chars-read
                     (parstate->chars-length parstate))
              (reterr t))
             (parstate (update-parstate->char parstate.chars-read
                                              (make-char+position
                                               :char code
                                               :position parstate.position)
                                              parstate))
             (parstate (update-parstate->chars-read (1+ parstate.chars-read)
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
             ((unless (< parstate.chars-read
                         (parstate->chars-length parstate)))
              (raise "Internal error: index ~x0 out of bound ~x1."
                     parstate.chars-read
                     (parstate->chars-length parstate))
              (reterr t))
             (parstate (update-parstate->char parstate.chars-read
                                              (make-char+position
                                               :char code
                                               :position parstate.position)
                                              parstate))
             (parstate (update-parstate->chars-read (1+ parstate.chars-read)
                                                    parstate))
             (parstate (update-parstate->size (- parstate.size 4) parstate)))
          (retok code parstate.position parstate))))
    (reterr-msg :where (position-to-msg parstate.position)
                :expected "a byte in the range 9-13 or 32-126 or 192-223"
                :found (msg "the byte ~x0" byte)))
  :guard-hints (("Goal" :in-theory (enable len fix natp)))
  :prepwork ((local (in-theory (enable acl2-numberp-when-bytep
                                       acl2-numberp-when-natp
                                       rationalp-when-bytep
                                       rationalp-when-natp
                                       integerp-when-natp
                                       natp-when-bytep))))

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
    "We move the character from the sequence of read characters
     to the sequence of unread characters,
     by incrementing @('chars-unread') and decrementing @('chars-read').")
   (xdoc::p
    "It is an internal error if @('chars-read') is 0.
     It means that the calling code is wrong.
     In this case, after raising the hard error,
     logically we return a parser state
     where we still increment @('chars-unread')
     so that the theorem about @(tsee parsize) holds unconditionally."))
  (b* ((parstate.chars-read (parstate->chars-read parstate))
       (parstate.chars-unread (parstate->chars-unread parstate))
       (parstate.size (parstate->size parstate))
       ((unless (> parstate.chars-read 0))
        (raise "Internal error: no character to unread.")
        (b* ((parstate (update-parstate->chars-unread (1+ parstate.chars-unread)
                                                      parstate))
             (parstate (update-parstate->size (1+ parstate.size) parstate)))
          parstate))
       (parstate (update-parstate->chars-read (1- parstate.chars-read)
                                              parstate))
       (parstate (update-parstate->chars-unread (1+ parstate.chars-unread)
                                                parstate))
       (parstate (update-parstate->size (1+ parstate.size) parstate)))
    parstate)
  :guard-hints (("Goal" :in-theory (enable natp)))

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
    "We move characters
     from the sequence of read characters
     to the sequence of unread characters
     by incrementing the number of unread characters by @('n')
     and decrementing the number of read characters by @('n').")
   (xdoc::p
    "It is an internal error if @('n') exceeds
     the number of character read so far.
     In this case, besides raising the error,
     we increment @('chars-unread') so that
     the theorem on the parser state size holds unconditionally."))
  (b* ((n (nfix n))
       (chars-read (parstate->chars-read parstate))
       (chars-unread (parstate->chars-unread parstate))
       (size (parstate->size parstate))
       ((unless (<= n chars-read))
        (raise "Internal error: ~
                attempting to unread ~x0 characters ~
                from ~x1 read characters."
               n chars-read)
        (b* ((parstate
              (update-parstate->chars-unread (+ chars-unread n) parstate))
             (parstate
              (update-parstate->size (+ size n) parstate)))
          parstate))
       (new-chars-read (- chars-read n))
       (new-chars-unread (+ chars-unread n))
       (new-size (+ size n))
       (parstate (update-parstate->chars-read new-chars-read parstate))
       (parstate (update-parstate->chars-unread new-chars-unread parstate))
       (parstate (update-parstate->size new-size parstate)))
    parstate)
  :guard-hints (("Goal" :in-theory (enable natp)))

  ///

  (defret parsize-of-unread-chars
    (equal (parsize new-parstate)
           (+ (parsize parstate) (nfix n)))
    :hints (("Goal" :in-theory (enable parsize nfix fix)))))
