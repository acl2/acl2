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
(include-book "parser-messages")
(include-book "abstract-syntax-irrelevants")
(include-book "files")
(include-book "implementation-environments")

(include-book "kestrel/fty/character-list" :dir :system)
(include-book "kestrel/fty/nat-option" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

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

(defmacro utf8-= (x y)
  `(= (the unsigned-byte ,x)
      (the unsigned-byte ,y)))

(defmacro utf8-<= (x y)
  `(<= (the unsigned-byte ,x)
       (the unsigned-byte ,y)))

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
                    t)
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pchar-to-msg ((char nat-optionp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp
                                                   character-alistp))))
  :short "Represent an optional character as a message,
          in the preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is almost identical to @(tsee char-to-msg)
     (see its documentation first)
     with the difference that we consider LF and CR separately.
     This matches the fact that @(tsee pread-char), unlike @(tsee read-char),
     does not normalize the three possible kinds of new lines to LF."))
  (cond ((not char) "end of file")
        ((< char 32) (msg "the ~s0 character (ASCII code ~x1)"
                          (nth char *pchar-to-msg-ascii-control-char-names*)
                          char))
        ((utf8-= char 32) "the SP (space) character (ASCII code 32)")
        ((and (utf8-<= 33 char) (utf8-<= char 126))
         (msg "the ~s0 character (ASCII code ~x1)"
              (str::implode (list (code-char char))) char))
        ((utf8-= char 127) "the DEL (delete) character (ASCII code 127)")
        (t (msg "the non-ASCII Unicode character with code ~x0" char)))
  :guard-hints (("Goal" :in-theory (enable character-listp
                                           nat-optionp)))

  :prepwork
  ((defconst *pchar-to-msg-ascii-control-char-names*
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
       "LF (line feed)"
       "VT (vertical tab)"
       "FF (form feed)"
       "CR (carriage return)"
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-ppstate-for-char ((char natp)
                                 (new-bytes byte-listp)
                                 (new-position positionp)
                                 (size-decrement posp)
                                 (ppstate ppstatep))
  :guard (and (< (ppstate->chars-read ppstate)
                 (ppstate->chars-length ppstate))
              (>= (ppstate->size ppstate) size-decrement))
  :returns (new-ppstate ppstatep :hyp (ppstatep ppstate))
  :short "Update the preprocessor state for a character."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when @(tsee pread-char)
     reads a character from the data bytes (not from the unread characters).
     The @('new-bytes') input consists of the remaining data bytes,
     i.e. after the one ore more bytes that form the character
     have already been removed (and decoded).
     The @('new-position') input consists of the next position,
     which is normally one column more than the current one,
     except when dealing with new-line characters."))
  (b* ((position (ppstate->position ppstate))
       (chars-read (ppstate->chars-read ppstate))
       (size (ppstate->size ppstate))
       (new-size (- size (pos-fix size-decrement)))
       (char+pos (make-char+position :char char :position position))
       (ppstate (update-ppstate->bytes new-bytes ppstate))
       (ppstate (update-ppstate->char chars-read char+pos ppstate))
       (ppstate (update-ppstate->chars-read (1+ chars-read) ppstate))
       (ppstate (update-ppstate->position new-position ppstate))
       (ppstate (update-ppstate->size new-size ppstate)))
    ppstate)
  :guard-hints (("Goal" :in-theory (enable natp)))

  ///

  (defret ppstate->size-of-update-ppstate-for-char
    (equal (ppstate->size new-ppstate)
           (- (ppstate->size ppstate)
              (pos-fix size-decrement)))
    :hyp (>= (ppstate->size ppstate)
             (pos-fix size-decrement))
    :hints (("Goal" :in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pread-char ((ppstate ppstatep))
  :returns (mv erp
               (char? nat-optionp
                      :hints (("Goal" :induct t :in-theory (enable natp))))
               (pos positionp)
               (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Read a character during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is almost identical to @(tsee read-char)
     (see its documentation first),
     but with some differences.")
   (xdoc::p
    "Here we perform phases 1 and 2 of [C17:5.1.1.2].")
   (xdoc::p
    "Here the implementation-defined mapping
     from physical source file multibyte characters to the source character set
     amounts to UTF-8 decoding.")
   (xdoc::p
    "Unlike @(tsee read-char),
     here we do not normalize the three kinds of new lines to LF,
     because we want to preserve line endings.
     However, we need to be careful about how we increment the current position.
     If we read a CR, we check whether it is followed by LF.
     If that is the case, the line ending is the combination of CR and LF,
     and thus we do not change the position upon reading the CR
     (as if the CR took no visual space);
     when this function is called again next,
     it will read the LF, which always changes the position to the next line.
     If instead the CR is not followed by LF,
     then the CR is the whole line ending,
     and we change the position to the next line.
     Reading an LF always changes the position to the next line,
     whether it is preceded by CR (see above) or not;
     in the latter case, the LF is the whole line ending.")
   (xdoc::p
    "If the next character is a question mark,
     we check the subsequent characters (if any)
     to see whether we have a trigraph sequence,
     which we turn into the single character it denotes [C17:5.2.1.1].")
   (xdoc::p
    "If the next character is a backslash,
     we check whether it is followed by new-line characters,
     namely CR (not followed by LF), LF, or CR LF.
     If that is the case,
     the backslash and the new-line character(s) are skipped,
     and we recursively try to read another character.
     We also ensure that the backslash-new-line being deleted
     is not at the end of the file [C17:5.1.1.2/2]."))
  (b* (((reterr) nil (irr-position) ppstate)
       (ppstate.bytes (ppstate->bytes ppstate))
       (ppstate.position (ppstate->position ppstate))
       (ppstate.chars-read (ppstate->chars-read ppstate))
       (ppstate.chars-unread (ppstate->chars-unread ppstate))
       (ppstate.size (ppstate->size ppstate))
       ((when (> ppstate.chars-unread 0))
        (b* (((unless (> ppstate.size 0))
              (raise "Internal error: ~
                      there are ~x0 unread characters ~
                      but the size of the preprocessing state is 0."
                     ppstate.chars-unread)
              (reterr t))
             ((unless (< ppstate.chars-read (ppstate->chars-length ppstate)))
              (raise "Internal error: index ~x0 out of bound ~x1."
                     ppstate.chars-read
                     (ppstate->chars-length ppstate))
              (reterr t))
             (char+pos (ppstate->char ppstate.chars-read ppstate))
             (ppstate (update-ppstate->chars-unread (1- ppstate.chars-unread)
                                                    ppstate))
             (ppstate (update-ppstate->chars-read (1+ ppstate.chars-read)
                                                  ppstate))
             (ppstate (update-ppstate->size (1- ppstate.size) ppstate)))
          (retok (char+position->char char+pos)
                 (char+position->position char+pos)
                 ppstate)))
       ((unless (consp ppstate.bytes))
        (if (> ppstate.size 0)
            (prog2$ (raise "Internal error: ~
                            there are no unread characters and no more bytes, ~
                            but the size of the preprocessing state is ~x0."
                           ppstate.size)
                    (reterr t))
          (retok nil ppstate.position ppstate)))
       ((unless (> ppstate.size 0))
        (raise "Internal error: ~
                there are more bytes but ~
                the size of the preprocessing state is 0.")
        (reterr t))
       (byte (car ppstate.bytes))
       (bytes (cdr ppstate.bytes))
       ((unless (< ppstate.chars-read (ppstate->chars-length ppstate)))
        (raise "Internal error: index ~x0 out of bound ~x1."
               ppstate.chars-read
               (ppstate->chars-length ppstate))
        (reterr t))
       ;; new lines:
       ((when (utf8-= byte 13)) ; CR
        (b* ((lf-follows-cr-p (and (consp bytes) (utf8-= (car bytes) 10)))
             (new-position (if lf-follows-cr-p
                               ppstate.position
                             (position-inc-line 1 ppstate.position)))
             (ppstate
              (update-ppstate-for-char 13 bytes new-position 1 ppstate)))
          (retok 13 ppstate.position ppstate)))
       ((when (utf8-= byte 10)) ; LF
        (b* ((new-position (position-inc-line 1 ppstate.position))
             (ppstate
              (update-ppstate-for-char 10 bytes new-position 1 ppstate)))
          (retok 10 ppstate.position ppstate)))
       ;; trigraph sequences (or just '?'):
       ((when (utf8-= byte (char-code #\?))) ; ?
        (b* (((mv char new-bytes num-chars/bytes)
              (if (and (consp bytes)
                       (utf8-= (car bytes) (char-code #\?)) ; ??
                       (consp (cdr bytes)))
                  (b* (((unless (>= ppstate.size 3))
                        (raise "Internal error: ~
                                there are three or more bytes ~
                                but the size of the preprocessing state is ~x0."
                               ppstate.size)
                        (mv 0 nil 1)))
                    (cond ((utf8-= (cadr bytes) (char-code #\=)) ; ??=
                           (mv (char-code #\#) (cddr bytes) 3))
                          ((utf8-= (cadr bytes) (char-code #\()) ; ??(
                           (mv (char-code #\[) (cddr bytes) 3))
                          ((utf8-= (cadr bytes) (char-code #\/)) ; ??/
                           (mv (char-code #\\) (cddr bytes) 3))
                          ((utf8-= (cadr bytes) (char-code #\))) ; ??)
                           (mv (char-code #\]) (cddr bytes) 3))
                          ((utf8-= (cadr bytes) (char-code #\')) ; ??'
                           (mv (char-code #\^) (cddr bytes) 3))
                          ((utf8-= (cadr bytes) (char-code #\<)) ; ??<
                           (mv (char-code #\{) (cddr bytes) 3))
                          ((utf8-= (cadr bytes) (char-code #\!)) ; ??!
                           (mv (char-code #\|) (cddr bytes) 3))
                          ((utf8-= (cadr bytes) (char-code #\>)) ; ??>
                           (mv (char-code #\}) (cddr bytes) 3))
                          ((utf8-= (cadr bytes) (char-code #\-)) ; ??-
                           (mv (char-code #\~) (cddr bytes) 3))
                          (t (mv byte bytes 1)))) ; just ?, not a tripgraph
                (mv byte bytes 1))) ; just ?, not a trigraph
             (new-position
              (position-inc-column num-chars/bytes ppstate.position))
             (ppstate
              (update-ppstate-for-char
               char new-bytes new-position num-chars/bytes ppstate)))
          (retok char ppstate.position ppstate)))
       ;; line splicing (or just '\'):
       ((when (utf8-= byte (char-code #\\))) ; \
        (b* (((when (endp bytes)) ; \ EOF
              (reterr (msg "File ends with backslash instead of new line.")))
             ((when (utf8-= (car bytes) 10)) ; \ LF
              (b* (((unless (>= ppstate.size 2))
                    (raise "Internal error: ~
                            there are two or more bytes ~
                            but the size of the preprocessing state is ~x0."
                           ppstate.size)
                    (reterr t))
                   (new-bytes (cdr bytes))
                   (new-position (position-inc-line 1 ppstate.position))
                   (new-size (- ppstate.size 2))
                   (ppstate (update-ppstate->bytes new-bytes ppstate))
                   (ppstate (update-ppstate->position new-position ppstate))
                   (ppstate (update-ppstate->size new-size ppstate))
                   ((unless (consp new-bytes))
                    (reterr (msg "File ends with backslash and new line."))))
                (pread-char ppstate)))
             ((when (utf8-= (car bytes) 13)) ; \ CR
              (if (and (consp (cdr bytes))
                       (utf8-= (cadr bytes) 10)) ; \ CR LF
                  (b* (((when (endp (cddr bytes))) ; \ CR LF EOF
                        (reterr (msg "File ends with backslash and new line ~
                                      instead of new line.")))
                       ((unless (>= ppstate.size 3))
                        (raise "Internal error: ~
                                there are three or more bytes ~
                                but the size of the preprocessing state is ~x0."
                               ppstate.size)
                        (reterr t))
                       (new-bytes (cddr bytes))
                       (new-position (position-inc-line 1 ppstate.position))
                       (new-size (- ppstate.size 3))
                       (ppstate (update-ppstate->bytes new-bytes ppstate))
                       (ppstate (update-ppstate->position new-position ppstate))
                       (ppstate (update-ppstate->size new-size ppstate))
                       ((unless (consp new-bytes))
                        (reterr
                         (msg "File ends with backslash and new line."))))
                    (pread-char ppstate))
                (b* (((when (endp (cdr bytes))) ; \ CR EOF
                      (reterr (msg "File ends with backslash and new line ~
                                    instead of new line.")))
                     ((unless (>= ppstate.size 2))
                      (raise "Internal error: ~
                              there are three or more bytes ~
                              but the size of the preprocessing state is ~x0."
                             ppstate.size)
                      (reterr t))
                     (new-bytes (cdr bytes))
                     (new-position (position-inc-line 1 ppstate.position))
                     (new-size (- ppstate.size 2))
                     (ppstate (update-ppstate->bytes new-bytes ppstate))
                     (ppstate (update-ppstate->position new-position ppstate))
                     (ppstate (update-ppstate->size new-size ppstate))
                     ((unless (consp new-bytes))
                      (reterr (msg "File ends with backslash and new line."))))
                  (pread-char ppstate))))
             ;; just \, no line splicing
             (new-position (position-inc-column 1 ppstate.position))
             (ppstate
              (update-ppstate-for-char byte bytes new-position 1 ppstate)))
          (retok byte ppstate.position ppstate)))
       ;; other ASCII:
       ((when (or (utf8-= byte 9) ; HT
                  (utf8-= byte 11) ; VT
                  (utf8-= byte 12) ; FF
                  (and (utf8-<= 32 byte) (utf8-<= byte 126))))
        (b* ((new-position (position-inc-column 1 ppstate.position))
             (ppstate
              (update-ppstate-for-char byte bytes new-position 1 ppstate)))
          (retok byte ppstate.position ppstate)))
       ;; 2-byte UTF-8:
       ((when (utf8-= (logand byte #b11100000) #b11000000)) ; 110xxxyy
        (b* (((unless (consp bytes))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 110... ~
                                          (i.e. between 192 and 223) ~
                                          of a two-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
             ((unless (>= ppstate.size 2))
              (raise "Internal error: ~
                      there are two or more bytes ~
                      but the size of the preprocessing state is ~x0."
                     ppstate.size)
              (reterr t))
             (byte2 (car bytes))
             (bytes (cdr bytes))
             ((unless (utf8-= (logand byte2 #b11000000) #b10000000)) ; 10yyzzzz
              (reterr-msg :where (position-to-msg ppstate.position)
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
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a value between 80h and 7FFh ~
                                          UTF-8-encoded in the two bytes ~
                                          (~x0 ~x1)"
                                         byte byte2)
                          :found (msg "the value ~x0" code)))
             (new-position (position-inc-column 1 ppstate.position))
             (ppstate
              (update-ppstate-for-char code bytes new-position 2 ppstate)))
          (retok code ppstate.position ppstate)))
       ;; 3-byte UTF-8:
       ((when (utf8-= (logand byte #b11110000) #b11100000)) ; 1110xxxx
        (b* (((unless (consp bytes))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 1110... ~
                                          (i.e. between 224 to 239) ~
                                          of a three-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
             ((unless (>= ppstate.size 2))
              (raise "Internal error: ~
                      there are two or more bytes ~
                      but the size of the preprocessing state is ~x0."
                     ppstate.size)
              (reterr t))
             (byte2 (car bytes))
             (bytes (cdr bytes))
             ((unless (utf8-= (logand byte2 #b11000000) #b10000000)) ; 10yyyyzz
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 1110... ~
                                          (i.e. between 224 and 239) ~
                                          of a three-byte UTF-8 encoding"
                                         byte)
                          :found (msg "the byte ~x0" byte2)))
             ((unless (consp bytes))
              (reterr-msg :where (position-to-msg ppstate.position)
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
             ((unless (>= ppstate.size 3))
              (raise "Internal error: ~
                      there are three or more bytes ~
                      but the size of the preprocessing state is ~x0."
                     ppstate.size)
              (reterr t))
             (byte3 (car bytes))
             (bytes (cdr bytes))
             ((unless (utf8-= (logand byte3 #b11000000) #b10000000)) ; 10zzwwww
              (reterr-msg :where (position-to-msg ppstate.position)
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
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a value between 800h and FFFFh ~
                                          UTF-8-encoded in the three bytes ~
                                          (~x0 ~x1 ~x2)"
                                         byte byte2 byte3)
                          :found (msg "the value ~x0" code)))
             ((when (or (and (utf8-<= #x202a code)
                             (utf8-<= code #x202e))
                        (and (utf8-<= #x2066 code)
                             (utf8-<= code #x2069))))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected "a Unicode character with code ~
                                     in the range 9-13 or 32-126 ~
                                     or 128-8233 or 8239-8293 or ~
                                     or 8298-55295 or 57344-1114111"
                          :found (char-to-msg code)))
             (new-position (position-inc-column 1 ppstate.position))
             (ppstate
              (update-ppstate-for-char code bytes new-position 3 ppstate)))
          (retok code ppstate.position ppstate)))
       ;; 4-byte UTF-8:
       ((when (utf8-= (logand #b11111000 byte) #b11110000)) ; 11110xyy
        (b* (((unless (consp bytes))
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 to 247) ~
                                          of a four-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
             ((unless (>= ppstate.size 2))
              (raise "Internal error: ~
                      there are two or more bytes ~
                      but the size of the preprocessing state is ~x0."
                     ppstate.size)
              (reterr t))
             (byte2 (car bytes))
             (bytes (cdr bytes))
             ((unless (utf8-= (logand byte2 #b11000000) #b10000000)) ; 10yyzzzz
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a byte of the form 10... ~
                                          (i.e. between 128 and 191) ~
                                          after the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 and 247) ~
                                          of a four-byte UTF-8 encoding"
                                         byte)
                          :found (msg "the byte ~x0" byte2)))
             ((unless (consp bytes))
              (reterr-msg :where (position-to-msg ppstate.position)
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
             ((unless (>= ppstate.size 3))
              (raise "Internal error: ~
                      there are three or more bytes ~
                      but the size of the preprocessing state is ~x0."
                     ppstate.size)
              (reterr t))
             (byte3 (car bytes))
             (bytes (cdr bytes))
             ((unless (utf8-= (logand byte3 #b11000000) #b10000000)) ; 10wwwwuu
              (reterr-msg :where (position-to-msg ppstate.position)
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
              (reterr-msg :where (position-to-msg ppstate.position)
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
             ((unless (>= ppstate.size 4))
              (raise "Internal error: ~
                      there are four or more bytes ~
                      but the size of the preprocessing state is ~x0."
                     ppstate.size)
              (reterr t))
             (byte4 (car bytes))
             (bytes (cdr bytes))
             ((unless (utf8-= (logand byte4 #b11000000) #b10000000)) ; 10uuvvvv
              (reterr-msg :where (position-to-msg ppstate.position)
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
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "a value between 10000h and 10FFFFh ~
                                          UTF-8-encoded in the four bytes ~
                                          (~x0 ~x1 ~x2 ~x3)"
                                         byte byte2 byte3 byte4)
                          :found (msg "the value ~x0" code)))
             (new-position (position-inc-column 1 ppstate.position))
             (ppstate
              (update-ppstate-for-char code bytes new-position 3 ppstate)))
          (retok code ppstate.position ppstate))))
    (reterr-msg :where (position-to-msg ppstate.position)
                :expected "a byte in the range 9-13 or 32-126 or 192-223"
                :found (msg "the byte ~x0" byte)))
  :measure (ppstate->size ppstate)
  :hints (("Goal" :in-theory (enable nfix)))
  :guard-hints (("Goal" :in-theory (enable len fix natp)))
  :prepwork ((local (in-theory (enable acl2-numberp-when-bytep
                                       rationalp-when-bytep
                                       integerp-when-bytep
                                       car-of-byte-list-geq-0))))

  ///

  (more-returns
   (char? (or (equal char? nil)
              (natp char?))
          :rule-classes :type-prescription
          :name pread-char.char?-type-prescription))

  (defret ppstate->size-of-pread-char-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal"
             :induct t
             :in-theory (enable nfix))))

  (defret ppstate->size-of-pread-char-cond
    (implies (and (not erp)
                  char?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal"
             :induct t
             :in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define punread-char ((ppstate ppstatep))
  :returns (new-ppstate ppstatep :hyp (ppstatep ppstate))
  :short "Unread a character during preprocessing."
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
     logically we return a preprocessing state
     where we still increment @('chars-unread')
     so that the theorem about @(tsee ppstate->size) holds unconditionally."))
  (b* ((ppstate.chars-read (ppstate->chars-read ppstate))
       (ppstate.chars-unread (ppstate->chars-unread ppstate))
       (ppstate.size (ppstate->size ppstate))
       ((unless (> ppstate.chars-read 0))
        (raise "Internal error: no character to unread.")
        (b* ((ppstate (update-ppstate->chars-unread (1+ ppstate.chars-unread)
                                                    ppstate))
             (ppstate (update-ppstate->size (1+ ppstate.size) ppstate)))
          ppstate))
       (ppstate (update-ppstate->chars-read (1- ppstate.chars-read)
                                            ppstate))
       (ppstate (update-ppstate->chars-unread (1+ ppstate.chars-unread)
                                              ppstate))
       (ppstate (update-ppstate->size (1+ ppstate.size) ppstate)))
    ppstate)
  :guard-hints (("Goal" :in-theory (enable natp)))

  ///

  (defret ppstate->size-of-punread-char
    (equal (ppstate->size new-ppstate)
           (1+ (ppstate->size ppstate)))
    :hints (("Goal" :in-theory (enable len nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define punread-chars ((n natp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep :hyp (ppstatep ppstate))
  :short "Unread a specified number of characters during preprocessing."
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
     In this case, after raising the hard error,
     logically we return a preprocessing state
     where we still increment @('chars-unread')
     so that the theorem about @(tsee ppstate->size) holds unconditionally."))
  (b* ((n (nfix n))
       (chars-read (ppstate->chars-read ppstate))
       (chars-unread (ppstate->chars-unread ppstate))
       (size (ppstate->size ppstate))
       ((unless (<= n chars-read))
        (raise "Internal error: ~
                attempting to unread ~x0 characters ~
                from ~x1 read characters."
               n chars-read)
        (b* ((ppstate
              (update-ppstate->chars-unread (+ chars-unread n) ppstate))
             (ppstate
              (update-ppstate->size (+ size n) ppstate)))
          ppstate))
       (new-chars-read (- chars-read n))
       (new-chars-unread (+ chars-unread n))
       (new-size (+ size n))
       (ppstate (update-ppstate->chars-read new-chars-read ppstate))
       (ppstate (update-ppstate->chars-unread new-chars-unread ppstate))
       (ppstate (update-ppstate->size new-size ppstate)))
    ppstate)
  :guard-hints (("Goal" :in-theory (enable natp)))

  ///

  (defret ppstate->size-of-punread-chars
    (equal (ppstate->size new-ppstate)
           (+ (ppstate->size ppstate) (nfix n)))
    :hints (("Goal" :in-theory (enable nfix fix)))))

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
