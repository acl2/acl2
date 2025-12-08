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

(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl car-of-byte-list-geq-0
  (implies (byte-listp x)
           (>= (car x) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor-reader
  :parents (preprocessor)
  :short "Reader component of the preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to the parser's @(see reader),
     but for the preprocessor."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  :hooks nil

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
  :no-function nil
  :hooks nil

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
  :no-function nil

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
  :no-function nil

  ///

  (defret ppstate->size-of-punread-chars
    (equal (ppstate->size new-ppstate)
           (+ (ppstate->size ppstate) (nfix n)))
    :hints (("Goal" :in-theory (enable nfix fix)))))
