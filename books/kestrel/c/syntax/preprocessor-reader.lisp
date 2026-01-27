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

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
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

(defruledl integerp-when-natp
  (implies (natp x)
           (integerp x)))

(defruledl rationalp-when-natp
  (implies (natp x)
           (rationalp x)))

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
    "This is analogous to the parser's @(see reader),
     but for the preprocessor.")
   (xdoc::p
    "An additional complication here is that
     @(tsee ppstate), unlike @(tsee parstate),
     has the input bytes organized as an array of lists,
     instead of just a list.
     So it is convenient to wrap the reading of a byte
     into an abstraction, namely @(tsee read-byte);
     its name has no @('p') (unlike @(tsee read-pchar) and others,
     because there is no counterpart in the parser.")
   (xdoc::p
    "Instead of reading characters from bytes on the fly,
     we could consider reading all the characters from each file first,
     and then operating directly on lists of characters.
     Essentially, we would replace bytes with characters in @(tsee ppstate),
     and maybe also revise the array and indices for read and unread characters;
     but this is future work."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-byte ((ppstate ppstatep))
  :returns (mv erp
               (byte? byte-optionp)
               (new-ppstate ppstatep))
  :short "Read the next data byte from the preprocessing state."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an invariant that the current index into the array is in range
     (we should enforce this statically, probably via an abstract stobj),
     which we double-check here, throwing a hard error if the check fails.
     If the current list of bytes has at least one byte,
     we remove it from the list, updating the stobj,
     and we return the byte.
     Otherwise, we move to the previous list of bytes in the array,
     by decrementing the index and recursively calling this function.
     But if the index is 0, we cannot decrement it,
     and so we return @('nil'), signaling the end of input.")
   (xdoc::p
    "If we find a byte to return,
     we also decrement the preprocessing state size by one."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil ppstate)
       (current (ppstate->bytess-current ppstate))
       ((unless (< current (ppstate->bytess-length ppstate)))
        (raise "Internal error: index ~x0 not below length ~x1."
               current (ppstate->bytess-length ppstate))
        (reterr t))
       (bytes (ppstate->bytes current ppstate))
       ((when (consp bytes))
        (b* ((psize (ppstate->size ppstate))
             ((unless (> psize 0))
              (raise "Internal error: ~
                      there is a byte but the preprocessor state size is 0.")
              (reterr t))
             (byte (car bytes))
             (ppstate (update-ppstate->bytes current (cdr bytes) ppstate))
             (ppstate (update-ppstate->size (1- psize) ppstate)))
          (retok byte ppstate)))
       ((when (zp current))
        (retok nil ppstate))
       (ppstate (update-ppstate->bytess-current (1- current) ppstate)))
    (read-byte ppstate))
  :measure (nfix (ppstate->bytess-current ppstate))
  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp
                                           integerp-when-natp)))
  :no-function nil

  ///

  (defret read-byte-geq-0
    (>= byte? 0)
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (byte-optionp)
                             (byte-optionp-of-read-byte.byte?
                              read-byte))
             :use byte-optionp-of-read-byte.byte?)))

  (defret ppstate->chars-length-of-read-byte
    (equal (ppstate->chars-length new-ppstate)
           (ppstate->chars-length ppstate))
    :hints (("Goal" :induct t)))

  (defret ppstate->chars-read-of-read-byte
    (equal (ppstate->chars-read new-ppstate)
           (ppstate->chars-read ppstate))
    :hints (("Goal" :induct t)))

  (defret ppstate->lexmarks-of-read-byte
    (equal (ppstate->lexmarks new-ppstate)
           (ppstate->lexmarks ppstate))
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-read-byte-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret ppstat->size-of-read-byte-cond
    (implies (and (not erp)
                  byte?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peek-byte ((ppstate ppstatep))
  :returns (byte? byte-optionp)
  :short "Peek the next data byte from the preprocessing state,
          without removing it from the state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The code is similar to @(tsee read-byte).
     Although we do not remove the byte,
     we decrement the current index into the array
     if the current byte list is empty,
     until we find a non-empty one,
     or until the list at index 0 is empty."))
  (b* ((current (ppstate->bytess-current ppstate))
       ((unless (< current (ppstate->bytess-length ppstate)))
        (raise "Internal error: index ~x0 not below length ~x1."
               current (ppstate->bytess-length ppstate))))
    (peek-byte-loop current ppstate))
  :no-function nil

  :prepwork
  ((define peek-byte-loop ((current natp) (ppstate ppstatep))
     :guard (< current (ppstate->bytess-length ppstate))
     :returns (byte? byte-optionp)
     :parents nil
     (b* ((bytes (ppstate->bytes current ppstate))
          ((when (consp bytes)) (car bytes))
          ((when (zp current)) nil))
       (peek-byte-loop (1- current) ppstate))))

  ///

  (defret peek-byte-geq-0
    (>= byte? 0)
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (byte-optionp)
                             (byte-optionp-of-peek-byte
                              peek-byte))
             :use byte-optionp-of-peek-byte))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peek2-byte ((ppstate ppstatep))
  :returns (byte? byte-optionp)
  :short "Peek the second next data byte from the preprocessing state,
          without removing any byte from the state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee peek-byte),
     but with the additional complications to skip the next byte
     in order to get to the one just after it:
     the recursive companion function takes a boolean flag
     saying whether we should skip the next byte found,
     or not (i.e. if we have already skipped it)."))
  (b* ((current (ppstate->bytess-current ppstate))
       ((unless (< current (ppstate->bytess-length ppstate)))
        (raise "Internal error: index ~x0 not below length ~x1."
               current (ppstate->bytess-length ppstate))))
    (peek2-byte-loop current t ppstate))
  :no-function nil
  :prepwork
  ((define peek2-byte-loop ((current natp) (skip booleanp) (ppstate ppstatep))
     :guard (< current (ppstate->bytess-length ppstate))
     :returns (byte? byte-optionp)
     :parents nil
     (b* ((bytes (ppstate->bytes current ppstate)))
       (if (consp bytes)
           (if skip
               (b* ((bytes (cdr bytes))
                    ((when (consp bytes)) (car bytes))
                    ((when (zp current)) nil))
                 (peek2-byte-loop (1- current) nil ppstate))
             (car bytes))
         (b* (((when (zp current)) nil))
           (peek2-byte-loop (1- current) skip ppstate))))))

  ///

  (defret peek2-byte-geq-0
    (>= byte? 0)
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (byte-optionp)
                             (byte-optionp-of-peek2-byte
                              peek2-byte))
             :use byte-optionp-of-peek2-byte))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-ppstate-for-char ((char natp)
                                 (new-position positionp)
                                 (ppstate ppstatep))
  :guard (< (ppstate->chars-read ppstate)
            (ppstate->chars-length ppstate))
  :returns (new-ppstate ppstatep)
  :short "Update the preprocessor state for a character."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when @(tsee read-pchar)
     reads a character from the data bytes (not from the unread characters).
     The @('new-position') input consists of the next position,
     which is normally one column more than the current one,
     except when dealing with new-line characters."))
  (b* ((position (ppstate->position ppstate))
       (chars-read (ppstate->chars-read ppstate))
       (char+pos (make-char+position :char char :position position))
       (ppstate (update-ppstate->char chars-read char+pos ppstate))
       (ppstate (update-ppstate->chars-read (1+ chars-read) ppstate))
       (ppstate (update-ppstate->position new-position ppstate)))
    ppstate)

  ///

  (defret ppstate->lexmarks-of-update-ppstate-for-char
    (equal (ppstate->lexmarks new-ppstate)
           (ppstate->lexmarks ppstate)))

  (defret ppstate->size-of-update-ppstate-for-char
    (equal (ppstate->size new-ppstate)
           (ppstate->size ppstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-pchar ((ppstate ppstatep))
  :returns (mv erp
               (char? nat-optionp
                      :hints (("Goal" :induct t :in-theory (enable natp))))
               (pos positionp)
               (new-ppstate ppstatep))
  :short "Read a character during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is almost identical to @(tsee read-char)
     (see its documentation first),
     but with some differences.")
   (xdoc::p
    "One difference is that we use @(tsee read-byte) and @(tsee peek-byte)
     instead of directly operating on
     the single list of bytes in the parser state,
     since the preprocessor state has an array of lists.")
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
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) nil (irr-position) ppstate)
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
       ((erp byte ppstate) (read-byte ppstate))
       ((unless byte) (retok nil ppstate.position ppstate))
       ((unless (< ppstate.chars-read (ppstate->chars-length ppstate)))
        (raise "Internal error: index ~x0 out of bound ~x1."
               ppstate.chars-read
               (ppstate->chars-length ppstate))
        (reterr t))
       ;; new lines:
       ((when (utf8-= byte 13)) ; CR
        (b* ((byte2 (peek-byte ppstate))
             (lf-follows-cr-p (and byte2 (utf8-= byte2 10)))
             (new-position (if lf-follows-cr-p
                               ppstate.position
                             (position-inc-line 1 ppstate.position)))
             (ppstate (update-ppstate-for-char 13 new-position ppstate)))
          (retok 13 ppstate.position ppstate)))
       ((when (utf8-= byte 10)) ; LF
        (b* ((new-position (position-inc-line 1 ppstate.position))
             (ppstate (update-ppstate-for-char 10 new-position ppstate)))
          (retok 10 ppstate.position ppstate)))
       ;; trigraph sequences (or just '?'):
       ((when (utf8-= byte (char-code #\?))) ; ?
        (b* (((mv char trigraphp)
              (b* ((byte2 (peek-byte ppstate)))
                (if (and byte2
                         (utf8-= byte2 (char-code #\?))) ; ? ?
                    (b* ((byte3 (peek2-byte ppstate)))
                      (cond ((not byte3) (mv byte nil)) ; ? ? EOF
                            ((utf8-= byte3 (char-code #\=)) ; ? ? =
                             (mv (char-code #\#) t))
                            ((utf8-= byte3 (char-code #\()) ; ? ? (
                             (mv (char-code #\[) t))
                            ((utf8-= byte3 (char-code #\/)) ; ? ? /
                             (mv (char-code #\\) t))
                            ((utf8-= byte3 (char-code #\))) ; ? ? )
                             (mv (char-code #\]) t))
                            ((utf8-= byte3 (char-code #\')) ; ? ? '
                             (mv (char-code #\^) t))
                            ((utf8-= byte3 (char-code #\<)) ; ? ? <
                             (mv (char-code #\{) t))
                            ((utf8-= byte3 (char-code #\!)) ; ? ? !
                             (mv (char-code #\|) t))
                            ((utf8-= byte3 (char-code #\>)) ; ? ? >
                             (mv (char-code #\}) t))
                            ((utf8-= byte3 (char-code #\-)) ; ? ? -
                             (mv (char-code #\~) t))
                            (t (mv byte nil)))) ; ? ? other, not a trigraph
                  (mv byte nil)))) ; ? other, not a tripgraph
             ((erp ppstate) (b* (((reterr) ppstate))
                              (if trigraphp ; consume BYTE2 and BYTE3
                                  (b* (((erp & ppstate) (read-byte ppstate))
                                       ((erp & ppstate) (read-byte ppstate)))
                                    (retok ppstate))
                                (retok ppstate))))
             (num-columns (if trigraphp 3 1))
             (new-position (position-inc-column num-columns ppstate.position))
             (ppstate (update-ppstate-for-char char new-position ppstate)))
          (retok char ppstate.position ppstate)))
       ;; line splicing (or just '\'):
       ((when (utf8-= byte (char-code #\\))) ; \
        (b* ((byte2 (peek-byte ppstate))
             ((unless byte2) ; \ EOF
              (reterr (msg "File ends with backslash.")))
             ((when (utf8-= byte2 10)) ; \ LF
              (b* (((erp & ppstate) (read-byte ppstate)) ; consume LF
                   ((unless (> (ppstate->size ppstate) 0)) ; \ LF EOF
                    (reterr (msg "File ends with backslash and new line.")))
                   ;; \ LF other
                   (new-position (position-inc-line 1 ppstate.position))
                   (ppstate (update-ppstate->position new-position ppstate)))
                (read-pchar ppstate)))
             ((when (utf8-= byte2 13)) ; \ CR
              (b* (((erp & ppstate) (read-byte ppstate)) ; consume CR
                   (byte3 (peek-byte ppstate))
                   ((unless byte3) ; \ CR EOF
                    (reterr (msg "File ends with backslash and new line.")))
                   ((when (utf8-= byte3 10)) ; \ CR LF
                    (b* (((erp & ppstate) (read-byte ppstate)) ; consume LF
                         ((unless (> (ppstate->size ppstate) 0)) ; \ CR LF EOF
                          (reterr
                           (msg "File ends with backslash and new line.")))
                         ;; \ CR LF other
                         (new-position (position-inc-line 1 ppstate.position))
                         (ppstate
                          (update-ppstate->position new-position ppstate)))
                      (read-pchar ppstate)))
                   ;; \ CR other
                   (new-position (position-inc-line 1 ppstate.position))
                   (ppstate (update-ppstate->position new-position ppstate)))
                (read-pchar ppstate)))
             ;; \ other
             (new-position (position-inc-column 1 ppstate.position))
             (ppstate (update-ppstate-for-char byte new-position ppstate)))
          (retok byte ppstate.position ppstate)))
       ;; other ASCII:
       ((when (or (utf8-= byte 9) ; HT
                  (utf8-= byte 11) ; VT
                  (utf8-= byte 12) ; FF
                  (and (utf8-<= 32 byte) (utf8-<= byte 126))))
        (b* ((new-position (position-inc-column 1 ppstate.position))
             (ppstate (update-ppstate-for-char byte new-position ppstate)))
          (retok byte ppstate.position ppstate)))
       ;; 2-byte UTF-8:
       ((when (utf8-= (logand byte #b11100000) #b11000000)) ; 110xxxyy
        (b* (((erp byte2 ppstate) (read-byte ppstate))
             ((unless byte2)
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 110... ~
                                          (i.e. between 192 and 223) ~
                                          of a two-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
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
             (ppstate (update-ppstate-for-char code new-position ppstate)))
          (retok code ppstate.position ppstate)))
       ;; 3-byte UTF-8:
       ((when (utf8-= (logand byte #b11110000) #b11100000)) ; 1110xxxx
        (b* (((erp byte2 ppstate) (read-byte ppstate))
             ((unless byte2)
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 1110... ~
                                          (i.e. between 224 to 239) ~
                                          of a three-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
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
             ((erp byte3 ppstate) (read-byte ppstate))
             ((unless byte3)
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
             (ppstate (update-ppstate-for-char code new-position ppstate)))
          (retok code ppstate.position ppstate)))
       ;; 4-byte UTF-8:
       ((when (utf8-= (logand #b11111000 byte) #b11110000)) ; 11110xyy
        (b* (((erp byte2 ppstate) (read-byte ppstate))
             ((unless byte2)
              (reterr-msg :where (position-to-msg ppstate.position)
                          :expected (msg "another byte after ~
                                          the first byte ~x0 ~
                                          of the form 11110... ~
                                          (i.e. between 240 to 247) ~
                                          of a four-byte UTF-8 encoding"
                                         byte)
                          :found "end of file"))
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
             ((erp byte3 ppstate) (read-byte ppstate))
             ((unless byte3)
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
             ((erp byte4 ppstate) (read-byte ppstate))
             ((unless byte4)
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
             (ppstate (update-ppstate-for-char code new-position ppstate)))
          (retok code ppstate.position ppstate))))
    (reterr-msg :where (position-to-msg ppstate.position)
                :expected "a byte in the range 9-13 or 32-126 or 192-223"
                :found (msg "the byte ~x0" byte)))
  :measure (ppstate->size ppstate)
  :prepwork ((local (in-theory (enable acl2-numberp-when-bytep
                                       rationalp-when-bytep
                                       integerp-when-bytep))))
  :no-function nil

  ///

  (more-returns
   (char? (or (equal char? nil)
              (natp char?))
          :rule-classes :type-prescription
          :name read-pchar.char?-type-prescription))

  (defret ppstate->lexmarks-of-read-pchar
    (equal (ppstate->lexmarks new-ppstate)
           (ppstate->lexmarks ppstate))
    :hints (("Goal" :induct t)))

  (defret ppstate->size-of-read-pchar-uncond
    (<= (ppstate->size new-ppstate)
        (ppstate->size ppstate))
    :rule-classes :linear
    :hints (("Goal"
             :induct t
             :in-theory (enable nfix))))

  (defret ppstate->size-of-read-pchar-cond
    (implies (and (not erp)
                  char?)
             (<= (ppstate->size new-ppstate)
                 (1- (ppstate->size ppstate))))
    :rule-classes :linear
    :hints (("Goal"
             :induct t
             :in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-pchar ((ppstate ppstatep))
  :returns (new-ppstate ppstatep)
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

  (defret ppstate->lexmarks-of-unread-pchar
    (equal (ppstate->lexmarks new-ppstate)
           (ppstate->lexmarks ppstate)))

  (defret ppstate->size-of-unread-pchar
    (equal (ppstate->size new-ppstate)
           (1+ (ppstate->size ppstate)))
    :hints (("Goal" :in-theory (enable len nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-pchars ((n natp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
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

  (defret ppstate->size-of-unread-pchars
    (equal (ppstate->size new-ppstate)
           (+ (ppstate->size ppstate) (nfix n)))
    :hints (("Goal" :in-theory (enable nfix fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unread-pchar-to-bytes ((ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Put the unread character, if any,
          back into the current list of bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called just before @(tsee ppstate-add-bytes),
     when a file included via @('#include') is expanded in place.
     This is called after consuming the @('#include') directive,
     but possibly after having unread a character,
     if the new line is a carriage return not followed by a line feed:
     see @(tsee plex-lexeme).
     That unread character would be read by the next call of @(tsee read-char),
     which is incorrect because that character must come
     after all the characters produced from the bytes of the included file.
     So here we put the unread character, if any,
     back into the current list of input bytes,
     performing UTF-8 encoding of them.
     We also change the current position back to the one of the character."))
  (b* ((ppstate (ppstate-fix ppstate))
       (chars-unread (ppstate->chars-unread ppstate))
       ((when (= chars-unread 0)) ppstate)
       ((unless (= chars-unread 1))
        (raise "Internal error: ~x0 unread characters." chars-unread)
        ppstate)
       (chars-length (ppstate->chars-length ppstate))
       (chars-read (ppstate->chars-read ppstate))
       (char-index (+ chars-read (1- chars-unread)))
       ((unless (< char-index chars-length))
        (raise "Internal error: ~
                index of next unread character ~x0 is not below ~x1."
               char-index chars-length)
        ppstate)
       (char+pos (ppstate->char char-index ppstate))
       (char (char+position->char char+pos))
       (pos (char+position->position char+pos))
       (char-bytes
        (cond ((< char #x80) (list char))
              ((< char #x800) (list (logior (ash char -6)
                                            #b11000000)
                                    (logior (logand char
                                                    #b00111111)
                                            #b10000000)))
              ((< char #x10000) (list (logior (ash char -12)
                                              #b11100000)
                                      (logior (logand (ash char -6)
                                                      #b00111111)
                                              #b10000000)
                                      (logior (logand char
                                                      #b00111111)
                                              #b10000000)))
              ((< char #x10ffff) (list (logior (ash char -18)
                                               #b11110000)
                                       (logior (logand (ash char -12)
                                                       #b00111111)
                                               #b10000000)
                                       (logior (logand (ash char -6)
                                                       #b00111111)
                                               #b10000000)
                                       (logior (logand char
                                                       #b00111111)
                                               #b10000000)))
              (t (raise "Internal error: character code ~x0." char))))
       (bytess-length (ppstate->bytess-length ppstate))
       (bytess-current (ppstate->bytess-current ppstate))
       ((unless (< bytess-current bytess-length))
        (raise "Internal error: ~
                index of current input bytes ~x0 is not below ~x1."
               bytess-current bytess-length)
        ppstate)
       (bytes (ppstate->bytes bytess-current ppstate))
       (new-bytes (append char-bytes bytes))
       (ppstate (update-ppstate->bytes bytess-current new-bytes ppstate))
       (ppstate (update-ppstate->position pos ppstate))
       (ppstate (update-ppstate->chars-unread 0 ppstate)))
    ppstate)
  :guard-hints (("Goal" :in-theory (enable fix
                                           bytep
                                           unsigned-byte-p
                                           integer-range-p)))
  :no-function nil)
