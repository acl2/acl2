; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../preprocessor")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/testing/assert-bang-stobj" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro init (input)
  `(init-ppstate ,input (c::version-c23) ppstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-lex (fn input &key pos more-inputs std gcc cond)
  ;; INPUT is an ACL2 term with the text to lex,
  ;; where the term evaluates to a string or a list of bytes.
  ;; Optional POS is the initial position for the preprocessing state.
  ;; Optional MORE-INPUTS go just before preprocessing state input.
  ;; STD indicates the C standard version (17 or 23; default 17).
  ;; GCC flag says whether GCC extensions are enabled (default NIL).
  ;; Optional COND may be over variables AST, POS/SPAN, PPSTATE.
  `(assert!-stobj
    (b* ((version (if (eql ,std 23)
                      (if ,gcc (c::version-c23+gcc) (c::version-c23))
                    (if ,gcc (c::version-c17+gcc) (c::version-c17))))
         (ppstate (init-ppstate (if (stringp ,input)
                                    (acl2::string=>nats ,input)
                                  ,input)
                                version
                                ppstate))
         ,@(and pos
                `((ppstate (update-ppstate->position ,pos ppstate))))
         ((mv erp ?ast ?pos/span ppstate)
          (,fn ,@more-inputs ppstate)))
      (mv
       (if erp
           (cw "~@0" erp) ; CW returns NIL, so ASSERT!-STOBJ fails
         ,(or cond t)) ; assertion passes if COND is absent or else holds
       ppstate))
    ppstate))

(defmacro test-lex-fail (fn input &key pos more-inputs std gcc)
  ;; INPUT is an ACL2 term with the text to lex,
  ;; where the term evaluates to a string or a list of bytes.
  ;; Optional POS is the initial position for the preprocessing state.
  ;; Optional MORE-INPUTS go just before preproceessing state input.
  ;; STD indicates the C standard version (17 or 23; default 17).
  ;; GCC flag says whether GCC extensions are enabled (default NIL).
  `(assert!-stobj
    (b* ((version (if (eql ,std 23)
                      (if ,gcc (c::version-c23+gcc) (c::version-c23))
                    (if ,gcc (c::version-c17+gcc) (c::version-c17))))
         (ppstate (init-ppstate (if (stringp ,input)
                                    (acl2::string=>nats ,input)
                                  ,input)
                                version
                                ppstate))
         ,@(and pos
                `((ppstate (update-ppstate->position ,pos ppstate))))
         ((mv erp & & ppstate)
          (,fn ,@more-inputs ppstate)))
      (mv erp ppstate))
    ppstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; pread-char

(assert!-stobj ; empty file
 (b* ((ppstate (init nil))
      ((mv erp char? pos ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (not char?)
            (equal pos (position 1 0))) ; just past end of (empty) file
       ppstate))
 ppstate)

(assert!-stobj ; disallowed character 0
 (b* ((ppstate (init '(0)))
      ((mv erp & & ppstate) (pread-char ppstate))
      (- (cw "~@0" erp)))
   (mv erp ppstate))
 ppstate)

(assert!-stobj ; character 32
 (b* ((ppstate (init '(32 65)))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char 32)
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 65)
            (equal pos2 (position 1 1)))
       ppstate))
 ppstate)

(assert!-stobj ; line feed
 (b* ((ppstate (init '(10 65)))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char 10)
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 65)
            (equal pos2 (position 2 0)))
       ppstate))
 ppstate)

(assert!-stobj ; carriage return
 (b* ((ppstate (init '(13 65)))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char 13)
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 65)
            (equal pos2 (position 2 0)))
       ppstate))
 ppstate)

(assert!-stobj ; carriage return + line feed
 (b* ((ppstate (init '(13 10 65)))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate))
      ((mv erp3 char3 pos3 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char 13)
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 10)
            (equal pos2 (position 1 0))
            (not erp3)
            (equal char3 65)
            (equal pos3 (position 2 0)))
       ppstate))
 ppstate)

(assert!-stobj ; disallowed byte 255
 (b* ((ppstate (init '(255)))
      ((mv erp & & ppstate) (pread-char ppstate))
      (- (cw "~@0" erp)))
   (mv erp ppstate))
 ppstate)

(assert!-stobj ; ??=
 (b* ((ppstate (init (acl2::string=>nats "??=A")))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\#))
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 65)
            (equal pos2 (position 1 3)))
       ppstate))
 ppstate)

(assert!-stobj ; ??(
 (b* ((ppstate (init (acl2::string=>nats "??(A")))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\[))
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 65)
            (equal pos2 (position 1 3)))
       ppstate))
 ppstate)

(assert!-stobj ; ??/
 (b* ((ppstate (init (acl2::string=>nats "??/A")))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\\))
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 65)
            (equal pos2 (position 1 3)))
       ppstate))
 ppstate)

(assert!-stobj ; ??)
 (b* ((ppstate (init (acl2::string=>nats "??)A")))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\]))
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 65)
            (equal pos2 (position 1 3)))
       ppstate))
 ppstate)

(assert!-stobj ; ??'
 (b* ((ppstate (init (acl2::string=>nats "??'A")))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\^))
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 65)
            (equal pos2 (position 1 3)))
       ppstate))
 ppstate)

(assert!-stobj ; ??<
 (b* ((ppstate (init (acl2::string=>nats "??<A")))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\{))
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 65)
            (equal pos2 (position 1 3)))
       ppstate))
 ppstate)

(assert!-stobj ; ??!
 (b* ((ppstate (init (acl2::string=>nats "??!A")))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\|))
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 65)
            (equal pos2 (position 1 3)))
       ppstate))
 ppstate)

(assert!-stobj ; ??>
 (b* ((ppstate (init (acl2::string=>nats "??>A")))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\}))
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 65)
            (equal pos2 (position 1 3)))
       ppstate))
 ppstate)

(assert!-stobj ; ??-
 (b* ((ppstate (init (acl2::string=>nats "??-A")))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\~))
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 65)
            (equal pos2 (position 1 3)))
       ppstate))
 ppstate)

(assert!-stobj ; ??a
 (b* ((ppstate (init (acl2::string=>nats "??a")))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate))
      ((mv erp3 char3 pos3 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\?))
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 (char-code #\?))
            (equal pos2 (position 1 1))
            (not erp3)
            (equal char3 (char-code #\a))
            (equal pos3 (position 1 2)))
       ppstate))
 ppstate)

(assert!-stobj ; ?a
 (b* ((ppstate (init (acl2::string=>nats "?a")))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\?))
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 (char-code #\a))
            (equal pos2 (position 1 1)))
       ppstate))
 ppstate)

(assert!-stobj ; ??
 (b* ((ppstate (init (acl2::string=>nats "??")))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\?))
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 (char-code #\?))
            (equal pos2 (position 1 1)))
       ppstate))
 ppstate)

(assert!-stobj ; ?
 (b* ((ppstate (init (acl2::string=>nats "?")))
      ((mv erp char pos ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\?))
            (equal pos (position 1 0)))
       ppstate))
 ppstate)

(assert!-stobj ; \ at end of file
 (b* ((ppstate (init (list (char-code #\\))))
      ((mv erp & & ppstate) (pread-char ppstate))
      (- (cw "~@0" erp)))
   (mv erp ppstate))
 ppstate)

(assert!-stobj ; \ LF at end of file
 (b* ((ppstate (init (list (char-code #\\) 10)))
      ((mv erp & & ppstate) (pread-char ppstate))
      (- (cw "~@0" erp)))
   (mv erp ppstate))
 ppstate)

(assert!-stobj ; \ LF a
 (b* ((ppstate (init (list (char-code #\\) 10 (char-code #\a))))
      ((mv erp char pos ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\a))
            (equal pos (position 2 0)))
       ppstate))
 ppstate)

(assert!-stobj ; \ CR a
 (b* ((ppstate (init (list (char-code #\\) 13 (char-code #\a))))
      ((mv erp char pos ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\a))
            (equal pos (position 2 0)))
       ppstate))
 ppstate)

(assert!-stobj ; \ CR LF a
 (b* ((ppstate (init (list (char-code #\\) 13 10 (char-code #\a))))
      ((mv erp char pos ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\a))
            (equal pos (position 2 0)))
       ppstate))
 ppstate)

(assert!-stobj ; \ n
 (b* ((ppstate (init (list (char-code #\\) (char-code #\n))))
      ((mv erp char pos ppstate) (pread-char ppstate))
      ((mv erp2 char2 pos2 ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char (char-code #\\))
            (equal pos (position 1 0))
            (not erp2)
            (equal char2 (char-code #\n))
            (equal pos2 (position 1 1)))
       ppstate))
 ppstate)

(assert!-stobj ; 2-byte UTF-8 encoding of Greek capital letter sigma
 (b* ((ppstate (init (acl2::string=>nats "Σ")))
      ((mv erp char? pos ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char? #x03a3)
            (equal pos (position 1 0)))
       ppstate))
 ppstate)

(assert!-stobj ; invalid 2-byte UTF-8 encoding of 0
 (b* ((ppstate (init (list #b11000000 #b10000000)))
      ((mv erp & & ppstate) (pread-char ppstate))
      (- (cw "~@0" erp)))
   (mv erp ppstate))
 ppstate)

(assert!-stobj ; 3-byte UTF-8 encoding of anticlockwise top semicircle arrow
 (b* ((ppstate (init (acl2::string=>nats "↺")))
      ((mv erp char? pos ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char? #x21ba)
            (equal pos (position 1 0)))
       ppstate))
 ppstate)

(assert!-stobj ; disallowed 3-byte UTF-8 encoding
 (b* ((ppstate (init (list #b11100010 #b10000000 #b10101010))) ; 202Ah
      ((mv erp & & ppstate) (pread-char ppstate))
      (- (cw "~@0" erp)))
   (mv erp ppstate))
 ppstate)

(assert!-stobj ; invalid 3-byte UTF-8 encoding of 0
 (b* ((ppstate (init (list #b11100000 #b10000000 #b10000000)))
      ((mv erp & & ppstate) (pread-char ppstate))
      (- (cw "~@0" erp)))
   (mv erp ppstate))
 ppstate)

(assert!-stobj ; 4-byte UTF-8 encoding of musical symbol eighth note
 (b* ((ppstate (init (acl2::string=>nats "𝅘𝅥𝅮")))
      ((mv erp char? pos ppstate) (pread-char ppstate)))
   (mv (and (not erp)
            (equal char? #x1d160)
            (equal pos (position 1 0)))
       ppstate))
 ppstate)

(assert!-stobj ; invalid 4-byte UTF-8 encoding of 0
 (b* ((ppstate (init (list #b11110000 #b10000000 #b10000000 #b10000000)))
      ((mv erp & & ppstate) (pread-char ppstate))
      (- (cw "~@0" erp)))
   (mv erp ppstate))
 ppstate)

(assert!-stobj ; invalid 4-byte UTF-8 encoding of 1FFFFFh
 (b* ((ppstate (init (list #b11110111 #b10111111 #b10111111 #b10111111)))
      ((mv erp & & ppstate) (pread-char ppstate))
      (- (cw "~@0" erp)))
   (mv erp ppstate))
 ppstate)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-identifier

(test-lex
 plex-identifier
 " abc"
 :pos (position 8 4)
 :more-inputs ((char-code #\w) (position 8 3))
 :cond (and (equal ast (plexeme-ident (ident "w")))
            (equal pos/span (span (position 8 3) (position 8 3)))))

(test-lex
 plex-identifier
 "abc456"
 :pos (position 8 4)
 :more-inputs ((char-code #\u) (position 8 3))
 :cond (and (equal ast (plexeme-ident (ident "uabc456")))
            (equal pos/span (span (position 8 3) (position 8 9)))))

(test-lex
 plex-identifier
 "tatic"
 :pos (position 8 4)
 :more-inputs ((char-code #\s) (position 8 3))
 :cond (and (equal ast (plexeme-ident (ident "static")))
            (equal pos/span (span (position 8 3) (position 8 8)))))

(test-lex
 plex-identifier
 "nclude"
 :pos (position 8 4)
 :more-inputs ((char-code #\i) (position 8 3))
 :cond (and (equal ast (plexeme-ident (ident "include")))
            (equal pos/span (span (position 8 3) (position 8 9)))))

(test-lex
 plex-identifier
 "nclud_"
 :pos (position 8 4)
 :more-inputs ((char-code #\i) (position 8 3))
 :cond (and (equal ast (plexeme-ident (ident "includ_")))
            (equal pos/span (span (position 8 3) (position 8 9)))))

(test-lex
 plex-identifier
 "nclud+"
 :pos (position 8 4)
 :more-inputs ((char-code #\i) (position 8 3))
 :cond (and (equal ast (plexeme-ident (ident "includ")))
            (equal pos/span (span (position 8 3) (position 8 8)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-pp-number

(test-lex
 plex-pp-number
 ""
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number (pnumber-digit #\3))))

(test-lex
 plex-pp-number
 "+"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number (pnumber-digit #\3))))

(test-lex
 plex-pp-number
 ""
 :more-inputs (t #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number (pnumber-dot-digit #\3))))

(test-lex
 plex-pp-number
 "+"
 :more-inputs (t #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number (pnumber-dot-digit #\3))))

(test-lex
 plex-pp-number
 "4"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-digit (pnumber-digit #\3) #\4))))

(test-lex
 plex-pp-number
 "4"
 :more-inputs (t #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-digit (pnumber-dot-digit #\3) #\4))))

(test-lex
 plex-pp-number
 "e+"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-locase-e-sign (pnumber-digit #\3)
                                             (sign-plus)))))

(test-lex
 plex-pp-number
 "e-"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-locase-e-sign (pnumber-digit #\3)
                                             (sign-minus)))))

(test-lex
 plex-pp-number
 "e*"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-nondigit (pnumber-digit #\3) #\e))))

(test-lex
 plex-pp-number
 "E+"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-upcase-e-sign (pnumber-digit #\3)
                                             (sign-plus)))))

(test-lex
 plex-pp-number
 "E-"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-upcase-e-sign (pnumber-digit #\3)
                                             (sign-minus)))))

(test-lex
 plex-pp-number
 "E/"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-nondigit (pnumber-digit #\3) #\E))))

(test-lex
 plex-pp-number
 "p+"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-locase-p-sign (pnumber-digit #\3)
                                             (sign-plus)))))

(test-lex
 plex-pp-number
 "p-"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-locase-p-sign (pnumber-digit #\3)
                                             (sign-minus)))))

(test-lex
 plex-pp-number
 "p*"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-nondigit (pnumber-digit #\3) #\p))))

(test-lex
 plex-pp-number
 "P+"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-upcase-p-sign (pnumber-digit #\3)
                                             (sign-plus)))))

(test-lex
 plex-pp-number
 "P-"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-upcase-p-sign (pnumber-digit #\3)
                                             (sign-minus)))))

(test-lex
 plex-pp-number
 "P/"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-nondigit (pnumber-digit #\3) #\P))))

(test-lex
 plex-pp-number
 "a"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-nondigit (pnumber-digit #\3) #\a))))

(test-lex
 plex-pp-number
 "a+"
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-nondigit (pnumber-digit #\3) #\a))))

(test-lex
 plex-pp-number
 "."
 :more-inputs (nil #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-dot (pnumber-digit #\3)))))

(test-lex
 plex-pp-number
 "7abP-.x"
 :more-inputs (t #\3 (position 3 7))
 :cond (equal ast
              (plexeme-number
               (pnumber-number-nondigit
                (pnumber-number-dot
                 (pnumber-number-upcase-p-sign
                  (pnumber-number-nondigit
                   (pnumber-number-nondigit
                    (pnumber-number-digit
                     (pnumber-dot-digit #\3)
                     #\7)
                    #\a)
                   #\b)
                  (sign-minus)))
                #\x))))
