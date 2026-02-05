; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "parser-messages")
(include-book "preprocessor-states")

(include-book "kestrel/fty/nat-option" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Library extensions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro utf8-= (x y)
  `(= (the unsigned-byte ,x)
      (the unsigned-byte ,y)))

(defmacro utf8-<= (x y)
  `(<= (the unsigned-byte ,x)
       (the unsigned-byte ,y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor-messages
  :parents (preprocessor)
  :short "Messages from he preprocessor (including lexer and reader)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are similar to the "
    (xdoc::seetopic "parser-messages" "parser messages")
    ", but for the preprocessor.")
   (xdoc::p
    "The preprocessor also uses some code from the file of parser messages,
     and so the file is included here for convenience."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pchar-to-msg ((char nat-optionp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp character-alistp))))
  :short "Represent an optional character as a message,
          in the preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is almost identical to @(tsee char-to-msg)
     (see its documentation first)
     with the difference that we consider LF and CR separately.
     This matches the fact that @(tsee read-pchar), unlike @(tsee read-char),
     does not normalize the three possible kinds of new lines to LF."))
  (b* ((char (nat-option-fix char)))
    (cond ((not char) "end of file")
          ((< char 32) (msg "the ~s0 character (ASCII code ~x1)"
                            (nth char *pchar-to-msg-ascii-control-char-names*)
                            char))
          ((utf8-= char 32) "the SP (space) character (ASCII code 32)")
          ((and (utf8-<= 33 char) (utf8-<= char 126))
           (msg "the ~s0 character (ASCII code ~x1)"
                (str::implode (list (code-char char))) char))
          ((utf8-= char 127) "the DEL (delete) character (ASCII code 127)")
          (t (msg "the non-ASCII Unicode character with code ~x0" char))))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexeme-to-msg ((lexeme plexeme-optionp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp character-alistp))))
  :short "Represent a preprocessing lexeme as a message."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in preprocessor error messages.
     It is similar to @(tsee token-to-msg) for the parser."))
  (if lexeme
      (plexeme-case
       lexeme
       :header "a header name"
       :ident (msg "the identifier ~x0" (ident->unwrap lexeme.ident))
       :number "a preprocessing number"
       :char "a character constant"
       :string "a string literal"
       :punctuator "a punctuator"
       :other "some other character"
       :block-comment "a block comment"
       :line-comment "a line comment"
       :newline "a new line"
       :spaces "one ore more spaces"
       :horizontal-tab "a horizontal tab"
       :vertical-tab "a vertical tab"
       :form-feed "a form feed")
    "end of file"))
