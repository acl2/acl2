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

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser-messages
  :parents (parser)
  :short "Messages from the parser (including lexer and reader)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide some code for handling error messages."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-msg ((token token-optionp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp character-alistp))))
  :short "Represent a token as a message."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in parser error messages,
     so it does not have to provide a complete description of the token
     for all possible tokens.
     We only give a complete description of keyword and punctuator tokens,
     because those are the kinds that may be a mismatch
     (e.g. expecing a @(':'), found a @(';') instead).
     For the other kinds, we give a more generic description.")
   (xdoc::p
    "It is convenient to treat uniformly tokens and @('nil'),
     which happens when the end of the file is reached.
     This is why this function takes an optional token as input."))
  (if token
      (token-case
       token
       :keyword (msg "the keyword ~x0" token.keyword)
       :ident "an identifier"
       :const "a constant"
       :string "a string literal"
       :punctuator (msg "the punctuator ~x0" token.punctuator)
       :header "a header name")
    "end of file"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-to-msg ((pos positionp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp character-alistp))))
  :short "Represent a position as a message."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in user-oriented error messages."))
  (msg "(line ~x0, column ~x1)" (position->line pos) (position->column pos)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define span-to-msg ((span spanp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp character-alistp))))
  :short "Represent a span as a message."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in user-oriented messages."))
  (msg "[~@0 to ~@1]"
       (position-to-msg (span->start span))
       (position-to-msg (span->end span))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  :hooks nil

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

(defmacro+ reterr-msg (&key where expected found extra)
  :short "Return an error consisting of a message
          with information about what was expected and what was found where."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by our lexing and parsing functions
     to more concisely return more uniform error messages.")
   (xdoc::p
    "This macro assumes that a suitable local macro @('reterr') is in scope
     (see "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuples")
    "), which is the case for our lexing and parsing functions.
     This macro takes as inputs four terms,
     which must evaluate to messages (i.e. values satisfying @(tsee msgp)).
     Those are used to form a larger message,
     in the manner that should be obvious from the body of this macro.
     Note that the fourth term is optional,
     in case we want to provide additional information.")
   (xdoc::p
    "For now we also include, at the end of the message,
     an indication of the ACL2 function that caused the error.
     This is useful as we are debugging the parser,
     but we may remove it once the parser is more tested or even verified."))
  `(reterr (msg "Expected ~@0 at ~@1; found ~@2 instead.~@3~%~
                 [from function ~x4]~%"
                ,expected
                ,where
                ,found
                ,(if extra
                     `(msg " ~@0" ,extra)
                   "")
                __function__)))
