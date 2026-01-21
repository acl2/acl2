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
(include-book "grammar-characters")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/typed-lists/nat-listp" :dir :system))

(acl2::controlled-configuration :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled grammar-character-p-when-letter/uscore-char-p
  (implies (str::letter/uscore-char-p char)
           (grammar-character-p (char-code char)))
  :enable (str::letter/uscore-char-p
           grammar-character-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor-printer
  :parents (preprocessor)
  :short "Printer component of the preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our preprocessor
     reads files from specified paths,
     preprocessed them,
     and generates a file set with the files after preprocessing;
     see @(see preprocessor).
     The preprocessing of the files results in a list of lexemes,
     which we turn into bytes via this printer.")
   (xdoc::p
    "Since our preprocessing lexemes include white space,
     the printing is relatively easy.
     We do not need to add white space, keep track of indentation, etc.
     Compare this with the @(see printer).")
   (xdoc::p
    "Our printing functions take as input and return as output a list of bytes,
     which form the growing result in reverse.
     The list of bytes is extended by the printing functions
     via @(tsee cons) (which motivates the reversal of the list).
     The list of bytes is reversed after it is complete."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-char ((char natp) (bytes byte-listp))
  :guard (grammar-character-p char)
  :returns (new-bytes byte-listp
                      :hints (("Goal" :in-theory (enable grammar-character-p
                                                         nfix
                                                         bytep
                                                         unsigned-byte-p
                                                         integer-range-p))))
  :short "Print a character after preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "The character is supplied as its code.")
   (xdoc::p
    "We UTF-8-encode the character code into one, two, three, or four bytes.")
   (xdoc::p
    "This is the most basic printing function in our preprocessor printer.
     All other printing functions call this one, directly or indirectly."))
  (b* (((when (not (mbt (grammar-character-p char)))) (byte-list-fix bytes))
       (char (lnfix char))
       (encoding (cond
                  ((< char #x80) (list char))
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
                  (t (list (logior (ash char -18)
                                   #b11110000)
                           (logior (logand (ash char -12)
                                           #b00111111)
                                   #b10000000)
                           (logior (logand (ash char -6)
                                           #b00111111)
                                   #b10000000)
                           (logior (logand char
                                           #b00111111)
                                   #b10000000)))))
       (new-bytes (append (rev encoding) (byte-list-fix bytes))))
    new-bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-chars ((chars nat-listp) (bytes byte-listp))
  :guard (grammar-character-listp chars)
  :returns (new-bytes byte-listp)
  :short "Print zero or more characters after preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "The characters are supplied in a list (of their codes).
     They are printed from left to right."))
  (b* (((when (endp chars)) (byte-list-fix bytes))
       (bytes (pprint-char (car chars) bytes)))
    (pprint-chars (cdr chars) bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-astring ((string stringp) (bytes byte-listp))
  :guard (grammar-character-listp (acl2::string=>nats string))
  :returns (new-bytes byte-listp)
  :short "Print the characters from an ACL2 string after preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This provides the convenience to use ACL2 strings,
     instead of using character codes.")
   (xdoc::p
    "Since most of the C syntax is ASCII,
     this printing function is used to print most of the code.")
   (xdoc::p
    "Note that an ACL2 string can contain characters that,
     when converted to natural numbers, are larger than 127,
     and therefore are not ASCII.
     But we always call this printing function with ASCII strings."))
  (pprint-chars (acl2::string=>nats string) bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-form-feed ((bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a form feed after preprocessing."
  (pprint-char 12 bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-horizontal-tab ((bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a horizontal tab after preprocessing."
  (pprint-char 9 bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-vertical-tab ((bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a vertical tab after preprocessing."
  (pprint-char 11 bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-spaces ((count posp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print one or more spaces after preprocessing."
  (pprint-chars (repeat count 32) bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-newline ((newline newlinep) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a new line after preprocessing."
  (newline-case newline
                :lf (pprint-char 10 bytes)
                :cr (pprint-char 13 bytes)
                :crlf (pprint-chars (list 13 10) bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-line-comment ((content nat-listp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a line comment after preprocessing."
  (b* ((bytes (pprint-astring "//" bytes))
       ((unless (grammar-character-listp content))
        (raise "Internal error: bad line comment content ~x0."
               (nat-list-fix content)))
       (bytes (pprint-chars content bytes)))
    bytes)
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-block-comment ((content nat-listp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a block comment after preprocessing."
  (b* ((bytes (pprint-astring "/*" bytes))
       ((unless (grammar-character-listp content))
        (raise "Internal error: bad block comment content ~x0."
               (nat-list-fix content)))
       (bytes (pprint-chars content bytes))
       (bytes (pprint-astring "*/" bytes)))
    bytes)
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-other ((char natp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a character that does not fit any lexeme after preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for the @(':other') case of @(tsee plexeme)."))
  (b* (((unless (grammar-character-p char))
        (raise "Internal error: bad character code ~x0." (nfix char))))
    (pprint-char char bytes))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-punctuator ((punctuator stringp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a punctuator after preprocessing."
  (b* ((chars (acl2::string=>nats punctuator))
       ((unless (grammar-character-listp chars))
        (raise "Internal error: bad punctuator ~x0." (str-fix punctuator))))
    (pprint-chars chars bytes))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-dec-digit-achar ((achar dec-digit-char-p) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print an ACL2 decimal digit character after preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "We turn the character into its code and print it.
     Note that we do not need the numeric value of the character;
     we just need to print the character itself."))
  (pprint-char (char-code achar) bytes)
  :guard-hints (("Goal" :in-theory (enable grammar-character-p
                                           dec-digit-char-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-oct-digit-achar ((achar oct-digit-char-p) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print an ACL2 octal digit character after preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "We turn the character into its code and print it.
     Note that we do not need the numeric value of the character;
     we just need to print the character itself."))
  (pprint-char (char-code achar) bytes)
  :guard-hints (("Goal" :in-theory (enable grammar-character-p
                                           oct-digit-char-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-hex-digit-achar ((achar hex-digit-char-p) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print an ACL2 hexadecimal digit character after preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "We turn the character into its code and print it.
     Note that we do not need the numeric value of the character;
     we just need to print the character itself."))
  (pprint-char (char-code achar) bytes)
  :guard-hints (("Goal" :in-theory (enable grammar-character-p
                                           hex-digit-char-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-hex-quad ((quad hex-quad-p) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a quadruple of hexadecimal digits after preprocessing."
  (b* (((hex-quad quad) quad)
       (bytes (pprint-hex-digit-achar quad.1st bytes))
       (bytes (pprint-hex-digit-achar quad.2nd bytes))
       (bytes (pprint-hex-digit-achar quad.3rd bytes))
       (bytes (pprint-hex-digit-achar quad.4th bytes)))
    bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-hex-digit-achars ((achars hex-digit-char-listp)
                                 (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print zero or more ACL2 hexadecimal digit characters
          after preprocessing."
  (b* (((when (endp achars)) (byte-list-fix bytes))
       (bytes (pprint-hex-digit-achar (car achars) bytes)))
    (pprint-hex-digit-achars (cdr achars) bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-univ-char-name ((ucname univ-char-name-p) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a universal character name after preprocessing."
  (univ-char-name-case
   ucname
   :locase-u (b* ((bytes (pprint-astring "\\u" bytes)) ; \u
                  (bytes (pprint-hex-quad ucname.quad bytes)))
               bytes)
   :upcase-u (b* ((bytes (pprint-astring "\\U" bytes)) ; \U
                  (bytes (pprint-hex-quad ucname.quad1 bytes))
                  (bytes (pprint-hex-quad ucname.quad2 bytes)))
               bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-simple-escape ((esc simple-escapep) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a simple escape after preprocessing."
  (simple-escape-case
   esc
   :squote (pprint-astring "\\'" bytes)    ; \'
   :dquote (pprint-astring "\\\"" bytes)   ; \"
   :qmark (pprint-astring "\\?" bytes)     ; \?
   :bslash (pprint-astring "\\\\" bytes)   ; \\
   :a (pprint-astring "\\a" bytes)         ; \a
   :b (pprint-astring "\\b" bytes)         ; \b
   :f (pprint-astring "\\f" bytes)         ; \f
   :n (pprint-astring "\\n" bytes)         ; \n
   :r (pprint-astring "\\r" bytes)         ; \r
   :t (pprint-astring "\\t" bytes)         ; \t
   :v (pprint-astring "\\v" bytes)         ; \v
   :percent (pprint-astring "\\%" bytes))) ; \%

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-oct-escape ((esc oct-escapep) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print an octal escape after preprocessing."
  (b* ((bytes (pprint-astring "\\" bytes))
       (bytes (oct-escape-case
               esc
               :one (pprint-oct-digit-achar esc.digit bytes)
               :two (b* ((bytes (pprint-oct-digit-achar esc.digit1 bytes))
                         (bytes (pprint-oct-digit-achar esc.digit2 bytes)))
                      bytes)
               :three (b* ((bytes (pprint-oct-digit-achar esc.digit1 bytes))
                           (bytes (pprint-oct-digit-achar esc.digit2 bytes))
                           (bytes (pprint-oct-digit-achar esc.digit3 bytes)))
                        bytes))))
    bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-escape ((esc escapep) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print an escape sequence."
  (escape-case
   esc
   :simple (pprint-simple-escape esc.escape bytes)
   :oct (pprint-oct-escape esc.escape bytes)
   :hex (b* ((bytes (pprint-astring "\\x" bytes)) ; \x
             (bytes (pprint-hex-digit-achars esc.escape bytes)))
          bytes)
   :univ (pprint-univ-char-name esc.escape bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-c-char ((cchar c-char-p) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a character or escape sequence usable in character constants,
          after preprocessing."
  (c-char-case
   cchar
   :char (b* (((unless (grammar-character-p cchar.code))
               (raise "Internal error: bad character code ~x0." cchar.code)))
           (pprint-char cchar.code bytes))
   :escape (pprint-escape cchar.escape bytes))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-s-char ((schar s-char-p) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a character or escape sequence usable in string literals,
          after preprocessing."
  (s-char-case
   schar
   :char (b* (((unless (grammar-character-p schar.code))
               (raise "Internal error: bad character code ~x0." schar.code)))
           (pprint-char schar.code bytes))
   :escape (pprint-escape schar.escape bytes))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-h-char ((hchar h-char-p) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a character usable in header names between angle brackets
          after preprocessing."
  (b* ((code (h-char->code hchar))
       ((unless (grammar-character-p code))
        (raise "Internal error: bad character code ~x0." code)))
    (pprint-char code bytes))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-q-char ((qchar q-char-p) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a character usable in header names between double quotes
          after preprocessing."
  (b* ((code (q-char->code qchar))
       ((unless (grammar-character-p code))
        (raise "Internal error: bad character code ~x0." code)))
    (pprint-char code bytes))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-c-char-list ((cchars c-char-listp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a list of characters and escape sequences
          usable in character constants,
          after preprocessing."
  (b* (((when (endp cchars)) (byte-list-fix bytes))
       (bytes (pprint-c-char (car cchars) bytes)))
    (pprint-c-char-list (cdr cchars) bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-s-char-list ((schars s-char-listp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a list of characters and escape sequences
          usable in string literals,
          after preprocessing."
  (b* (((when (endp schars)) (byte-list-fix bytes))
       (bytes (pprint-s-char (car schars) bytes)))
    (pprint-s-char-list (cdr schars) bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-h-char-list ((hchars h-char-listp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a list of characters
          usable in header names between angle brackets,
          after preprocessing."
  (b* (((when (endp hchars)) (byte-list-fix bytes))
       (bytes (pprint-h-char (car hchars) bytes)))
    (pprint-h-char-list (cdr hchars) bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-q-char-list ((qchars q-char-listp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a list of characters
          usable in header names between double quotes,
          after preprocessing."
  (b* (((when (endp qchars)) (byte-list-fix bytes))
       (bytes (pprint-q-char (car qchars) bytes)))
    (pprint-q-char-list (cdr qchars) bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-header-name ((header header-namep) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a header name after preprocessing."
  (header-name-case
   header
   :angles (b* ((bytes (pprint-astring "<" bytes))
                (bytes (pprint-h-char-list header.chars bytes))
                (bytes (pprint-astring ">" bytes)))
             bytes)
   :quotes (b* ((bytes (pprint-astring "\"" bytes))
                (bytes (pprint-q-char-list header.chars bytes))
                (bytes (pprint-astring "\"" bytes)))
             bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-cprefix ((cprefix cprefixp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a character constant prefix after preprocessing."
  (cprefix-case
   cprefix
   :upcase-l (pprint-astring "L" bytes)
   :locase-u (pprint-astring "u" bytes)
   :upcase-u (pprint-astring "U" bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-eprefix ((eprefix eprefixp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print an encoding prefix after preprocessing."
  (eprefix-case
   eprefix
   :locase-u8 (pprint-astring "u8" bytes)
   :locase-u (pprint-astring "u" bytes)
   :upcase-u (pprint-astring "U" bytes)
   :upcase-l (pprint-astring "L" bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-cconst ((cconst cconstp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a character constant after preprocessing."
  (b* (((cconst cconst) cconst)
       (bytes (cprefix-option-case
               cconst.prefix?
               :some (pprint-cprefix cconst.prefix?.val bytes)
               :none bytes))
       (bytes (pprint-astring "'" bytes))
       (bytes (pprint-c-char-list cconst.cchars bytes))
       (bytes (pprint-astring "'" bytes)))
    bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-stringlit ((stringlit stringlitp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a string literal after preprocessing."
  (b* (((stringlit stringlit) stringlit)
       (bytes (eprefix-option-case
               stringlit.prefix?
               :some (pprint-eprefix stringlit.prefix?.val bytes)
               :none bytes))
       (bytes (pprint-astring "\"" bytes))
       (bytes (pprint-s-char-list stringlit.schars bytes))
       (bytes (pprint-astring "\"" bytes)))
    bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-sign ((sign signp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a sign after preprocessing."
  (sign-case
   sign
   :plus (pprint-astring "+" bytes)
   :minus (pprint-astring "-" bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-pnumber ((number pnumberp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a preprocessing number after preprocessing."
  (pnumber-case
   number
   :digit (pprint-dec-digit-achar number.digit bytes)
   :dot-digit (b* ((bytes (pprint-astring "." bytes))
                   (bytes (pprint-dec-digit-achar number.digit bytes)))
                bytes)
   :number-digit (b* ((bytes (pprint-pnumber number.number bytes))
                      (bytes (pprint-dec-digit-achar number.digit bytes)))
                   bytes)
   :number-nondigit (b* ((bytes (pprint-pnumber number.number bytes))
                         (bytes (pprint-char (char-code number.nondigit)
                                             bytes)))
                      bytes)
   :number-locase-e-sign (b* ((bytes (pprint-pnumber number.number bytes))
                              (bytes (pprint-astring "e" bytes))
                              (bytes (pprint-sign number.sign bytes)))
                           bytes)
   :number-upcase-e-sign (b* ((bytes (pprint-pnumber number.number bytes))
                              (bytes (pprint-astring "E" bytes))
                              (bytes (pprint-sign number.sign bytes)))
                           bytes)
   :number-locase-p-sign (b* ((bytes (pprint-pnumber number.number bytes))
                              (bytes (pprint-astring "p" bytes))
                              (bytes (pprint-sign number.sign bytes)))
                           bytes)
   :number-upcase-p-sign (b* ((bytes (pprint-pnumber number.number bytes))
                              (bytes (pprint-astring "P" bytes))
                              (bytes (pprint-sign number.sign bytes)))
                           bytes)
   :number-dot (b* ((bytes (pprint-pnumber number.number bytes))
                    (bytes (pprint-astring "." bytes)))
                 bytes))
  :measure (pnumber-count number)
  :verify-guards :after-returns
  :guard-hints
  (("Goal" :in-theory (enable grammar-character-p-when-letter/uscore-char-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-ident ((ident identp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print an identifier after preprocessing."
  (b* ((string (ident->unwrap ident))
       ((unless (stringp string))
        (raise "Internal error: bad identifier non-string ~x0." string))
       (chars (acl2::string=>nats string))
       ((unless (grammar-character-listp chars))
        (raise "Internal error: bad identifier characters ~x0." chars)))
    (pprint-chars chars bytes))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-lexeme ((lexeme plexemep) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a lexeme after preprocessing."
  (plexeme-case
   lexeme
   :header (pprint-header-name lexeme.name bytes)
   :ident (pprint-ident lexeme.ident bytes)
   :number (pprint-pnumber lexeme.number bytes)
   :char (pprint-cconst lexeme.const bytes)
   :string (pprint-stringlit lexeme.literal bytes)
   :punctuator (pprint-punctuator lexeme.punctuator bytes)
   :other (pprint-other lexeme.char bytes)
   :block-comment (pprint-block-comment lexeme.content bytes)
   :line-comment (pprint-line-comment lexeme.content bytes)
   :newline (pprint-newline lexeme.chars bytes)
   :spaces (pprint-spaces lexeme.count bytes)
   :horizontal-tab (pprint-horizontal-tab bytes)
   :vertical-tab (pprint-vertical-tab bytes)
   :form-feed (pprint-form-feed bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-lexeme-list ((lexemes plexeme-listp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a list of lexemes after preprocessing."
  (b* (((when (endp lexemes)) (byte-list-fix bytes))
       (bytes (pprint-lexeme (car lexemes) bytes)))
    (pprint-lexeme-list (cdr lexemes) bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexemes-to-bytes ((lexemes plexeme-listp))
  :returns (bytes byte-listp)
  :short "Turn a list of preprocessor lexemes into a list of bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level function of our printer.
     The reversed list of bytes is initialized to empty,
     and we call the top-level printing function,
     reversing the final byte list."))
  (rev (pprint-lexeme-list lexemes nil)))
