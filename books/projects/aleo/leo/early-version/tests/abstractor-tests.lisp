; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "../testing/abstraction")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We test the abstraction functions over CSTs
; returned by lexing and parsing functions.
; Certain abstraction functions are not tested directly
; because there are no lexing or parsing functions that return
; the CSTs expected by those abstraction functions;
; these abstraction functions are tested indirectly,
; by testing abstraction functions that call them.
; Certain abstraction functions are tested directly only on some kinds of CSTs,
; because those are the only CSTs
; returned by existing lexing and parsing functions;
; these abstraction functions are tested indirectly on the other kinds of CSTs,
; by testing abstraction functions that call them.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of decimal digits to naturals.

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-nat
              "0"
              0)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-nat
              "1"
              1)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-nat
              "2"
              2)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-nat
              "3"
              3)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-nat
              "4"
              4)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-nat
              "5"
              5)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-nat
              "6"
              6)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-nat
              "7"
              7)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-nat
              "8"
              8)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-nat
              "9"
              9)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of sequences of zero or more decimal digits to naturals.

(test-lex-abs lex-*-decimal-digit
              abs-*-decimal-digit-to-nat
              ""
              0)

(test-lex-abs lex-*-decimal-digit
              abs-*-decimal-digit-to-nat
              "123"
              123)

(test-lex-abs lex-*-decimal-digit
              abs-*-decimal-digit-to-nat
              "820984923123"
              820984923123)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of decimal digits to characters.

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-char
              "0"
              #\0)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-char
              "1"
              #\1)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-char
              "2"
              #\2)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-char
              "3"
              #\3)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-char
              "4"
              #\4)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-char
              "5"
              #\5)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-char
              "6"
              #\6)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-char
              "7"
              #\7)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-char
              "8"
              #\8)

(test-lex-abs lex-decimal-digit
              abs-decimal-digit-to-char
              "9"
              #\9)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of octal digits to naturals.

(test-lex-abs lex-octal-digit
              abs-octal-digit-to-nat
              "0"
              0)

(test-lex-abs lex-octal-digit
              abs-octal-digit-to-nat
              "1"
              1)

(test-lex-abs lex-octal-digit
              abs-octal-digit-to-nat
              "2"
              2)

(test-lex-abs lex-octal-digit
              abs-octal-digit-to-nat
              "3"
              3)

(test-lex-abs lex-octal-digit
              abs-octal-digit-to-nat
              "4"
              4)

(test-lex-abs lex-octal-digit
              abs-octal-digit-to-nat
              "5"
              5)

(test-lex-abs lex-octal-digit
              abs-octal-digit-to-nat
              "6"
              6)

(test-lex-abs lex-octal-digit
              abs-octal-digit-to-nat
              "7"
              7)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of hexadecimal digits to naturals.

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "0"
              0)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "1"
              1)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "2"
              2)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "3"
              3)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "4"
              4)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "5"
              5)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "6"
              6)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "7"
              7)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "8"
              8)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "9"
              9)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "A"
              10)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "a"
              10)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "B"
              11)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "b"
              11)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "C"
              12)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "c"
              12)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "D"
              13)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "d"
              13)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "E"
              14)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "e"
              14)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "F"
              15)

(test-lex-abs lex-hexadecimal-digit
              abs-hexadecimal-digit-to-nat
              "f"
              15)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of uppercase letters.

(test-lex-abs lex-uppercase-letter
              abs-uppercase-letter
              "A"
              #\A)

(test-lex-abs lex-uppercase-letter
              abs-uppercase-letter
              "C"
              #\C)

(test-lex-abs lex-uppercase-letter
              abs-uppercase-letter
              "Z"
              #\Z)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of lowercase letters.

(test-lex-abs lex-lowercase-letter
              abs-lowercase-letter
              "h"
              #\h)

(test-lex-abs lex-lowercase-letter
              abs-lowercase-letter
              "r"
              #\r)

(test-lex-abs lex-lowercase-letter
              abs-lowercase-letter
              "z"
              #\z)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of letters.

(test-lex-abs lex-letter
              abs-letter
              "E"
              #\E)

(test-lex-abs lex-letter
              abs-letter
              "y"
              #\y)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of letters, decimal digits, and underscores.

(test-lex-abs lex-letter/decdigit/underscore
              abs-letter/decimaldigit/underscore
              "a"
              #\a)

(test-lex-abs lex-letter/decdigit/underscore
              abs-letter/decimaldigit/underscore
              "X"
              #\X)

(test-lex-abs lex-letter/decdigit/underscore
              abs-letter/decimaldigit/underscore
              "5"
              #\5)

(test-lex-abs lex-letter/decdigit/underscore
              abs-letter/decimaldigit/underscore
              "_"
              #\_)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of sequences of zero or more
; letters, decimal digits, and underscores.

(test-lex-abs lex-*-letter/decdigit/underscore
              abs-*-letter/decimaldigit/underscore
              "abc"
              (list #\a #\b #\c))

(test-lex-abs lex-*-letter/decdigit/underscore
              abs-*-letter/decimaldigit/underscore
              "x2"
              (list #\x #\2))

(test-lex-abs lex-*-letter/decdigit/underscore
              abs-*-letter/decimaldigit/underscore
              "my_var"
              (list #\m #\y #\_ #\v #\a #\r))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of identifiers.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; With lexer.

(test-lex-abs lex-identifier
              abs-identifier
              "i"
              (identifier "i"))

(test-lex-abs lex-identifier
              abs-identifier
              "user_hash_20"
              (identifier "user_hash_20"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; With parser.

(test-parse-abs parse-identifier
                abs-identifier
                "AppState"
                (identifier "AppState"))

(test-parse-abs parse-identifier
                abs-identifier
                "a12"
                (identifier "a12"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of lowercase letters and decimal digits.

(test-lex-abs lex-lcletter/decdigit
              abs-lowercaseletter/decimaldigit
              "l"
              #\l)

(test-lex-abs lex-lcletter/decdigit
              abs-lowercaseletter/decimaldigit
              "8"
              #\8)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of sequences of zero or more
; lowercase letters and decimal digits.

(test-lex-abs lex-*-lcletter/decdigit
              abs-*-lowercaseletter/decimaldigit
              ""
              nil)

(test-lex-abs lex-*-lcletter/decdigit
              abs-*-lowercaseletter/decimaldigit
              "a1b2c3"
              (list #\a #\1 #\b #\2 #\c #\3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of numerals.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; With lexer.

(test-lex-abs lex-numeral
              abs-numeral
              "0"
              0)

(test-lex-abs lex-numeral
              abs-numeral
              "00"
              0)

(test-lex-abs lex-numeral
              abs-numeral
              "8"
              8)

(test-lex-abs lex-numeral
              abs-numeral
              "54"
              54)

(test-lex-abs lex-numeral
              abs-numeral
              "054"
              54)

(test-lex-abs lex-numeral
              abs-numeral
              "3298584905"
              3298584905)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; With parser.

(test-parse-abs parse-numeral
                abs-numeral
                "72"
                72)

(test-parse-abs parse-numeral
                abs-numeral
                "007"
                7)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of unsigned literals.

(test-lex-abs lex-unsigned-literal
              abs-unsigned-literal
              "0u8"
              (literal-unsigned 0 (bitsize-8)))

(test-lex-abs lex-unsigned-literal
              abs-unsigned-literal
              "10000u32"
              (literal-unsigned 10000 (bitsize-32)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of signed literals.

(test-lex-abs lex-signed-literal
              abs-signed-literal
              "256i16"
              (literal-signed 256 (bitsize-16)))

(test-lex-abs lex-signed-literal
              abs-signed-literal
              "6678i16"
              (literal-signed 6678 (bitsize-16)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of field literals.

(test-lex-abs lex-field-literal
              abs-field-literal
              "8field"
              (literal-field 8))

(test-lex-abs lex-field-literal
              abs-field-literal
              "0field"
              (literal-field 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of product group literals.

(test-lex-abs lex-product-group-literal
              abs-product-group-literal
              "0group"
              (literal-group (group-literal-product 0)))

(test-lex-abs lex-product-group-literal
              abs-product-group-literal
              "1000group"
              (literal-group (group-literal-product 1000)))

(test-lex-abs lex-product-group-literal
              abs-product-group-literal
              "1group"
              (literal-group (group-literal-product 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of boolean literals.

(test-lex-abs lex-identifier/keyword/boolean/address
              abs-boolean-literal
              "true"
              (literal-bool t))

(test-lex-abs lex-identifier/keyword/boolean/address
              abs-boolean-literal
              "false"
              (literal-bool nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of address literals.

(test-lex-abs lex-identifier/keyword/boolean/address
              abs-address-literal
              "aleo1y90yg3yzs4g7q25f9nn8khuu00m8ysynxmcw8aca2d0phdx8dgpq4vw348"
              (literal-address
               (address
                "aleo1y90yg3yzs4g7q25f9nn8khuu00m8ysynxmcw8aca2d0phdx8dgpq4vw348")))

(test-lex-abs lex-identifier/keyword/boolean/address
              abs-address-literal
              "aleo1oooooooooooooooooooooooooooooooooooooooooooooooooooooooooo"
              (literal-address
               (address
                "aleo1oooooooooooooooooooooooooooooooooooooooooooooooooooooooooo")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of double quote.

(test-lex-abs lex-double-quote
              abs-double-quote
              "\""
              (char (char-code #\")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of double quote escape.

(test-lex-abs lex-double-quote-escape
              abs-double-quote-escape
              "\\\""
              (char (char-code #\")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of backslash escape.

(test-lex-abs lex-backslash-escape
              abs-backslash-escape
              "\\\\"
              (char (char-code #\\)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of line feed escape.

(test-lex-abs lex-line-feed-escape
              abs-line-feed-escape
              "\\n"
              (char 10))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of carriage return escape.

(test-lex-abs lex-carriage-return-escape
              abs-carriage-return-escape
              "\\r"
              (char 13))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of horizontal tab escape.

(test-lex-abs lex-horizontal-tab-escape
              abs-horizontal-tab-escape
              "\\t"
              (char 9))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of null character escape.

(test-lex-abs lex-null-character-escape
              abs-null-character-escape
              "\\0"
              (char 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of simple character escapes.

(test-lex-abs lex-simple-character-escape
              abs-simple-character-escape
              "\\\""
              (char (char-code #\")))

(test-lex-abs lex-simple-character-escape
              abs-simple-character-escape
              "\\\\"
              (char (char-code #\\)))

(test-lex-abs lex-simple-character-escape
              abs-simple-character-escape
              "\\n"
              (char 10))

(test-lex-abs lex-simple-character-escape
              abs-simple-character-escape
              "\\r"
              (char 13))

(test-lex-abs lex-simple-character-escape
              abs-simple-character-escape
              "\\t"
              (char 9))

(test-lex-abs lex-simple-character-escape
              abs-simple-character-escape
              "\\0"
              (char 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of ASCII character escapes.

(test-lex-abs lex-ascii-character-escape
              abs-ascii-character-escape
              "\\x00"
              (char 0))

(test-lex-abs lex-ascii-character-escape
              abs-ascii-character-escape
              "\\x41"
              (char (char-code #\A)))

(test-lex-abs lex-ascii-character-escape
              abs-ascii-character-escape
              "\\x7f"
              (char 127))

(test-lex-abs lex-ascii-character-escape
              abs-ascii-character-escape
              "\\x7F"
              (char 127))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of ASCII character escapes.

(test-lex-abs lex-unicode-character-escape
              abs-unicode-character-escape
              "\\u{0}"
              (char 0))

(test-lex-abs lex-unicode-character-escape
              abs-unicode-character-escape
              "\\u{33}"
              (char (char-code #\3)))

(test-lex-abs lex-unicode-character-escape
              abs-unicode-character-escape
              "\\u{Ff}"
              (char 255))

(test-lex-abs lex-unicode-character-escape
              abs-unicode-character-escape
              "\\u{10abcd}"
              (char #x10abcd))

(test-lex-abs lex-unicode-character-escape
              abs-unicode-character-escape
              "\\u{10FFFF}"
              (char #x10ffff))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of anything that is not a double quote or a backslash.

(test-lex-abs lex-not-double-quote-or-backslash-or-line-feed-or-carriage-return
              abs-not-double-quote-or-backslash-or-line-feed-or-carriage-return
              "B"
              (char 66))

; U+1 is no longer supported (not in safe-ascii lexical rule)
#||
(test-lex-abs lex-not-double-quote-or-backslash-or-line-feed-or-carriage-return
              abs-not-double-quote-or-backslash-or-line-feed-or-carriage-return
              (list 1)
              (char 1))
||#

(test-lex-abs lex-not-double-quote-or-backslash-or-line-feed-or-carriage-return
              abs-not-double-quote-or-backslash-or-line-feed-or-carriage-return
              "'"
              (char (char-code #\')))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of string literal elements.

(test-lex-abs lex-string-literal-element
              abs-string-literal-element
              "h"
              (char (char-code #\h)))

(test-lex-abs lex-string-literal-element
              abs-string-literal-element
              "\\n"
              (char 10))

(test-lex-abs lex-string-literal-element
              abs-string-literal-element
              "\\x18"
              (char 24))

(test-lex-abs lex-string-literal-element
              abs-string-literal-element
              "\\u{123}"
              (char #x123))

(test-lex-abs lex-string-literal-element
              abs-string-literal-element
              "'"
              (char (char-code #\')))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of sequences of string literal elements.

(test-lex-abs lex-*-string-literal-element
              abs-*-string-literal-element
              ""
              nil)

(test-lex-abs lex-*-string-literal-element
              abs-*-string-literal-element
              "abc"
              (list (char (char-code #\a))
                    (char (char-code #\b))
                    (char (char-code #\c))))

(test-lex-abs lex-*-string-literal-element
              abs-*-string-literal-element
              "1\\x11\\u{1111}"
              (list (char (char-code #\1))
                    (char #x11)
                    (char #x1111)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of string literals.

(test-lex-abs lex-string-literal
              abs-string-literal
              "\"\""
              (literal-string nil))

(test-lex-abs lex-string-literal
              abs-string-literal
              "\"Hello.\""
              (literal-string (list (char (char-code #\H))
                                    (char (char-code #\e))
                                    (char (char-code #\l))
                                    (char (char-code #\l))
                                    (char (char-code #\o))
                                    (char (char-code #\.)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of numeric literals.

(test-lex-abs lex-numeric-literal
              abs-numeric-literal
              "15i8"
              (literal-signed 15 (bitsize-8)))

(test-lex-abs lex-numeric-literal
              abs-numeric-literal
              "100field"
              (literal-field 100))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of primitive types.

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "u8"
                (type-unsigned (bitsize-8)))

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "u16"
                (type-unsigned (bitsize-16)))

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "u32"
                (type-unsigned (bitsize-32)))

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "u64"
                (type-unsigned (bitsize-64)))

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "u128"
                (type-unsigned (bitsize-128)))

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "i8"
                (type-signed (bitsize-8)))

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "i16"
                (type-signed (bitsize-16)))

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "i32"
                (type-signed (bitsize-32)))

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "i64"
                (type-signed (bitsize-64)))

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "i128"
                (type-signed (bitsize-128)))

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "field"
                (type-field))

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "group"
                (type-group))

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "bool"
                (type-bool))

(test-parse-abs parse-named-primitive-type
                abs-named-primitive-type
                "address"
                (type-address))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of types.

(test-parse-abs parse-type
                abs-type
                "u8"
                (type-unsigned (bitsize-8)))

(test-parse-abs parse-type
                abs-type
                "u16"
                (type-unsigned (bitsize-16)))

(test-parse-abs parse-type
                abs-type
                "u32"
                (type-unsigned (bitsize-32)))

(test-parse-abs parse-type
                abs-type
                "u64"
                (type-unsigned (bitsize-64)))

(test-parse-abs parse-type
                abs-type
                "u128"
                (type-unsigned (bitsize-128)))

(test-parse-abs parse-type
                abs-type
                "i8"
                (type-signed (bitsize-8)))

(test-parse-abs parse-type
                abs-type
                "i16"
                (type-signed (bitsize-16)))

(test-parse-abs parse-type
                abs-type
                "i32"
                (type-signed (bitsize-32)))

(test-parse-abs parse-type
                abs-type
                "i64"
                (type-signed (bitsize-64)))

(test-parse-abs parse-type
                abs-type
                "i128"
                (type-signed (bitsize-128)))

(test-parse-abs parse-type
                abs-type
                "field"
                (type-field))

(test-parse-abs parse-type
                abs-type
                "group"
                (type-group))

(test-parse-abs parse-type
                abs-type
                "bool"
                (type-bool))

(test-parse-abs parse-type
                abs-type
                "address"
                (type-address))

(test-parse-abs parse-type
                abs-type
                "()"
                (type-unit))

(test-parse-abs parse-type
                abs-type
                "(u8, i8)"
                (type-tuple (list (type-unsigned (bitsize-8))
                                  (type-signed (bitsize-8)))))

(test-parse-abs parse-type
                abs-type
                "(address, (), (bool, group, field))"
                (type-tuple (list (type-address)
                                  (type-unit)
                                  (type-tuple (list (type-bool)
                                                    (type-group)
                                                    (type-field))))))

(test-parse-abs parse-type
                abs-type
                "abc"
                (type-internal-named (identifier "abc") nil))

(test-parse-abs parse-type
                abs-type
                "abc.record"
                (type-internal-named (identifier "abc") t))

(test-parse-abs parse-type
                abs-type
                "vote.aleo/nandemo"
                (type-external-named
                 (make-locator
                  :program (make-programid :name (identifier "vote")
                                           :network (identifier "aleo"))
                  :name (identifier "nandemo"))
                 nil))

(test-parse-abs parse-type
                abs-type
                "vote.aleo/nandemo.record"
                (type-external-named
                 (make-locator
                  :program (make-programid :name (identifier "vote")
                                           :network (identifier "aleo"))
                  :name (identifier "nandemo"))
                 t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of group coordinates.

(test-parse-abs parse-group-coordinate
                abs-group-coordinate
                "+"
                (coordinate-sign-high))

(test-parse-abs parse-group-coordinate
                abs-group-coordinate
                "-"
                (coordinate-sign-low))

(test-parse-abs parse-group-coordinate
                abs-group-coordinate
                "_"
                (coordinate-inferred))

(test-parse-abs parse-group-coordinate
                abs-group-coordinate
                "87393"
                (coordinate-explicit 87393))

(test-parse-abs parse-group-coordinate
                abs-group-coordinate
                "-128"
                (coordinate-explicit -128))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of affine group literals.

(test-parse-abs parse-affine-group-literal
                abs-affine-group-literal
                "(0, 0)group"
                (group-literal-affine (coordinate-explicit 0)
                                      (coordinate-explicit 0)))

(test-parse-abs parse-affine-group-literal
                abs-affine-group-literal
                "(-2222, +)group"
                (group-literal-affine (coordinate-explicit -2222)
                                      (coordinate-sign-high)))

(test-parse-abs parse-affine-group-literal
                abs-affine-group-literal
                "(_, _)group"
                (group-literal-affine (coordinate-inferred)
                                      (coordinate-inferred)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of literals.

(test-parse-abs parse-literal
                abs-literal
                "64u64"
                (literal-unsigned 64 (bitsize-64)))

(test-parse-abs parse-literal
                abs-literal
                "664i64"
                (literal-signed 664 (bitsize-64)))

(test-parse-abs parse-literal
                abs-literal
                "10field"
                (literal-field 10))

(test-parse-abs parse-literal
                abs-literal
                "8group"
                (literal-group (group-literal-product 8)))

(test-parse-abs parse-literal
                abs-literal
                "(1, 0)group"
                (literal-group (group-literal-affine (coordinate-explicit 1)
                                                     (coordinate-explicit 0))))

(test-parse-abs parse-literal
                abs-literal
                "true"
                (literal-bool t))

(test-parse-abs parse-literal
                abs-literal
                "false"
                (literal-bool nil))

(test-parse-abs
 parse-literal
 abs-literal
 "aleo1oooooooooooooooooooooooooooooooooooooooooooooooooooooooooo"
 (literal-address
  (address
   "aleo1oooooooooooooooooooooooooooooooooooooooooooooooooooooooooo")))

(test-parse-abs parse-literal
                abs-literal
                "\"\\x41\""
                (literal-string (list (char #x41))))

(test-parse-abs parse-literal
                abs-literal
                "\"OoO\""
                (literal-string (list (char (char-code #\O))
                                      (char (char-code #\o))
                                      (char (char-code #\O)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of program IDs

(test-parse-abs parse-program-id
                abs-program-id
                "vote.aleo"
                (make-programid
                 :name (identifier "vote")
                 :network (identifier "aleo")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of locators.

(test-parse-abs parse-locator
                abs-locator
                "vote.aleo/nandemo"
                (make-locator
                 :program (make-programid
                           :name (identifier "vote")
                           :network (identifier "aleo"))
                 :name (identifier "nandemo")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of primary expressions.

(test-parse-abs parse-primary-expression
                abs-primary-expression
                "abc"
                (expression-var/const (identifier "abc")))

(test-parse-abs parse-primary-expression
                abs-primary-expression
                "77u8"
                (expression-literal (literal-unsigned 77 (bitsize-8))))

(test-parse-abs parse-primary-expression
                abs-primary-expression
                "(a**b)"
                (make-expression-binary
                 :op (binop-pow)
                 :arg1 (expression-var/const (identifier "a"))
                 :arg2 (expression-var/const (identifier "b"))))

(test-parse-abs parse-primary-expression
                abs-primary-expression
                "f()"
                (make-expression-internal-call
                 :fun (identifier "f")
                 :args nil))

(test-parse-abs parse-primary-expression
                abs-primary-expression
                "f.g/h()"
                (make-expression-external-call
                 :fun (make-locator :program (make-programid
                                              :name (identifier "f")
                                              :network (identifier "g"))
                                    :name (identifier "h"))
                 :args nil))

(test-parse-abs parse-primary-expression
                abs-primary-expression
                "solve(a, b, 1i8)"
                (make-expression-internal-call
                 :fun (identifier "solve")
                 :args (list
                        (expression-var/const (identifier "a"))
                        (expression-var/const (identifier "b"))
                        (expression-literal (literal-signed 1 (bitsize-8))))))

(test-parse-abs parse-primary-expression
                abs-primary-expression
                "solve(a, b, 1i8)"
                (make-expression-internal-call
                 :fun (identifier "solve")
                 :args (list
                        (expression-var/const (identifier "a"))
                        (expression-var/const (identifier "b"))
                        (expression-literal (literal-signed 1 (bitsize-8))))))

(test-parse-abs parse-primary-expression
                abs-primary-expression
                "()"
                (make-expression-unit))

(test-parse-abs parse-primary-expression
                abs-primary-expression
                "(a,b)"
                (make-expression-tuple
                 :components (list (expression-var/const (identifier "a"))
                                   (expression-var/const (identifier "b")))))

(test-parse-abs parse-primary-expression
                abs-primary-expression
                "Foo { x }"
                (make-expression-struct
                 :type (identifier "Foo")
                 :components
                 (list (make-struct-init :name (identifier "x")
                                         :expr (expression-var/const
                                                (identifier "x"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of sequences of
; zero or more comma-preceded expressions.

(test-parse-abs parse-*-comma-expression
                abs-*-comma-expression
                ""
                nil)

(test-parse-abs parse-*-comma-expression
                abs-*-comma-expression
                ", var"
                (list (expression-var/const (identifier "var"))))

(test-parse-abs parse-*-comma-expression
                abs-*-comma-expression
                ", r, x + y"
                (list (expression-var/const (identifier "r"))
                      (make-expression-binary
                       :op (binop-add)
                       :arg1 (expression-var/const (identifier "x"))
                       :arg2 (expression-var/const (identifier "y")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of function arguments.

(test-parse-abs parse-function-arguments
                abs-function-arguments
                "(    )"
                nil)

(test-parse-abs parse-function-arguments
                abs-function-arguments
                "(first)"
                (list (expression-var/const (identifier "first"))))

(test-parse-abs parse-function-arguments
                abs-function-arguments
                "(first, second, third)"
                (list (expression-var/const (identifier "first"))
                      (expression-var/const (identifier "second"))
                      (expression-var/const (identifier "third"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of unary expressions.

(test-parse-abs parse-unary-expression
                abs-unary-expression
                "!x"
                (make-expression-unary
                 :op (unop-not)
                 :arg (expression-var/const (identifier "x"))))

(test-parse-abs parse-unary-expression
                abs-unary-expression
                "-x"
                (make-expression-unary
                 :op (unop-neg)
                 :arg (expression-var/const (identifier "x"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of exponential expressions.

(test-parse-abs parse-exponential-expression
                abs-exponential-expression
                "x ** y"
                (make-expression-binary
                 :op (binop-pow)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of multiplicative expressions.

(test-parse-abs parse-multiplicative-expression
                abs-multiplicative-expression
                "x * y"
                (make-expression-binary
                 :op (binop-mul)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-multiplicative-expression
                abs-multiplicative-expression
                "x / y"
                (make-expression-binary
                 :op (binop-div)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-multiplicative-expression
                abs-multiplicative-expression
                "x % y"
                (make-expression-binary
                 :op (binop-rem)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of additive expressions.

(test-parse-abs parse-additive-expression
                abs-additive-expression
                "x + y"
                (make-expression-binary
                 :op (binop-add)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-additive-expression
                abs-additive-expression
                "x - y"
                (make-expression-binary
                 :op (binop-sub)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of shift expressions.

(test-parse-abs parse-shift-expression
                abs-shift-expression
                "x << y"
                (make-expression-binary
                 :op (binop-shl)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-shift-expression
                abs-shift-expression
                "x >> y"
                (make-expression-binary
                 :op (binop-shr)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of bitwise expressions.

(test-parse-abs parse-conjunctive-expression
                abs-conjunctive-expression
                "x & y"
                (make-expression-binary
                 :op (binop-bitand)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-disjunctive-expression
                abs-disjunctive-expression
                "x | y"
                (make-expression-binary
                 :op (binop-bitior)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-exclusive-disjunctive-expression
                abs-exclusive-disjunctive-expression
                "x ^ y"
                (make-expression-binary
                 :op (binop-bitxor)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of ordering expressions.

(test-parse-abs parse-ordering-expression
                abs-ordering-expression
                "x < y"
                (make-expression-binary
                 :op (binop-lt)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-ordering-expression
                abs-ordering-expression
                "x > y"
                (make-expression-binary
                 :op (binop-gt)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-ordering-expression
                abs-ordering-expression
                "x <= y"
                (make-expression-binary
                 :op (binop-le)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-ordering-expression
                abs-ordering-expression
                "x >= y"
                (make-expression-binary
                 :op (binop-ge)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of equality expressions.

(test-parse-abs parse-equality-expression
                abs-equality-expression
                "x == y"
                (make-expression-binary
                 :op (binop-eq)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-equality-expression
                abs-equality-expression
                "x != y"
                (make-expression-binary
                 :op (binop-ne)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of conditional conjunctive expressions.
; (These are conditional in the sense that if the first value
; determines the result value, the second value is not evaluated.)

(test-parse-abs parse-conditional-conjunctive-expression
                abs-conditional-conjunctive-expression
                "x && y"
                (make-expression-binary
                 :op (binop-and)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of conditional-disjunctive expressions.

(test-parse-abs parse-conditional-disjunctive-expression
                abs-conditional-disjunctive-expression
                "x || y"
                (make-expression-binary
                 :op (binop-or)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of conditional ternary expressions.

(test-parse-abs parse-conditional-ternary-expression
                abs-conditional-ternary-expression
                "x ? y : z"
                (make-expression-cond
                 :test (expression-var/const (identifier "x"))
                 :then (expression-var/const (identifier "y"))
                 :else (expression-var/const (identifier "z"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of expressions.

(test-parse-abs parse-expression
                abs-expression
                "x"
                (expression-var/const (identifier "x")))

(test-parse-abs parse-expression
                abs-expression
                "count_max"
                (expression-var/const (identifier "count_max")))

(test-parse-abs parse-expression
                abs-expression
                "true"
                (expression-literal (literal-bool t)))

(test-parse-abs parse-expression
                abs-expression
                "1field"
                (expression-literal (literal-field 1)))

(test-parse-abs parse-expression
                abs-expression
                "(x + y)"
                (make-expression-binary
                 :op (binop-add)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "f()"
                (make-expression-internal-call
                 :fun (identifier "f")
                 :args nil))

(test-parse-abs parse-expression
                abs-expression
                "solve(a, b, 0field)"
                (make-expression-internal-call
                 :fun (identifier "solve")
                 :args (list
                        (expression-var/const (identifier "a"))
                        (expression-var/const (identifier "b"))
                        (expression-literal (literal-field 0)))))

(test-parse-abs parse-unary-expression
                abs-unary-expression
                "!x"
                (make-expression-unary
                 :op (unop-not)
                 :arg (expression-var/const (identifier "x"))))

(test-parse-abs parse-unary-expression
                abs-unary-expression
                "-x"
                (make-expression-unary
                 :op (unop-neg)
                 :arg (expression-var/const (identifier "x"))))

(test-parse-abs parse-expression
                abs-expression
                "x ** y"
                (make-expression-binary
                 :op (binop-pow)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x * y"
                (make-expression-binary
                 :op (binop-mul)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x / y"
                (make-expression-binary
                 :op (binop-div)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x % y"
                (make-expression-binary
                 :op (binop-rem)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x.rem(y)"
                (make-expression-binary
                 :op (binop-rem)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x.rem_wrapped(y)"
                (make-expression-binary
                 :op (binop-rem-wrapped)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x + y"
                (make-expression-binary
                 :op (binop-add)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x - y"
                (make-expression-binary
                 :op (binop-sub)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x < y"
                (make-expression-binary
                 :op (binop-lt)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x > y"
                (make-expression-binary
                 :op (binop-gt)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x <= y"
                (make-expression-binary
                 :op (binop-le)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x >= y"
                (make-expression-binary
                 :op (binop-ge)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x == y"
                (make-expression-binary
                 :op (binop-eq)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x != y"
                (make-expression-binary
                 :op (binop-ne)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x && y"
                (make-expression-binary
                 :op (binop-and)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x || y"
                (make-expression-binary
                 :op (binop-or)
                 :arg1 (expression-var/const (identifier "x"))
                 :arg2 (expression-var/const (identifier "y"))))

(test-parse-abs parse-expression
                abs-expression
                "x ? y : z"
                (make-expression-cond
                 :test (expression-var/const (identifier "x"))
                 :then (expression-var/const (identifier "y"))
                 :else (expression-var/const (identifier "z"))))

(test-parse-abs parse-expression
                abs-expression
                "x.double().val"
                (make-expression-struct-component
                 :struct (make-expression-unary
                          :op (make-unop-double)
                          :arg (expression-var/const (identifier "x")))
                 :component (identifier "val")))

(test-parse-abs parse-expression
                abs-expression
                "x.double().1"
                (make-expression-tuple-component
                 :tuple (make-expression-unary
                         :op (make-unop-double)
                         :arg (expression-var/const (identifier "x")))
                 :index 1))

(test-parse-abs parse-expression
                abs-expression
                "x.val.double()"
                (make-expression-unary
                 :op (make-unop-double)
                 :arg (make-expression-struct-component
                       :struct (expression-var/const (identifier "x"))
                       :component (identifier "val"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of return statements.

(test-parse-abs parse-return-statement
                abs-return-statement
                "return x + y * z;"
                (statement-return
                 (make-expression-binary
                  :op (binop-add)
                  :arg1 (expression-var/const (identifier "x"))
                  :arg2 (make-expression-binary
                         :op (binop-mul)
                         :arg1 (expression-var/const (identifier "y"))
                         :arg2 (expression-var/const (identifier "z"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of variable declarations.

(test-parse-abs parse-variable-declaration
                abs-variable-declaration
                "let u: bool = false;"
                (make-vardecl
                 :name (identifier "u")
                 :type (type-bool)
                 :init (expression-literal (literal-bool nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of constant declarations.

(test-parse-abs parse-constant-declaration
                abs-constant-declaration
                "const u: bool = false;"
                (make-constdecl
                 :name (identifier "u")
                 :type (type-bool)
                 :init (expression-literal (literal-bool nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of assert calls.

(test-parse-abs parse-assert-call
                abs-assert-call
                "assert(a == b)"
                (console-assert
                 (make-expression-binary
                  :op (binop-eq)
                  :arg1 (expression-var/const (identifier "a"))
                  :arg2 (expression-var/const (identifier "b")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of console calls.

(test-parse-abs parse-console-call
                abs-console-call
                "assert(a == b)"
                (console-assert
                 (make-expression-binary
                  :op (binop-eq)
                  :arg1 (expression-var/const (identifier "a"))
                  :arg2 (expression-var/const (identifier "b")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of console statements.

(test-parse-abs parse-console-statement
                abs-console-statement
                "console.assert(a == b);"
                (statement-console
                 (console-assert
                  (make-expression-binary
                   :op (binop-eq)
                   :arg1 (expression-var/const (identifier "a"))
                   :arg2 (expression-var/const (identifier "b"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of finalize statements.

(test-parse-abs parse-finalize-statement
                abs-finalize-statement
                "async finalize(self.caller, amount);"
                (make-statement-finalize
                 :arguments
                 (list
                  (make-expression-struct-component
                   :struct (make-expression-var/const :name (identifier "self"))
                   :component (identifier "caller"))
                  (make-expression-var/const :name (identifier "amount")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of increment statements.

(test-parse-abs parse-increment-statement
                abs-increment-statement
                "increment(disagree_votes, pid, 1u64);"
                (make-statement-increment
                 :mapping (identifier "disagree_votes")
                 :index (make-expression-var/const :name (identifier "pid"))
                 :amount (expression-literal
                          (literal-unsigned 1 (bitsize-64)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of decrement statements.

(test-parse-abs parse-decrement-statement
                abs-decrement-statement
                "decrement(account, sender, amount);"
                (make-statement-decrement
                 :mapping (identifier "account")
                 :index (make-expression-var/const
                         :name (identifier "sender"))
                 :amount (make-expression-var/const
                          :name (identifier "amount"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of statements.

(test-parse-abs parse-statement
                abs-statement
                "return x ? y : z;"
                (statement-return
                 (make-expression-cond
                  :test (expression-var/const (identifier "x"))
                  :then (expression-var/const (identifier "y"))
                  :else (expression-var/const (identifier "z")))))

(test-parse-abs parse-statement
                abs-statement
                "let x: field = 111field;"
                (statement-let
                 (make-vardecl
                  :name(identifier "x")
                  :type (type-field)
                  :init (expression-literal (literal-field 111)))))

(test-parse-abs parse-statement
                abs-statement
                "const c: group = d + 1group;"
                (statement-const
                 (make-constdecl
                  :name (identifier "c")
                  :type (type-group)
                  :init (make-expression-binary
                         :op (binop-add)
                         :arg1 (expression-var/const (identifier "d"))
                         :arg2 (expression-literal
                                (literal-group (group-literal-product 1)))))))

(test-parse-abs parse-statement
                abs-statement
                "if test { x = 1field; }"
                (make-statement-if
                 :branches
                 (list
                  (make-branch
                   :test (expression-var/const (identifier "test"))
                   :body (list
                          (make-statement-assign
                           :op (make-asgop-asg)
                           :left (expression-var/const (identifier "x"))
                           :right (expression-literal (literal-field 1))))))
                 :else nil))

(test-parse-abs parse-statement
                abs-statement
                "if test { x = 1field; } else if test2 { return 15field; }"
                (make-statement-if
                 :branches
                 (list
                  (make-branch
                   :test (expression-var/const (identifier "test"))
                   :body (list
                          (make-statement-assign
                           :op (make-asgop-asg)
                           :left (expression-var/const (identifier "x"))
                           :right (expression-literal (literal-field 1)))))
                  (make-branch
                   :test (expression-var/const (identifier "test2"))
                   :body (list
                          (statement-return
                           (expression-literal (literal-field 15))))))
                 :else nil))

(test-parse-abs parse-statement
                abs-statement
                "if test { x = 1field; }
                 else if test2 { return 15field; }
                 else { return f(); }"
                (make-statement-if
                 :branches
                 (list
                  (make-branch
                   :test (expression-var/const (identifier "test"))
                   :body (list
                          (make-statement-assign
                           :op (make-asgop-asg)
                           :left (expression-var/const (identifier "x"))
                           :right (expression-literal (literal-field 1)))))
                  (make-branch
                   :test (expression-var/const (identifier "test2"))
                   :body (list
                          (statement-return
                           (expression-literal (literal-field 15))))))
                 :else (list
                        (statement-return
                         (make-expression-internal-call
                          :fun (identifier "f")
                          :args nil)))))

(test-parse-abs parse-statement
                abs-statement
                "for i: field in 0field..10field { x = i; }"
                (make-statement-for
                 :name (identifier "i")
                 :type (type-field)
                 :from (expression-literal (literal-field 0))
                 :to (expression-literal (literal-field 10))
                 :inclusivep nil
                 :body (list (make-statement-assign
                              :op (make-asgop-asg)
                              :left (expression-var/const (identifier "x"))
                              :right (expression-var/const (identifier "i"))))))

(test-parse-abs parse-statement
                abs-statement
                "for i: field in 0field..=10field { x = i; }"
                (make-statement-for
                 :name (identifier "i")
                 :type (type-field)
                 :from (expression-literal (literal-field 0))
                 :to (expression-literal (literal-field 10))
                 :inclusivep t
                 :body (list (make-statement-assign
                              :op (make-asgop-asg)
                              :left (expression-var/const (identifier "x"))
                              :right (expression-var/const (identifier "i"))))))

#||  TDDO consider reintroducing without console.log
(test-parse-abs parse-statement
                abs-statement
                "console.log(\"a\", a);"
                (statement-console
                 (make-console-log
                  :string (list (char (char-code #\a)))
                  :exprs (list (expression-var/const (identifier "a"))))))
||#

(test-parse-abs parse-statement
                abs-statement
                "{ return a; return b; return c; }"
                (statement-block
                 (list
                  (statement-return (expression-var/const (identifier "a")))
                  (statement-return (expression-var/const (identifier "b")))
                  (statement-return (expression-var/const (identifier "c"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of blocks.

(test-parse-abs parse-block
                abs-block
                "{}"
                nil)

(test-parse-abs parse-block
                abs-block
                "{ let x: field = 22field; }"
                (list
                 (statement-let
                  (make-vardecl
                   :name (identifier "x")
                   :type (type-field)
                   :init (expression-literal (literal-field 22))))))

(test-parse-abs parse-block
                abs-block
                "{ return a; return b; }"
                (list
                 (statement-return (expression-var/const (identifier "a")))
                 (statement-return (expression-var/const (identifier "b")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of branches.

(test-parse-abs parse-branch
                abs-branch
                "if x == y { b &&= true; }"
                (make-branch
                 :test (make-expression-binary
                        :op (binop-eq)
                        :arg1 (expression-var/const (identifier "x"))
                        :arg2 (expression-var/const (identifier "y")))
                 :body (list
                        (make-statement-assign
                         :op (make-asgop-asg-and)
                         :left (expression-var/const (identifier "b"))
                         :right (expression-literal (literal-bool t))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of conditional statements.

(test-parse-abs parse-conditional-statement
                abs-conditional-statement
                "if test { x = 1field; }"
                (make-statement-if
                 :branches
                 (list
                  (make-branch
                   :test (expression-var/const (identifier "test"))
                   :body (list
                          (make-statement-assign
                           :op (make-asgop-asg)
                           :left (expression-var/const (identifier "x"))
                           :right (expression-literal (literal-field 1))))))
                 :else nil))

(test-parse-abs parse-conditional-statement
                abs-conditional-statement
                "if test { x = 1field; } else if test2 { return 15field; }"
                (make-statement-if
                 :branches
                 (list
                  (make-branch
                   :test (expression-var/const (identifier "test"))
                   :body (list
                          (make-statement-assign
                           :op (make-asgop-asg)
                           :left (expression-var/const (identifier "x"))
                           :right (expression-literal (literal-field 1)))))
                  (make-branch
                   :test (expression-var/const (identifier "test2"))
                   :body (list
                          (statement-return
                           (expression-literal (literal-field 15))))))
                 :else nil))

(test-parse-abs parse-conditional-statement
                abs-conditional-statement
                "if test { x = 1field; }
                 else if test2 { return 15field; }
                 else { return f(); }"
                (make-statement-if
                 :branches
                 (list
                  (make-branch
                   :test (expression-var/const (identifier "test"))
                   :body (list
                          (make-statement-assign
                           :op (make-asgop-asg)
                           :left (expression-var/const (identifier "x"))
                           :right (expression-literal (literal-field 1)))))
                  (make-branch
                   :test (expression-var/const (identifier "test2"))
                   :body (list
                          (statement-return
                           (expression-literal (literal-field 15))))))
                 :else (list
                        (statement-return
                         (make-expression-internal-call
                          :fun (identifier "f")
                          :args nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of loops.

(test-parse-abs parse-loop-statement
                abs-loop-statement
                "for i:field in 0field..10field { x = i; }"
                (make-statement-for
                 :name (identifier "i")
                 :type (type-field)
                 :from (expression-literal (literal-field 0))
                 :to (expression-literal (literal-field 10))
                 :inclusivep nil
                 :body (list (make-statement-assign
                              :op (make-asgop-asg)
                              :left (expression-var/const (identifier "x"))
                              :right (expression-var/const (identifier
                                                            "i"))))))

(test-parse-abs parse-loop-statement
                abs-loop-statement
                "for i:field in 0field..=10field { x = i; }"
                (make-statement-for
                 :name (identifier "i")
                 :type (type-field)
                 :from (expression-literal (literal-field 0))
                 :to (expression-literal (literal-field 10))
                 :inclusivep t
                 :body (list (make-statement-assign
                              :op (make-asgop-asg)
                              :left (expression-var/const (identifier "x"))
                              :right (expression-var/const (identifier "i"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of single function parameters.

(test-parse-abs parse-function-parameter
                abs-function-parameter
                "a: bool"
                (make-funparam
                 :name (identifier "a")
                 :sort (var/const-sort-private)
                 :type (type-bool)))

(test-parse-abs parse-function-parameter
                abs-function-parameter
                "public a: bool"
                (make-funparam
                 :name (identifier "a")
                 :sort (var/const-sort-public)
                 :type (type-bool)))

(test-parse-abs parse-function-parameter
                abs-function-parameter
                "const a: bool"
                (make-funparam
                 :name (identifier "a")
                 :sort (var/const-sort-const)
                 :type (type-bool)))

(test-parse-abs parse-function-parameter
                abs-function-parameter
                "constant a: bool"
                (make-funparam
                 :name (identifier "a")
                 :sort (var/const-sort-constant)
                 :type (type-bool)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of sequences of
; zero or more comma-preceded function parameters.

(test-parse-abs parse-*-comma-function-parameter
                abs-*-comma-function-parameter
                ""
                nil)

(test-parse-abs parse-*-comma-function-parameter
                abs-*-comma-function-parameter
                ", ch: field"
                (list (make-funparam
                       :name (identifier "ch")
                       :sort (var/const-sort-private)
                       :type (type-field))))

(test-parse-abs parse-*-comma-function-parameter
                abs-*-comma-function-parameter
                ", ch: group, const c: field"
                (list (make-funparam
                       :name (identifier "ch")
                       :sort (var/const-sort-private)
                       :type (type-group))
                      (make-funparam
                       :name (identifier "c")
                       :sort (var/const-sort-const)
                       :type (type-field))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of multiple function inputs.

(test-parse-abs parse-function-parameters
                abs-function-parameters
                "x: u32"
                (list (make-funparam
                       :name (identifier "x")
                       :sort (var/const-sort-private)
                       :type (type-unsigned (bitsize-32)))))

(test-parse-abs parse-function-parameters
                abs-function-parameters
                "x: u32, constant y: i8"
                (list (make-funparam
                       :name (identifier "x")
                       :sort (var/const-sort-private)
                       :type (type-unsigned (bitsize-32)))
                      (make-funparam
                       :name (identifier "y")
                       :sort (var/const-sort-constant)
                       :type (type-signed (bitsize-8)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of function declarations.

(test-parse-abs parse-function-declaration
                abs-function-declaration
                "function f() -> field {}"
                (make-fundecl
                 :sort (fun-sort-standard)
                 :name (identifier "f")
                 :inputs nil
                 :output (type-field)
                 :body nil))

(test-parse-abs parse-function-declaration
                abs-function-declaration
                "function f(x: u8) -> group {}"
                (make-fundecl
                 :sort (fun-sort-standard)
                 :name (identifier "f")
                 :inputs (list (make-funparam
                                :name (identifier "x")
                                :sort (var/const-sort-private)
                                :type (type-unsigned (bitsize-8))))
                 :output (type-group)
                 :body nil))

(test-parse-abs parse-function-declaration
                abs-function-declaration
                "function f(x: u8, public y: u8) -> u8 { return x + y; }"
                (make-fundecl
                 :sort (fun-sort-standard)
                 :name (identifier "f")
                 :inputs (list (make-funparam
                                :name (identifier "x")
                                :sort (var/const-sort-private)
                                :type (type-unsigned (bitsize-8)))
                               (make-funparam
                                :name (identifier "y")
                                :sort (var/const-sort-public)
                                :type (type-unsigned (bitsize-8))))
                 :output (type-unsigned (bitsize-8))
                 :body (list
                        (statement-return
                         (make-expression-binary
                          :op (binop-add)
                          :arg1 (expression-var/const (identifier "x"))
                          :arg2 (expression-var/const (identifier "y")))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of transition declarations.

(test-parse-abs parse-transition-declaration
                abs-transition-declaration
                "transition f() -> field {}"
                (make-fundecl
                 :sort (fun-sort-transition)
                 :name (identifier "f")
                 :inputs nil
                 :output (type-field)
                 :body nil
                 :finalizer nil))

;; from examples/token/src/main.leo
(test-parse-abs parse-transition-declaration
                abs-transition-declaration
                "transition transfer_public_to_private(public receiver: address, public amount: u64) -> token {
        // Produces a token record for the token receiver.
        let transferred: token = token {
            owner: receiver,
            gates: 0u64,
            amount: amount,
        };

        // Decrement the token amount of the caller publicly.
        async finalize(self.caller, amount);

        // Output the receiver's record.
        return transferred;
    }

    finalize transfer_public_to_private(public sender: address, public amount: u64) {
        // Decrements `account[sender]` by `amount`.
        // If `account[sender]` does not exist, it will be created.
        // If `account[sender] - amount` underflows, `transfer_public_to_private` is reverted.
        decrement(account, sender, amount);
    }"
                (make-fundecl
                 :annotations nil
                 :sort (fun-sort-transition)
                 :name (identifier "transfer_public_to_private")
                 :inputs (list (make-funparam
                                :name (identifier "receiver")
                                :sort (var/const-sort-public)
                                :type (type-address))
                               (make-funparam
                                :name (identifier "amount")
                                :sort (var/const-sort-public)
                                :type (type-unsigned (bitsize-64))))
                 :output (type-internal-named (identifier "token") nil)
                 :body
                 (list (make-statement-let
                        :get (make-vardecl
                              :name (identifier "transferred")
                              :type (type-internal-named
                                     (identifier "token") nil)
                              :init (make-expression-struct
                                     :type (identifier "token")
                                     :components
                                     (list
                                      (make-struct-init
                                       :name (identifier "owner")
                                       :expr (make-expression-var/const
                                              :name (identifier "receiver")))
                                      (make-struct-init
                                       :name (identifier "gates")
                                       :expr (make-expression-literal
                                              :get (make-literal-unsigned
                                                    :val 0
                                                    :size (bitsize-64))))
                                      (make-struct-init
                                       :name (identifier "amount")
                                       :expr (make-expression-var/const
                                              :name (identifier "amount")))))))
                       (make-statement-finalize
                        :arguments
                        (list (make-expression-struct-component
                               :struct (make-expression-var/const
                                        :name (identifier "self"))
                               :component (identifier "caller"))
                              (make-expression-var/const
                               :name (identifier "amount"))))
                       (make-statement-return
                        :value (make-expression-var/const
                                :name (identifier "transferred"))))
                 :finalizer
                 (make-finalizer
                  :name (identifier "transfer_public_to_private")
                  :inputs (list (make-funparam
                                 :name (identifier "sender")
                                 :sort (var/const-sort-public)
                                 :type (type-address))
                                (make-funparam
                                 :name (identifier "amount")
                                 :sort (var/const-sort-public)
                                 :type (type-unsigned (bitsize-64))))
                  :output nil
                  :body (list (make-statement-decrement
                               :mapping (identifier "account")
                               :index (make-expression-var/const
                                       :name (identifier "sender"))
                               :amount (make-expression-var/const
                                        :name (identifier "amount")) )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of struct declarations.

(test-parse-abs parse-struct-declaration
                abs-struct-declaration
                "struct token {owner: address, gates: u64, amount: u64,}"
                (make-structdecl
                 :name (identifier "token")
                 :components
                 (list (make-compdecl :name (identifier "owner")
                                      :type (type-address))
                       (make-compdecl :name (identifier "gates")
                                      :type (type-unsigned (bitsize-64)))
                       (make-compdecl :name (identifier "amount")
                                      :type (type-unsigned (bitsize-64))))
                 :recordp nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of record declarations.

(test-parse-abs parse-record-declaration
                abs-record-declaration
                "record token {owner: address, gates: u64, amount: u64,}"
                (make-structdecl
                 :name (identifier "token")
                 :components
                 (list (make-compdecl :name (identifier "owner")
                                      :type (type-address))
                       (make-compdecl :name (identifier "gates")
                                      :type (type-unsigned (bitsize-64)))
                       (make-compdecl :name (identifier "amount")
                                      :type (type-unsigned (bitsize-64))))
                 :recordp t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of mapping declarations.

(test-parse-abs parse-mapping-declaration
                abs-mapping-declaration
                "mapping known_addrs: address => bool;"
                (make-mappingdecl
                 :name (identifier "known_addrs")
                 :domain-type (type-address)
                 :range-type (type-bool)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of program items

(test-parse-abs parse-program-item
                abs-program-item
                "function f() -> field {}"
                (topdecl-function
                 (make-fundecl
                  :sort (fun-sort-standard)
                  :name (identifier "f")
                  :inputs nil
                  :output (type-field)
                  :body nil)))

(test-parse-abs parse-program-item
                abs-program-item
                "function f(x: u8) -> group {}"
                (topdecl-function
                 (make-fundecl
                  :sort (fun-sort-standard)
                  :name (identifier "f")
                  :inputs (list (make-funparam
                                 :name (identifier "x")
                                 :sort (var/const-sort-private)
                                 :type (type-unsigned (bitsize-8))))
                  :output (type-group)
                  :body nil)))

(test-parse-abs parse-program-item
                abs-program-item
                "function f(x: u8, public y: u8) -> u8 { return x + y; }"
                (topdecl-function
                 (make-fundecl
                  :sort (fun-sort-standard)
                  :name (identifier "f")
                  :inputs (list (make-funparam
                                 :name (identifier "x")
                                 :sort (var/const-sort-private)
                                 :type (type-unsigned (bitsize-8)))
                                (make-funparam
                                 :name (identifier "y")
                                 :sort (var/const-sort-public)
                                 :type (type-unsigned (bitsize-8))))
                  :output (type-unsigned (bitsize-8))
                  :body (list
                         (statement-return
                          (make-expression-binary
                           :op (binop-add)
                           :arg1 (expression-var/const (identifier "x"))
                           :arg2 (expression-var/const (identifier "y"))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parse-abs parse-program-item
                abs-program-item
                "struct token {owner: address, gates: u64, amount: u64,}"
                (topdecl-struct
                 (make-structdecl
                  :name (identifier "token")
                  :components (list
                               (make-compdecl
                                :name (identifier "owner")
                                :type (type-address))
                               (make-compdecl
                                :name (identifier "gates")
                                :type (type-unsigned (bitsize-64)))
                               (make-compdecl
                                :name (identifier "amount")
                                :type (type-unsigned (bitsize-64))))
                  :recordp nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parse-abs parse-program-item
                abs-program-item
                "record token {owner: address, gates: u64, amount: u64,}"
                (topdecl-struct
                 (make-structdecl
                  :name (identifier "token")
                  :components (list (make-compdecl :name (identifier "owner")
                                                   :type (type-address))
                                    (make-compdecl :name (identifier "gates")
                                                   :type (type-unsigned (bitsize-64)))
                                    (make-compdecl :name (identifier "amount")
                                                   :type (type-unsigned (bitsize-64))))
                  :recordp t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parse-abs parse-program-item
                abs-program-item
                "mapping known_addrs: address => bool;"
                (topdecl-mapping
                 (make-mappingdecl
                  :name (identifier "known_addrs")
                  :domain-type (type-address)
                  :range-type (type-bool))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of program declarations.

(test-parse-abs parse-program-declaration
                abs-program-declaration
                "program x.y{}"
                (make-programdecl :id (make-programid :name (identifier "x")
                                                      :network (identifier "y"))
                                  :items nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of import declarations

(test-parse-abs parse-import-declaration
                abs-import-declaration
                "import board.leo;"
                (importdecl (make-programid :name (identifier "board")
                                            :network (identifier "leo"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test abstraction of files.

(test-parse-abs-file
 "program x.y{}"
 (make-file :imports nil
            :program (make-programdecl
                      :id (make-programid :name (identifier "x")
                                          :network (identifier "y"))
                      :items nil)))

(test-parse-abs-file
 "import board.leo;
program x.y{}"
 (make-file :imports (list (make-importdecl
                            :program (make-programid
                                      :name (identifier "board")
                                      :network (identifier "leo"))))
            :program (make-programdecl
                      :id (make-programid :name (identifier "x")
                                          :network (identifier "y"))
                      :items nil)))

(test-parse-abs-file
 "program two.aleo {
  function f() -> field {}

  function f(x: u8) -> group {
  }

  function f(x: u8, public y: u8) -> u8 {
      return x + y;
  }
}"
 (make-file
  :imports nil
  :program (make-programdecl
            :id (make-programid :name (identifier "two")
                                :network (identifier "aleo"))
            :items
            (list
             (topdecl-function
              (make-fundecl
               :sort (fun-sort-standard)
               :name (identifier "f")
               :inputs nil
               :output (type-field)
               :body nil))
             (topdecl-function
              (make-fundecl
               :sort (fun-sort-standard)
               :name (identifier "f")
               :inputs (list (make-funparam
                              :name (identifier "x")
                              :sort (var/const-sort-private)
                              :type (type-unsigned (bitsize-8))))
               :output (type-group)
               :body nil))
             (topdecl-function
              (make-fundecl
               :sort (fun-sort-standard)
               :name (identifier "f")
               :inputs (list (make-funparam
                              :name (identifier "x")
                              :sort (var/const-sort-private)
                              :type (type-unsigned (bitsize-8)))
                             (make-funparam
                              :name (identifier "y")
                              :sort (var/const-sort-public)
                              :type (type-unsigned (bitsize-8))))
               :output (type-unsigned (bitsize-8))
               :body (list
                      (statement-return
                       (make-expression-binary
                        :op (binop-add)
                        :arg1 (expression-var/const (identifier "x"))
                        :arg2 (expression-var/const (identifier "y")))))))))))
