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

(include-book "../testing/lexing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test lexing of whitespace.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Spaces.

(test-lex-whitespace '(32) nil)

(test-lex-whitespace '(32) '(1 2 3))

(test-lex-whitespace " " nil)

(test-lex-whitespace " " "abc")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Horizontal tabs.

(test-lex-whitespace '(9) nil)

(test-lex-whitespace '(9) '(1 2 3))

(test-lex-whitespace '(9) "more")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Newlines.

(test-lex-whitespace '(10) nil)

(test-lex-whitespace '(10) '(10))

(test-lex-whitespace '(10) '(13))

(test-lex-whitespace '(10) '(100))

(test-lex-whitespace '(13) nil)

(test-lex-whitespace '(13) '(13))

(test-lex-whitespace '(13) '(150))

(test-lex-whitespace '(13 10) nil)

(test-lex-whitespace '(13 10) '(1 2 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test lexing of comments.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Line comments.

(test-lex-comment "// line-comment" ; comment at end of file
                  "")

(test-lex-comment "// line-comment"
                  (append '(10) (string=>nats "more text")))

(test-lex-comment "// line-comment"
                  (append '(13) (string=>nats "more text")))

(test-lex-comment "// line-comment"
                  (append '(13 10) (string=>nats "more text")))

(test-lex-comment "// line-comment"
                  (append '(10) (string=>nats "// maybe another line comment")))

(test-lex-comment "// line-comment⭿"
                  (append '(10) (string=>nats "more text")))

; U+B is no longer supported (not in safe-ascii lexical rule)
#||
(test-lex-comment "// line-comment"  ; "LINE TABULATION" (U+B) at end
                  "")
||#

(test-lex-comment "// line-comment⭿"  ; "vertical tab key" (U+2B7F) at end
                  "")

(test-lex-comment "////////////"
                  (append '(10) (string=>nats "more text")))

(test-lex-comment "// and /* block */"
                  (append '(10) (string=>nats "more text")))

(test-lex-comment "// and // more //"
                  (append '(10) (string=>nats "more text")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Block comments.

(test-lex-comment "/* */"
                  "more text")

(test-lex-comment "/**/"
                  "more text")

(test-lex-comment "/* abc */"
                  "more text")

(test-lex-comment "/* 壮 */"  ; zhuàng
                  "more text")

(test-lex-comment "/** abc */"
                  "more text")

(test-lex-comment "/***** abc de f . */"
                  "more text")

(test-lex-comment (append (string=>nats "/* multi-line") '(10)
                          (string=>nats "   block") '(13)
                          (string=>nats "   comment */"))
                  "more text")

(test-lex-comment "/* no /* nesting */" " allowed /*")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Texting lexing of tokens.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifiers.

(test-lex lex-identifier/keyword/boolean/address
          "identifier"
          "x"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "identifier"
          "a_valid_identifier"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "identifier"
          "abc123"
          " more")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Keywords.

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "address"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "bool"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "console"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "const"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "constant"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "else"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "field"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "for"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "function"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "group"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "i8"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "i16"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "i32"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "i64"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "i128"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "if"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "in"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "let"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "public"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "record"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "mapping"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "return"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "scalar"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "string"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "struct"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "transition"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "u8"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "u16"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "u32"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "u64"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "keyword"
          "u128"
          " more")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Boolean literals.

(test-lex lex-identifier/keyword/boolean/address
          "boolean-literal"
          "true"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "boolean-literal"
          "false"
          " more")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Addresses.

(test-lex lex-identifier/keyword/boolean/address
          "address-literal"
          "aleo1y90yg3yzs4g7q25f9nn8khuu00m8ysynxmcw8aca2d0phdx8dgpq4vw348"
          " more")

(test-lex lex-identifier/keyword/boolean/address
          "address-literal"
          "aleo1oooooooooooooooooooooooooooooooooooooooooooooooooooooooooo"
          " more")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Annotations.

(test-lex lex-annotation
          "annotation"
          "@program"
          " more")

(test-lex lex-annotation
          "annotation"
          "@foo"
          " more")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Symbols.

(test-lex lex-symbol
          "symbol"
          ")group"
          " more")

(test-lex lex-symbol
          "symbol"
          ")group"
          "more")

(test-lex lex-symbol
          "symbol"
          "("
          "more")

(test-lex lex-symbol
          "symbol"
          ")"
          "more")

(test-lex lex-symbol
          "symbol"
          "{"
          "more")

(test-lex lex-symbol
          "symbol"
          "}"
          "more")

(test-lex lex-symbol
          "symbol"
          "&&"
          "more")

(test-lex lex-symbol
          "symbol"
          "||"
          "more")

(test-lex lex-symbol
          "symbol"
          "&"
          "more")

(test-lex lex-symbol
          "symbol"
          "|"
          "more")

(test-lex lex-symbol
          "symbol"
          "^"
          "more")

(test-lex lex-symbol
          "symbol"
          "_"
          "more")

(test-lex lex-symbol
          "symbol"
          "?"
          "more")

(test-lex lex-symbol
          "symbol"
          ","
          "more")

(test-lex lex-symbol
          "symbol"
          ";"
          "more")

(test-lex lex-symbol
          "symbol"
          ".."
          "more")

(test-lex lex-symbol
          "symbol"
          "."
          "more")

(test-lex lex-symbol
          "symbol"
          ":"
          "more")

(test-lex lex-symbol
          "symbol"
          "::"
          "more")

(test-lex lex-symbol
          "symbol"
          "!="
          "more")

(test-lex lex-symbol
          "symbol"
          "!"
          "more")

(test-lex lex-symbol
          "symbol"
          "<<"
          "more")

(test-lex lex-symbol
          "symbol"
          ">>"
          "more")

(test-lex lex-symbol
          "symbol"
          "=="
          "more")

(test-lex lex-symbol
          "symbol"
          "="
          "more")

(test-lex lex-symbol
          "symbol"
          "<="
          "more")

(test-lex lex-symbol
          "symbol"
          "<"
          "more")

(test-lex lex-symbol
          "symbol"
          ">="
          "more")

(test-lex lex-symbol
          "symbol"
          ">"
          "more")

(test-lex lex-symbol
          "symbol"
          "+"
          "more")

(test-lex lex-symbol
          "symbol"
          "/"
          "more")

(test-lex lex-symbol
          "symbol"
          "%"
          "more")

(test-lex lex-symbol
          "symbol"
          "->"
          "more")

(test-lex lex-symbol
          "symbol"
          "=>"
          "more")

(test-lex lex-symbol
          "symbol"
          "=>"
          ">more")

(test-lex lex-symbol
          "symbol"
          "-"
          "more")

(test-lex lex-symbol
          "symbol"
          "**"
          "more")

(test-lex lex-symbol
          "symbol"
          "*"
          "more")

(test-lex lex-symbol
          "symbol"
          "+="
          "more")

(test-lex lex-symbol
          "symbol"
          "-="
          "more")

(test-lex lex-symbol
          "symbol"
          "*="
          "more")

(test-lex lex-symbol
          "symbol"
          "/="
          "more")

(test-lex lex-symbol
          "symbol"
          "%="
          "more")

(test-lex lex-symbol
          "symbol"
          "**="
          "more")

(test-lex lex-symbol
          "symbol"
          "<<="
          "more")

(test-lex lex-symbol
          "symbol"
          ">>="
          "more")

(test-lex lex-symbol
          "symbol"
          "&="
          "more")

(test-lex lex-symbol
          "symbol"
          "|="
          "more")

(test-lex lex-symbol
          "symbol"
          "^="
          "more")

(test-lex lex-symbol
          "symbol"
          "&&="
          "more")

(test-lex lex-symbol
          "symbol"
          "||="
          "more")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; unsigned, signed, field, and group literals.

(test-lex lex-numeric-literal
          "numeric-literal"
          "77u8"
          " ")

(test-lex lex-numeric-literal
          "numeric-literal"
          "77u16"
          " ")

(test-lex lex-numeric-literal
          "numeric-literal"
          "77u32"
          " ")

(test-lex lex-numeric-literal
          "numeric-literal"
          "77u64"
          " ")

(test-lex lex-numeric-literal
          "numeric-literal"
          "77u128"
          " ")

(test-lex lex-numeric-literal
          "numeric-literal"
          "77i8"
          " ")

(test-lex lex-numeric-literal
          "numeric-literal"
          "77i16"
          " ")

(test-lex lex-numeric-literal
          "numeric-literal"
          "77i32"
          " ")

(test-lex lex-numeric-literal
          "numeric-literal"
          "77i64"
          " ")

(test-lex lex-numeric-literal
          "numeric-literal"
          "77i128"
          " ")

(test-lex lex-numeric-literal
          "numeric-literal"
          "8350387580975field"
          " ")

(test-lex lex-numeric-literal
          "numeric-literal"
          "8350387580975group"
          " ")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; String literals.

(test-lex lex-string-literal
          "string-literal"
          "\"abc\""
          " ")

(test-lex lex-string-literal
          "string-literal"
          "\"\\0ABC\\x20123\\u{CafE}\""
          " ")

(test-lex lex-string-literal
          "string-literal"
          "\"אֶу́🤷🏿‍♀️\""  ; examples in developer.aleo.org
          " ")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tokens

(test-lex-token
 "atomic-literal"
 "\"abc\""
 " ")

(test-lex-token
 "atomic-literal"
 "7777u32"
 " ")

(test-lex-token
 "atomic-literal"
 "121i8"
 " ")

(test-lex-token
 "atomic-literal"
 "1field"
 " ")

(test-lex-token
 "atomic-literal"
 "3group"
 " ")

(test-lex-token
 "numeral"
 "33"
 " ")

(test-lex-token
 "identifier"
 "my_variable_name"
 " ")

(test-lex-token
 "keyword"
 "function"
 " ")

(test-lex-token
 "atomic-literal"
 "true"
 " ")

(test-lex-token
 "atomic-literal"
 "aleo1y90yg3yzs4g7q25f9nn8khuu00m8ysynxmcw8aca2d0phdx8dgpq4vw348"
 " ")

(test-lex-token
 "annotation"
 "@program"
 " more")

(test-lex-token
 "annotation"
 "@foo"
 " more")

(test-lex-token
 "symbol"
 ">"
 " ")

(test-lex-token
 "symbol"
 ">>"
 " ")

(test-lex-token
 "symbol"
 "&"
 " ")

(test-lex-token
 "symbol"
 "&&"
 " ")

(test-lex-token
 "symbol"
 "|"
 " ")

(test-lex-token
 "symbol"
 "||"
 " ")

(test-lex-token
 "symbol"
 "-"
 "")

(test-lex-token
 "symbol"
 "-"
 " ")

(test-lex-token
 "symbol"
 "-"
 "x")

(test-lex-token
 "symbol"
 "%"
 "x")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lexemes

(test-lex lex-lexeme "lexeme"
          " " " ")

(test-lex lex-lexeme "lexeme"
          "//a" "")

(test-lex lex-lexeme "lexeme"
          "//a" '(10))

(test-lex lex-lexeme "lexeme"
          "//⭿" "")

(test-lex lex-lexeme "lexeme"
          "//⭿" '(10))

(test-lex lex-lexeme "lexeme"
          "/" " ")

(test-lex lex-lexeme "lexeme"
          "@f" " ")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lexemize tests

(test-lexemize-string "壮" :fail)
(test-lexemize-string "\"x" :fail)
(test-lexemize-string "\\xFF" :fail)

(test-lexemize-string " \"壮\" \"壮\"" :succeed)
(test-lexemize-string " \"壮\"
\"壮\"" :succeed)

;; symbols and whitespace
(test-lexemize-string "! && || & | ^ == != < <= > >= << >> + - * / ** = ( ) { } , . .. ; :
  ? -> _ )group += -= *= /= %= **= <<= >>= &= |= ^= &&= ||= " :succeed)

;; keywords and whitespace
(test-lexemize-string "address bool console const constant else field for function
 group i8 i16 i32 i64 i128 if in let public return u8 u16 u32 u64 u128" :succeed)

;; identifiers and comments
(test-lexemize-string "i8x//壮
u128x/**/" :succeed)

;; affine group literal (the only place "numeral" is its own token)
;; many of these don't make sense but they should lex
(test-lexemize-string "(1,2)group" :succeed)
(test-lexemize-string "(+,-)group" :succeed)
(test-lexemize-string "(-,+)group" :succeed)
(test-lexemize-string "(_,_)group" :succeed)
(test-lexemize-string "(-1,-2)group" :succeed)

;; No whitespace allowed after "@" in annotation
(test-lexemize-string "@f" :succeed)
(test-lexemize-string "@ f" :fail)
;; and bare atsign isn't a lexeme
(test-lexemize-string "@" :fail)
