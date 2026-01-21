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

(include-book "../testing/parsing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of tokens.

(test-parse-token " \"abc\"" " "
                  "atomic-literal")

(test-parse-token "/*a*/121" " "
                  "numeral")

(test-parse-token "/*a*/121" ","
                  "numeral")

(test-parse-token "  7777u32" " "
                  "atomic-literal")

(test-parse-token "  7777u32" "+"
                  "atomic-literal")

(test-parse-token " 3group" " "
                  "atomic-literal")

(test-parse-token "  my_variable_name" " "
                  "identifier")

(test-parse-token " function" " "
                  "keyword")

(test-parse-token "/**/true" " "
                  "atomic-literal")

(test-parse-token
 " aleo1y90yg3yzs4g7q25f9nn8khuu00m8ysynxmcw8aca2d0phdx8dgpq4vw348" " "
 "atomic-literal")

(test-parse-token " @program" " "
                  "annotation")

(test-parse-token " @foo" " "
                  "annotation")

(test-parse-token " >" " "
                  "symbol")

(test-parse-token " >" "ab"
                  "symbol")

(test-parse-token " >>" " "
                  "symbol")

(test-parse-token " >>" "ab"
                  "symbol")

;; there is no ">>>" symbol
(test-parse-token " >>" ">"
                  "symbol")

(test-parse-token " :" " "
                  "symbol")

(test-parse-token " :" "ab"
                  "symbol")

(test-parse-token " ::" " "
                  "symbol")

(test-parse-token " ::" "ab"
                  "symbol")

;; there is no ">>>" symbol
(test-parse-token " ::" ":"
                  "symbol")

;; there is no "%%" symbol
(test-parse-token " %" "%"
                  "symbol")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of the same tokens using a simpler interface.
; Makes sure both interfaces work.

(test-parse-token-basic "\"abc\"")

(test-parse-token-basic " \"abc\"")

(test-parse-token-basic "121")

(test-parse-token-basic "/*a*/121")

(test-parse-token-basic "7777u32")

(test-parse-token-basic "  7777u32")

(test-parse-token-basic " 3group")

(test-parse-token-basic "  my_variable_name")

(test-parse-token-basic "function")
(test-parse-token-basic " function")
(test-parse-token-basic "function ")

(test-parse-token-basic "true")

(test-parse-token-basic "/**/true")

(test-parse-token-basic "true/**/")

(test-parse-token-basic
 " aleo1y90yg3yzs4g7q25f9nn8khuu00m8ysynxmcw8aca2d0phdx8dgpq4vw348")

(test-parse-token-basic "@program")
(test-parse-token-basic " @program")
(test-parse-token-basic "@foo")

(test-parse-token-basic ">")

(test-parse-token-basic " >")

(test-parse-token-basic ">>")

(test-parse-token-basic " >>")

(test-parse-token-basic ":")

(test-parse-token-basic " :")

(test-parse-token-basic "::")

(test-parse-token-basic " ::")

(test-parse-token-basic " %")

(test-parse-token-basic "\"\\u{10FFFF}\"")

;; the check on the value is during static semantics time,
;; so up to 6 of any hex digits can be parsed
(test-parse-token-basic "\"\\u{FFFFFF}\"")
(test-parse-token-basic "\"\\u{000000}\"")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing fails on invalid tokens

; characters have been taken out, so parse-token should fail on them
(test-parse-token-fail "'a'")

(test-parse-token-fail "'a")

(test-parse-token-fail "'a '")

(test-parse-token-fail "\"abc")

;; non-utf8, but done in a way that makes this source file remain utf-8
(test-parse-token-fail (string-append (string-append "\"abc" (nats=>string '(255)))
                                      "\""))

(test-parse-token-fail "/* ...")

(test-parse-token-fail "// ...")

;; The token is OK, but the string won't lex
(test-parse-token-fail "abc/*")

;; 7 digits
(test-parse-token-fail "\"\\u{FFFFFFF}\"")
(test-parse-token-fail "\"\\u{0000000}\"")
(test-parse-token-fail "\"\\u{0000001}\"")

(test-parse-token-fail "@")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of keywords.

(test-parse-keyword "for"
                    "for")

(test-parse-keyword "for"
                    "/* ... */ for ")

(test-parse-keyword "function"
                    "function ")

(test-parse-keyword "function"
                    " function")

(test-parse-keyword "function"
                    " function ")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of symbols.

(test-parse-symbol "<="
                   "<=")

(test-parse-symbol "<<"
                   "<<")

;; compound assignment symbols
(test-parse-symbol "+="
                   "+=")

(test-parse-symbol "-="
                   "-=")

(test-parse-symbol "*="
                   "*=")

(test-parse-symbol "/="
                   "/=")

(test-parse-symbol "%="
                   "%=")

(test-parse-symbol "**="
                   "**=")

(test-parse-symbol "<<="
                   "<<=")

(test-parse-symbol ">>="
                   ">>=")

(test-parse-symbol "&="
                   "&=")

(test-parse-symbol "|="
                   "|=")

(test-parse-symbol "^="
                   "^=")

(test-parse-symbol "&&="
                   "&&=")

(test-parse-symbol "||="
                   "||=")

;; after a comment or whitespace
(test-parse-symbol "*"
                   "/* ... */*")

(test-parse-symbol "/"
                   "/* ... *//")

(test-parse-symbol "+"
                   " + ")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of identifiers.

(test-parse parse-identifier
            "identifier"
            "var2")

(test-parse parse-identifier
            "identifier"
            "var2 ")

(test-parse parse-identifier
            "identifier"
            "var2")

(test-parse parse-identifier
            "identifier"
            " /* ... */ var22")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of atomic literals.

(test-parse parse-atomic-literal
            "atomic-literal"
            "\"string\"")

(test-parse parse-atomic-literal
            "atomic-literal"
            "aleo1y90yg3yzs4g7q25f9nn8khuu00m8ysynxmcw8aca2d0phdx8dgpq4vw348")

(test-parse parse-atomic-literal
            "atomic-literal"
            "32768u32")

(test-parse parse-atomic-literal
            "atomic-literal"
            "32768i32")

(test-parse parse-atomic-literal
            "atomic-literal"
            "32768u64/*type*/")

(test-parse parse-atomic-literal
            "atomic-literal"
            "1field")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of numerals.

(test-parse parse-numeral
            "numeral"
            "88")

(test-parse parse-numeral
            "numeral"
            "0")

(test-parse parse-numeral
            "numeral"
            "332384239203202")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of program IDs.

(test-parse parse-program-id
            "program-id"
            "abc.def")

(test-parse parse-program-id
            "program-id"
            "vote.aleo")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of locators.

(test-parse parse-locator
            "locator"
            "abc.def/ghi")

(test-parse parse-locator
            "locator"
            "vote.aleo/nandemo")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of annotations.

(test-parse parse-annotation
            "annotation"
            "@program")

(test-parse parse-annotation
            "annotation"
            " @foo ")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of primitive types.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "u8")

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "u16")

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "u32")

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "u64")

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "u128")

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "i8")

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "i16")

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "i32")

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "i64")

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "i128")

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "field")

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "group")

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "bool")

(test-parse parse-named-primitive-type
            "named-primitive-type"
            "address")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Named types.

(test-parse parse-named-type
            "named-type"
            "i128")

(test-parse parse-named-type
            "named-type"
            "abc")

(test-parse parse-named-type
            "named-type"
            "abc.record")

(test-parse parse-named-type
            "named-type"
            "abc.def/ghi")

(test-parse parse-named-type
            "named-type"
            "abc.def/ghi.record")

(test-parse parse-named-type
            "named-type"
            "vote.aleo/nandemo")

(test-parse parse-named-type
            "named-type"
            "vote.aleo/nandemo.record")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unit type.

(test-parse parse-unit-type
            "unit-type"
            "()")

(test-parse parse-unit-type
            "unit-type"
            "( )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tuple types.

(test-parse parse-tuple-type
            "tuple-type"
            "(u8,i8)")

(test-parse parse-tuple-type
            "tuple-type"
            "(u8,i8,)")

(test-parse parse-tuple-type
            "tuple-type"
            "((abc,bool),(field,group))")

(test-parse parse-tuple-type
            "tuple-type"
            "((abc,bool,),(field,group))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Types.

(test-parse parse-type
            "type"
            "u8")

(test-parse parse-type
            "type"
            "u16")

(test-parse parse-type
            "type"
            "u32")

(test-parse parse-type
            "type"
            "u64")

(test-parse parse-type
            "type"
            "u128")

(test-parse parse-type
            "type"
            "i8")

(test-parse parse-type
            "type"
            "i16")

(test-parse parse-type
            "type"
            "i32")

(test-parse parse-type
            "type"
            "i64")

(test-parse parse-type
            "type"
            "i128")

(test-parse parse-type
            "type"
            "field")

(test-parse parse-type
            "type"
            "group")

(test-parse parse-type
            "type"
            "bool")

(test-parse parse-type
            "type"
            "address")

(test-parse parse-type
            "type"
            "()") ; parses as the unit-type wrapped with "type"

(test-parse parse-type
            "type"
            "((abc,bool,),(field,group,),)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of group coordinates.

(test-parse parse-group-coordinate
            "group-coordinate"
            "+")

(test-parse parse-group-coordinate
            "group-coordinate"
            "-")

(test-parse parse-group-coordinate
            "group-coordinate"
            "_")

(test-parse parse-group-coordinate
            "group-coordinate"
            "1800")

(test-parse parse-group-coordinate
            "group-coordinate"
            "-1800")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of affine group literals.

(test-parse parse-affine-group-literal
            "affine-group-literal"
            "(0, 0)group")

(test-parse parse-affine-group-literal
            "affine-group-literal"
            "( +, -38438 )group")

(test-parse parse-affine-group-literal
            "affine-group-literal"
            "(55, -)group")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of literals.

(test-parse parse-literal
            "literal"
            "838392i128")

(test-parse parse-literal
            "literal"
            "000u8")

(test-parse parse-literal
            "literal"
            "0i8")

(test-parse parse-literal
            "literal"
            "007i8")

(test-parse parse-literal
            "literal"
            "10field")

(test-parse parse-literal
            "literal"
            "0group")

(test-parse parse-literal
            "literal"
            "3u8")

(test-parse parse-literal
            "literal"
            "\"\\u{0001}\"")

(test-parse parse-literal
            "literal"
            "\"abc\\ndef\"")

(test-parse parse-literal
            "literal"
            "aleo1y90yg3yzs4g7q25f9nn8khuu00m8ysynxmcw8aca2d0phdx8dgpq4vw348")

(test-parse parse-literal
            "literal"
            "true")

(test-parse parse-literal
            "literal"
            "false")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of expressions.

(test-parse parse-expression
            "expression"
            "a")

(test-parse parse-expression
            "expression"
            "1u8")

(test-parse parse-expression
            "expression"
            "-1u8")

(test-parse parse-expression
            "expression"
            "a ? b : c")

(test-parse parse-expression
            "expression"
            "a ? b : c ? d : f")

(test-parse parse-expression
            "expression"
            "a ? b ? c : d : e")

(test-parse parse-expression
            "expression"
            "a || b")

(test-parse parse-expression
            "expression"
            "a || b || c")

(test-parse parse-expression
            "expression"
            "a && b")

(test-parse parse-expression
            "expression"
            "a && b && c")

(test-parse parse-expression
            "expression"
            "a == b")

(test-parse parse-expression
            "expression"
            "a != b")

(test-parse parse-expression
            "expression"
            "a < b")

(test-parse parse-expression
            "expression"
            "a > b")

(test-parse parse-expression
            "expression"
            "a <= b")

(test-parse parse-expression
            "expression"
            "a >= b")

(test-parse parse-expression
            "expression"
            "a | b")

(test-parse parse-expression
            "expression"
            "a | b | c")

(test-parse parse-expression
            "expression"
            "a & b")

(test-parse parse-expression
            "expression"
            "a & b & c")

(test-parse parse-expression
            "expression"
            "a ^ b")

(test-parse parse-expression
            "expression"
            "a ^ b ^ c")

(test-parse parse-expression
            "expression"
            "a << b")

(test-parse parse-expression
            "expression"
            "a << b << c")

(test-parse parse-expression
            "expression"
            "a >> b")

(test-parse parse-expression
            "expression"
            "a >> b >> c")

(test-parse parse-expression
            "expression"
            "a << b >> c")

(test-parse parse-expression
            "expression"
            "a >> b << c")

(test-parse parse-expression
            "expression"
            "a + b")

(test-parse parse-expression
            "expression"
            "a + b + c")

(test-parse parse-expression
            "expression"
            "a - b")

(test-parse parse-expression
            "expression"
            "a - b - c")

(test-parse parse-expression
            "expression"
            "a * b")

(test-parse parse-expression
            "expression"
            "a * b * c")

(test-parse parse-expression
            "expression"
            "a / b")

(test-parse parse-expression
            "expression"
            "a / b / c")

(test-parse parse-expression
            "expression"
            "a % b % c")

(test-parse parse-expression
            "expression"
            "a ** b")

(test-parse parse-expression
            "expression"
            "a ** b ** c")

(test-parse parse-expression
            "expression"
            "!a")

(test-parse parse-expression
            "expression"
            "-a")

(test-parse parse-expression
            "expression"
            "1556u16")

(test-parse parse-expression
            "expression"
            "1556i16")

(test-parse parse-expression
            "expression"
            "-1556i16")

(test-parse parse-expression
            "expression"
            "7u8")

(test-parse parse-expression
            "expression"
            "-7i16")

(test-parse parse-expression
            "expression"
            "1field")

(test-parse parse-expression
            "expression"
            "0field")

(test-parse parse-expression
            "expression"
            "\"\\x61\"")

(test-parse parse-expression
            "expression"
            "\"\\x61___abc\"")

(test-parse parse-expression
            "expression"
            "true")

(test-parse parse-expression
            "expression"
            "false")

(test-parse parse-expression
            "expression"
            "aleo1y90yg3yzs4g7q25f9nn8khuu00m8ysynxmcw8aca2d0phdx8dgpq4vw348")

(test-parse parse-expression
            "expression"
            "x")

(test-parse parse-expression
            "expression"
            "a_variable_NAME_with_123digits")

(test-parse parse-expression
            "expression"
            "(a)")

(test-parse parse-expression
            "expression"
            "f()")

(test-parse parse-expression
            "expression"
            "f(a)")

(test-parse parse-expression
            "expression"
            "f(a,)")

(test-parse parse-expression
            "expression"
            "f(a,b)")

(test-parse parse-expression
            "expression"
            "f(a,b,)")

(test-parse parse-expression
            "expression"
            "f(a, b)")

(test-parse parse-expression
            "expression"
            "f(a, b,)")

(test-parse parse-expression
            "expression"
            "f(a, b, c)")

(test-parse parse-expression
            "expression"
            "f(a, b, c,)")

;; external calls
(test-parse parse-expression
            "expression"
            "vote.aleo/nandemo()")
(test-parse parse-expression
            "expression"
            "vote.aleo/nandemo(a)")
(test-parse parse-expression
            "expression"
            "vote.aleo/nandemo(a,)")

(test-parse parse-expression
            "expression"
            "a + b * c")

(test-parse parse-expression
            "expression"
            "a * b + c")

(test-parse parse-expression
            "expression"
            "a * (b + c)")

;; struct component
(test-parse parse-expression
            "expression"
            "c.c")

;; tuple component
(test-parse parse-expression
            "expression"
            "c.42")

;; unary operator call
(test-parse parse-expression
            "expression"
            "g.double()")

;; binary operator call
(test-parse parse-expression
            "expression"
            "g.add(g1)")

;; combination
(test-parse parse-expression
            "expression"
            "(a+b).add(g1).double().val")

(test-parse parse-expression
            "expression"
            "(a+b).add(g1).double().0")

;; associated constant, resulting in a primitive type "u8"
(test-parse parse-expression
            "expression"
            "u8::v")

;; associated constant, resulting in a named type identifier "U8"
(test-parse parse-expression
            "expression"
            "U8::v")

;; static function call
(test-parse parse-expression
            "expression"
            "PED64::commit(true)")

;; static function call with primitive type (this doesn't mean anything)
(test-parse parse-expression
            "expression"
            "u8::commit()")

;; static function call using a locator
(test-parse parse-expression
            "expression"
            "vote.aleo/nandemo::foo()")

;; struct expressions
(test-parse parse-expression
            "expression"
            "Foo { x: x }")

(test-parse parse-expression
            "expression"
            "Foo { x }")

(test-parse parse-expression
            "expression"
            "Foo{x:x,}")

(test-parse parse-expression
            "expression"
            "Foo{x,}")

(test-parse parse-expression
            "expression"
            "Foo{x:x,y:y}")

(test-parse parse-expression
            "expression"
            "Foo{x,y}")

(test-parse parse-expression
            "expression"
            "Foo{x:x,y:y, }")

(test-parse parse-expression
            "expression"
            "Foo{x,y, }")

;; unit expressions
(test-parse parse-unit-expression
            "unit-expression"
            "()")
(test-parse parse-expression
            "expression"
            "()")

;; tuple expressions
(test-parse parse-primary-expression
            "primary-expression"
            "(abc)") ; not a tuple, just parens around an identifier

(test-parse parse-expression
            "expression"
            "(a,b)")
(test-parse parse-tuple-expression
            "tuple-expression"
            "(a,b)")

(test-parse parse-expression
            "expression"
            "(a,b,)")
(test-parse parse-tuple-expression
            "tuple-expression"
            "(a,b,)")

;; Make sure external free function calls are chosen over struct component
;; divisions by internal free function calls.

(test-parse parse-free-function-call
            "free-function-call"
            "vote.aleo/nandemo()")

(test-parse parse-expression
            "expression"
            "(vote.aleo)/nandemo()")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of expressions, using another interface.
; Note, the purpose of this section is also to test that the
; expression-parses-same-fringe? interface function works the same as
; the test-parse testing function used for the expressions above.

(test-parse-expression
 "a")

(test-parse-expression
 "1u8")

(test-parse-expression
 "-1u8")

(test-parse-expression
 "a ? b : c")

(test-parse-expression
 "a ? b : c ? d : f")

(test-parse-expression
 "a ? b ? c : d : e")

(test-parse-expression
 "a || b")

(test-parse-expression
 "a || b || c")

(test-parse-expression
 "a && b")

(test-parse-expression
 "a && b && c")

(test-parse-expression
 "a == b")

(test-parse-expression
 "a != b")

(test-parse-expression
 "a < b")

(test-parse-expression
 "a > b")

(test-parse-expression
 "a <= b")

(test-parse-expression
 "a >= b")

(test-parse-expression
 "a | b")

(test-parse-expression
 "a | b | c")

(test-parse-expression
 "a & b")

(test-parse-expression
 "a & b & c")

(test-parse-expression
 "a ^ b")

(test-parse-expression
 "a ^ b ^ c")

(test-parse-expression
 "a << b")

(test-parse-expression
 "a << b << c")

(test-parse-expression
 "a >> b")

(test-parse-expression
 "a >> b >> c")

(test-parse-expression
 "a << b >> c")

(test-parse-expression
 "a >> b << c")

(test-parse-expression
 "a + b")

(test-parse-expression
 "a + b + c")

(test-parse-expression
 "a - b")

(test-parse-expression
 "a - b - c")

(test-parse-expression
 "a * b")

(test-parse-expression
 "a * b * c")

(test-parse-expression
 "a / b")

(test-parse-expression
 "a / b / c")

(test-parse-expression
 "a % b % c")

(test-parse-expression
 "a ** b")

(test-parse-expression
 "a ** b ** c")

(test-parse-expression
 "!a")

(test-parse-expression
 "-a")

(test-parse-expression
 "1556u16")

(test-parse-expression
 "1556i16")

(test-parse-expression
 "-1556i16")

(test-parse-expression
 "7u8")

(test-parse-expression
 "-7i16")

(test-parse-expression
 "1field")

(test-parse-expression
 "0field")

(test-parse-expression
 "\"\\x61\"")

(test-parse-expression
 "\"\\x61___abc\"")

(test-parse-expression
 "true")

(test-parse-expression
 "false")

(test-parse-expression
 "aleo1y90yg3yzs4g7q25f9nn8khuu00m8ysynxmcw8aca2d0phdx8dgpq4vw348")

(test-parse-expression
 "x")

(test-parse-expression
 "a_variable_NAME_with_123digits")

(test-parse-expression
 "(a)")

(test-parse-expression
 "f()")

(test-parse-expression
 "f(a)")

(test-parse-expression
 "f(a,)")

(test-parse-expression
 "f(a,b)")

(test-parse-expression
 "f(a,b,)")

(test-parse-expression
 "f(a, b)")

(test-parse-expression
 "f(a, b,)")

(test-parse-expression
 "f(a, b, c)")

(test-parse-expression
 "f(a, b, c,)")

;; external calls
(test-parse-expression
 "vote.aleo/nandemo()")
(test-parse-expression
 "vote.aleo/nandemo(a)")
(test-parse-expression
 "vote.aleo/nandemo(a,)")

(test-parse-expression
 "a + b * c")

(test-parse-expression
 "a * b + c")

(test-parse-expression
 "a * (b + c)")

(test-parse-expression
 "c.c")

(test-parse-expression
 "c.3")

(test-parse-expression
 "g.double()")

(test-parse-expression
 "g.add(g1)")

(test-parse-expression
 "(a+b).add(g1).double().val")

(test-parse-expression
 "(a+b).add(g1).double().0")

(test-parse-expression
 "u8::v")

(test-parse-expression
 "U8::v")

(test-parse-expression
 "PED64::commit(true)")

(test-parse-expression
 "u8::commit()")

;; static function call using a locator
(test-parse-expression
 "vote.aleo/nandemo::foo()")

(test-parse-expression
 "Foo { x: x }")

(test-parse-expression
 "Foo { x }")

(test-parse-expression
 "Foo{x:x,}")

(test-parse-expression
 "Foo{x,}")

(test-parse-expression
 "Foo{x:x,y:y}")

(test-parse-expression
 "Foo{x,y}")

(test-parse-expression
 "Foo{x:x,y:y, }")

(test-parse-expression
 "Foo{x,y, }")

;; tuple expressions
(test-parse-expression
 "()")
(test-parse-expression
 "(abc)")
(test-parse-expression
 "(a,b)")
(test-parse-expression
 "(a,b,)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing fails on invalid expressions

(test-parse-expression-fail
 "1")

(test-parse-expression-fail
 "f(,)")

(test-parse-expression-fail
 "u8.something")

(test-parse-expression-fail
 "(abc,)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of constant declarations.

(test-parse parse-constant-declaration
            "constant-declaration"
            "const c: u8 = a + b;")

(test-parse parse-constant-declaration
            "constant-declaration"
            "const c: field = a + b;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of variable declarations.

(test-parse parse-variable-declaration
            "variable-declaration"
            "let c: u8 = a + b;")

(test-parse parse-variable-declaration
            "variable-declaration"
            "let c: group = a + b;")

(test-parse parse-variable-declaration
            "variable-declaration"
            "let world: string = \"world\";")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of return statements.

(test-parse parse-return-statement
            "return-statement"
            "return x + y;")

(test-parse parse-return-statement
            "return-statement"
            "return 0u8;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of string literals.

(test-parse parse-string-literal
            "string-literal"
            "\"hello\"")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of assertions.

(test-parse parse-assert-call
            "assert-call"
            "assert(p)")

(test-parse parse-assert-call
            "assert-call"
            "assert(x == y)")

(test-parse parse-assert-call
            "assert-call"
            "assert(x == y && z > w)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of console calls.

(test-parse parse-console-call
            "console-call"
            "assert(x == y && z > w)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of console statements.

(test-parse parse-console-statement
            "console-statement"
            "console.assert(x == y && z > w);")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of assignment operators.

(test-parse parse-assignment-operator
            "assignment-operator"
            "=")

(test-parse parse-assignment-operator
            "assignment-operator"
            "+=")

(test-parse parse-assignment-operator
            "assignment-operator"
            "-=")

(test-parse parse-assignment-operator
            "assignment-operator"
            "*=")

(test-parse parse-assignment-operator
            "assignment-operator"
            "/=")

(test-parse parse-assignment-operator
            "assignment-operator"
            "%=")

(test-parse parse-assignment-operator
            "assignment-operator"
            "**=")

(test-parse parse-assignment-operator
            "assignment-operator"
            "<<=")

(test-parse parse-assignment-operator
            "assignment-operator"
            ">>=")

(test-parse parse-assignment-operator
            "assignment-operator"
            "&=")

(test-parse parse-assignment-operator
            "assignment-operator"
            "|=")

(test-parse parse-assignment-operator
            "assignment-operator"
            "^=")

(test-parse parse-assignment-operator
            "assignment-operator"
            "&&=")

(test-parse parse-assignment-operator
            "assignment-operator"
            "||=")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of statements.

(test-parse parse-statement
            "statement"
            "let c:i8 = a + b;")

(test-parse parse-statement
            "statement"
            "return x + y;")

(test-parse parse-statement
            "statement"
            "console.assert(x == y && z > w);")

(test-parse parse-statement
            "statement"
            "x = 3u8;")

(test-parse parse-statement
            "statement"
            "x = a * b;")

(test-parse parse-statement
            "statement"
            "x += 3u8;")

(test-parse parse-statement
            "statement"
            "{ a = 1i128; b = 2u128; }")

(test-parse parse-statement
            "statement"
            "if a { return b; }")

(test-parse parse-statement
            "statement"
            "if a { return b; } else { return c; }")

(test-parse parse-statement
            "statement"
            "if a { return b; } else if c { return d; }")

(test-parse parse-statement
            "statement"
            "if a { return b; } else if c { return d; } else { return e; }")

(test-parse parse-statement
            "statement"
            "for i:u8 in 0u8..10u8 { y = do_something(i); z = and_more(i); }")

(test-parse parse-statement
            "statement"
            "for i:u8 in 0u8..=10u8 { y = do_something(i); z = and_more(i); }")

(test-parse parse-statement
            "statement"
            "for i:u8 in 0u8..(a==b ? 1u8 : 0u8) { y = do_something(i); z = and_more(i); }")

(test-parse parse-statement
            "statement"
            "for i:u8 in 0u8.. =(a==b ? 1u8 : 0u8) { y = do_something(i); z = and_more(i); }")

(test-parse parse-statement
            "statement"
            "async finalize(self.caller, amount);")

(test-parse parse-statement
            "statement"
            "increment(tickets, pid, 0u64);")

(test-parse parse-statement
            "statement"
            "decrement(tickets, pid, 1u64);")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of statements, using another interface


(test-parse-statement
 "let c:i8 = a + b;")

(test-parse-statement
 "return x + y;")

(test-parse-statement
 "console.assert(x == y && z > w);")

(test-parse-statement
 "x = 3u8;")

(test-parse-statement
 "x = a * b;")

(test-parse-statement
 "x += 3u8;")

(test-parse-statement
 "{ a = 1i128; b = 2u128; }")

(test-parse-statement
 "if a { return b; }")

(test-parse-statement
 "if a { return b; } else { return c; }")

(test-parse-statement
 "if a { return b; } else if c { return d; }")

(test-parse-statement
 "if a { return b; } else if c { return d; } else { return e; }")

(test-parse-statement
 "for i:u8 in 0u8..10u8 { y = do_something(i); z = and_more(i); }")

(test-parse-statement
 "for i:u8 in 0u8..=10u8 { y = do_something(i); z = and_more(i); }")

(test-parse-statement
 "for i:u8 in 0u8..(a==b ? 1u8 : 0u8) { y = do_something(i); z = and_more(i); }")

(test-parse-statement
 "for i:u8 in 0u8.. =(a==b ? 1u8 : 0u8) { y = do_something(i); z = and_more(i); }")

(test-parse-statement
 "async finalize(self.caller, amount);")

(test-parse-statement
 "increment(tickets, pid, 0u64);")

(test-parse-statement
 "decrement(tickets, pid, 1u64);")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing failure of statements

; there is no empty statement
(test-parse-statement-fail "")

; missing type on let-var
(test-parse-statement-fail "let c = a + b;")

; missing type on literal
(test-parse-statement-fail
 "{ a = 1i128; b = 2; }")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of function parameters.

(test-parse parse-function-parameter
            "function-parameter"
            "x: u32")

(test-parse parse-function-parameter
            "function-parameter"
            "public x: u32")

(test-parse parse-function-parameter
            "function-parameter"
            "constant x: u32")

(test-parse parse-function-parameter
            "function-parameter"
            "const x: u32")

(test-parse parse-function-parameters
            "function-parameters"
            "x: u32")

(test-parse parse-function-parameters
            "function-parameters"
            "x: u32,")

(test-parse parse-function-parameters
            "function-parameters"
            "public x: u32")

(test-parse parse-function-parameters
            "function-parameters"
            "public x: u32,")

(test-parse parse-function-parameters
            "function-parameters"
            "constant x: u32")

(test-parse parse-function-parameters
            "function-parameters"
            "constant x: u32,")

(test-parse parse-function-parameters
            "function-parameters"
            "const x: u32")

(test-parse parse-function-parameters
            "function-parameters"
            "const x: u32,")

(test-parse parse-function-parameters
            "function-parameters"
            "const x: u32, y: group")

(test-parse parse-function-parameters
            "function-parameters"
            "const x: u32, y: group,")

(test-parse parse-function-parameters
            "function-parameters"
            "x: u32, y: i16, z: field")

(test-parse parse-function-parameters
            "function-parameters"
            "x: u32, y: i16, z: field,")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of record declarations.

(test-parse parse-record-declaration
            "record-declaration"
            "record Token {
    // The token owner.
    owner: address,
    // The Aleo balance (in gates).
    balance: u64,
    // The token amount.
    amount: u64,
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of mapping declarations.

(test-parse parse-mapping-declaration
            "mapping-declaration"
            "mapping account: address => u64;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of struct declarations.

(test-parse parse-struct-declaration
            "struct-declaration"
            "// The \"Message\" struct type.
struct Message {
    // A struct member named \"first\" with type \"field\".
    first: field,
    // A struct member named \"second\" with type \"field\".
    second: field,
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of function declarations.

(test-parse parse-function-declaration
            "function-declaration"
            "function f()->group{}")

(test-parse parse-function-declaration
            "function-declaration"
            "function f(x: u8) -> u8 {}")

(test-parse parse-function-declaration
            "function-declaration"
            "function f(x: u8,) -> u8 {}")

(test-parse parse-function-declaration
            "function-declaration"
            "function f(const s: i8, x: u8) -> u8 {}")

(test-parse parse-function-declaration
            "function-declaration"
            "@program @foo function f(const s: i8, x: u8) -> u8 {}")

(test-parse parse-function-declaration
            "function-declaration"
            "@program
function f(const s: i8, x: u8) -> u8 {}")

(test-parse parse-function-declaration
            "function-declaration"
            "@program @foo
function f(const s: i8, x: u8) -> u8 {}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of transition declarations.

(test-parse parse-transition-declaration
            "transition-declaration"
            "transition new() -> Board {
        return Board {
            r1: Row { c1: 0u8, c2: 0u8, c3: 0u8 },
            r2: Row { c1: 0u8, c2: 0u8, c3: 0u8 },
            r3: Row { c1: 0u8, c2: 0u8, c3: 0u8 },
        };
    }")

;; Try the same thing both with and without a 'finalize'; from workshop/token/src/main.leo
(test-parse parse-transition-declaration
            "transition-declaration"
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
    }")

(test-parse parse-transition-declaration
            "transition-declaration"
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
    }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of program-item

(test-parse parse-program-item
            "program-item"
            "function compare(s: i8, other: u8) -> bool {
                 return s == 1i8 && other == 1u8;
             }")

(test-parse parse-program-item
            "program-item"
            "record Token {
    // The token owner.
    owner: address,
    // The Aleo balance (in gates).
    balance: u64,
    // The token amount.
    amount: u64,
}")

(test-parse parse-program-item
            "program-item"
            "// The \"Message\" struct type.
struct Message {
    // A struct member named \"first\" with type \"field\".
    first: field,
    // A struct member named \"second\" with type \"field\".
    second: field,
}")

(test-parse parse-program-item
            "program-item"
            "@program
function f(const s: i8, x: u8) -> u8 {}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of program-declaration

(test-parse parse-program-declaration
            "program-declaration"
            "program x.y{}")

(test-parse parse-program-declaration
            "program-declaration"
            "program twoadicity.aleo {
    // This function calculates the number of powers of two (\"twoadicity\")
    // in the prime factorization of the input number `n`.
    transition main(public n: field) -> u8 {
        let remaining_n: field = n;
        let powers_of_two: u8 = 0u8;
        // Since field ints are 253 bits or fewer, any number in the field
        // will have at most 252 powers of two in its prime factoring.
        for i:u8 in 0u8..252u8 {
            if is_even_and_nonzero(remaining_n) {
                remaining_n = remaining_n / 2field;
                powers_of_two = powers_of_two + 1u8;
            }
        }
        return powers_of_two;
    }

    /* We define the is_even predicate on fields as follows.
       If n is even and nonzero, clearly n/2 < n.
       If n is odd, n-p is a field-equivalent negative number that is even, and
       (n-p)/2 is a field-equivalent negative number closer to 0, greater than n-p.
       If we add p to both of these negative numbers, we have
       n/2 = (n-p)/2 + p = (n+p)/2 is greater than n and still less than p.
    */
    function is_even_and_nonzero (n: field) -> bool {
        return n / 2field < n;
    }
}")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of import-declaration

(test-parse parse-import-declaration
            "import-declaration"
            "import board.leo;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing of files.

(test-parse-file
 "program two.aleo {
 function compare(s: i8, other: u8) -> bool {
   return s == 1i8 && other == 1u8;
 }
function compare2(s: i8, other: u8) -> bool {
   return s == 1i8 && other == 1u8;
 }
/* */}")

(test-parse-file
 "program two.aleo {/* */function compare(s: i8, other: u8) -> bool {
   return s == 1i8 && other == 1u8;
 }/* */function compare2(s: i8, other: u8) -> bool {
   return s == 1i8 && other == 1u8;
 }/* */}")

;; TODO: perhaps move these interesting strings to a still-supported construct
;; Commenting out for now, since console.log is not currently supported.
#||
(test-parse-file "function main(a: i8, y: bool) -> bool {
    console.log(\"👍\");
    return y == true && a == -128i8;
}
")

(test-parse-file "function main(a: i8, y: bool) -> bool {
    console.log(\"å\");
    return y == true && a == -128i8;
}
")

; Fail because there is an extra semicolon at the end
(test-parse-file-fail "function main(a: i8, y: bool) -> bool {
    console.log(\"å\");
    return y == true && a == 127i8;
};
")
||#

(test-parse-file "program two.aleo{
function main(a: ()) -> bool {
    return true;
}}
")

(test-parse-file "program two.aleo{
function main(a: (i8, i8),) -> bool {
    return true;
}
}
")

; Fail because a tuple type has exactly one component
(test-parse-file-fail "program two.aleo{
function main(a: (i8)) -> bool {
    return true;
}
}")

(test-parse-file-fail "program two.aleo{
function main(a: (i8,)) -> bool {
    return true;
} }
")

;; annotations
(test-parse-file "program two.aleo{
@program
function main(a: (i8, i8),) -> bool {
    return true;
}
}
")

(test-parse-file-fail "program two.aleo{
@
function main(a: (i8, i8),) -> bool {
    return true;
}
}
")
