; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../lexer")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/testing/assert-bang-stobj" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Testing lexing functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-lex (fn input &key pos more-inputs gcc cond)
  ;; INPUT is an ACL2 term with the text to lex,
  ;; where the term evaluates to a string or a list of bytes.
  ;; Optional POS is the initial position for the parser state.
  ;; Optional MORE-INPUTS go just before parser state input.
  ;; GCC flag says whether GCC extensions are enabled.
  ;; Optional COND may be over variables AST, POS/SPAN, PARSTATE,
  ;; and also POS/SPAN2 for LEX-*-DIGIT and LEX-*-HEXADECIMAL-DIGIT.
  `(assert!-stobj
    (b* ((parstate (init-parstate (if (stringp ,input)
                                      (acl2::string=>nats ,input)
                                    ,input)
                                  ,gcc
                                  parstate))
         ,@(and pos
                `((parstate (update-parstate->position ,pos parstate))))
         (,(if (member-eq fn '(lex-*-digit
                               lex-*-hexadecimal-digit))
               '(mv erp ?ast ?pos/span ?pos/span2 parstate)
             '(mv erp ?ast ?pos/span parstate))
          (,fn ,@more-inputs parstate)))
      (mv
       (if erp
           (cw "~@0" erp) ; CW returns NIL, so ASSERT!-STOBJ fails
         ,(or cond t)) ; assertion passes if COND is absent or else holds
       parstate))
    parstate))

(defmacro test-lex-fail (fn input &key pos more-inputs gcc)
  ;; INPUT is an ACL2 term with the text to lex,
  ;; where the term evaluates to a string or a list of bytes.
  ;; Optional POS is the initial position for the parser state.
  ;; Optional MORE-INPUTS go just before parser state input.
  ;; GCC flag says whether GCC extensions are enabled.
  `(assert!-stobj
    (b* ((parstate (init-parstate (if (stringp ,input)
                                      (acl2::string=>nats ,input)
                                    ,input)
                                  ,gcc
                                  parstate))
         ,@(and pos
                `((parstate (update-parstate->position ,pos parstate))))
         (,(if (member-eq fn '(lex-*-digit
                               lex-*-hexadecimal-digit))
               '(mv erp & & & parstate)
             '(mv erp & & parstate))
          (,fn ,@more-inputs parstate)))
      (mv erp parstate))
    parstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-identifier/keyword

(test-lex
 lex-identifier/keyword
 " abc"
 :pos (position 8 4)
 :more-inputs ((char-code #\w) (position 8 3))
 :cond (and (equal ast (lexeme-token (token-ident (ident "w"))))
            (equal pos/span (span (position 8 3) (position 8 3)))))

(test-lex
 lex-identifier/keyword
 "abc456"
 :pos (position 8 4)
 :more-inputs ((char-code #\u) (position 8 3))
 :cond (and (equal ast (lexeme-token (token-ident (ident "uabc456"))))
            (equal pos/span (span (position 8 3) (position 8 9)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-hexadecimal-digit

(test-lex
 lex-hexadecimal-digit
 "0"
 :cond (equal ast #\0))

(test-lex
 lex-hexadecimal-digit
 "1"
 :cond (equal ast #\1))

(test-lex
 lex-hexadecimal-digit
 "8"
 :cond (equal ast #\8))

(test-lex
 lex-hexadecimal-digit
 "A"
 :cond (equal ast #\A))

(test-lex
 lex-hexadecimal-digit
 "b"
 :cond (equal ast #\b))

(test-lex
 lex-hexadecimal-digit
 "fy"
 :cond (and (equal ast #\f)
            (equal (parstate->bytes parstate) (list (char-code #\y)))))

(test-lex-fail
 lex-hexadecimal-digit
 "")

(test-lex-fail
 lex-hexadecimal-digit
 " ")

(test-lex-fail
 lex-hexadecimal-digit
 " c")

(test-lex-fail
 lex-hexadecimal-digit
 "g")

(test-lex-fail
 lex-hexadecimal-digit
 "@")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-hex-quad

(test-lex
 lex-hex-quad
 "0000"
 :cond (equal ast (hex-quad #\0 #\0 #\0 #\0)))

(test-lex
 lex-hex-quad
 "b8F0"
 :cond (equal ast (hex-quad #\b #\8 #\F #\0)))

(test-lex
 lex-hex-quad
 "DeadBeef"
 :cond (and (equal ast (hex-quad #\D #\e #\a #\d))
            (equal (parstate->bytes parstate) (acl2::string=>nats "Beef"))))

(test-lex-fail
 lex-hex-quad
 "")

(test-lex-fail
 lex-hex-quad
 "7aa")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-*-digit

(test-lex
 lex-*-digit
 ""
 :pos (position 1 1)
 :more-inputs ((position 1 0))
 :cond (and (equal ast nil)
            (equal pos/span (position 1 0))
            (equal pos/span2 (position 1 1))))

(test-lex
 lex-*-digit
 "+"
 :pos (position 1 1)
 :more-inputs ((position 1 0))
 :cond (and (equal ast nil)
            (equal pos/span (position 1 0))
            (equal pos/span2 (position 1 1))))

(test-lex
 lex-*-digit
 "6"
 :pos (position 10 10)
 :more-inputs ((position 10 9))
 :cond (and (equal ast '(#\6))
            (equal pos/span (position 10 10))
            (equal pos/span2 (position 10 11))))

(test-lex
 lex-*-digit
 "183a"
 :pos (position 10 10)
 :more-inputs ((position 10 9))
 :cond (and (equal ast '(#\1 #\8 #\3))
            (equal pos/span (position 10 12))
            (equal pos/span2 (position 10 13))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-*-hexadecimal-digit

(test-lex
 lex-*-hexadecimal-digit
 ""
 :pos (position 20 88)
 :more-inputs ((position 20 87))
 :cond (and (equal ast nil)
            (equal pos/span (position 20 87))
            (equal pos/span2 (position 20 88))))

(test-lex
 lex-*-hexadecimal-digit
 "dEadbeFf"
 :pos (position 1 1)
 :more-inputs ((position 1 0))
 :cond (and (equal ast '(#\d #\E #\a #\d #\b #\e #\F #\f))
            (equal pos/span (position 1 8))
            (equal pos/span2 (position 1 9))))

(test-lex
 lex-*-hexadecimal-digit
 "1"
 :pos (position 10 10)
 :more-inputs ((position 10 9))
 :cond (and (equal ast '(#\1))
            (equal pos/span (position 10 10))
            (equal pos/span2 (position 10 11))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-escape-sequence

(test-lex
 lex-escape-sequence
 "'"
 :cond (equal ast (escape-simple (simple-escape-squote))))

(test-lex
 lex-escape-sequence
 "\""
 :cond (equal ast (escape-simple (simple-escape-dquote))))

(test-lex
 lex-escape-sequence
 "?"
 :cond (equal ast (escape-simple (simple-escape-qmark))))

(test-lex
 lex-escape-sequence
 "\\"
 :cond (equal ast (escape-simple (simple-escape-bslash))))

(test-lex
 lex-escape-sequence
 "a"
 :cond (equal ast (escape-simple (simple-escape-a))))

(test-lex
 lex-escape-sequence
 "b"
 :cond (equal ast (escape-simple (simple-escape-b))))

(test-lex
 lex-escape-sequence
 "f"
 :cond (equal ast (escape-simple (simple-escape-f))))

(test-lex
 lex-escape-sequence
 "n"
 :cond (equal ast (escape-simple (simple-escape-n))))

(test-lex
 lex-escape-sequence
 "r"
 :cond (equal ast (escape-simple (simple-escape-r))))

(test-lex
 lex-escape-sequence
 "t"
 :cond (equal ast (escape-simple (simple-escape-t))))

(test-lex
 lex-escape-sequence
 "v"
 :cond (equal ast (escape-simple (simple-escape-v))))

(test-lex
 lex-escape-sequence
 "vv"
 :cond (equal ast (escape-simple (simple-escape-v))))

(test-lex-fail
 lex-escape-sequence
 "w")

(test-lex
 lex-escape-sequence
 "6"
 :cond (equal ast (escape-oct (oct-escape-one #\6))))

(test-lex
 lex-escape-sequence
 "68"
 :cond (equal ast (escape-oct (oct-escape-one #\6))))

(test-lex
 lex-escape-sequence
 "60"
 :cond (equal ast (escape-oct (oct-escape-two #\6 #\0))))

(test-lex
 lex-escape-sequence
 "601"
 :cond (equal ast (escape-oct (oct-escape-three #\6 #\0 #\1))))

(test-lex
 lex-escape-sequence
 "6011"
 :cond (equal ast (escape-oct (oct-escape-three #\6 #\0 #\1))))

(test-lex-fail
 lex-escape-sequence
 "8")

(test-lex
 lex-escape-sequence
 "xf8"
 :cond (equal ast (escape-hex (list #\f #\8))))

(test-lex
 lex-escape-sequence
 "x829s"
 :cond (equal ast (escape-hex (list #\8 #\2 #\9))))

(test-lex-fail
 lex-escape-sequence
 "x")

(test-lex-fail
 lex-escape-sequence
 "x+")

(test-lex
 lex-escape-sequence
 "uabBA"
 :cond (equal ast (escape-univ
                   (univ-char-name-locase-u (hex-quad #\a #\b #\B #\A)))))

(test-lex
 lex-escape-sequence
 "U744dD900"
 :cond (equal ast (escape-univ
                   (univ-char-name-upcase-u (hex-quad #\7 #\4 #\4 #\d)
                                            (hex-quad #\D #\9 #\0 #\0)))))

(test-lex-fail
 lex-escape-sequence
 "u123")

(test-lex-fail
 lex-escape-sequence
 "U0000123")

(test-lex-fail
 lex-escape-sequence
 "%")

(test-lex
 lex-escape-sequence
 "%"
 :gcc t
 :cond (equal ast (escape-simple (simple-escape-percent))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-*-c-char

(test-lex
 lex-*-c-char
 "a'"
 :cond (equal ast (list (c-char-char (char-code #\a)))))

(test-lex
 lex-*-c-char
 "\\a'"
 :cond (equal ast (list (c-char-escape (escape-simple (simple-escape-a))))))

(test-lex
 lex-*-c-char
 "&\\xf7'"
 :cond (equal ast (list (c-char-char (char-code #\&))
                        (c-char-escape (escape-hex (list #\f #\7))))))

(test-lex
 lex-*-c-char
 "\\1111'"
 :cond (equal ast (list (c-char-escape
                         (escape-oct (oct-escape-three #\1 #\1 #\1)))
                        (c-char-char (char-code #\1)))))

(test-lex
 lex-*-c-char
 "ABC'"
 :cond (and (equal ast (list (c-char-char (char-code #\A))
                             (c-char-char (char-code #\B))
                             (c-char-char (char-code #\C))))
            (equal pos/span (position 1 3))))

(test-lex
 lex-*-c-char
 "d\"q'"
 :cond (and (equal ast (list (c-char-char (char-code #\d))
                             (c-char-char (char-code #\"))
                             (c-char-char (char-code #\q))))
            (equal pos/span (position 1 3))))

(test-lex-fail
 lex-*-c-char
 "")

(test-lex-fail
 lex-*-c-char
 "a")

(test-lex-fail
 lex-*-c-char
 "a\\'")

(test-lex-fail
 lex-*-c-char
 "a\\z'")

(test-lex-fail
 lex-*-c-char
 (list (char-code #\a) 10 (char-code #\b) (char-code #\')))

(test-lex-fail
 lex-*-c-char
 (list (char-code #\a) 13 10 (char-code #\')))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-*-s-char

(test-lex
 lex-*-s-char
 "p\""
 :cond (equal ast (list (s-char-char (char-code #\p)))))

(test-lex
 lex-*-s-char
 "'\""
 :cond (equal ast (list (s-char-char (char-code #\')))))

(test-lex
 lex-*-s-char
 "\\n\""
 :cond (equal ast (list (s-char-escape (escape-simple (simple-escape-n))))))

(test-lex
 lex-*-s-char
 "12\""
 :cond (equal ast (list (s-char-char (char-code #\1))
                        (s-char-char (char-code #\2)))))

(test-lex-fail
 lex-*-s-char
 "")

(test-lex-fail
 lex-*-s-char
 "noclose")

(test-lex-fail
 lex-*-s-char
 "\\k\"")

(test-lex-fail
 lex-*-s-char
 (list (char-code #\U) 10 (char-code #\")))

(test-lex-fail
 lex-*-s-char
 (list (char-code #\U) 13 (char-code #\")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-character-constant

(test-lex
 lex-character-constant
 "e'"
 :pos (position 1 1)
 :more-inputs (nil (position 1 0))
 :cond (equal ast
              (lexeme-token
               (token-const
                (const-char
                 (cconst nil
                         (list (c-char-char (char-code #\e)))))))))

(test-lex
 lex-character-constant
 "\\aA'"
 :pos (position 1 2)
 :more-inputs ((cprefix-locase-u) (position 1 1))
 :cond (equal ast
              (lexeme-token
               (token-const
                (const-char
                 (cconst (cprefix-locase-u)
                         (list (c-char-escape (escape-simple (simple-escape-a)))
                               (c-char-char (char-code #\A)))))))))

(test-lex-fail
 lex-character-constant
 "''"
 :pos (position 1 1)
 :more-inputs (nil (position 1 0)))

(test-lex-fail
 lex-character-constant
 (list 10 (char-code #\'))
 :pos (position 1 1)
 :more-inputs (nil (position 1 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-string-literal

(test-lex
 lex-string-literal
 "\""
 :pos (position 1 1)
 :more-inputs (nil (position 1 0))
 :cond (equal ast
              (lexeme-token
               (token-string
                (stringlit nil nil)))))

(test-lex
 lex-string-literal
 "helo\""
 :pos (position 10 10)
 :more-inputs ((eprefix-upcase-l) (position 10 9))
 :cond (equal ast
              (lexeme-token
               (token-string
                (stringlit (eprefix-upcase-l)
                           (list (s-char-char (char-code #\h))
                                 (s-char-char (char-code #\e))
                                 (s-char-char (char-code #\l))
                                 (s-char-char (char-code #\o))))))))

(test-lex-fail
 lex-string-literal
 "wrong'"
 :more-inputs (nil (position 1 0)))

(test-lex-fail
 lex-string-literal
 (list 10 (char-code #\"))
 :more-inputs (nil (position 1 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-*-h-char

(test-lex
 lex-*-h-char
 "abc>"
 :cond (equal ast (list (h-char (char-code #\a))
                        (h-char (char-code #\b))
                        (h-char (char-code #\c)))))

(test-lex
 lex-*-h-char
 "\">"
 :cond (equal ast (list (h-char (char-code #\")))))

(test-lex
 lex-*-h-char
 "'>"
 :cond (equal ast (list (h-char (char-code #\')))))

(test-lex
 lex-*-h-char
 "<>"
 :cond (equal ast (list (h-char (char-code #\<)))))

(test-lex-fail
 lex-*-h-char
 "")

(test-lex-fail
 lex-*-h-char
 "noclose")

(test-lex-fail
 lex-*-h-char
 (list (char-code #\U) 10 (char-code #\>)))

(test-lex-fail
 lex-*-h-char
 (list (char-code #\U) 13 (char-code #\>)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-*-q-char

(test-lex
 lex-*-q-char
 "abc\""
 :cond (equal ast (list (q-char (char-code #\a))
                        (q-char (char-code #\b))
                        (q-char (char-code #\c)))))

(test-lex
 lex-*-q-char
 ">\""
 :cond (equal ast (list (q-char (char-code #\>)))))

(test-lex
 lex-*-q-char
 "'\""
 :cond (equal ast (list (q-char (char-code #\')))))

(test-lex-fail
 lex-*-q-char
 "")

(test-lex-fail
 lex-*-q-char
 "noclose")

(test-lex-fail
 lex-*-q-char
 (list (char-code #\U) 10 (char-code #\")))

(test-lex-fail
 lex-*-q-char
 (list (char-code #\U) 13 (char-code #\")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-header-name

(test-lex
 lex-header-name
 "<stdio.h>"
 :cond (equal ast (header-name-angles (list (h-char (char-code #\s))
                                            (h-char (char-code #\t))
                                            (h-char (char-code #\d))
                                            (h-char (char-code #\i))
                                            (h-char (char-code #\o))
                                            (h-char (char-code #\.))
                                            (h-char (char-code #\h))))))

(test-lex
 lex-header-name
 "\"parser.h\""
 :cond (equal ast (header-name-quotes (list (q-char (char-code #\p))
                                            (q-char (char-code #\a))
                                            (q-char (char-code #\r))
                                            (q-char (char-code #\s))
                                            (q-char (char-code #\e))
                                            (q-char (char-code #\r))
                                            (q-char (char-code #\.))
                                            (q-char (char-code #\h))))))

(test-lex-fail
 lex-header-name
 "")

(test-lex-fail
 lex-header-name
 "noopen")

(test-lex-fail
 lex-header-name
 "<noclose")

(test-lex-fail
 lex-header-name
 "\"noclose")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-?-integer-suffix

(test-lex
 lex-?-integer-suffix
 ""
 :cond (equal ast nil))

(test-lex
 lex-?-integer-suffix
 "u"
 :cond (equal ast (isuffix-u (usuffix-locase-u))))

(test-lex
 lex-?-integer-suffix
 "ul"
 :cond (equal ast (isuffix-ul (usuffix-locase-u) (lsuffix-locase-l))))

(test-lex
 lex-?-integer-suffix
 "ull"
 :cond (equal ast (isuffix-ul (usuffix-locase-u) (lsuffix-locase-ll))))

(test-lex
 lex-?-integer-suffix
 "uL"
 :cond (equal ast (isuffix-ul (usuffix-locase-u) (lsuffix-upcase-l))))

(test-lex
 lex-?-integer-suffix
 "uLL"
 :cond (equal ast (isuffix-ul (usuffix-locase-u) (lsuffix-upcase-ll))))

(test-lex
 lex-?-integer-suffix
 "U"
 :cond (equal ast (isuffix-u (usuffix-upcase-u))))

(test-lex
 lex-?-integer-suffix
 "Ul"
 :cond (equal ast (isuffix-ul (usuffix-upcase-u) (lsuffix-locase-l))))

(test-lex
 lex-?-integer-suffix
 "Ull"
 :cond (equal ast (isuffix-ul (usuffix-upcase-u) (lsuffix-locase-ll))))

(test-lex
 lex-?-integer-suffix
 "UL"
 :cond (equal ast (isuffix-ul (usuffix-upcase-u) (lsuffix-upcase-l))))

(test-lex
 lex-?-integer-suffix
 "ULL"
 :cond (equal ast (isuffix-ul (usuffix-upcase-u) (lsuffix-upcase-ll))))

(test-lex
 lex-?-integer-suffix
 "l"
 :cond (equal ast (isuffix-l (lsuffix-locase-l))))

(test-lex
 lex-?-integer-suffix
 "ll"
 :cond (equal ast (isuffix-l (lsuffix-locase-ll))))

(test-lex
 lex-?-integer-suffix
 "L"
 :cond (equal ast (isuffix-l (lsuffix-upcase-l))))

(test-lex
 lex-?-integer-suffix
 "LL"
 :cond (equal ast (isuffix-l (lsuffix-upcase-ll))))

(test-lex
 lex-?-integer-suffix
 "lu"
 :cond (equal ast (isuffix-lu (lsuffix-locase-l) (usuffix-locase-u))))

(test-lex
 lex-?-integer-suffix
 "llu"
 :cond (equal ast (isuffix-lu (lsuffix-locase-ll) (usuffix-locase-u))))

(test-lex
 lex-?-integer-suffix
 "Lu"
 :cond (equal ast (isuffix-lu (lsuffix-upcase-l) (usuffix-locase-u))))

(test-lex
 lex-?-integer-suffix
 "LLu"
 :cond (equal ast (isuffix-lu (lsuffix-upcase-ll) (usuffix-locase-u))))

(test-lex
 lex-?-integer-suffix
 "lU"
 :cond (equal ast (isuffix-lu (lsuffix-locase-l) (usuffix-upcase-u))))

(test-lex
 lex-?-integer-suffix
 "llU"
 :cond (equal ast (isuffix-lu (lsuffix-locase-ll) (usuffix-upcase-u))))

(test-lex
 lex-?-integer-suffix
 "LU"
 :cond (equal ast (isuffix-lu (lsuffix-upcase-l) (usuffix-upcase-u))))

(test-lex
 lex-?-integer-suffix
 "LLU"
 :cond (equal ast (isuffix-lu (lsuffix-upcase-ll) (usuffix-upcase-u))))

(test-lex
 lex-?-integer-suffix
 "lLu" ; only l is lexed
 :cond (equal ast (isuffix-l (lsuffix-locase-l))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-?-floating-suffix

(test-lex
 lex-?-floating-suffix
 ""
 :cond (equal ast nil))

(test-lex
 lex-?-floating-suffix
 "f"
 :cond (equal ast (fsuffix-locase-f)))

(test-lex
 lex-?-floating-suffix
 "F"
 :cond (equal ast (fsuffix-upcase-f)))

(test-lex
 lex-?-floating-suffix
 "l"
 :cond (equal ast (fsuffix-locase-l)))

(test-lex
 lex-?-floating-suffix
 "L"
 :cond (equal ast (fsuffix-upcase-l)))

(test-lex
 lex-?-floating-suffix
 "other"
 :cond (equal ast nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-lex
 lex-?-sign
 ""
 :cond (equal ast nil))

(test-lex
 lex-?-sign
 "+"
 :cond (equal ast (sign-plus)))

(test-lex
 lex-?-sign
 "-"
 :cond (equal ast (sign-minus)))

(test-lex
 lex-?-sign
 "*"
 :cond (equal ast nil))

(test-lex
 lex-?-sign
 "6"
 :cond (equal ast nil))

(test-lex
 lex-?-sign
 "L"
 :cond (equal ast nil))
