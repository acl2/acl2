; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../preprocessor-lexer")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/testing/assert-bang-stobj" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-lex (fn ; lexing function
                    input ; ACL2 term with text to lex (string or bytes)
                    &key
                    more-inputs ; additional inputs to lexing function
                    (index '0) ; where to start lexing
                    (cond 't) ; condition on AST for success
                    (std '17)
                    (gcc 'nil)
                    (clang 'nil)
                    (fail 'nil)) ; test must fail
  `(assert!-stobj
    (b* ((version (case ,std
                    (17 (cond (,gcc (c::version-c17+gcc))
                              (,clang (c::version-c17+clang))
                              (t (c::version-c17))))
                    (23 (cond (,gcc (c::version-c23+gcc))
                              (,clang (c::version-c23+clang))
                              (t (c::version-c23))))))
         (ienv (change-ienv (ienv-default) :version version))
         (macros (macro-init version))
         (options (make-ppoptions :full-expansion nil
                                  :keep-comments t
                                  :trace-expansion t
                                  :no-errors/warnings nil))
         ((mv erp ppstate)
          (ppstate-for-file (if (stringp ,input)
                                (acl2::string=>nats ,input)
                              ,input)
                            macros
                            options
                            ienv
                            ppstate))
         ((when erp) (mv (cw "Initialization fails.") ppstate))
         (ppstate (update-ppstate->char-index ,index ppstate))
         (,(if (eq fn 'plex-*-hexadecimal-digit)
               '(mv erp ?ast ?pos/span ?pos/span2 ppstate)
             '(mv erp ?ast ?pos/span ppstate))
          (,fn ,@more-inputs ppstate)))
      (if ,fail
          (mv (and erp (not (cw "~@0" erp))) ppstate)
        (mv (and (not erp) ,cond) ppstate)))
    ppstate))

(defmacro test-lex-lexeme (input
                           &key
                           (cond 't)
                           (std '17)
                           (gcc 'nil)
                           (clang 'nil)
                           (fail 'nil))
  `(test-lex plex-lexeme
             ,input
             :more-inputs (nil)
             :index 0
             :cond ,cond
             :std ,std
             :gcc ,gcc
             :clang ,clang
             :fail ,fail))

(defmacro test-lex-lexeme-headerp (input
                                   &key
                                   (cond 't)
                                   (std '17)
                                   (gcc 'nil)
                                   (clang 'nil)
                                   (fail 'nil))
  `(test-lex plex-lexeme
             ,input
             :more-inputs (t)
             :index 0
             :cond ,cond
             :std ,std
             :gcc ,gcc
             :clang ,clang
             :fail ,fail))

(defmacro pos (line column)
  `(position ,line ,column))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-identifier

(test-lex
 plex-identifier
 "w abc"
 :more-inputs ((char-code #\w) (pos 1 1))
 :index 1
 :cond (equal ast (plexeme-ident (ident "w"))))

(test-lex
 plex-identifier
 "uabc456"
 :more-inputs ((char-code #\u) (pos 1 1))
 :index 1
 :cond (equal ast (plexeme-ident (ident "uabc456"))))

(test-lex
 plex-identifier
 "static"
 :more-inputs ((char-code #\s) (pos 1 1))
 :index 1
 :cond (equal ast (plexeme-ident (ident "static"))))

(test-lex
 plex-identifier
 "include"
 :more-inputs ((char-code #\i) (pos 1 1))
 :index 1
 :cond (equal ast (plexeme-ident (ident "include"))))

(test-lex
 plex-identifier
 "includ_"
 :more-inputs ((char-code #\i) (pos 1 1))
 :index 1
 :cond (equal ast (plexeme-ident (ident "includ_"))))

(test-lex
 plex-identifier
 "includ+"
 :more-inputs ((char-code #\i) (pos 1 1))
 :index 1
 :cond (equal ast (plexeme-ident (ident "includ"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-pp-number

(test-lex
 plex-pp-number
 "3"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number (pnumber-digit #\3))))

(test-lex
 plex-pp-number
 "3+"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number (pnumber-digit #\3))))

(test-lex
 plex-pp-number
 ".3"
 :more-inputs (t #\3 (pos 1 2))
 :index 2
 :cond (equal ast
              (plexeme-number (pnumber-dot-digit #\3))))

(test-lex
 plex-pp-number
 ".3+"
 :more-inputs (t #\3 (pos 1 2))
 :index 2
 :cond (equal ast
              (plexeme-number (pnumber-dot-digit #\3))))

(test-lex
 plex-pp-number
 "34"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-digit (pnumber-digit #\3) #\4))))

(test-lex
 plex-pp-number
 ".34"
 :more-inputs (t #\3 (pos 1 2))
 :index 2
 :cond (equal ast
              (plexeme-number
               (pnumber-number-digit (pnumber-dot-digit #\3) #\4))))

(test-lex
 plex-pp-number
 "3e+"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-locase-e-sign (pnumber-digit #\3)
                                             (sign-plus)))))

(test-lex
 plex-pp-number
 "3e-"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-locase-e-sign (pnumber-digit #\3)
                                             (sign-minus)))))

(test-lex
 plex-pp-number
 "3e*"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-nondigit (pnumber-digit #\3) #\e))))

(test-lex
 plex-pp-number
 "3E+"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-upcase-e-sign (pnumber-digit #\3)
                                             (sign-plus)))))

(test-lex
 plex-pp-number
 "3E-"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-upcase-e-sign (pnumber-digit #\3)
                                             (sign-minus)))))

(test-lex
 plex-pp-number
 "3E/"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-nondigit (pnumber-digit #\3) #\E))))

(test-lex
 plex-pp-number
 "3p+"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-locase-p-sign (pnumber-digit #\3)
                                             (sign-plus)))))

(test-lex
 plex-pp-number
 "3p-"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-locase-p-sign (pnumber-digit #\3)
                                             (sign-minus)))))

(test-lex
 plex-pp-number
 "3p*"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-nondigit (pnumber-digit #\3) #\p))))

(test-lex
 plex-pp-number
 "3P+"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-upcase-p-sign (pnumber-digit #\3)
                                             (sign-plus)))))

(test-lex
 plex-pp-number
 "3P-"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-upcase-p-sign (pnumber-digit #\3)
                                             (sign-minus)))))

(test-lex
 plex-pp-number
 "3P/"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-nondigit (pnumber-digit #\3) #\P))))

(test-lex
 plex-pp-number
 "3a"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-nondigit (pnumber-digit #\3) #\a))))

(test-lex
 plex-pp-number
 "3a+"
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-nondigit (pnumber-digit #\3) #\a))))

(test-lex
 plex-pp-number
 "3."
 :more-inputs (nil #\3 (pos 1 1))
 :index 1
 :cond (equal ast
              (plexeme-number
               (pnumber-number-dot (pnumber-digit #\3)))))

(test-lex
 plex-pp-number
 "37abP-.x"
 :more-inputs (t #\3 (pos 1 1))
 :index 1
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-hexadecimal-digit

(test-lex
 plex-hexadecimal-digit
 "0"
 :cond (equal ast #\0))

(test-lex
 plex-hexadecimal-digit
 "1"
 :cond (equal ast #\1))

(test-lex
 plex-hexadecimal-digit
 "8"
 :cond (equal ast #\8))

(test-lex
 plex-hexadecimal-digit
 "A"
 :cond (equal ast #\A))

(test-lex
 plex-hexadecimal-digit
 "b"
 :cond (equal ast #\b))

(test-lex
 plex-hexadecimal-digit
 "fy"
 :cond (equal ast #\f))

(test-lex
 plex-hexadecimal-digit
 ""
 :fail t)

(test-lex
 plex-hexadecimal-digit
 " "
 :fail t)

(test-lex
 plex-hexadecimal-digit
 " c"
 :fail t)

(test-lex
 plex-hexadecimal-digit
 "g"
 :fail t)

(test-lex
 plex-hexadecimal-digit
 "@"
 :fail t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-hex-quad

(test-lex
 plex-hex-quad
 "0000"
 :cond (equal ast (hex-quad #\0 #\0 #\0 #\0)))

(test-lex
 plex-hex-quad
 "b8F0"
 :cond (equal ast (hex-quad #\b #\8 #\F #\0)))

(test-lex
 plex-hex-quad
 "DeadBeef"
 :cond (equal ast (hex-quad #\D #\e #\a #\d)))

(test-lex
 plex-hex-quad
 ""
 :fail t)

(test-lex
 plex-hex-quad
 "7aa"
 :fail t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-*-hexadecimal-digit

(test-lex
 plex-*-hexadecimal-digit
 ""
 :more-inputs ((pos 1 0))
 :cond (equal ast nil))

(test-lex
 plex-*-hexadecimal-digit
 "dEadbeFf"
 :more-inputs ((pos 1 0))
 :cond (equal ast '(#\d #\E #\a #\d #\b #\e #\F #\f)))

(test-lex
 plex-*-hexadecimal-digit
 "1"
 :more-inputs ((pos 1 0))
 :cond (equal ast '(#\1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-escape-sequence

(test-lex
 plex-escape-sequence
 "'"
 :cond (equal ast (escape-simple (simple-escape-squote))))

(test-lex
 plex-escape-sequence
 "\""
 :cond (equal ast (escape-simple (simple-escape-dquote))))

(test-lex
 plex-escape-sequence
 "?"
 :cond (equal ast (escape-simple (simple-escape-qmark))))

(test-lex
 plex-escape-sequence
 "\\"
 :cond (equal ast (escape-simple (simple-escape-bslash))))

(test-lex
 plex-escape-sequence
 "a"
 :cond (equal ast (escape-simple (simple-escape-a))))

(test-lex
 plex-escape-sequence
 "b"
 :cond (equal ast (escape-simple (simple-escape-b))))

(test-lex
 plex-escape-sequence
 "f"
 :cond (equal ast (escape-simple (simple-escape-f))))

(test-lex
 plex-escape-sequence
 "n"
 :cond (equal ast (escape-simple (simple-escape-n))))

(test-lex
 plex-escape-sequence
 "r"
 :cond (equal ast (escape-simple (simple-escape-r))))

(test-lex
 plex-escape-sequence
 "t"
 :cond (equal ast (escape-simple (simple-escape-t))))

(test-lex
 plex-escape-sequence
 "v"
 :cond (equal ast (escape-simple (simple-escape-v))))

(test-lex
 plex-escape-sequence
 "vv"
 :cond (equal ast (escape-simple (simple-escape-v))))

(test-lex
 plex-escape-sequence
 "w"
 :fail t)

(test-lex
 plex-escape-sequence
 "6"
 :cond (equal ast (escape-oct (oct-escape-one #\6))))

(test-lex
 plex-escape-sequence
 "68"
 :cond (equal ast (escape-oct (oct-escape-one #\6))))

(test-lex
 plex-escape-sequence
 "60"
 :cond (equal ast (escape-oct (oct-escape-two #\6 #\0))))

(test-lex
 plex-escape-sequence
 "601"
 :cond (equal ast (escape-oct (oct-escape-three #\6 #\0 #\1))))

(test-lex
 plex-escape-sequence
 "6011"
 :cond (equal ast (escape-oct (oct-escape-three #\6 #\0 #\1))))

(test-lex
 plex-escape-sequence
 "8"
 :fail t)

(test-lex
 plex-escape-sequence
 "xf8"
 :cond (equal ast (escape-hex (list #\f #\8))))

(test-lex
 plex-escape-sequence
 "x829s"
 :cond (equal ast (escape-hex (list #\8 #\2 #\9))))

(test-lex
 plex-escape-sequence
 "x"
 :fail t)

(test-lex
 plex-escape-sequence
 "x+"
 :fail t)

(test-lex
 plex-escape-sequence
 "uabBA"
 :cond (equal ast (escape-univ
                   (univ-char-name-locase-u (hex-quad #\a #\b #\B #\A)))))

(test-lex
 plex-escape-sequence
 "U744dD900"
 :cond (equal ast (escape-univ
                   (univ-char-name-upcase-u (hex-quad #\7 #\4 #\4 #\d)
                                            (hex-quad #\D #\9 #\0 #\0)))))

(test-lex
 plex-escape-sequence
 "u123"
 :fail t)

(test-lex
 plex-escape-sequence
 "U0000123"
 :fail t)

(test-lex
 plex-escape-sequence
 "%"
 :fail t)

(test-lex
 plex-escape-sequence
 "%"
 :gcc t
 :cond (equal ast (escape-simple (simple-escape-percent))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-*-c-char

(test-lex
 plex-*-c-char
 "a'"
 :cond (equal ast (list (c-char-char (char-code #\a)))))

(test-lex
 plex-*-c-char
 "\\a'"
 :cond (equal ast (list (c-char-escape (escape-simple (simple-escape-a))))))

(test-lex
 plex-*-c-char
 "&\\xf7'"
 :cond (equal ast (list (c-char-char (char-code #\&))
                        (c-char-escape (escape-hex (list #\f #\7))))))

(test-lex
 plex-*-c-char
 "\\1111'"
 :cond (equal ast (list (c-char-escape
                         (escape-oct (oct-escape-three #\1 #\1 #\1)))
                        (c-char-char (char-code #\1)))))

(test-lex
 plex-*-c-char
 "ABC'"
 :cond (and (equal ast (list (c-char-char (char-code #\A))
                             (c-char-char (char-code #\B))
                             (c-char-char (char-code #\C))))
            (equal pos/span (position 1 3))))

(test-lex
 plex-*-c-char
 "d\"q'"
 :cond (and (equal ast (list (c-char-char (char-code #\d))
                             (c-char-char (char-code #\"))
                             (c-char-char (char-code #\q))))
            (equal pos/span (position 1 3))))

(test-lex
 plex-*-c-char
 ""
 :fail t)

(test-lex
 plex-*-c-char
 "a"
 :fail t)

(test-lex
 plex-*-c-char
 "a\\'"
 :fail t)

(test-lex
 plex-*-c-char
 "a\\z'"
 :fail t)

(test-lex
 plex-*-c-char
 (list (char-code #\a) 10 (char-code #\b) (char-code #\'))
 :fail t)

(test-lex
 plex-*-c-char
 (list (char-code #\a) 13 (char-code #\b) (char-code #\'))
 :fail t)

(test-lex
 plex-*-c-char
 (list (char-code #\a) 13 10 (char-code #\'))
 :fail t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-*-s-char

(test-lex
 plex-*-s-char
 "p\""
 :cond (equal ast (list (s-char-char (char-code #\p)))))

(test-lex
 plex-*-s-char
 "'\""
 :cond (equal ast (list (s-char-char (char-code #\')))))

(test-lex
 plex-*-s-char
 "\\n\""
 :cond (equal ast (list (s-char-escape (escape-simple (simple-escape-n))))))

(test-lex
 plex-*-s-char
 "12\""
 :cond (equal ast (list (s-char-char (char-code #\1))
                        (s-char-char (char-code #\2)))))

(test-lex
 plex-*-s-char
 ""
 :fail t)

(test-lex
 plex-*-s-char
 "noclose"
 :fail t)

(test-lex
 plex-*-s-char
 "\\k\""
 :fail t)

(test-lex
 plex-*-s-char
 (list (char-code #\U) 10 (char-code #\"))
 :fail t)

(test-lex
 plex-*-s-char
 (list (char-code #\U) 13 (char-code #\"))
 :fail t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-*-h-char

(test-lex
 plex-*-h-char
 "abc>"
 :cond (equal ast (list (h-char (char-code #\a))
                        (h-char (char-code #\b))
                        (h-char (char-code #\c)))))

(test-lex
 plex-*-h-char
 "\">"
 :cond (equal ast (list (h-char (char-code #\")))))

(test-lex
 plex-*-h-char
 "'>"
 :cond (equal ast (list (h-char (char-code #\')))))

(test-lex
 plex-*-h-char
 "<>"
 :cond (equal ast (list (h-char (char-code #\<)))))

(test-lex
 plex-*-h-char
 ""
 :fail t)

(test-lex
 plex-*-h-char
 "noclose"
 :fail t)

(test-lex
 plex-*-h-char
 (list (char-code #\U) 10 (char-code #\>))
 :fail t)

(test-lex
 plex-*-h-char
 (list (char-code #\U) 13 (char-code #\>))
 :fail t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-*-q-char

(test-lex
 plex-*-q-char
 "abc\""
 :cond (equal ast (list (q-char (char-code #\a))
                        (q-char (char-code #\b))
                        (q-char (char-code #\c)))))

(test-lex
 plex-*-q-char
 ">\""
 :cond (equal ast (list (q-char (char-code #\>)))))

(test-lex
 plex-*-q-char
 "'\""
 :cond (equal ast (list (q-char (char-code #\')))))

(test-lex
 plex-*-q-char
 ""
 :fail t)

(test-lex
 plex-*-q-char
 "noclose"
 :fail t)

(test-lex
 plex-*-q-char
 (list (char-code #\U) 10 (char-code #\"))
 :fail t)

(test-lex
 plex-*-q-char
 (list (char-code #\U) 13 (char-code #\"))
 :fail t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-character-constant

(test-lex
 plex-character-constant
 "e'"
 :more-inputs (nil (pos 1 0))
 :cond (equal ast
              (plexeme-char
               (cconst nil
                       (list (c-char-char (char-code #\e)))))))

(test-lex
 plex-character-constant
 "\\aA'"
 :more-inputs ((cprefix-locase-u) (pos 1 0))
 :cond (equal ast
              (plexeme-char
               (cconst (cprefix-locase-u)
                       (list (c-char-escape (escape-simple (simple-escape-a)))
                             (c-char-char (char-code #\A)))))))

(test-lex
 plex-character-constant
 "''"
 :more-inputs (nil (pos 1 0))
 :fail t)

(test-lex
 plex-character-constant
 (list 10 (char-code #\'))
 :more-inputs (nil (pos 1 0))
 :fail t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-string-literal

(test-lex
 plex-string-literal
 "\""
 :more-inputs (nil (pos 1 0))
 :cond (equal ast
              (plexeme-string
               (stringlit nil nil))))

(test-lex
 plex-string-literal
 "helo\""
 :more-inputs ((eprefix-upcase-l) (pos 1 0))
 :cond (equal ast
              (plexeme-string
               (stringlit (eprefix-upcase-l)
                          (list (s-char-char (char-code #\h))
                                (s-char-char (char-code #\e))
                                (s-char-char (char-code #\l))
                                (s-char-char (char-code #\o)))))))

(test-lex
 plex-string-literal
 "wrong'"
 :more-inputs (nil (pos 1 0))
 :fail t)

(test-lex
 plex-string-literal
 (list 10 (char-code #\"))
 :more-inputs (nil (pos 1 0))
 :fail t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;l

; plex-header-name

(test-lex
 plex-header-name
 "<stdio.h>"
 :cond (equal ast
              (plexeme-header
               (header-name-angles (list (h-char (char-code #\s))
                                         (h-char (char-code #\t))
                                         (h-char (char-code #\d))
                                         (h-char (char-code #\i))
                                         (h-char (char-code #\o))
                                         (h-char (char-code #\.))
                                         (h-char (char-code #\h)))))))

(test-lex
 plex-header-name
 "\"parser.h\""
 :cond (equal ast
              (plexeme-header
               (header-name-quotes (list (q-char (char-code #\p))
                                         (q-char (char-code #\a))
                                         (q-char (char-code #\r))
                                         (q-char (char-code #\s))
                                         (q-char (char-code #\e))
                                         (q-char (char-code #\r))
                                         (q-char (char-code #\.))
                                         (q-char (char-code #\h)))))))

(test-lex
 plex-header-name
 ""
 :fail t)

(test-lex
 plex-header-name
 "noopen"
 :fail t)

(test-lex
 plex-header-name
 "<noclose"
 :fail t)

(test-lex
 plex-header-name
 "\"noclose"
 :fail t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-block-comment

(test-lex
 plex-block-comment
 "*/"
 :more-inputs ((pos 1 0))
 :cond (equal ast
              (plexeme-block-comment nil)))

(test-lex
 plex-block-comment
 "comment*/"
 :more-inputs ((pos 1 0))
 :cond (equal ast
              (plexeme-block-comment (acl2::string=>nats "comment"))))

(test-lex
 plex-block-comment
 "comment****/"
 :more-inputs ((pos 1 0))
 :cond (equal ast
              (plexeme-block-comment (acl2::string=>nats "comment***"))))

(test-lex
 plex-block-comment
 "/*comment*/"
 :more-inputs ((pos 1 0))
 :cond (equal ast
              (plexeme-block-comment (acl2::string=>nats "/*comment"))))

(test-lex
 plex-block-comment
 (append (acl2::string=>nats " This is a")
         (list 10)
         (acl2::string=>nats "multiline comment.")
         (list 10)
         (acl2::string=>nats "*/"))
 :more-inputs ((pos 1 0))
 :cond (equal ast
              (plexeme-block-comment
               (append (acl2::string=>nats " This is a")
                       (list 10)
                       (acl2::string=>nats "multiline comment.")
                       (list 10)))))

(test-lex
 plex-block-comment
 (append (acl2::string=>nats "// no special significance")
         (list 10)
         (acl2::string=>nats "*/"))
 :more-inputs ((pos 1 0))
 :cond (equal ast
              (plexeme-block-comment
               (append (acl2::string=>nats "// no special significance")
                       (list 10)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-line-comment

(test-lex
 plex-line-comment
 (list (char-code #\/) (char-code #\/) 10)
 :more-inputs ((pos 1 0) (pos 1 1))
 :index 2
 :cond (equal ast
              (plexeme-line-comment nil)))

(test-lex
 plex-line-comment
 (append (acl2::string=>nats "//comment") (list 10 13))
 :more-inputs ((pos 1 0) (pos 1 1))
 :index 2
 :cond (equal ast
              (plexeme-line-comment (acl2::string=>nats "comment"))))

(test-lex
 plex-line-comment
 (append (acl2::string=>nats "///* no special significance */") (list 13))
 :more-inputs ((pos 1 0) (pos 1 1))
 :index 2
 :cond (equal ast
              (plexeme-line-comment
               (acl2::string=>nats "/* no special significance */"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-spaces

(test-lex
 plex-spaces
 nil
 :more-inputs ((pos 1 0))
 :cond (equal ast (plexeme-spaces 1)))

(test-lex
 plex-spaces
 "a"
 :more-inputs ((pos 1 0))
 :cond (equal ast (plexeme-spaces 1)))

(test-lex
 plex-spaces
 "    "
 :more-inputs ((pos 1 0))
 :cond (equal ast (plexeme-spaces 5)))

(test-lex
 plex-spaces
 "   a"
 :more-inputs ((pos 1 0))
 :cond (equal ast (plexeme-spaces 4)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; plex-lexer

; no lexeme

(test-lex-lexeme
 nil
 :cond (equal ast nil))

(test-lex-lexeme-headerp
 nil
 :cond (equal ast nil))

; white space

(test-lex-lexeme
 " "
 :cond (equal ast (plexeme-spaces 1)))

(test-lex-lexeme
 "       "
 :cond (equal ast (plexeme-spaces 7)))

(test-lex-lexeme
 (list 9)
 :cond (equal ast (plexeme-horizontal-tab)))

(test-lex-lexeme
 (list 11)
 :cond (equal ast (plexeme-vertical-tab)))

(test-lex-lexeme
 (list 12)
 :cond (equal ast (plexeme-form-feed)))

(test-lex-lexeme
 (list 10)
 :cond (equal ast (plexeme-newline (newline-lf))))

(test-lex-lexeme
 (list 13)
 :cond (equal ast (plexeme-newline (newline-cr))))

(test-lex-lexeme
 (list 13 (char-code #\a))
 :cond (equal ast (plexeme-newline (newline-cr))))

(test-lex-lexeme
 (list 13 10)
 :cond (equal ast (plexeme-newline (newline-crlf))))

; preprocessing numbers

(test-lex-lexeme
 "124"
 :cond (equal ast (plexeme-number
                   (pnumber-number-digit
                    (pnumber-number-digit
                     (pnumber-digit #\1) #\2) #\4))))

(test-lex-lexeme
 "124e+"
 :cond (equal ast (plexeme-number
                   (pnumber-number-locase-e-sign
                    (pnumber-number-digit
                     (pnumber-number-digit
                      (pnumber-digit #\1) #\2) #\4)
                    (sign-plus)))))

(test-lex-lexeme
 "124x"
 :cond (equal ast (plexeme-number
                   (pnumber-number-nondigit
                    (pnumber-number-digit
                     (pnumber-number-digit
                      (pnumber-digit #\1) #\2) #\4)
                    #\x))))

(test-lex-lexeme
 ".5"
 :cond (equal ast (plexeme-number
                   (pnumber-dot-digit #\5))))

; identifiers

(test-lex-lexeme
 "x"
 :cond (equal ast (plexeme-ident (ident "x"))))

(test-lex-lexeme
 "an_identifier_88"
 :cond (equal ast (plexeme-ident (ident "an_identifier_88"))))

(test-lex-lexeme
 "u"
 :cond (equal ast (plexeme-ident (ident "u"))))

(test-lex-lexeme
 "u*"
 :cond (equal ast (plexeme-ident (ident "u"))))

(test-lex-lexeme
 "U*"
 :cond (equal ast (plexeme-ident (ident "U"))))

(test-lex-lexeme
 "L*"
 :cond (equal ast (plexeme-ident (ident "L"))))

(test-lex-lexeme
 "u8*"
 :cond (equal ast (plexeme-ident (ident "u8"))))

(test-lex-lexeme
 "u8'"
 :cond (equal ast (plexeme-ident (ident "u8"))))

; character constants

(test-lex-lexeme
 "'k'"
 :cond (equal ast (plexeme-char
                   (cconst nil (list (c-char-char (char-code #\k)))))))

(test-lex-lexeme
 "U'\\n'" ; lexer sees just one \
 :cond (equal ast (plexeme-char
                   (cconst (cprefix-upcase-u)
                           (list (c-char-escape
                                  (escape-simple (simple-escape-n))))))))

; string literals

(test-lex-lexeme
 "\"hello\""
 :cond (equal ast (plexeme-string
                   (stringlit nil (list (s-char-char (char-code #\h))
                                        (s-char-char (char-code #\e))
                                        (s-char-char (char-code #\l))
                                        (s-char-char (char-code #\l))
                                        (s-char-char (char-code #\o)))))))

(test-lex-lexeme
 "u8\"a\\123b\"" ; lexer sees just one \ before 123
 :cond (equal ast (plexeme-string
                   (stringlit (eprefix-locase-u8)
                              (list (s-char-char (char-code #\a))
                                    (s-char-escape
                                     (escape-oct
                                      (oct-escape-three #\1 #\2 #\3)))
                                    (s-char-char (char-code #\b)))))))

; punctuators

(test-lex-lexeme
 "[ "
 :cond (equal ast (plexeme-punctuator "[")))

(test-lex-lexeme
 "] "
 :cond (equal ast (plexeme-punctuator "]")))

(test-lex-lexeme
 "( "
 :cond (equal ast (plexeme-punctuator "(")))

(test-lex-lexeme
 ") "
 :cond (equal ast (plexeme-punctuator ")")))

(test-lex-lexeme
 "{ "
 :cond (equal ast (plexeme-punctuator "{")))

(test-lex-lexeme
 "} "
 :cond (equal ast (plexeme-punctuator "}")))

(test-lex-lexeme
 ". "
 :cond (equal ast (plexeme-punctuator ".")))

(test-lex-lexeme
 ".. "
 :cond (equal ast (plexeme-punctuator ".")))

(test-lex-lexeme
 "... "
 :cond (equal ast (plexeme-punctuator "...")))

(test-lex-lexeme
 "- "
 :cond (equal ast (plexeme-punctuator "-")))

(test-lex-lexeme
 "-- "
 :cond (equal ast (plexeme-punctuator "--")))

(test-lex-lexeme
 "-= "
 :cond (equal ast (plexeme-punctuator "-=")))

(test-lex-lexeme
 "-> "
 :cond (equal ast (plexeme-punctuator "->")))

(test-lex-lexeme
 "-+ "
 :cond (equal ast (plexeme-punctuator "-")))

(test-lex-lexeme
 "+ "
 :cond (equal ast (plexeme-punctuator "+")))

(test-lex-lexeme
 "++ "
 :cond (equal ast (plexeme-punctuator "++")))

(test-lex-lexeme
 "+= "
 :cond (equal ast (plexeme-punctuator "+=")))

(test-lex-lexeme
 "+- "
 :cond (equal ast (plexeme-punctuator "+")))

(test-lex-lexeme
 "& "
 :cond (equal ast (plexeme-punctuator "&")))

(test-lex-lexeme
 "&& "
 :cond (equal ast (plexeme-punctuator "&&")))

(test-lex-lexeme
 "&= "
 :cond (equal ast (plexeme-punctuator "&=")))

(test-lex-lexeme
 "&| "
 :cond (equal ast (plexeme-punctuator "&")))

(test-lex-lexeme
 "* "
 :cond (equal ast (plexeme-punctuator "*")))

(test-lex-lexeme
 "*= "
 :cond (equal ast (plexeme-punctuator "*=")))

(test-lex-lexeme
 "** "
 :cond (equal ast (plexeme-punctuator "*")))

(test-lex-lexeme
 "~ "
 :cond (equal ast (plexeme-punctuator "~")))

(test-lex-lexeme
 "! "
 :cond (equal ast (plexeme-punctuator "!")))

(test-lex-lexeme
 "!= "
 :cond (equal ast (plexeme-punctuator "!=")))

(test-lex-lexeme
 "!! "
 :cond (equal ast (plexeme-punctuator "!")))

(test-lex-lexeme
 "/ "
 :cond (equal ast (plexeme-punctuator "/")))

(test-lex-lexeme
 "/= "
 :cond (equal ast (plexeme-punctuator "/=")))

(test-lex-lexeme
 "/- "
 :cond (equal ast (plexeme-punctuator "/")))

(test-lex-lexeme
 "% "
 :cond (equal ast (plexeme-punctuator "%")))

(test-lex-lexeme
 "%= "
 :cond (equal ast (plexeme-punctuator "%=")))

(test-lex-lexeme
 "%> "
 :cond (equal ast (plexeme-punctuator "%>")))

(test-lex-lexeme
 "%: "
 :cond (equal ast (plexeme-punctuator "%:")))

(test-lex-lexeme
 "%:%: "
 :cond (equal ast (plexeme-punctuator "%:%:")))

(test-lex-lexeme
 "%. "
 :cond (equal ast (plexeme-punctuator "%")))

(test-lex-lexeme
 "%:%. "
 :cond (equal ast (plexeme-punctuator "%:")))

(test-lex-lexeme
 "< "
 :cond (equal ast (plexeme-punctuator "<")))

(test-lex-lexeme
 "<< "
 :cond (equal ast (plexeme-punctuator "<<")))

(test-lex-lexeme
 "<= "
 :cond (equal ast (plexeme-punctuator "<=")))

(test-lex-lexeme
 "<<= "
 :cond (equal ast (plexeme-punctuator "<<=")))

(test-lex-lexeme
 "<: "
 :cond (equal ast (plexeme-punctuator "<:")))

(test-lex-lexeme
 "<% "
 :cond (equal ast (plexeme-punctuator "<%")))

(test-lex-lexeme
 "<- "
 :cond (equal ast (plexeme-punctuator "<")))

(test-lex-lexeme
 "> "
 :cond (equal ast (plexeme-punctuator ">")))

(test-lex-lexeme
 ">> "
 :cond (equal ast (plexeme-punctuator ">>")))

(test-lex-lexeme
 ">= "
 :cond (equal ast (plexeme-punctuator ">=")))

(test-lex-lexeme
 ">>= "
 :cond (equal ast (plexeme-punctuator ">>=")))

(test-lex-lexeme
 ">- "
 :cond (equal ast (plexeme-punctuator ">")))

(test-lex-lexeme
 "= "
 :cond (equal ast (plexeme-punctuator "=")))

(test-lex-lexeme
 "== "
 :cond (equal ast (plexeme-punctuator "==")))

(test-lex-lexeme
 "=+ "
 :cond (equal ast (plexeme-punctuator "=")))

(test-lex-lexeme
 "^ "
 :cond (equal ast (plexeme-punctuator "^")))

(test-lex-lexeme
 "^= "
 :cond (equal ast (plexeme-punctuator "^=")))

(test-lex-lexeme
 "^^ "
 :cond (equal ast (plexeme-punctuator "^")))

(test-lex-lexeme
 "| "
 :cond (equal ast (plexeme-punctuator "|")))

(test-lex-lexeme
 "|| "
 :cond (equal ast (plexeme-punctuator "||")))

(test-lex-lexeme
 "|= "
 :cond (equal ast (plexeme-punctuator "|=")))

(test-lex-lexeme
 "|& "
 :cond (equal ast (plexeme-punctuator "|")))

(test-lex-lexeme
 "? "
 :cond (equal ast (plexeme-punctuator "?")))

(test-lex-lexeme
 "?? "
 :cond (equal ast (plexeme-punctuator "?")))

(test-lex-lexeme
 ": "
 :cond (equal ast (plexeme-punctuator ":")))

(test-lex-lexeme
 ":> "
 :cond (equal ast (plexeme-punctuator ":>")))

(test-lex-lexeme
 ":: "
 :cond (equal ast (plexeme-punctuator ":")))

(test-lex-lexeme
 "; "
 :cond (equal ast (plexeme-punctuator ";")))

(test-lex-lexeme
 ";; "
 :cond (equal ast (plexeme-punctuator ";")))

(test-lex-lexeme
 ", "
 :cond (equal ast (plexeme-punctuator ",")))

(test-lex-lexeme
 ",, "
 :cond (equal ast (plexeme-punctuator ",")))

(test-lex-lexeme
 "# "
 :cond (equal ast (plexeme-punctuator "#")))

(test-lex-lexeme
 "## "
 :cond (equal ast (plexeme-punctuator "##")))

(test-lex-lexeme
 "#. "
 :cond (equal ast (plexeme-punctuator "#")))

(test-lex-lexeme
 "<not-header>"
 :cond (equal ast (plexeme-punctuator "<")))

; comments

(test-lex-lexeme
 "/* multi
   * line
   * comment
   */"
 :cond (equal ast (plexeme-block-comment
                   (append (acl2::string=>nats " multi")
                           (list 10)
                           (acl2::string=>nats "   * line")
                           (list 10)
                           (acl2::string=>nats "   * comment")
                           (list 10)
                           (acl2::string=>nats "   ")))))

(test-lex-lexeme
 "// single line comment
  "
 :cond (equal ast (plexeme-line-comment
                   (acl2::string=>nats " single line comment"))))

; header names

(test-lex-lexeme-headerp
 "\"hello\""
 :cond (equal ast (plexeme-header
                   (header-name-quotes
                    (list (q-char (char-code #\h))
                          (q-char (char-code #\e))
                          (q-char (char-code #\l))
                          (q-char (char-code #\l))
                          (q-char (char-code #\o)))))))

(test-lex-lexeme-headerp
 "<hello>"
 :cond (equal ast (plexeme-header
                   (header-name-angles
                    (list (q-char (char-code #\h))
                          (q-char (char-code #\e))
                          (q-char (char-code #\l))
                          (q-char (char-code #\l))
                          (q-char (char-code #\o)))))))

; other

(test-lex-lexeme
 (acl2::string=>nats "𝅘𝅥𝅮") ; 4-byte UTF-8 encoding of musical symbol eighth note
 :cond (equal ast (plexeme-other 119136)))
