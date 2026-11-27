; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "../lexing-uniqueness")
(include-book "../lexer")

; Tests of lexeme-cst-list->strings,
; applied to the CSTs that the (certified) lexer returns:
; the result has the string of each lexeme, in order,
; with the boundaries between the lexemes.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun strings-to-code-lists (strings)
  (declare (xargs :guard (string-listp strings)))
  (if (endp strings)
      nil
    (cons (acl2::string=>nats (car strings))
          (strings-to-code-lists (cdr strings)))))

; The first argument is the input;
; the others are the expected lexemes, as ACL2 strings (ASCII only).

(defmacro test-lexeme-strings (string &rest strings)
  `(assert-event
    (equal (lexeme-cst-list->strings (lexemize-rust-from-string ,string))
           ',(strings-to-code-lists strings))))

(test-lexeme-strings "")
(test-lexeme-strings "a" "a")
(test-lexeme-strings "a+b" "a" "+" "b")
(test-lexeme-strings "a + b" "a" " " "+" " " "b")
(test-lexeme-strings "x<<=1.5" "x" "<<=" "1.5")
(test-lexeme-strings "a/* b */c" "a" "/* b */" "c")
(test-lexeme-strings "r#fn 'a" "r#fn" " " "'a")
(test-lexeme-strings "\"a b\";" "\"a b\"" ";")
(test-lexeme-strings "\"a b\"c" "\"a b\"c") ; c is a suffix

; A lexeme whose string has two CSTs (see the lexing-uniqueness topic):
; the lexer returns one of them, and the string is the same for both.

(test-lexeme-strings "1e1_2" "1e1_2")

; The result has one string for each tree.

(assert-event
 (equal (len (lexeme-cst-list->strings (lexemize-rust-from-string "a b")))
        3))

; The function does not append the strings:
; two lists of trees that cover the same characters, split differently,
; give different results.

(assert-event
 (b* ((trees1 (list (abnf::tree-leafterm (list 97 98))
                    (abnf::tree-leafterm (list 99))))
      (trees2 (list (abnf::tree-leafterm (list 97))
                    (abnf::tree-leafterm (list 98 99)))))
   (and (equal (abnf::tree-list->string trees1)
               (abnf::tree-list->string trees2))
        (equal (lexeme-cst-list->strings trees1)
               '((97 98) (99)))
        (equal (lexeme-cst-list->strings trees2)
               '((97) (98 99))))))
