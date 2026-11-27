; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "lexer-tree-completeness")

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lexer-maximal-munch
  :parents (lexer-correctness)
  :short "Towards the theorem that the lexer satisfies maximal munch [SC1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorems in @(see lexer-correctness) say that
     the lexemes that the lexer returns satisfy
     every part of the specification @(tsee lexing-okp)
     other than maximal munch,
     which is the condition @(tsee lexeme-cst-maximal-p) on each lexeme:
     no valid lexeme CST covers the string of the lexeme
     and more of the input after it.")
   (xdoc::p
    "Maximal munch follows from this property of @(tsee lex-lexeme):
     on an input that consists of the string of a valid lexeme CST
     followed by any remaining input,
     the function, if it does not fail, leaves at most the remaining input.
     The lexeme that it returns is then at least as long as
     the string of that CST.
     The property is proved by cases on the kind of lexeme that the CST is.
     Each case rests on
     the order in which the lexer tries the kinds of lexemes,
     and on the theorem in @(see lexer-tree-completeness)
     for the function that lexes that kind.")
   (xdoc::p
    "This book has the case of block comments,
     which rests on [SC2] instead:
     a valid lexeme CST whose string starts with @('/*')
     is one complete block comment,
     and the lexer takes exactly that comment.
     The other cases, and the theorem for the lexer as a whole,
     are not here yet."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Block comments.

; The grammar rules for block comments overapproximate;
; a valid lexeme CST whose string starts with /* also satisfies [SC2]:
; its string is one complete block comment.
; On an input that starts with a complete block comment,
; the lexer takes exactly that comment.
; So, for this kind of lexeme, the lexer leaves exactly the remaining input.
; The hypothesis is about the string of the tree:
; the trees for the three kinds of block comments have such strings
; (see slash-star-prefixp-of-tree->string-when-block-comment
; and its companions).

(defruledl lex-lexeme-when-lexeme-cst-okp-and-slash-star
  (implies (and (lexeme-cst-okp tree)
                (prefixp (list #x2f #x2a) (abnf::tree->string tree))
                (not (reserrp
                      (mv-nth 0 (lex-lexeme
                                 (append (abnf::tree->string tree) rest))))))
           (equal (mv-nth 1 (lex-lexeme
                             (append (abnf::tree->string tree) rest)))
                  (nat-list-fix rest)))
  :enable (lexeme-cst-okp
           lexeme-cst-p
           cst-matchp$
           rest-input-of-lex-lexeme-when-block-comment-string-p))
