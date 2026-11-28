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
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

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
    "This book has the cases of whitespace and of comments.
     The lexer chooses the kind of a comment from its first characters,
     and its choice may differ from the kind of the CST:
     if the CST is the line comment @('//')
     and the remaining input starts with @('!'),
     the lexer lexes an inner line doc comment, which is longer.
     For block comments, the case rests on [SC2]:
     a valid lexeme CST whose string starts with @('/*')
     is one complete block comment,
     and the lexer takes exactly that comment.
     The case of tokens, and the theorem for the lexer as a whole,
     are not here yet."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Whitespace.

; The lexer tries whitespace first,
; and takes all the whitespace that it finds.

(defruledl lex-lexeme-when-whitespace
  (implies (cst-matchp tree "whitespace")
           (<= (len (mv-nth 1 (lex-lexeme
                               (append (abnf::tree->string tree) rest))))
               (len rest)))
  :rule-classes :linear
  :enable (lex-lexeme
           lex-whitespace-when-tree-match))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Line comments: the lexing functions.

; On an input that starts with //,
; the lexer chooses among the three kinds of line comments
; by the characters that follow:
; //! starts an inner line doc comment;
; /// starts an outer line doc comment, unless a fourth / follows;
; anything else starts a plain line comment.
; The first three theorems say, for each kind,
; that the lexer then leaves what the function for that kind leaves.
; Whitespace does not start with a "/",
; and the lexer looks for a comment before it lexes a token.

(local
 (deftheory lexeme-to-comment
   '(lex-lexeme
     lex-comment
     lex-whitespace
     lex-whitespace-char
     abnf::parse-next
     abnf::not-reserrp-when-treep)))

(defruledl lex-lexeme-when-inner-line-doc-ahead
  (implies (and (nat-listp input)
                (prefixp '(#x2f #x2f #x21) input)
                (not (reserrp (mv-nth 0 (lex-lexeme input)))))
           (and (not (reserrp (mv-nth 0 (lex-inner-line-doc input))))
                (equal (mv-nth 1 (lex-lexeme input))
                       (mv-nth 1 (lex-inner-line-doc input)))))
  :enable lexeme-to-comment)

(defruledl lex-lexeme-when-outer-line-doc-ahead
  (implies (and (nat-listp input)
                (prefixp '(#x2f #x2f #x2f) input)
                (not (prefixp '(#x2f #x2f #x2f #x2f) input))
                (not (reserrp (mv-nth 0 (lex-lexeme input)))))
           (and (not (reserrp (mv-nth 0 (lex-outer-line-doc input))))
                (equal (mv-nth 1 (lex-lexeme input))
                       (mv-nth 1 (lex-outer-line-doc input)))))
  :enable lexeme-to-comment)

(defruledl lex-lexeme-when-line-comment-ahead
  (implies (and (nat-listp input)
                (prefixp '(#x2f #x2f) input)
                (not (prefixp '(#x2f #x2f #x21) input))
                (or (not (prefixp '(#x2f #x2f #x2f) input))
                    (prefixp '(#x2f #x2f #x2f #x2f) input))
                (not (reserrp (mv-nth 0 (lex-lexeme input)))))
           (and (not (reserrp (mv-nth 0 (lex-line-comment input))))
                (equal (mv-nth 1 (lex-lexeme input))
                       (mv-nth 1 (lex-line-comment input)))))
  :enable lexeme-to-comment)

(local
 (deftheory lexeme-line-comment-choice
   '(lex-lexeme-when-inner-line-doc-ahead
     lex-lexeme-when-outer-line-doc-ahead
     lex-lexeme-when-line-comment-ahead)))

; Each kind of line comment takes at least its opening characters:
; three for the doc comments, two for a plain line comment,
; and four for a plain line comment that starts with ////.

(defruledl len-of-lex-inner-line-doc-bound
  (b* (((mv tree rest-input) (lex-inner-line-doc input)))
    (implies (and (nat-listp input)
                  (not (reserrp tree)))
             (<= (+ 3 (len rest-input)) (len input))))
  :rule-classes :linear
  :enable (lex-inner-line-doc
           parse-ichars-when-caseless-chars
           nfix))

(defruledl len-of-lex-outer-line-doc-bound
  (b* (((mv tree rest-input) (lex-outer-line-doc input)))
    (implies (and (nat-listp input)
                  (not (reserrp tree)))
             (<= (+ 3 (len rest-input)) (len input))))
  :rule-classes :linear
  :enable (lex-outer-line-doc
           parse-ichars-when-caseless-chars
           nfix))

(defruledl len-of-lex-line-comment-bound
  (b* (((mv tree rest-input) (lex-line-comment input)))
    (implies (and (nat-listp input)
                  (not (reserrp tree)))
             (<= (+ 2 (len rest-input)) (len input))))
  :rule-classes :linear
  :enable (lex-line-comment
           parse-ichars-when-caseless-chars
           nfix))

(defruledl len-of-lex-line-comment-bound-when-four-slashes
  (b* (((mv tree rest-input) (lex-line-comment input)))
    (implies (and (nat-listp input)
                  (prefixp '(#x2f #x2f #x2f #x2f) input)
                  (not (reserrp tree)))
             (<= (+ 4 (len rest-input)) (len input))))
  :rule-classes :linear
  :enable (lex-line-comment
           lex-not-slash-bang-lf-when-slash
           parse-ichars-when-caseless-chars
           nthcdr
           nfix))

; So, whichever kind the lexer chooses,
; it takes at least two characters of an input that starts with //,
; and at least three of an input that starts with ///.

(defruledl len-of-lex-lexeme-bound-when-two-slashes
  (implies (and (nat-listp input)
                (prefixp '(#x2f #x2f) input)
                (not (reserrp (mv-nth 0 (lex-lexeme input)))))
           (<= (+ 2 (len (mv-nth 1 (lex-lexeme input))))
               (len input)))
  :rule-classes :linear
  :cases ((prefixp '(#x2f #x2f #x21) input)
          (and (prefixp '(#x2f #x2f #x2f) input)
               (not (prefixp '(#x2f #x2f #x2f #x2f) input))))
  :enable (lexeme-line-comment-choice
           len-of-lex-inner-line-doc-bound
           len-of-lex-outer-line-doc-bound
           len-of-lex-line-comment-bound))

(defruledl len-of-lex-lexeme-bound-when-three-slashes
  (implies (and (nat-listp input)
                (prefixp '(#x2f #x2f #x2f) input)
                (not (reserrp (mv-nth 0 (lex-lexeme input)))))
           (<= (+ 3 (len (mv-nth 1 (lex-lexeme input))))
               (len input)))
  :rule-classes :linear
  :cases ((prefixp '(#x2f #x2f #x2f #x2f) input))
  :enable (lexeme-line-comment-choice
           len-of-lex-outer-line-doc-bound
           len-of-lex-line-comment-bound-when-four-slashes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Line comments: the trees.

; For a tree of each kind of line comment, followed by any remaining input.
; The start of the string of the tree
; (see start-of-tree->string-when-line-comment and its companions)
; says which kind the lexer chooses.
; Where the lexer chooses the kind of the tree,
; the theorem for the function of that kind applies.
; The lexer chooses another kind only when
; the string of the tree is just the opening characters,
; // or ///, and the remaining input starts with ! or /;
; then the lexer takes at least those opening characters.
; (The tests on the start of the input are opened into
; tests on its first characters,
; which the rules about the first characters of an append reduce to
; the first characters of the string of the tree.)

(defruledl lex-lexeme-when-line-comment
  (implies (and (cst-matchp tree "line-comment")
                (nat-listp rest)
                (not (reserrp
                      (mv-nth 0 (lex-lexeme
                                 (append (abnf::tree->string tree) rest))))))
           (<= (len (mv-nth 1 (lex-lexeme
                               (append (abnf::tree->string tree) rest))))
               (len rest)))
  :rule-classes :linear
  :cases ((consp (cddr (abnf::tree->string tree))))
  :enable (cst-matchp$
           lexeme-line-comment-choice
           start-of-tree->string-when-line-comment
           lex-line-comment-when-tree-match
           len-of-lex-lexeme-bound-when-two-slashes)
  :disable acl2::prefixp-of-append-arg2)

(defruledl lex-lexeme-when-outer-line-doc
  (implies (and (cst-matchp tree "outer-line-doc")
                (nat-listp rest)
                (not (reserrp
                      (mv-nth 0 (lex-lexeme
                                 (append (abnf::tree->string tree) rest))))))
           (<= (len (mv-nth 1 (lex-lexeme
                               (append (abnf::tree->string tree) rest))))
               (len rest)))
  :rule-classes :linear
  :cases ((consp (cdddr (abnf::tree->string tree))))
  :enable (cst-matchp$
           lexeme-line-comment-choice
           start-of-tree->string-when-outer-line-doc
           lex-outer-line-doc-when-tree-match
           len-of-lex-lexeme-bound-when-three-slashes)
  :disable acl2::prefixp-of-append-arg2)

(defruledl lex-lexeme-when-inner-line-doc
  (implies (and (cst-matchp tree "inner-line-doc")
                (nat-listp rest)
                (not (reserrp
                      (mv-nth 0 (lex-lexeme
                                 (append (abnf::tree->string tree) rest))))))
           (<= (len (mv-nth 1 (lex-lexeme
                               (append (abnf::tree->string tree) rest))))
               (len rest)))
  :rule-classes :linear
  :enable (cst-matchp$
           lexeme-line-comment-choice
           start-of-tree->string-when-inner-line-doc
           lex-inner-line-doc-when-tree-match)
  :disable acl2::prefixp-of-append-arg2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Comments.

; A comment is of one of six kinds.
; The three kinds of line comments are above.
; The grammar rules for the three kinds of block comments overapproximate;
; a valid lexeme CST whose string starts with /* also satisfies [SC2]:
; its string is one complete block comment.
; On an input that starts with a complete block comment,
; the lexer takes exactly that comment.
; So the hypothesis for block comments is that side condition,
; as lexeme-cst-okp states it.

(defruledl lex-lexeme-when-comment
  (implies (and (cst-matchp tree "comment")
                (implies (prefixp '(#x2f #x2a) (abnf::tree->string tree))
                         (block-comment-string-p (abnf::tree->string tree)))
                (nat-listp rest)
                (not (reserrp
                      (mv-nth 0 (lex-lexeme
                                 (append (abnf::tree->string tree) rest))))))
           (<= (len (mv-nth 1 (lex-lexeme
                               (append (abnf::tree->string tree) rest))))
               (len rest)))
  :rule-classes :linear
  :enable (tree-matching
           lex-lexeme-when-line-comment
           lex-lexeme-when-outer-line-doc
           lex-lexeme-when-inner-line-doc
           start-of-tree->string-when-block-comment
           start-of-tree->string-when-outer-block-doc
           start-of-tree->string-when-inner-block-doc
           rest-input-of-lex-lexeme-when-block-comment-string-p)
  :expand ((:free (element rules)
            (abnf::tree-match-element-p tree element rules))
           (abnf::tree-terminatedp tree)))
