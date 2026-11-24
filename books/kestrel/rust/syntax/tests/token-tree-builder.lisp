; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "../tokenizer")
(include-book "../token-tree-builder")

; Tests of the token-tree builder, on the tokens of source text.
; We check the shape of the trees, the errors and where they are,
; the spans of the delimiters,
; and that flattening the trees gives back the tokens.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Abbreviations for the tests.

(defmacro toks (string)
  `(tokenize-rust-from-string ,string (rust::edition-2024) "test.rs"))

; The token trees of a string, or an error
; (from the tokenizer or from the builder).

(define trees ((string stringp))
  (b* ((tokens (toks string))
       ((when (reserrp tokens)) tokens))
    (build-token-trees tokens))
  :guard-hints
  (("Goal" :in-theory (enable token+span-listp-when-result-not-error))))

; The shape of a token tree, without spans:
; a leaf is its token,
; and a delimited group is the kind of its delimiters
; (:paren, :bracket, or :brace) consed to the shapes of its trees.

(defines token-tree-shapes

  (define token-tree-shape ((tree token-treep))
    :measure (token-tree-count tree)
    (token-tree-case
     tree
     :leaf (token+span->token tree.token)
     :delimited (cons (delim-kind tree.delim)
                      (token-tree-list-shape tree.trees))))

  (define token-tree-list-shape ((trees token-tree-listp))
    :measure (token-tree-list-count trees)
    (if (endp trees)
        nil
      (cons (token-tree-shape (car trees))
            (token-tree-list-shape (cdr trees))))))

(defmacro test-trees (string expected)
  `(assert-event
    (b* ((trees (trees ,string)))
      (and (not (reserrp trees))
           (equal (token-tree-list-shape trees) ,expected)))))

; What an error of the builder holds:
; a keyword for the kind of error, and the delimiter tokens at fault.

(defun trees-error (x)
  (and (reserrp x)
       (cadr (car (fty::reserr->info x)))))

(defmacro test-trees-fail (string kind)
  `(assert-event (equal (car (trees-error (trees ,string))) ,kind)))

; The column where a token with span starts.

(defun start-column (token+span)
  (position->column (span->start (token+span->span token+span))))

; Tokens used in several tests.

(defconst *a* (token-ident "a" nil))
(defconst *b* (token-ident "b" nil))
(defconst *c* (token-ident "c" nil))
(defconst *comma* (token-punct ","))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; No tokens, no trees.

(test-trees "" nil)
(test-trees " " nil)
(test-trees "// comment" nil)
(test-trees "/* ( */" nil)

; Leaves.

(test-trees "a" (list *a*))
(test-trees "a b c" (list *a* *b* *c*))
(test-trees "fn" (list (token-keyword "fn")))

; Empty groups, of each kind.

(test-trees "()" (list (list :paren)))
(test-trees "[]" (list (list :bracket)))
(test-trees "{}" (list (list :brace)))
(test-trees "( )" (list (list :paren)))

; Groups with contents.

(test-trees "(a)" (list (list :paren *a*)))
(test-trees "[a, b]" (list (list :bracket *a* *comma* *b*)))
(test-trees "{a b c}" (list (list :brace *a* *b* *c*)))

; Groups in sequence, and around leaves.

(test-trees "(){}[]" (list (list :paren) (list :brace) (list :bracket)))
(test-trees "a(b)c" (list *a* (list :paren *b*) *c*))
(test-trees "(a)(b)" (list (list :paren *a*) (list :paren *b*)))

; Nested groups.

(test-trees "(())" (list (list :paren (list :paren))))
(test-trees "([{}])" (list (list :paren (list :bracket (list :brace)))))
(test-trees "((((a))))"
            (list (list :paren (list :paren (list :paren (list :paren *a*))))))
(test-trees "a(b, [c, {a}])"
            (list *a*
                  (list :paren
                        *b* *comma*
                        (list :bracket
                              *c* *comma*
                              (list :brace *a*)))))
(test-trees "(a)[(b){c}]"
            (list (list :paren *a*)
                  (list :bracket
                        (list :paren *b*)
                        (list :brace *c*))))

; A function, and a macro definition.

(test-trees "fn a() { b!(c); }"
            (list (token-keyword "fn")
                  *a*
                  (list :paren)
                  (list :brace
                        *b*
                        (token-punct "!")
                        (list :paren *c*)
                        (token-punct ";"))))

(test-trees "macro_rules! a { ($b:tt) => { $b } }"
            (list (token-ident "macro_rules" nil)
                  (token-punct "!")
                  *a*
                  (list :brace
                        (list :paren
                              (token-punct "$")
                              *b*
                              (token-punct ":")
                              (token-ident "tt" nil))
                        (token-punct "=>")
                        (list :brace
                              (token-punct "$")
                              *b*))))

; Angle brackets are punctuation, not delimiters;
; a punctuation token of several characters is one leaf.

(test-trees "a<b<c>>"
            (list *a* (token-punct "<") *b* (token-punct "<") *c*
                  (token-punct ">>")))
(test-trees "a < (b >> c)"
            (list *a*
                  (token-punct "<")
                  (list :paren *b* (token-punct ">>") *c*)))

; A doc comment is a leaf.

(test-trees "/** a */ (b)"
            (list (token-doc-comment (doc-style-outer) t " a ")
                  (list :paren *b*)))

; Delimiter characters in literals and comments are not delimiters.

(test-trees "\"(\""
            (list (token-lit (lit-str (make-str-lit :kind (str-kind-plain)
                                                    :raw nil
                                                    :text "("
                                                    :suffix "")))))
(test-trees "')'"
            (list (token-lit (lit-char (make-char-lit :byte nil
                                                      :text ")"
                                                      :suffix "")))))
(test-trees "(a /* ] */ b) // }"
            (list (list :paren *a* *b*)))
(test-trees "[\"]\"]"
            (list (list :bracket
                        (token-lit (lit-str (make-str-lit
                                             :kind (str-kind-plain)
                                             :raw nil
                                             :text "]"
                                             :suffix ""))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; An opening delimiter whose group is still open at the end.

(test-trees-fail "(" :unclosed-delimiter)
(test-trees-fail "[" :unclosed-delimiter)
(test-trees-fail "{" :unclosed-delimiter)
(test-trees-fail "(a" :unclosed-delimiter)
(test-trees-fail "((a)" :unclosed-delimiter)
(test-trees-fail "(a) (" :unclosed-delimiter)
(test-trees-fail "fn a() { b" :unclosed-delimiter)
(test-trees-fail "{[(" :unclosed-delimiter)

; A closing delimiter when no group is open.

(test-trees-fail ")" :unexpected-closing-delimiter)
(test-trees-fail "]" :unexpected-closing-delimiter)
(test-trees-fail "}" :unexpected-closing-delimiter)
(test-trees-fail "a)" :unexpected-closing-delimiter)
(test-trees-fail "())" :unexpected-closing-delimiter)
(test-trees-fail "(a) ] (b)" :unexpected-closing-delimiter)
(test-trees-fail "fn a() {} }" :unexpected-closing-delimiter)

; A closing delimiter of another kind than the group that is open.

(test-trees-fail "(]" :mismatched-closing-delimiter)
(test-trees-fail "(}" :mismatched-closing-delimiter)
(test-trees-fail "[)" :mismatched-closing-delimiter)
(test-trees-fail "[}" :mismatched-closing-delimiter)
(test-trees-fail "{)" :mismatched-closing-delimiter)
(test-trees-fail "{]" :mismatched-closing-delimiter)
(test-trees-fail "{(})" :mismatched-closing-delimiter)
(test-trees-fail "(a]b)" :mismatched-closing-delimiter)
(test-trees-fail "fn a() { (b + c }" :mismatched-closing-delimiter)

; The first error is the one reported.

(test-trees-fail "(] )" :mismatched-closing-delimiter)
(test-trees-fail ") (" :unexpected-closing-delimiter)
(test-trees-fail "(a) ) (" :unexpected-closing-delimiter)

; An error of the tokenizer is not an error of the builder.

(assert-event (reserrp (trees "(\"")))
(assert-event (not (trees-error (trees "()"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Where the errors are: an error holds the delimiter tokens at fault.

; The opening delimiter that is not closed is the innermost one.

(assert-event
 (b* (((list kind open) (trees-error (trees "a { [ b (c"))))
   (and (equal kind :unclosed-delimiter)
        (equal (token+span->token open) (token-open-delim (delim-paren)))
        (equal (start-column open) 8))))

; The closing delimiter that closes nothing.

(assert-event
 (b* (((list kind close) (trees-error (trees "(a) b ] c"))))
   (and (equal kind :unexpected-closing-delimiter)
        (equal (token+span->token close) (token-close-delim (delim-bracket)))
        (equal (start-column close) 6))))

; The opening delimiter and the closing delimiter that do not match.

(assert-event
 (b* (((list kind open close) (trees-error (trees "a (b [c) ]"))))
   (and (equal kind :mismatched-closing-delimiter)
        (equal (token+span->token open) (token-open-delim (delim-bracket)))
        (equal (start-column open) 5)
        (equal (token+span->token close) (token-close-delim (delim-paren)))
        (equal (start-column close) 7))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A delimited group records the spans of its two delimiters.

(assert-event
 (b* ((trees (trees "a (b
  c) d"))
      ((when (reserrp trees)) nil)
      ((list & group &) trees)
      ((unless (token-tree-case group :delimited)) nil)
      (open (token-tree-delimited->open-span group))
      (close (token-tree-delimited->close-span group)))
   (and (equal (position->line (span->start open)) 1)
        (equal (position->column (span->start open)) 2)
        (equal (position->line (span->end open)) 1)
        (equal (position->column (span->end open)) 2)
        (equal (position->line (span->start close)) 2)
        (equal (position->column (span->start close)) 3)
        (equal (position->line (span->end close)) 2)
        (equal (position->column (span->end close)) 3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The trees are well-formed and flatten to the tokens, with their spans,
; and building again from the flattening gives the same trees.
; (These are theorems of the builder; here they are run.)

(defmacro test-round-trip (string)
  `(assert-event
    (b* ((tokens (toks ,string))
         ((when (reserrp tokens)) nil)
         (trees (build-token-trees tokens)))
      (and (not (reserrp trees))
           (token-tree-list-wfp trees)
           (equal (token-tree-list->tokens trees) tokens)
           (equal (build-token-trees (token-tree-list->tokens trees))
                  trees)))))

(test-round-trip "")
(test-round-trip "a")
(test-round-trip "()")
(test-round-trip "a(b, [c, {a}])")
(test-round-trip "(a)[(b){c}]")
(test-round-trip "fn a() { b!(c); }")
(test-round-trip "macro_rules! a { ($b:tt) => { $b } }")
(test-round-trip "/** a */ (b)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Cases transcribed from the rustc test suite
; (repository rust-lang/rust, tag 1.87.0 -- the pinned compiler),
; from the files named in the comments below, in tests/ui/parser.
; Each is a whole file, with the test's own annotations.
; rustc reports one of its three errors about delimiters on each,
; and on some a second one, since it goes on after the first;
; the builder must report the first one.
; We check the kind of the error, and the line of the delimiter
; that the error ends with:
; the opening delimiter that is not closed, or the closing delimiter.

(defun start-line (token+span)
  (position->line (span->start (token+span->span token+span))))

(defmacro test-trees-fail-at (string kind line)
  `(assert-event
    (b* ((error (trees-error (trees ,string))))
      (and (equal (car error) ,kind)
           (equal (start-line (car (last error))) ,line)))))

; macro-mismatched-delim-brace-paren.rs:
; rustc reports "mismatched closing delimiter: `)`".

(test-trees-fail-at "macro_rules! foo { ($($tt:tt)*) => () }

fn main() {
    foo! {
        bar, \"baz\", 1, 2.0
    ) //~ ERROR mismatched closing delimiter
}
" :mismatched-closing-delimiter 6)

; macro-mismatched-delim-paren-brace.rs:
; rustc reports "mismatched closing delimiter: `}`",
; and then "unexpected closing delimiter: `}`".

(test-trees-fail-at "fn main() {
    foo! (
        bar, \"baz\", 1, 2.0
    } //~ ERROR mismatched closing delimiter
} //~ ERROR unexpected closing delimiter: `}`
" :mismatched-closing-delimiter 4)

; mismatched-delim-brace-empty-block.rs:
; rustc reports "unexpected closing delimiter: `}`".

(test-trees-fail-at "fn main() {

}
    let _ = ();
} //~ ERROR unexpected closing delimiter
" :unexpected-closing-delimiter 5)

; mismatched-delimiter-corner-case-issue-127868.rs:
; rustc reports "mismatched closing delimiter: `}`",
; and then "this file contains an unclosed delimiter".

(test-trees-fail-at "// issue: rust-lang/rust#127868

fn main() {
    let a = [[[[[[[[[[[[[[[[[[[[1, {, (, [,;
} //~ ERROR mismatched closing delimiter: `}`
//~ ERROR this file contains an unclosed delimiter
" :mismatched-closing-delimiter 5)

; unclosed-braces.rs:
; rustc reports "this file contains an unclosed delimiter",
; and notes the one on line 13 as the unclosed delimiter.

(test-trees-fail-at "struct S {
    x: [usize; 3],
}

fn foo() {
    {
        {
            println!(\"hi\");
        }
    }
}

fn main() {
//~^ NOTE unclosed delimiter
    {
        {
        //~^ NOTE this delimiter might not be properly closed...
            foo();
    }
    //~^ NOTE ...as it matches this but it has different indentation
}
//~ ERROR this file contains an unclosed delimiter
" :unclosed-delimiter 13)

; unmatched-delimiter-at-end-of-file.rs:
; rustc reports "this file contains an unclosed delimiter".

(test-trees-fail-at "struct S {
    x: usize,
    y: usize,
}

fn main() {
    S { x: 4,
        y: 5 };
}

fn foo() { //~ ERROR this file contains an unclosed delimiter
" :unclosed-delimiter 11)

; issues/issue-98601-delimiter-error-1.rs:
; rustc reports "unexpected closing delimiter: `}`".

(test-trees-fail-at "fn foo() {
    match 0 {
      _ => {}
    }
    if foo
    }
} //~ ERROR unexpected closing delimiter: `}`

fn main() {}
" :unexpected-closing-delimiter 7)

; issues/issue-98601-delimiter-error-unexpected-close.rs:
; rustc reports "unexpected closing delimiter: `)`".

(test-trees-fail-at "fn main() {
    todo!();
}

fn other(_: i32)) {} //~ ERROR unexpected closing delimiter: `)`
" :unexpected-closing-delimiter 5)

; use-unclosed-brace.rs:
; rustc reports "this file contains an unclosed delimiter".

(test-trees-fail-at "//@ error-pattern: this file contains an unclosed delimiter
use foo::{bar, baz;

use std::fmt::Display;

mod bar { }

mod baz { }

fn main() {}
" :unclosed-delimiter 2)

; unclosed_delim_mod.rs:
; rustc reports "mismatched closing delimiter: `}`".

(test-trees-fail-at "fn main() {}

pub struct Value {}
pub fn new() -> Result<Value, ()> {
    Ok(Value {
    }
}
//~^ ERROR mismatched closing delimiter
" :mismatched-closing-delimiter 7)

; mismatched-braces/missing-close-brace-in-struct.rs:
; rustc reports "this file contains an unclosed delimiter".

(test-trees-fail-at "pub(crate) struct Bar<T> {
  foo: T,

trait T {
    fn foo(&self);
}


impl T for Bar<usize> {
fn foo(&self) {}
}

fn main() {} //~ ERROR this file contains an unclosed delimiter
" :unclosed-delimiter 1)
