; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "../source-units")

(include-book "std/testing/assert-bang-stobj" :dir :system)

; (depends-on "../../samples/aes_fixslice_encrypt.rs")

; Tests of source units:
; the text of tokens and of lexemes, the lexemes of a source unit
; and their spans, well-formedness, the tokens and the token trees,
; the digest, and source units from files.
; The tokens expected of whole files are what rustc 1.87.0 does:
; each case that is marked with a name, like [B2],
; is a case of harness/input_format.py, which runs it through rustc.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Abbreviations for the tests.

; A list of naturals, bytes or code points, from its pieces:
; ASCII strings, naturals, and lists of naturals.

(defun nats-fn (pieces)
  (cond ((atom pieces) nil)
        ((stringp (car pieces))
         (append (acl2::string=>nats (car pieces))
                 (nats-fn (cdr pieces))))
        ((natp (car pieces))
         (cons (car pieces) (nats-fn (cdr pieces))))
        (t (append (car pieces) (nats-fn (cdr pieces))))))

(defmacro nats (&rest pieces)
  `(nats-fn (list ,@pieces)))

(defconst *cr* #xd)

(defconst *lf* #xa)

(defconst *bom* '(#xef #xbb #xbf)) ; U+FEFF in UTF-8

(defconst *attr* "[allow(unused)]")

; The source unit of the bytes of a file, or an error.

(defmacro unit (bytes &optional (edition '(rust::edition-2021)))
  `(source-unit-from-bytes ,bytes ,edition "test.rs"))

; The list of bare tokens (spans stripped) of a source unit, or :error.

(defun toks-only-aux (tokens+spans)
  (if (atom tokens+spans)
      nil
    (cons (token+span->token (car tokens+spans))
          (toks-only-aux (cdr tokens+spans)))))

(defun toks-only (unit)
  (if (reserrp unit)
      :error
    (toks-only-aux (source-unit-tokens unit))))

; The bytes of a file give a source unit with the given tokens.
; We also check what the theorems say of every source unit:
; it is well-formed, its lexemes give back its text,
; and its source text gives back the bytes.

(defmacro test-file-tokens (bytes expected)
  `(assert-event
    (b* ((bytes ,bytes)
         (unit (unit bytes)))
      (and (equal (toks-only unit) ,expected)
           (source-unit-wfp unit)
           (equal (lexeme+span-list-code-points (source-unit->lexemes unit))
                  (source-unit-text unit))
           (equal (source-text-to-bytes (source-unit->source unit))
                  bytes)))))

(defmacro test-file-fail (bytes)
  `(assert-event (reserrp (unit ,bytes))))

(defmacro str-tok (kind raw text)
  `(token-lit (lit-str (make-str-lit :kind ,kind
                                     :raw ,raw
                                     :text ,text
                                     :suffix ""))))

; The tokens of "pub fn f(){}", which many cases end with.

(defconst *f* "pub fn f(){}")

(defconst *f-tokens*
  (list (token-keyword "pub")
        (token-keyword "fn")
        (token-ident "f" nil)
        (token-open-delim (delim-paren))
        (token-close-delim (delim-paren))
        (token-open-delim (delim-brace))
        (token-close-delim (delim-brace))))

; A lexeme with the offsets of its span.

(defmacro ls (lexeme start end)
  `(make-lexeme+span :lexeme ,lexeme
                     :span (make-span :start ,start :end ,end)))

; The line and the column of the start of a token with span,
; in the text of a source unit.

(defun line+column (token+span unit)
  (b* ((pos (position-of-offset (span->start (token+span->span token+span))
                                (source-unit-text unit))))
    (cons (position->line pos) (position->column pos))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The text of tokens.

(defmacro test-token-text (token text)
  `(assert-event (equal (token-text ,token) ,text)))

(test-token-text (token-ident "foo" nil) "foo")
(test-token-text (token-ident "fn" t) "r#fn")
(test-token-text (token-keyword "fn") "fn")
(test-token-text (token-lifetime "a" nil) "'a")
(test-token-text (token-lifetime "_" nil) "'_")
(test-token-text (token-lifetime "fn" t) "'r#fn")
(test-token-text (token-punct ">>=") ">>=")
(test-token-text (token-open-delim (delim-paren)) "(")
(test-token-text (token-close-delim (delim-paren)) ")")
(test-token-text (token-open-delim (delim-bracket)) "[")
(test-token-text (token-close-delim (delim-bracket)) "]")
(test-token-text (token-open-delim (delim-brace)) "{")
(test-token-text (token-close-delim (delim-brace)) "}")
(test-token-text (token-doc-comment (doc-style-outer) nil " d") "/// d")
(test-token-text (token-doc-comment (doc-style-inner) nil " d") "//! d")
(test-token-text (token-doc-comment (doc-style-outer) t " d ") "/** d */")
(test-token-text (token-doc-comment (doc-style-inner) t " d ") "/*! d */")

; Literals.

(defmacro int-tok (radix digits suffix)
  `(token-lit (lit-int (make-int-lit :radix ,radix
                                     :digits ,digits
                                     :suffix ,suffix))))

(test-token-text (int-tok (radix-dec) "1_000" "") "1_000")
(test-token-text (int-tok (radix-dec) "1" "u8") "1u8")
(test-token-text (int-tok (radix-bin) "1_0" "") "0b1_0")
(test-token-text (int-tok (radix-oct) "17" "i64") "0o17i64")
(test-token-text (int-tok (radix-hex) "7f_ff" "u16") "0x7f_ffu16")
(test-token-text (token-lit (lit-float (make-float-lit :text "1_000.0E-3"
                                                       :suffix "f64")))
                 "1_000.0E-3f64")
(test-token-text (token-lit (lit-float (make-float-lit :text "2." :suffix "")))
                 "2.")
(test-token-text (token-lit (lit-char (make-char-lit :byte nil
                                                     :text "\\n"
                                                     :suffix "")))
                 "'\\n'")
(test-token-text (token-lit (lit-char (make-char-lit :byte t
                                                     :text "x"
                                                     :suffix "s")))
                 "b'x's")
(test-token-text (str-tok (str-kind-plain) nil "a\\\"b") "\"a\\\"b\"")
(test-token-text (str-tok (str-kind-byte) nil "x") "b\"x\"")
(test-token-text (str-tok (str-kind-c) nil "x") "c\"x\"")
(test-token-text (str-tok (str-kind-plain) 0 "x") "r\"x\"")
(test-token-text (str-tok (str-kind-plain) 2 "a\"#b") "r##\"a\"#b\"##")
(test-token-text (str-tok (str-kind-byte) 1 "x") "br#\"x\"#")
(test-token-text (str-tok (str-kind-c) 0 "x") "cr\"x\"")
(test-token-text (token-lit (lit-str (make-str-lit :kind (str-kind-plain)
                                                   :raw 1
                                                   :text "a"
                                                   :suffix "s")))
                 "r#\"a\"#s")

; The text of lexemes that are not tokens.

(assert-event (equal (lexeme-text (lexeme-token (token-keyword "fn"))) "fn"))
(assert-event (equal (lexeme-text (lexeme-whitespace "  ")) "  "))
(assert-event (equal (lexeme-text (lexeme-comment nil " c")) "// c"))
(assert-event (equal (lexeme-text (lexeme-comment t " a /* b */ "))
                     "/* a /* b */ */"))
(assert-event (equal (lexeme-text (lexeme-shebang "/usr/bin/env rustx"))
                     "#!/usr/bin/env rustx"))

; Code points: the text holds UTF-8.

(assert-event (equal (lexeme-code-points (lexeme-comment nil " c"))
                     (nats "// c")))
(assert-event
 (equal (lexeme-code-points
         (lexeme-comment nil (acl2::implode (list (code-char #xc3)
                                                  (code-char #xa9)))))
        (nats "//" #xe9)))
(assert-event (equal (token-code-points (token-ident "fn" t))
                     (nats "r#fn")))

; A text that is not valid UTF-8 has no code points.

(assert-event
 (equal (lexeme-code-points
         (lexeme-comment nil (acl2::implode (list (code-char #xff)))))
        nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The lexemes of a source unit, with their spans.

; Every lexeme is there, with the span of its code points.

(assert-event
 (b* ((unit (unit (nats "a  /* c */b // d" *lf* "'x'"))))
   (and (not (reserrp unit))
        (equal (source-unit->lexemes unit)
               (list (ls (lexeme-token (token-ident "a" nil)) 0 1)
                     (ls (lexeme-whitespace "  ") 1 3)
                     (ls (lexeme-comment t " c ") 3 10)
                     (ls (lexeme-token (token-ident "b" nil)) 10 11)
                     (ls (lexeme-whitespace " ") 11 12)
                     (ls (lexeme-comment nil " d") 12 16)
                     (ls (lexeme-whitespace "
") 16 17)
                     (ls (lexeme-token
                          (token-lit (lit-char (make-char-lit :byte nil
                                                              :text "x"
                                                              :suffix ""))))
                         17 20))))))

; The byte order mark and the carriage return before a line feed
; are not in the text, so they do not count in the spans;
; a character of several bytes counts as one;
; and a shebang is the first lexeme.
; The source text has what was removed.

(assert-event
 (b* ((bytes (nats *bom* "#!/x" *cr* *lf* "fn f(){} // c" '(#xc3 #xa9) *lf*))
      (unit (unit bytes)))
   (and (not (reserrp unit))
        (equal (source-unit->label unit) "test.rs")
        (equal (source-unit->edition unit) (rust::edition-2021))
        (equal (source-unit-text unit)
               (nats "#!/x" *lf* "fn f(){} // c" #xe9 *lf*))
        (equal (source-text->bom (source-unit->source unit)) t)
        (equal (source-text->crs (source-unit->source unit)) '(4))
        (equal (source-unit->lexemes unit)
               (list (ls (lexeme-shebang "/x") 0 4)
                     (ls (lexeme-whitespace "
") 4 5)
                     (ls (lexeme-token (token-keyword "fn")) 5 7)
                     (ls (lexeme-whitespace " ") 7 8)
                     (ls (lexeme-token (token-ident "f" nil)) 8 9)
                     (ls (lexeme-token (token-open-delim (delim-paren))) 9 10)
                     (ls (lexeme-token (token-close-delim (delim-paren))) 10 11)
                     (ls (lexeme-token (token-open-delim (delim-brace))) 11 12)
                     (ls (lexeme-token (token-close-delim (delim-brace))) 12 13)
                     (ls (lexeme-whitespace " ") 13 14)
                     (ls (lexeme-comment
                          nil
                          (acl2::implode (list #\Space
                                               #\c
                                               (code-char #xc3)
                                               (code-char #xa9))))
                         14 19)
                     (ls (lexeme-whitespace "
") 19 20)))
        (equal (source-text-to-bytes (source-unit->source unit))
               bytes))))

; The empty file has no lexemes.

(assert-event
 (b* ((unit (unit nil)))
   (and (not (reserrp unit))
        (equal (source-unit->lexemes unit) nil)
        (source-unit-wfp unit))))

; The edition is that of the tokens.

(assert-event
 (b* ((unit (unit (nats "gen") (rust::edition-2024))))
   (and (equal (source-unit->edition unit) (rust::edition-2024))
        (equal (toks-only unit) (list (token-keyword "gen"))))))

(assert-event
 (equal (toks-only (unit (nats "gen")))
        (list (token-ident "gen" nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Well-formedness.

(defmacro test-unit (text lexemes)
  `(make-source-unit
    :label "test.rs"
    :edition (rust::edition-2021)
    :source (make-source-text :text ,text :bom nil :crs nil)
    :lexemes ,lexemes))

(defconst *a* (lexeme-token (token-ident "a" nil)))

(defconst *b* (lexeme-token (token-ident "b" nil)))

(defconst *space* (lexeme-whitespace " "))

(assert-event (source-unit-wfp (test-unit nil nil)))

(assert-event
 (source-unit-wfp
  (test-unit (nats "a b") (list (ls *a* 0 1) (ls *space* 1 2) (ls *b* 2 3)))))

; The spans must be adjacent, from 0 to the end of the text.

(assert-event
 (not (source-unit-wfp
       (test-unit (nats "a b") (list (ls *a* 0 1) (ls *b* 2 3))))))

(assert-event
 (not (source-unit-wfp
       (test-unit (nats "a b") (list (ls *a* 0 1) (ls *space* 1 2))))))

(assert-event
 (not (source-unit-wfp
       (test-unit (nats "a b")
                  (list (ls *a* 1 2) (ls *space* 2 3) (ls *b* 3 4))))))

(assert-event
 (not (source-unit-wfp
       (test-unit (nats "a") (list (ls *a* 0 1) (ls *space* 1 2))))))

(assert-event
 (not (source-unit-wfp (test-unit (nats "a") nil))))

; Each span must be as long as the text of its lexeme.

(assert-event
 (not (source-unit-wfp
       (test-unit (nats "a b") (list (ls *a* 0 2) (ls *b* 2 3))))))

; The text at each span must be the text of the lexeme.

(assert-event
 (not (source-unit-wfp
       (test-unit (nats "a b")
                  (list (ls *b* 0 1) (ls *space* 1 2) (ls *a* 2 3))))))

(assert-event
 (not (source-unit-wfp
       (test-unit (nats "r#a") (list (ls *a* 0 3))))))

(assert-event
 (source-unit-wfp
  (test-unit (nats "r#a") (list (ls (lexeme-token (token-ident "a" t)) 0 3)))))

; A shebang can only be the first lexeme.

(assert-event
 (source-unit-wfp
  (test-unit (nats "#!a b")
             (list (ls (lexeme-shebang "a b") 0 5)))))

(assert-event
 (not (source-unit-wfp
       (test-unit (nats "a #!b")
                  (list (ls *a* 0 1)
                        (ls *space* 1 2)
                        (ls (lexeme-shebang "b") 2 5))))))

; The code points of the text must be Unicode scalar values.

(assert-event
 (not (source-unit-wfp (test-unit (list #xd800) nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tokens of the bytes of a file.

(test-file-tokens nil nil)
(test-file-tokens (nats *f*) *f-tokens*)

; The byte order mark: one, at the start.

(test-file-tokens (nats *bom* *f*) *f-tokens*) ; [B1]
(test-file-fail (nats *bom* *bom* *f*)) ; [B2]
(test-file-fail (nats *f* *bom*)) ; [B3]
(test-file-tokens *bom* nil) ; [B8]
(test-file-fail (nats " " *bom* *f*)) ; [B10]
(test-file-tokens (nats "// " *bom* *lf* *f*) *f-tokens*) ; [B11]
(test-file-tokens (nats *bom* *cr* *lf* *f*) *f-tokens*) ; [B14]
(test-file-tokens (nats "\"" *bom* "\"") ; [B9]
                  (list (str-tok (str-kind-plain)
                                 nil
                                 (acl2::implode (list (code-char #xef)
                                                      (code-char #xbb)
                                                      (code-char #xbf))))))

; Carriage returns.  Before a line feed they are gone;
; elsewhere they are whitespace, but errors in doc comments and literals.

(test-file-tokens (nats *f* *cr* *lf*) *f-tokens*) ; [C1]
(test-file-tokens (nats "pub" *cr* "fn f(){}") *f-tokens*) ; [C2]
(test-file-tokens (nats "pub" *cr* *cr* *lf* "fn f(){}") *f-tokens*) ; [C16]
(test-file-tokens (nats "pub" *lf* *cr* "fn f(){}") *f-tokens*) ; [C19]
(test-file-tokens (nats "// c" *cr* *cr* *lf* *f*) *f-tokens*) ; [C11]
(test-file-tokens (nats "// c" *cr* *lf* *f* "// d" *cr* *lf*) ; [C22]
                  *f-tokens*)
(test-file-tokens (nats "/// a" *cr* *lf* *f*) ; [C3]
                  (cons (token-doc-comment (doc-style-outer) nil " a")
                        *f-tokens*))
(test-file-fail (nats "/// a" *cr* *cr* *lf* *f*)) ; [C4]
(test-file-tokens (nats "/** a" *cr* *lf* " b */" *f*) ; [C14]
                  (cons (token-doc-comment (doc-style-outer) t " a
 b ")
                        *f-tokens*))
(test-file-fail (nats "/** a" *cr* " b */" *f*)) ; [C15]
(test-file-tokens (nats "\"a" *cr* *lf* "b\"") ; [C5]
                  (list (str-tok (str-kind-plain) nil "a
b")))
(test-file-tokens (nats "r\"a" *cr* *lf* "b\"") ; [C6]
                  (list (str-tok (str-kind-plain) 0 "a
b")))
(test-file-tokens (nats "b\"a" *cr* *lf* "b\"") ; [C10]
                  (list (str-tok (str-kind-byte) nil "a
b")))
(test-file-tokens (nats "c\"a" *cr* *lf* "b\"") ; [C20]
                  (list (str-tok (str-kind-c) nil "a
b")))
(test-file-tokens (nats "\"a\\" *cr* *lf* "   b\"") ; [C9]
                  (list (str-tok (str-kind-plain) nil "a\\
   b")))
(test-file-fail (nats "\"a" *cr* "b\"")) ; [C7]
(test-file-fail (nats "\"a" *cr* *cr* *lf* "b\"")) ; [C8]
(test-file-fail (nats "r\"a" *cr* *cr* *lf* "b\"")) ; [C17]
(test-file-fail (nats "\"a" *cr* *cr* *lf* *lf* "b\"")) ; [C18]
(test-file-fail (nats "\"a\\" *cr* *cr* *lf* "   b\"")) ; [C23]

; A character that is not part of any token.

(test-file-fail (nats #x0 *f*)) ; [U17]
(test-file-tokens (nats "// " #x0 *lf* *f*) *f-tokens*) ; [U8]

; Bytes that are not valid UTF-8, wherever they are.

(test-file-fail (nats "// " #xff *lf* *f*)) ; [U1]
(test-file-tokens (nats "// " '(#xf0 #x9f #x98 #x80) *lf* *f*) ; [U6]
                  *f-tokens*)
(test-file-tokens (nats "// " '(#xef #xbf #xbe) *lf* *f*) ; [U7]
                  *f-tokens*)
(test-file-tokens (nats "// " '(#xf4 #x8f #xbf #xbf) *lf* *f*) ; [U16]
                  *f-tokens*)

; The shebang is not lexed: what is in it does not matter.

(test-file-tokens (nats "#!/usr/bin/env rustx \"" *lf* *f*) *f-tokens*) ; [S1]
(test-file-tokens (nats "#!") nil) ; [S2]
(test-file-tokens (nats "#!" *lf* *f*) *f-tokens*) ; [S3]
(test-file-tokens (nats "#!/x \"") nil) ; [S17]
(test-file-tokens (nats "#!/x \"" *cr* *lf* *f*) *f-tokens*) ; [S7]
(test-file-tokens (nats "#!/x \"" *cr* *cr* *lf* *f*) *f-tokens*) ; [S18]
(test-file-tokens (nats *bom* "#!/x \"" *lf* *f*) *f-tokens*) ; [B4]
(test-file-tokens (nats "#!/* unterminated" *lf* *f*) *f-tokens*) ; [S9]
(test-file-tokens (nats "#!/** unterminated" *lf* *f*) *f-tokens*) ; [S10]
(test-file-tokens (nats "#!/*! unterminated" *lf* *f*) *f-tokens*) ; [S11]
(test-file-tokens (nats "#!/*/ \"" *lf* *f*) *f-tokens*) ; [S15]
(test-file-tokens (nats "#!/**") nil) ; [S21]
(test-file-tokens (nats "#!/* c */") nil) ; [S23]
(test-file-tokens (nats "#!/** d */" *attr* " \"" *lf* *f*)
                  *f-tokens*) ; [S-removed-block-outer-doc]
(test-file-tokens (nats "#!" '(#xc2 #xa0) *attr* " \"" *lf* *f*)
                  *f-tokens*) ; [S-removed-u00a0]

; Only the first line is a shebang, and only at the start.

(test-file-fail (nats " #!/x \"" *lf* *f*)) ; [S4]
(test-file-fail (nats *lf* "#!/x \"" *lf* *f*)) ; [S5]
(test-file-fail (nats "#!/a \"" *lf* "#!/b \"" *lf* *f*)) ; [S6]
(test-file-fail (nats "#![allow(unused)]" *lf* "#!/x \"" *lf* *f*)) ; [S20]

; An inner attribute is lexed.

(test-file-tokens (nats "#![a]" *lf* *f*)
                  (list* (token-punct "#")
                         (token-punct "!")
                         (token-open-delim (delim-bracket))
                         (token-ident "a" nil)
                         (token-close-delim (delim-bracket))
                         *f-tokens*))
(test-file-fail (nats "#![ \"" *lf* *f*)) ; [S16]
(test-file-fail (nats "#!/* c */" *attr* " \"" *lf* *f*)) ; [S-removed-block]
(test-file-fail (nats "#! " *attr* " \"" *lf* *f*)) ; [S-removed-space]

; The shebang is a lexeme, and the first one.

(assert-event
 (b* ((unit (unit (nats "#!/usr/bin/env rustx" *lf* *f*))))
   (and (not (reserrp unit))
        (equal (car (source-unit->lexemes unit))
               (ls (lexeme-shebang "/usr/bin/env rustx") 0 20))
        (equal (cadr (source-unit->lexemes unit))
               (ls (lexeme-whitespace "
") 20 21)))))

; The tokens after a shebang are in the lines of the file:
; the first token here starts at offset 21, which is line 2, column 0.

(assert-event
 (b* ((unit (unit (nats "#!/usr/bin/env rustx" *lf* *f*)))
      ((when (reserrp unit)) nil)
      (first (car (source-unit-tokens unit))))
   (and (equal (token+span->token first) (token-keyword "pub"))
        (equal (token+span->span first) (make-span :start 21 :end 24))
        (equal (line+column first unit) '(2 . 0)))))

; A carriage return that was removed does not count in the offsets
; or in the columns, and the byte order mark does not either.

(assert-event
 (b* ((unit (unit (nats *bom* "a" *cr* *lf* " b")))
      ((when (reserrp unit)) nil)
      ((list a b) (source-unit-tokens unit)))
   (and (equal (token+span->span a) (make-span :start 0 :end 1))
        (equal (line+column a unit) '(1 . 0))
        (equal (token+span->span b) (make-span :start 3 :end 4))
        (equal (line+column b unit) '(2 . 1)))))

; The span of each token locates it in the text.

(assert-event
 (b* ((unit (unit (nats *bom* "#!/x" *cr* *lf* "fn f(){ \"a" #xc3 #xa9 "\" }")))
      ((when (reserrp unit)) nil))
   (and (token+span-list-located-p (source-unit-tokens unit)
                                   (source-unit-text unit))
        (lexeme+span-list-located-p (source-unit->lexemes unit)
                                    (source-unit-text unit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Token trees of a source unit.

(assert-event
 (b* ((unit (unit (nats "#!/x (" *lf* *f*)))
      ((when (reserrp unit)) nil)
      (trees (source-unit-token-trees unit)))
   (and (not (reserrp trees))
        (equal (len trees) 5)
        (equal (token-tree-list->tokens trees)
               (source-unit-tokens unit))
        (token+span-list-located-p (token-tree-list->tokens trees)
                                   (source-unit-text unit)))))

; The delimiters do not match: there is a source unit, but no token trees.

(assert-event
 (b* ((unit (unit (nats *f* " ("))))
   (and (not (reserrp unit))
        (reserrp (source-unit-token-trees unit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Digest.

; The digest is the SHA-256 hash of the bytes of the file:
; here the test vector for "abc" of FIPS 180-4,
; ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad.

(assert-event
 (b* ((unit (unit (nats "abc")))
      ((when (reserrp unit)) nil))
   (equal (source-unit-digest unit)
          '(#xba #x78 #x16 #xbf #x8f #x01 #xcf #xea
            #x41 #x41 #x40 #xde #x5d #xae #x22 #x23
            #xb0 #x03 #x61 #xa3 #x96 #x17 #x7a #x9c
            #xb4 #x10 #xff #x61 #xf2 #x00 #x15 #xad))))

; It is that of the file, not of the text:
; a byte order mark, or a carriage return before a line feed,
; changes the digest and not the text.

(assert-event
 (b* ((unit1 (unit (nats "a" *lf*)))
      (unit2 (unit (nats "a" *cr* *lf*)))
      (unit3 (unit (nats *bom* "a" *lf*)))
      ((when (or (reserrp unit1) (reserrp unit2) (reserrp unit3))) nil))
   (and (equal (source-unit-text unit1) (source-unit-text unit2))
        (equal (source-unit-text unit1) (source-unit-text unit3))
        (equal (source-unit-digest unit1)
               (sha2::sha-256-bytes (nats "a" *lf*)))
        (equal (source-unit-digest unit2)
               (sha2::sha-256-bytes (nats "a" *cr* *lf*)))
        (equal (source-unit-digest unit3)
               (sha2::sha-256-bytes (nats *bom* "a" *lf*)))
        (not (equal (source-unit-digest unit1) (source-unit-digest unit2)))
        (not (equal (source-unit-digest unit1) (source-unit-digest unit3)))
        (not (equal (source-unit-digest unit2) (source-unit-digest unit3))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Files.

; The sample file has 24,776 characters, in 9,116 lexemes,
; of which 5,769 are tokens, in 193 token trees.
; Its digest is what the command shasum -a 256 prints for it:
; 7495f08c8369425c08691f14d4f22d2095d6588eae29a7d54b052b7e4b9a4dab.

(assert!-stobj
 (b* (((mv unit state)
       (source-unit-from-file "../../samples/aes_fixslice_encrypt.rs"
                              (rust::edition-2021)
                              state))
      ((when (reserrp unit)) (mv nil state))
      (trees (source-unit-token-trees unit)))
   (mv (and (equal (source-unit->label unit)
                   "../../samples/aes_fixslice_encrypt.rs")
            (equal (len (source-unit-text unit)) 24776)
            (equal (len (source-unit->lexemes unit)) 9116)
            (equal (len (source-unit-tokens unit)) 5769)
            (not (reserrp trees))
            (equal (len trees) 193)
            (source-unit-wfp unit)
            (equal (lexeme+span-list-code-points (source-unit->lexemes unit))
                   (source-unit-text unit))
            (token+span-list-located-p (source-unit-tokens unit)
                                       (source-unit-text unit))
            (equal (source-unit-digest unit)
                   '(#x74 #x95 #xf0 #x8c #x83 #x69 #x42 #x5c
                     #x08 #x69 #x1f #x14 #xd4 #xf2 #x2d #x20
                     #x95 #xd6 #x58 #x8e #xae #x29 #xa7 #xd5
                     #x4b #x05 #x2b #x7e #x4b #x9a #x4d #xab)))
       state))
 state)

; The tokens do not depend on the edition in this file.

(assert!-stobj
 (b* (((mv unit state)
       (source-unit-from-file "../../samples/aes_fixslice_encrypt.rs"
                              (rust::edition-2024)
                              state)))
   (mv (and (not (reserrp unit))
            (equal (len (source-unit-tokens unit)) 5769))
       state))
 state)

; A file that does not exist.

(assert!-stobj
 (b* (((mv unit state)
       (source-unit-from-file "no-such-file.rs" (rust::edition-2021) state)))
   (mv (reserrp unit) state))
 state)
