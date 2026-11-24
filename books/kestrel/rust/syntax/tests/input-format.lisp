; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "../input-format")

(include-book "std/testing/assert-bang-stobj" :dir :system)

; (depends-on "../../samples/aes_fixslice_encrypt.rs")

; Tests of the input format:
; UTF-8 decoding, the byte order mark, CRLF normalization, the shebang,
; and the reading of a file.
; What is expected here is what rustc 1.87.0 does:
; each case that is marked with a name, like [S1],
; is a case of harness/input_format.py, which runs it through rustc.
; The tests of the tokens of whole files are with those of source units.

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

; The source text of some bytes has the given components,
; and it gives back the bytes.

(defmacro test-source-text (bytes &key text bom crs)
  `(assert-event
    (b* ((bytes ,bytes)
         (stext (source-text-from-bytes bytes)))
      (and (not (reserrp stext))
           (equal (source-text->text stext) ,text)
           (equal (source-text->bom stext) ,bom)
           (equal (source-text->crs stext) ,crs)
           (equal (source-text-to-bytes stext) bytes)))))

(defmacro test-source-text-fail (bytes)
  `(assert-event (reserrp (source-text-from-bytes ,bytes))))

(defmacro test-shebang (text length)
  `(assert-event (equal (shebang-length ,text) ,length)))

; A function, which many cases end with.

(defconst *f* "pub fn f(){}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; UTF-8 decoding.

; Encodings of one to four bytes, at the ends of each range.

(assert-event (equal (utf-8-bytes-to-code-points nil) nil))
(assert-event (equal (utf-8-bytes-to-code-points '(#x00)) '(#x0)))
(assert-event (equal (utf-8-bytes-to-code-points '(#x7f)) '(#x7f)))
(assert-event (equal (utf-8-bytes-to-code-points '(#xc2 #x80)) '(#x80)))
(assert-event (equal (utf-8-bytes-to-code-points '(#xdf #xbf)) '(#x7ff)))
(assert-event (equal (utf-8-bytes-to-code-points '(#xe0 #xa0 #x80)) '(#x800)))
(assert-event (equal (utf-8-bytes-to-code-points '(#xed #x9f #xbf)) '(#xd7ff)))
(assert-event (equal (utf-8-bytes-to-code-points '(#xee #x80 #x80)) '(#xe000)))
(assert-event (equal (utf-8-bytes-to-code-points '(#xef #xbf #xbf)) '(#xffff)))
(assert-event
 (equal (utf-8-bytes-to-code-points '(#xf0 #x90 #x80 #x80)) '(#x10000)))
(assert-event
 (equal (utf-8-bytes-to-code-points '(#xf4 #x8f #xbf #xbf)) '(#x10ffff)))
(assert-event
 (equal (utf-8-bytes-to-code-points
         (nats "a" '(#xc3 #xa9) "b" '(#xe2 #x82 #xac)))
        '(#x61 #xe9 #x62 #x20ac)))

; Bytes that are not valid UTF-8.

(defmacro test-decode-fail (bytes)
  `(assert-event (reserrp (utf-8-bytes-to-code-points ,bytes))))

(test-decode-fail '(#xff)) ; [U1] not a byte of UTF-8
(test-decode-fail '(#xc0 #xaf)) ; [U2] two bytes for U+002F
(test-decode-fail '(#xc1 #xbf)) ; two bytes for U+007F
(test-decode-fail '(#xed #xa0 #x80)) ; [U3] the surrogate U+D800
(test-decode-fail '(#xed #xbf #xbf)) ; the surrogate U+DFFF
(test-decode-fail '(#xf4 #x90 #x80 #x80)) ; [U4] above U+10FFFF
(test-decode-fail '(#xe2 #x82)) ; [U5] ends in the middle of an encoding
(test-decode-fail '(#xf8 #x88 #x80 #x80 #x80)) ; [U13] five bytes
(test-decode-fail '(#x80)) ; [U14] a continuation byte alone
(test-decode-fail '(#xe0 #x80 #x80)) ; [U15] three bytes for U+0000
(test-decode-fail '(#xf0 #x80 #x80 #x80)) ; four bytes for U+0000
(test-decode-fail '(#xc3)) ; no continuation byte
(test-decode-fail '(#xc3 #x41)) ; not a continuation byte
(test-decode-fail '(#x61 #xff #x62))

; Encoding, and the code points that have no encoding.

(assert-event
 (equal (code-points-to-utf-8-bytes '(#x61 #xe9 #x20ac #x10ffff))
        '(#x61 #xc3 #xa9 #xe2 #x82 #xac #xf4 #x8f #xbf #xbf)))
(assert-event (equal (code-points-to-utf-8-bytes nil) nil))
(assert-event (reserrp (code-points-to-utf-8-bytes '(#xd800))))
(assert-event (reserrp (code-points-to-utf-8-bytes '(#x110000))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Byte order mark.

(defmacro test-bom (text new-text bom)
  `(assert-event
    (b* ((text ,text)
         ((mv new-text bom) (remove-byte-order-mark text)))
      (and (equal new-text ,new-text)
           (equal bom ,bom)
           (equal (restore-byte-order-mark new-text bom) text)))))

(test-bom nil nil nil)
(test-bom '(#x61) '(#x61) nil)
(test-bom '(#xfeff) nil t)
(test-bom '(#xfeff #x61) '(#x61) t)
(test-bom '(#xfeff #xfeff #x61) '(#xfeff #x61) t) ; only one is removed
(test-bom '(#x61 #xfeff) '(#x61 #xfeff) nil) ; only at the start
(test-bom '(#xfffe #x61) '(#xfffe #x61) nil) ; not the byte order mark

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; CRLF normalization.

(defmacro test-crlf (text new-text crs)
  `(assert-event
    (b* ((text ,text)
         ((mv new-text crs) (normalize-crlf text)))
      (and (equal new-text ,new-text)
           (equal crs ,crs)
           (equal (restore-crlf new-text crs) text)))))

(test-crlf nil nil nil)
(test-crlf (nats "ab") (nats "ab") nil)
(test-crlf (nats "a" *lf* "b") (nats "a" *lf* "b") nil)
(test-crlf (nats "a" *cr* *lf* "b") (nats "a" *lf* "b") '(1))
(test-crlf (nats *cr* *lf*) (nats *lf*) '(0))
(test-crlf (nats *cr* *lf* *cr* *lf*) (nats *lf* *lf*) '(0 1))
(test-crlf (nats "a" *cr* *lf* "b" *lf* "c" *cr* *lf*)
           (nats "a" *lf* "b" *lf* "c" *lf*)
           '(1 5))

; A carriage return that is not immediately followed by a line feed stays.

(test-crlf (nats "a" *cr* "b") (nats "a" *cr* "b") nil)
(test-crlf (nats *cr*) (nats *cr*) nil)
(test-crlf (nats "a" *cr*) (nats "a" *cr*) nil)
(test-crlf (nats *lf* *cr*) (nats *lf* *cr*) nil)
(test-crlf (nats *cr* " " *lf*) (nats *cr* " " *lf*) nil)

; The text is gone through once: of two carriage returns before
; a line feed, the first stays, and is then followed by the line feed.

(test-crlf (nats "a" *cr* *cr* *lf* "b") (nats "a" *cr* *lf* "b") '(2))
(test-crlf (nats *cr* *cr* *cr* *lf*) (nats *cr* *cr* *lf*) '(2))
(test-crlf (nats *cr* *cr* *lf* *lf*) (nats *cr* *lf* *lf*) '(1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Source texts from bytes: decoding, then the byte order mark, then CRLF.

(test-source-text nil :text nil :bom nil :crs nil)
(test-source-text (nats *f*) :text (nats *f*) :bom nil :crs nil)
(test-source-text (nats *bom* *f*) :text (nats *f*) :bom t :crs nil)
(test-source-text *bom* :text nil :bom t :crs nil)
(test-source-text (nats *bom* *bom* "a")
                  :text (nats #xfeff "a") :bom t :crs nil)
(test-source-text (nats "a" *cr* *lf* "b" *cr* *lf*)
                  :text (nats "a" *lf* "b" *lf*) :bom nil :crs '(1 3))

; The positions of the removed carriage returns are positions
; in the text, where the byte order mark is no more
; and a character of several bytes counts as one.

(test-source-text (nats *bom* '(#xc3 #xa9) *cr* *lf* "b" *cr* *lf*)
                  :text (nats #xe9 *lf* "b" *lf*) :bom t :crs '(1 3))
(test-source-text (nats *bom* "#!/x" *cr* *lf* "a" *cr* *cr* *lf*)
                  :text (nats "#!/x" *lf* "a" *cr* *lf*) :bom t :crs '(4 7))

; A byte order mark after a line ending is not at the start.

(test-source-text (nats *cr* *lf* *bom*)
                  :text (nats *lf* #xfeff) :bom nil :crs '(0))

(test-source-text-fail '(#xff))
(test-source-text-fail (nats "// " #xff *lf* *f*)) ; [U1]
(test-source-text-fail (nats *f* "// " '(#xe2 #x82))) ; [U5]
(test-source-text-fail (nats *bom* #xc0 #xaf))

; A source text whose code points are not all scalar values
; does not come from a file.

(assert-event
 (reserrp (source-text-to-bytes
           (make-source-text :text '(#xd800) :bom nil :crs nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Shebang.

(test-shebang nil 0)
(test-shebang (nats "fn main() {}") 0)
(test-shebang (nats "#!/usr/bin/env rustx" *lf* "fn main() {}") 20) ; [S1]
(test-shebang (nats "#!") 2) ; [S2]
(test-shebang (nats "#!" *lf* *f*) 2) ; [S3]
(test-shebang (nats "#!/x") 4) ; [S17] no line feed
(test-shebang (nats "#") 0)
(test-shebang (nats "#a") 0)
(test-shebang (nats "!#/x") 0)

; Only at the start of the text.

(test-shebang (nats " #!/x" *lf* *f*) 0) ; [S4]
(test-shebang (nats *lf* "#!/x" *lf* *f*) 0) ; [S5]
(test-shebang (nats #xfeff "#!/x" *lf* *f*) 0) ; a second byte order mark

; The shebang ends before the first line ending,
; which is a line feed, or a carriage return and a line feed
; (as two carriage returns and a line feed in the file leave).
; A carriage return alone does not end it.

(test-shebang (nats "#!/a" *lf* "#!/b" *lf*) 4) ; [S6]
(test-shebang (nats "#!/x" *cr* *lf* *f*) 4) ; [S18]
(test-shebang (nats "#!/x" *cr* *f* *lf*) 17) ; [S8]
(test-shebang (nats "#!/x" *cr*) 5)
(test-shebang (nats "#!/x" *cr* *cr* *lf*) 5)

; What may come between the "#!" and the "[" of an inner attribute.
; A name in brackets, from here to [hash], is the name of the text
; between the two in the list XS of harness/input_format.py,
; where each text has two cases (S-kept- and S-removed-).

(defconst *attr* "[allow(unused)]")

; An inner attribute is not a shebang:
; whitespace can come between the "#!" and the "[".

(test-shebang (nats "#!" *attr*) 0) ; [empty]
(test-shebang (nats "#! " *attr*) 0) ; [space]
(test-shebang (nats "#!" #x9 *attr*) 0) ; [tab]
(test-shebang (nats "#!" *lf* *attr*) 0) ; [lf]
(test-shebang (nats "#!" *cr* *attr*) 0) ; [cr]
(test-shebang (nats "#!" *cr* *lf* *attr*) 0) ; [crlf]
(test-shebang (nats "#!" #xb *attr*) 0) ; [vt]
(test-shebang (nats "#!" #xc *attr*) 0) ; [ff]
(test-shebang (nats "#!" #x85 *attr*) 0) ; [u0085]
(test-shebang (nats "#!" #x200e *attr*) 0) ; [u200e]
(test-shebang (nats "#!" #x200f *attr*) 0) ; [u200f]
(test-shebang (nats "#!" #x2028 *attr*) 0) ; [u2028]
(test-shebang (nats "#!" #x2029 *attr*) 0) ; [u2029]

; Characters that are not whitespace.

(test-shebang (nats "#!" #xa0 *attr*) 18) ; [u00a0]
(test-shebang (nats "#!" #xfeff *attr*) 18) ; [bom]

; Comments that are not doc comments can come there too.

(test-shebang (nats "#!/* c */" *attr*) 0) ; [block]
(test-shebang (nats "#!/**/" *attr*) 0) ; [block-empty]
(test-shebang (nats "#!/***/" *attr*) 0) ; [block-3]
(test-shebang (nats "#!/*** c */" *attr*) 0) ; [block-3-stars]
(test-shebang (nats "#!/* a /* b */ c */" *attr*) 0) ; [block-nested]
(test-shebang (nats "#!/* a" *lf* " b */" *attr*) 0) ; [block-2-lines]
(test-shebang (nats "#!// c" *lf* *attr*) 0) ; [line]
(test-shebang (nats "#!//" *lf* *attr*) 0) ; [line-empty]
(test-shebang (nats "#!//// c" *lf* *attr*) 0) ; [line-4-slashes]
(test-shebang (nats "#! /* c */ // x" *lf* " /* d */ " *attr*) 0) ; [mixed]

; A doc comment cannot: the "#!" then starts a shebang.

(test-shebang (nats "#!/** d */" *attr*) 25) ; [block-outer-doc]
(test-shebang (nats "#!/*! d */" *attr*) 25) ; [block-inner-doc]
(test-shebang (nats "#!/// d" *lf* *attr*) 7) ; [line-outer-doc]
(test-shebang (nats "#!//! d" *lf* *attr*) 7) ; [line-inner-doc]
(test-shebang (nats "#!///" *lf* *attr*) 5) ; [line-3-slashes-only]
(test-shebang (nats "#!//!" *lf* *attr*) 5) ; [line-bang-only]
(test-shebang (nats "#!/** d *//* c */" *attr*) 32) ; [block-doc-then-block]
(test-shebang (nats "#!/* c *//** d */" *attr*) 32) ; [block-then-block-doc]

; Nor can anything else.

(test-shebang (nats "#!/" *attr*) 18) ; [slash]
(test-shebang (nats "#!a" *attr*) 18) ; [a]
(test-shebang (nats "#!!" *attr*) 18) ; [bang]
(test-shebang (nats "#!#" *attr*) 18) ; [hash]
(test-shebang (nats "#!/usr/bin/env [x]") 18)

; The attribute can start several lines down,
; and what follows the "[" does not matter.

(test-shebang (nats "#!" *lf* *lf* *lf* *attr*) 0) ; [S22]
(test-shebang (nats "#![") 0)
(test-shebang (nats "#![ \"") 0) ; [S16]

; A block comment that is not closed: nothing follows it,
; so the "#!" starts a shebang, which still ends with its line.

(test-shebang (nats "#!/* unterminated" *lf* *f*) 17) ; [S9]
(test-shebang (nats "#!/** unterminated" *lf* *f*) 18) ; [S10]
(test-shebang (nats "#!/*! unterminated" *lf* *f*) 18) ; [S11]
(test-shebang (nats "#!/*/ \"" *lf* *f*) 7) ; [S15]
(test-shebang (nats "#!/**") 5) ; [S21]

; A comment that is closed, and then no "[".

(test-shebang (nats "#!/* a" *lf* " b */ " *f*) 6) ; [S12]
(test-shebang (nats "#!/* c */") 9) ; [S23]
(test-shebang (nats "#!// c" *lf* *f*) 6)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Files.

; The sample file has 24,776 characters, all ASCII, and no carriage return.

(assert!-stobj
 (b* (((mv stext state)
       (source-text-from-file "../../samples/aes_fixslice_encrypt.rs" state)))
   (mv (and (not (reserrp stext))
            (equal (len (source-text->text stext)) 24776)
            (not (source-text->bom stext))
            (not (source-text->crs stext))
            (equal (shebang-length (source-text->text stext)) 0))
       state))
 state)

; A file that does not exist.

(assert!-stobj
 (b* (((mv stext state) (source-text-from-file "no-such-file.rs" state)))
   (mv (reserrp stext) state))
 state)
