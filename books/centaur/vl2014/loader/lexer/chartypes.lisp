; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "defchar")
(local (include-book "../../util/arithmetic"))

(defxdoc chartypes
  :parents (lexer)
  :short "Recognizers for basic character types (e.g., whitespace characters,
alphabetic characters, etc.), typically introduced with @(see defchar).")

(local (xdoc::set-default-parents chartypes))

(defmacro explicit-char-code (x)
  ;; Because this is a macro we know it resolves to a character code at compile
  ;; time.
  (declare (xargs :guard (characterp x)))
  (char-code x))

(defsection whitespace
  :short "We say whitespace includes spaces, tabs, newlines, carriage returns,
form feeds, and vertical tabs."

  :long "<p>The Verilog-2005 and SystemVerilog-2012 grammars both define
whitespace as follows:</p>

@({
     white_space ::= space | tab | newline | eof
})

<p>We do not consider EOF a character.  Instead, it the condition encountered
when the list we are processing runs out of characters.  The only place this
seems to matter is in our handling of escaped identifiers, where we believe we
account for it appropriately.</p>

<p>Section 3.2 of the Verilog-2005 spec contradicts the above definition and
says that whitespace also includes form feeds.  Section 5.3 of the
SystemVerilog-2012 spec says the same thing.  Testing shows that Verilog-XL
tolerates form feed characters as whitespace.  We therefore include form
feeds (ASCII character 12, Common Lisp #\\Page) in our definition of
whitespace.</p>

<p>It seems reasonable to also allow whitespace to include carriage
return (ASCII character 13) and vertical tab characters (ASCII character
11).</p>")

(defsection whitespace-mask
  :parents (whitespace)
  :short "We optimize the recognition of whitespace by basically using a
bitset."
  :long "<p>This is probably silly and not worth the effort.</p>"

  (defmacro vertical-tab-char () (code-char 11))
  (defmacro carriage-return-char () (code-char 13))

  (defmacro whitespace-mask ()
    ;; To generate this mask:
    ;; (include-book "centaur/bitops/bitsets" :dir :system)
    ;; (acl2::bitset-list (char-code #\Space)
    ;;                    (char-code #\Tab)
    ;;                    (char-code #\Page)
    ;;                    (char-code #\Newline)
    ;;                    (char-code (vertical-tab-char))
    ;;                    (char-code (carriage-return-char)))
    4294983168))

(defsection whitespace-p

  (local (in-theory (disable logbitp)))

  (local (defun test (n)
           (and (equal (logbitp n (whitespace-mask))
                       (let ((x (code-char n)))
                         (or (eql x #\Space)
                             (eql x #\Tab)
                             (eql x #\Page)
                             (eql x #\Newline)
                             (eql x (vertical-tab-char))
                             (eql x (carriage-return-char)))))
                (or (zp n)
                    (test (- n 1))))))

  (local (defthm test-lemma
           (implies (and (test n)
                         (natp i)
                         (natp n)
                         (<= i n))
                    (equal (logbitp i (whitespace-mask))
                           (let ((x (code-char i)))
                             (or (eql x #\Space)
                                 (eql x #\Tab)
                                 (eql x #\Page)
                                 (eql x #\Newline)
                                 (eql x (vertical-tab-char))
                                 (eql x (carriage-return-char))))))
           :hints(("Goal" :induct (test n)))))

  (local (defthm test-consequence
           (implies (characterp x)
                    (equal (logbitp (char-code x) (whitespace-mask))
                           (or (eql x #\Space)
                               (eql x #\Tab)
                               (eql x #\Page)
                               (eql x #\Newline)
                               (eql x (vertical-tab-char))
                               (eql x (carriage-return-char)))))
           :hints(("Goal" :use ((:instance test-lemma
                                           (n 255)
                                           (i (char-code x))))))))

  (defchar whitespace
    (mbe :logic (or (eql x #\Space)
                    (eql x #\Tab)
                    (eql x #\Page) ;; "form feed"
                    (eql x #\Newline)
                    (eql x (vertical-tab-char))
                    (eql x (carriage-return-char)))
         :exec (logbitp (char-code x) (whitespace-mask)))
    :parents (whitespace)))

(defchar printable-not-whitespace
  (b* (((the (unsigned-byte 8) code) (char-code x)))
    (and (<= 33 code)
         (<= code 126)))
  :parents (whitespace lex-identifiers)
  :short "Match any printable non-whitespace character."
  :long "<p>These characters are of interest in escaped identifiers.  We don't
have to explicitly check for whitespace, because that's ruled out by the
character code range.</p>")

(defrule printable-not-whitespace-not-whitespace
  :parents (vl-printable-not-whitespace-p)
  (implies (vl-whitespace-p x)
           (not (vl-printable-not-whitespace-p x)))
  :hints(("Goal" :in-theory (enable vl-whitespace-p
                                    vl-printable-not-whitespace-p))))


(defchar simple-id-head
  (b* (((the (unsigned-byte 8) code) (char-code x)))
    (and (<= (explicit-char-code #\A) code)
         (<= code (explicit-char-code #\z))
         (or (<= (explicit-char-code #\a) code) ;; lower-case
             (<= code (explicit-char-code #\Z)) ;; upper-case
             (= code (explicit-char-code #\_))  ;; underscore
             )))
  :parents (lex-identifiers chartypes)
  :short "[a-zA-Z_]"
  :long "<p>We originally defined this as:</p>
@({
     (or (and (char<= #\a x) (char<= x #\z))
         (and (char<= #\A x) (char<= x #\Z))
         (eql x #\_))
})

<p>The new definition is about 15% faster according to simple tests.  We take
advantage of the ASCII ordering.  We know uppercase comes before lowercase, and
underscore is between upper and lowercase.</p>

@({
  ;; (time$
  ;;  ;; 4.68 seconds with original definition,
  ;;  ;; 4.01 seconds with new definition.
  ;;  (loop for i fixnum from 1 to 1000000000 do
  ;;        (vl2014::vl-simple-id-head-p #\m)
  ;;        (vl2014::vl-simple-id-head-p #\M)
  ;;        (vl2014::vl-simple-id-head-p #\Space)))
})")

(defchar simple-id-tail
  (let ((code (char-code x)))
    (declare (type (unsigned-byte 8) code))
    (if (<= (explicit-char-code #\A) code)
        ;; Must be a letter or underscore.
        (and (<= code (explicit-char-code #\z))
             (or (<= (explicit-char-code #\a) code)   ;; lowercase
                 (<= code (explicit-char-code #\Z))   ;; uppercase
                 (= code (explicit-char-code #\_))))  ;; underscore
      ;; Must be a number or dollar.
      (if (<= (explicit-char-code #\0) code)
          (<= code (explicit-char-code #\9))
        (= code (explicit-char-code #\$)))))
  :parents (lex-identifiers chartypes)
  :short "[a-zA-Z0-9_$]"
  :long "<p>Original definition was:</p>

@({
    (or (and (char<= #\a x) (char<= x #\z))
        (and (char<= #\A x) (char<= x #\Z))
        (and (char<= #\0 x) (char<= x #\9))
        (eql x #\_)
        (eql x #\$))
})

<p>The new definition is almost twice as fast according to simple tests.  We
take advantage of ASCII ordering.  Uppercase comes before lowercase, and
underscore is in between.  Numbers are before uppercase, and dollar is before
numbers.  We first check against upper-case A.  If it's greater, it must be a
letter or underscore.  Otherwise, it must be a number or dollar.</p>

@({
  ;; (time$
  ;;  ;; 7.698 seconds with original definition
  ;;  ;; 4.690 seconds with alt definition
  ;;  (loop for i fixnum from 1 to 1000000000 do
  ;;        (vl2014::vl-simple-id-tail-p #\m)
  ;;        (vl2014::vl-simple-id-tail-p #\M)
  ;;        (vl2014::vl-simple-id-tail-p #\Space)))
})")

(defthm vl-simple-id-tail-p-when-vl-simple-id-head-p
  (implies (vl-simple-id-head-p x)
           (vl-simple-id-tail-p x))
  :hints(("Goal" :in-theory (enable vl-simple-id-head-p
                                    vl-simple-id-tail-p))))



(defchar z-digit
  (or (eql x #\z)
      (eql x #\Z)
      (eql x #\?))
  :parents (chartypes lex-numbers)
  :short "z | Z | ?")

(defchar x-digit
  (or (eql x #\x)
      (eql x #\X))
  :parents (chartypes lex-numbers)
  :short "x | X")

(defchar hex-digit
  (if (char<= x #\9)
      (char<= #\0 x)
    (or (and (char<= #\a x) (char<= x #\f))
        (and (char<= #\A x) (char<= x #\F))
        (vl-x-digit-p x)
        (vl-z-digit-p x)))
  :parents (chartypes lex-numbers)
  :short "x_digit | z_digit | [0-9a-fA-F]"
  :long "<p>We originally defined this as:</p>
@({
    (or (vl-x-digit-p x)
        (vl-z-digit-p x)
        (and (char<= #\0 x) (char<= x #\9))
        (and (char<= #\a x) (char<= x #\f))
        (and (char<= #\A x) (char<= x #\F)))
})

<p>The new definition takes advantage of the fact that in ASCII, the digits
come before ? or letters, and tries to optimize for numbers.</p>")

(defchar octal-digit
  (if (char<= x #\7)
      (char<= #\0 x)
    (or (vl-x-digit-p x)
        (vl-z-digit-p x)))
  :parents (chartypes lex-numbers)
  :short "x_digit | z_digit | [0-7]"
  :long "<p>We originally defined this as:</p>
@({
    (or (vl-x-digit-p x)
        (vl-z-digit-p x)
        (and (char<= #\0 x) (char<= x #\7)))
})

<p>The new definition takes advantage of the fact that in ASCII, the digits
come before ? or letters.</p>")


(defchar binary-digit
  (or (eql x #\0)
      (eql x #\1)
      (vl-x-digit-p x)
      (vl-z-digit-p x))
  :parents (chartypes lex-numbers)
  :short "x_digit | z_digit | 0 | 1")

(defchar decimal-digit
  (and (char<= #\0 x)
       (char<= x #\9))
  :parents (chartypes lex-numbers)
  :short "[0-9]")

(defchar non-zero-decimal-digit
  (and (char<= #\1 x)
       (char<= x #\9))
  :parents (chartypes lex-numbers)
  :short "[1-9]")


(defchar underscore-or-hex-digit
  (or (vl-hex-digit-p x)
      (eql x #\_))
  :parents (chartypes lex-numbers)
  :short "_ | hex_digit")

(defchar underscore-or-octal-digit
  (or (vl-octal-digit-p x)
      (eql x #\_))
  :parents (chartypes lex-numbers)
  :short "_ | octal_digit")

(defchar underscore-or-binary-digit
  (or (vl-binary-digit-p x)
      (eql x #\_))
  :parents (chartypes lex-numbers)
  :short "_ | binary_digit")

(defchar underscore-or-decimal-digit
  (or (vl-decimal-digit-p x)
      (eql x #\_))
  :parents (chartypes lex-numbers)
  :short "_ | decimal_digit")

(defchar underscore
  (eql x #\_)
  :parents (chartypes)
  :short "_")

