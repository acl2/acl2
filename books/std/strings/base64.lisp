; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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

(in-package "STR")
(include-book "std/util/define" :dir :system)
(include-book "cat")
(include-book "decimal")
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "arithmetic"))

(defsection base64
  :parents (std/strings)
  :short "Routines for Base 64 string encoding/decoding."

  :long "<p>We implement ACL2 functions for Base 64 encoding and decoding as
described in <a href='http://www.ietf.org/rfc/rfc4648.txt'>RFC 4648</a>.</p>

<p>Our functions are quite efficient, given the constraints of ACL2 string
processing.  We prove the following inversion theorem, which shows that if
encode some text and then try to decode it, then (1) decoding succeeds and (2)
we get the original text back.</p>

@(thm base64-decode-of-base64-encode)

<p>Of course, this theorem does not say anything about whether we have encoded
or decoded the text \"correctly\" as described in RFC 4648.  After all, if we
simply used the identity function as our encoder and decoder, the above theorem
would still hold.</p>

<p>However, to the degree possible, our encoder/decoder are intended to
implement Base64 encoding as described by RFC 4648.  We do not implement
variants of base64 encoding such as \"base64 URL encoding\" and \"base64 MIME
encoding.\" Some particular details of our implementation:</p>

<ul>

<li>Per Section 3.1, our encoder does not add line breaks.</li>

<li>Per Section 3.2, our encoder adds appropriate padding characters.</li>

<li>Per Section 3.3, our decoder rejects data with non-alphabet
characters.</li>

<li>Per Section 3.5, our encoder sets the pad bits to zero.</li>

<li>We use the Base64 alphabet described in Table 1.  We do not use the \"URL
and Filename safe\" Base64 alphabet.</li>

</ul>

<p>We have not attempted to prove the \"other\" inversion property, i.e., if we
start with some encoded text, decode it, and re-encode the result, then we
should get back our initial, encoded text.  This is probably not currently
true.  To prove it, we would need to change the decoder to reject inputs where
the pad bits are nonzero.  Implementations \"may\" choose to implement this
check according to Section 3.5, and in principle it would be a nice
enhancement.</p>")


(defsection base64-impl
  :parents (base64)
  :short "Implementation details of @(see base64) encoding/decoding."

  :long "<p>These routines should generally not be used directly, and may be
changed in future versions of the library.</p>

<p>Here are some naming conventions used throughout these functions:</p>

<ul>

<li><b>chars</b> refer to actual @(see acl2::characters), which typically will
be in the Base64 alphabet, i.e., @('A-Z'), @('a-z'), @('0-9'), @('+'), and
@('/').  Of course, when decoding, data might be coming from some external
source; it might contain pad characters @('=') or even arbitrary, invalid
characters from beyond the Base64 alphabet.</li>

<li><b>codes</b> refer to actual @(see char-code)s, with the usual
correspondence to <i>chars</i>.</li>

<li><b>values</b> refer to the interpretation of each Base64 character as a
numeric value.  For instance, the value of @('#\\A') is 0; the value of @('#\\B')
is 1, and so on.  In our representation, the values are exactly the 64 natural
numbers from 0-63, and can be recognized with, e.g., @('(unsigned-byte-p 6
val)').</li>

<li><b>bytes</b> refer to ordinary 8-bit bytes, which typically will be part of
the original, un-encoded data.</li>

</ul>")


; ----------------------------------------------------------------------------
;
;                           SUPPORTING LEMMAS
;
; ----------------------------------------------------------------------------

(define char-code-list ((x character-listp))
  (if (atom x)
      nil
    (cons (char-code (car x))
          (char-code-list (cdr x)))))

(local (defsection characterp-of-char

         (local (defthm x0
                  (equal (< (+ c a) (+ c b))
                         (< a b))))

         (local (defthm x1
                  (equal (< (+ -1 a) b)
                         (< a (+ 1 b)))
                  :hints(("Goal"
                          :in-theory (disable x0)
                          :use ((:instance x0 (c 1)
                                           (a (+ -1 a))
                                           (b b)))))))

         (local (defthm characterp-of-nth
                  (implies (character-listp x)
                           (equal (characterp (nth n x))
                                  (< (nfix n) (len x))))))

         (defthm characterp-of-char
           (equal (characterp (char s n))
                  (< (nfix n) (len (explode s)))))))

(local (defsection unsigned-byte-p-lemmas

         (defthm unsigned-byte-p-6-upper-bound
           (implies (unsigned-byte-p 6 x)
                    (< x 64)))

         (defthm unsigned-byte-p-8-upper-bound
           (implies (unsigned-byte-p 8 x)
                    (< x 256)))

         (defthm unsigned-byte-p-8-of-char-code
           (unsigned-byte-p 8 (char-code x)))))

(local (in-theory (disable unsigned-byte-p char)))

(local (defthm true-listp-when-character-listp
         (implies (character-listp x)
                  (true-listp x))
         :rule-classes ((:rewrite) (:compound-recognizer))))

(local (defthm stringp-when-character-listp
         (implies (character-listp x)
                  (equal (stringp x)
                         nil))))

(local (defthm consp-under-iff-when-true-listp
         (implies (true-listp x)
                  (iff (consp x)
                       x))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))




; ----------------------------------------------------------------------------
;
;                 Value (0-63) <---> Base 64 Alphabet Character
;
; ----------------------------------------------------------------------------

(defsection *b64-chars-from-vals-array*
  :parents (b64-char-from-value)
  :short "Array mapping each value to its associated character."

  :long "<p>This array is the main lookup table used for encoding.  It
corresponds to Table 1 from RFC 4648.</p>

@(def *b64-chars-from-vals-alist*)
@(def *b64-chars-from-vals-array*)"

  (defconst *b64-chars-from-vals-alist*
    '((0  . #\A)
      (1  . #\B)
      (2  . #\C)
      (3  . #\D)
      (4  . #\E)
      (5  . #\F)
      (6  . #\G)
      (7  . #\H)
      (8  . #\I)
      (9  . #\J)
      (10 . #\K)
      (11 . #\L)
      (12 . #\M)
      (13 . #\N)
      (14 . #\O)
      (15 . #\P)
      (16 . #\Q)
      (17 . #\R)
      (18 . #\S)
      (19 . #\T)
      (20 . #\U)
      (21 . #\V)
      (22 . #\W)
      (23 . #\X)
      (24 . #\Y)
      (25 . #\Z)
      (26 . #\a)
      (27 . #\b)
      (28 . #\c)
      (29 . #\d)
      (30 . #\e)
      (31 . #\f)
      (32 . #\g)
      (33 . #\h)
      (34 . #\i)
      (35 . #\j)
      (36 . #\k)
      (37 . #\l)
      (38 . #\m)
      (39 . #\n)
      (40 . #\o)
      (41 . #\p)
      (42 . #\q)
      (43 . #\r)
      (44 . #\s)
      (45 . #\t)
      (46 . #\u)
      (47 . #\v)
      (48 . #\w)
      (49 . #\x)
      (50 . #\y)
      (51 . #\z)
      (52 . #\0)
      (53 . #\1)
      (54 . #\2)
      (55 . #\3)
      (56 . #\4)
      (57 . #\5)
      (58 . #\6)
      (59 . #\7)
      (60 . #\8)
      (61 . #\9)
      (62 . #\+)
      (63 . #\/)))

  (defconst *b64-chars-from-vals-array*
    (compress1 '*b64-chars-from-vals-array*
               (cons (list :header
                           :dimensions (list 64)
                           :maximum-length 65
                           :default #\0
                           :name '*b64-chars-from-vals-array*)
                     *b64-chars-from-vals-alist*))))

(defsection *b64-vals-from-codes-array*
  :parents (b64-value-from-code)
  :short "Array mapping each character code back to its associated value."

  :long "<p>This is the main lookup table used for decoding.  It covers every
character code from 0...255.  Codes for characters that aren't part of the
Base64 alphabet are mapped to NIL.</p>

@(def *b64-vals-from-codes-array*)"

  (defconst *b64-vals-from-codes-array*
    (compress1 '*b64-vals-from-codes-array*
               (cons (list :header
                           :dimensions (list 256)
                           :maximum-length 257
                           :default nil
                           :name '*b64-vals-from-codes-array*)
                     (pairlis$ (char-code-list (strip-cdrs *b64-chars-from-vals-alist*))
                               (strip-cars *b64-chars-from-vals-alist*))))))


(define b64-char-from-value ((value :type (unsigned-byte 6)))
  :returns (char characterp :rule-classes :type-prescription)
  :parents (base64-impl)
  :short "Look up the Base64 character for a value, e.g., @('0') &rarr; @('#\\A')."
  :long "<p>This is our lowest level encoding function.  It's just an array
lookup.</p>"
  :inline t
  (the character (aref1 '*b64-chars-from-vals-array*
                        *b64-chars-from-vals-array*
                        value))
  ///
  (defthm b64-char-from-value-never-produces-a-pad
    (not (equal (b64-char-from-value value) #\=))))


(define b64-value-from-code ((code :type (unsigned-byte 8)))
  :returns (value (or (not value)
                      (natp value))
                  :rule-classes :type-prescription)
  :parents (base64-impl)
  :short "Look up the value of a Base64 character code, e.g., @('(char-code
#\\A)') &rarr; @('0')."
  :long "<p>This is our lowest level decoding function.  It's just an array
lookup.  Codes for characters that aren't part of the Base64 alphabet are
mapped to NIL.</p>"
  :inline t
  (aref1 '*b64-vals-from-codes-array*
         *b64-vals-from-codes-array*
         (lnfix code))
  ///
  (defthm unsigned-byte-p-6-of-b64-value-from-code
    (iff (unsigned-byte-p 6 (b64-value-from-code code))
         (b64-value-from-code code)))

  (defthm b64-value-from-code-of-b64-char-from-value
    (implies (unsigned-byte-p 6 value)
             (equal (b64-value-from-code (char-code (b64-char-from-value value)))
                    value))
    :hints(("Goal" :in-theory (e/d (b64-char-from-value unsigned-byte-p)
                                   (equal-of-char-code-and-constant))))))



; ----------------------------------------------------------------------------
;
;                    3 Bytes (0-255) <---> 4 Values (0-63)
;
; ----------------------------------------------------------------------------

(define b64-vals-from-bytes (b1 b2 b3)
  (declare (type (unsigned-byte 8) b1 b2 b3))
  :returns (mv (v1 natp :rule-classes :type-prescription)
               (v2 natp :rule-classes :type-prescription)
               (v3 natp :rule-classes :type-prescription)
               (v4 natp :rule-classes :type-prescription))
  :parents (base64-impl)
  :short "Encode 3 bytes into 4 base-64 characters."
  :long "<p>Convert three bytes into four values, basically as follows:</p>
@({
      Byte   Bit Pattern  --->  Values
      b1      aaaaaabb           aaaaaa  v1
      b2      bbbbcccc           bbbbbb  v2
      b3      ccdddddd           cccccc  v3
                                 dddddd  v4
})"
  :inline t
  (b* ((v1  (the (unsigned-byte 6) (ash (lnfix b1) -2)))           ;; top 6 bits of b1

       (v2h (the (unsigned-byte 2) (logand (lnfix b1) #b11)))      ;; bottom 2 bits of b1
       (v2l (the (unsigned-byte 4) (ash (lnfix b2) -4)))           ;; top 4 bits of b2
       (v2  (the (unsigned-byte 6)
             (logior (the (unsigned-byte 6)
                       (ash (the (unsigned-byte 2) v2h) 4))
                     (the (unsigned-byte 4) v2l))))

       (v3h (the (unsigned-byte 4) (logand (lnfix b2) #b1111)))    ;; bottom 4 bits of b2
       (v3l (the (unsigned-byte 2) (ash (lnfix b3) -6)))           ;; top 2 bits of b3
       (v3 (the (unsigned-byte 6)
            (logior (the (unsigned-byte 6)
                      (ash (the (unsigned-byte 4) v3h) 2))
                    (the (unsigned-byte 2) v3l))))

       (v4  (the (unsigned-byte 6) (logand (lnfix b3) #b111111)))) ;; bottom 6 bits of b3

    (mv v1 v2 v3 v4))
  ///
  (defthm unsigned-byte-p-6-of-b64-vals-from-bytes
    (implies (and (force (unsigned-byte-p 8 b1))
                  (force (unsigned-byte-p 8 b2))
                  (force (unsigned-byte-p 8 b3)))
             (b* (((mv v1 v2 v3 v4) (b64-vals-from-bytes b1 b2 b3)))
               (and (unsigned-byte-p 6 v1)
                    (unsigned-byte-p 6 v2)
                    (unsigned-byte-p 6 v3)
                    (unsigned-byte-p 6 v4)))))

  ;; Some lemmas related to the correctness of padding:

  (defthm b64-vals-from-bytes-padding-1
    (b* (((mv ?v1 ?v2 ?v3 ?v4) (b64-vals-from-bytes b1 b2 0)))
      (equal v4 0)))

  (defthm b64-vals-from-bytes-padding-2
    (b* (((mv ?v1 ?v2 ?v3 ?v4) (b64-vals-from-bytes b1 0 0)))
      (equal v3 0))))



(define b64-bytes-from-vals (v1 v2 v3 v4)
  (declare (type (unsigned-byte 6) v1 v2 v3 v4))
  :returns (mv (b1 natp :rule-classes :type-prescription)
               (b2 natp :rule-classes :type-prescription)
               (b3 natp :rule-classes :type-prescription))
  :parents (base64-impl)
  :short "Decode 4 base-64 values into 3 bytes."
  :long "<p>This is just doing the inverse of @(see b64-vals-from-bytes).</p>"
  :inline t
  (b* ((b1 (the (unsigned-byte 8)
            (logior (the (unsigned-byte 8) (ash (lnfix v1) 2))
                    (the (unsigned-byte 8) (ash (lnfix v2) -4)))))
       (b2 (the (unsigned-byte 8)
            (logior (the (unsigned-byte 8)
                      (ash (the (unsigned-byte 8) (logand (lnfix v2) #b1111)) 4))
                    (the (unsigned-byte 8) (ash (lnfix v3) -2)))))
       (b3 (the (unsigned-byte 8)
            (logior (the (unsigned-byte 8)
                      (ash (the (unsigned-byte 8) (logand (lnfix v3) #b11)) 6))
                    (lnfix v4)))))
    (mv b1 b2 b3))
  ///
  (defthm unsigned-byte-p-8-of-b64-decode-4-chars
    (implies (and (force (unsigned-byte-p 6 v1))
                  (force (unsigned-byte-p 6 v2))
                  (force (unsigned-byte-p 6 v3))
                  (force (unsigned-byte-p 6 v4)))
             (b* (((mv b1 b2 b3) (b64-bytes-from-vals v1 v2 v3 v4)))
               (and (unsigned-byte-p 8 b1)
                    (unsigned-byte-p 8 b2)
                    (unsigned-byte-p 8 b3)))))

  (defthm b64-bytes-from-vals-of-b64-vals-from-bytes
    (b* (((mv v1 v2 v3 v4) (b64-vals-from-bytes b1 b2 b3))
         ((mv x1 x2 x3)    (b64-bytes-from-vals v1 v2 v3 v4)))
      (implies (and (force (unsigned-byte-p 8 b1))
                    (force (unsigned-byte-p 8 b2))
                    (force (unsigned-byte-p 8 b3)))
               (and (equal x1 b1)
                    (equal x2 b2)
                    (equal x3 b3))))
    :hints(("Goal" :in-theory (enable b64-vals-from-bytes))
           (acl2::equal-by-logbitp-hammer)))

  ;; Some corollaries related to the correctness of padding:

  (defthm b64-bytes-from-vals-padding-1
    (b* (((mv v1 v2 v3 ?v4) (b64-vals-from-bytes b1 b2 0))
         ((mv x1 x2 ?x3)    (b64-bytes-from-vals v1 v2 v3 0)))
      (implies (and (force (unsigned-byte-p 8 b1))
                    (force (unsigned-byte-p 8 b2)))
               (and (equal x1 b1)
                    (equal x2 b2))))
    :hints(("Goal"
            :in-theory (disable b64-bytes-from-vals-of-b64-vals-from-bytes)
            :use ((:instance b64-bytes-from-vals-of-b64-vals-from-bytes
                             (b3 0))))))

  (defthm b64-bytes-from-vals-padding-2
    (b* (((mv v1 v2 ?v3 ?v4) (b64-vals-from-bytes b1 0 0))
         ((mv x1 ?x2 ?x3)    (b64-bytes-from-vals v1 v2 0 0)))
      (implies (force (unsigned-byte-p 8 b1))
               (equal x1 b1)))
    :hints(("Goal"
            :in-theory (disable b64-bytes-from-vals-of-b64-vals-from-bytes)
            :use ((:instance b64-bytes-from-vals-of-b64-vals-from-bytes
                             (b2 0)
                             (b3 0)))))))




; ----------------------------------------------------------------------------
;
;                    Character List Encoding/Decoding
;
; ----------------------------------------------------------------------------

; Encoding is somewhat nicer than decoding because we don't have to worry about
; how to handle extraneous characters, etc.

(define b64-enc3 (c1 c2 c3)
  (declare (type character c1 c2 c3))
  :returns (mv (e1 characterp :rule-classes :type-prescription)
               (e2 characterp :rule-classes :type-prescription)
               (e3 characterp :rule-classes :type-prescription)
               (e4 characterp :rule-classes :type-prescription))
  :parents (base64-impl)
  :short "Encode 3 arbitrary characters into 4 base-64 characters."
  :long "<p>This is the main function for encoding, which is used for all but
perhaps the last one or two characters.</p>"
  (b* ((byte1 (char-code c1))
       (byte2 (char-code c2))
       (byte3 (char-code c3))
       ((mv val1 val2 val3 val4)
        (b64-vals-from-bytes byte1 byte2 byte3))
       (char1 (b64-char-from-value val1))
       (char2 (b64-char-from-value val2))
       (char3 (b64-char-from-value val3))
       (char4 (b64-char-from-value val4)))
    (mv char1 char2 char3 char4)))

(define b64-enc2 (c1 c2)
  (declare (type character c1 c2))
  :returns (mv (e1 characterp :rule-classes :type-prescription)
               (e2 characterp :rule-classes :type-prescription)
               (e3 characterp :rule-classes :type-prescription))
  :parents (base64-impl)
  :short "Encode 2 final characters into base-64 characters."
  :long "<p>This is only used if we have almost reached the end of the string
and there are exactly two characters left to encode; note that in this case we
also need to insert one explicit pad character (=).</p>"
  (b* ((byte1 (char-code c1))
       (byte2 (char-code c2))
       ((mv val1 val2 val3 &) (b64-vals-from-bytes byte1 byte2 0))
       (char1 (b64-char-from-value val1))
       (char2 (b64-char-from-value val2))
       (char3 (b64-char-from-value val3)))
    (mv char1 char2 char3)))

(define b64-enc1 (c1)
  (declare (type character c1))
  :returns (mv (e1 characterp :rule-classes :type-prescription)
               (e2 characterp :rule-classes :type-prescription))
  :parents (base64-impl)
  :short "Encode 1 final character into base-64 characters."
  :long "<p>This is only used if we have almost reached the end of the string
and there is exactly one character left to encode; note that in this case we
need to insert two explicit pad characters (=).</p>"
  (b* ((byte1 (char-code c1))
       ((mv val1 val2 & &) (b64-vals-from-bytes byte1 0 0))
       (char1 (b64-char-from-value val1))
       (char2 (b64-char-from-value val2)))
    (mv char1 char2)))

(define b64-encode-last-group ((x character-listp))
  :returns (mv (e1 characterp :rule-classes :type-prescription)
               (e2 characterp :rule-classes :type-prescription)
               (e3 characterp :rule-classes :type-prescription)
               (e4 characterp :rule-classes :type-prescription))
  :guard (consp x)
  :parents (base64-impl)
  :short "Encode the last group of (up to three) characters."
  (cond ((atom (cdr x))
         ;; Only one character, need two pads
         (b* (((mv c1 c2) (b64-enc1 (first x))))
           (mv c1 c2 #\= #\=)))
        ((atom (cddr x))
         ;; Only two characters, need one pad
         (b* (((mv c1 c2 c3) (b64-enc2 (first x) (second x))))
           (mv c1 c2 c3 #\=)))
        (t
         ;; Three characters, no pads
         (b64-enc3 (first x) (second x) (third x)))))

(define b64-encode-list-impl ((x character-listp)
                              (acc))
  :returns (acc character-listp :hyp (character-listp acc))
  :parents (base64-impl)
  :short "Tail-recursive version of @(see base64-encode-list)."
  (b* (((when (atom x))
        acc)
       ((when (atom (cdddr x)))
        (b* (((mv c1 c2 c3 c4) (b64-encode-last-group x)))
          (list* c4 c3 c2 c1 acc)))
       ((mv c1 c2 c3 c4)
        (b64-enc3 (first x) (second x) (third x)))
       (acc (list* c4 c3 c2 c1 acc)))
    (b64-encode-list-impl (cdddr x) acc)))

(define base64-encode-list ((x character-listp "Character list to encode."))
  :returns (x-enc character-listp "Encoded version of @('x').")
  :parents (base64)
  :short "Base64 encode a character list."
  :verify-guards nil
  (mbe :logic (b* (((when (atom x))
                    nil)
                   ((when (atom (cdddr x)))
                    (b* (((mv c1 c2 c3 c4) (b64-encode-last-group x)))
                      (list c1 c2 c3 c4)))
                   ((mv c1 c2 c3 c4)
                    (b64-enc3 (first x) (second x) (third x))))
                (append (list c1 c2 c3 c4)
                        (base64-encode-list (cdddr x))))
       :exec (reverse (b64-encode-list-impl x nil)))
  ///
  (defthm b64-encode-list-impl-removal
    (equal (b64-encode-list-impl x acc)
           (revappend (base64-encode-list x) acc))
    :hints(("Goal" :in-theory (enable b64-encode-list-impl))))

  (verify-guards base64-encode-list))




(define b64-dec3 (c1 c2 c3 c4)
  (declare (type character c1 c2 c3 c4))
  :parents (base64-impl)
  :short "Decode 3 arbitrary characters from 4 base-64 characters."
  :long "<p>This is the main function for decoding, which is used for all but
perhaps the last one or two characters.</p>"
  :returns (mv (okp booleanp
                    "Decoding can fail if we encounter non Base-64 alphabetic
                     characters in the input."
                    :rule-classes :type-prescription)
               (d1  characterp :rule-classes :type-prescription)
               (d2  characterp :rule-classes :type-prescription)
               (d3  characterp :rule-classes :type-prescription))
  (b* ((code1 (char-code c1))
       (code2 (char-code c2))
       (code3 (char-code c3))
       (code4 (char-code c4))
       (val1  (b64-value-from-code code1))
       (val2  (b64-value-from-code code2))
       (val3  (b64-value-from-code code3))
       (val4  (b64-value-from-code code4))
       ((unless (and val1 val2 val3 val4))
        (mv nil #\0 #\0 #\0))
       ((mv (the (unsigned-byte 8) b1)
            (the (unsigned-byte 8) b2)
            (the (unsigned-byte 8) b3))
        (b64-bytes-from-vals val1 val2 val3 val4))
       (char1 (code-char b1))
       (char2 (code-char b2))
       (char3 (code-char b3)))
    (mv t char1 char2 char3))
  ///
  (defthm b64-dec3-of-b64-enc3
    (implies (and (characterp c1)
                  (characterp c2)
                  (characterp c3))
             (b* (((mv e1 e2 e3 e4)  (b64-enc3 c1 c2 c3))
                  ((mv okp x1 x2 x3) (b64-dec3 e1 e2 e3 e4)))
               (and okp
                    (equal x1 c1)
                    (equal x2 c2)
                    (equal x3 c3))))
    :hints(("Goal" :in-theory (enable b64-enc3)))))

(define b64-dec2 (c1 c2 c3)
  (declare (type character c1 c2 c3))
  :parents (base64-impl)
  :short "Decode three base-64 characters to recover 2 arbitrary characters."
  :long "<p>This is only used to decode the last group of base-64 characters,
when there is exactly one pad.</p>"
  :returns (mv (okp booleanp
                    "Decoding can fail if we encounter non Base-64 alphabetic
                     characters in the input."
                    :rule-classes :type-prescription)
               (d1  characterp :rule-classes :type-prescription)
               (d2  characterp :rule-classes :type-prescription))
  (b* ((code1 (char-code c1))
       (code2 (char-code c2))
       (code3 (char-code c3))
       (val1  (b64-value-from-code code1))
       (val2  (b64-value-from-code code2))
       (val3  (b64-value-from-code code3))
       ((unless (and val1 val2 val3))
        (mv nil #\0 #\0))
       ((mv (the (unsigned-byte 8) b1)
            (the (unsigned-byte 8) b2)
            &)
        (b64-bytes-from-vals val1 val2 val3 0))
       (char1 (code-char b1))
       (char2 (code-char b2)))
    (mv t char1 char2))
  ///
  (defthm b64-dec2-of-b64-enc2
    (implies (and (characterp c1)
                  (characterp c2))
             (b* (((mv e1 e2 e3)  (b64-enc2 c1 c2))
                  ((mv okp x1 x2) (b64-dec2 e1 e2 e3)))
               (and okp
                    (equal x1 c1)
                    (equal x2 c2))))
    :hints(("Goal" :in-theory (enable b64-enc2)))))

(define b64-dec1 (c1 c2)
  (declare (type character c1 c2))
  :parents (base64-impl)
  :short "Decode two base-64 characters to recover 1 arbitrary character."
  :long "<p>This is only used to decode the last group of base-64 characters,
when there are two pads.</p>"
  :returns (mv (okp booleanp
                    "Decoding can fail if we encounter non Base-64 alphabetic
                     characters in the input."
                    :rule-classes :type-prescription)
               (d1  characterp :rule-classes :type-prescription))
  (b* ((code1 (char-code c1))
       (code2 (char-code c2))
       (val1  (b64-value-from-code code1))
       (val2  (b64-value-from-code code2))
       ((unless (and val1 val2))
        (mv nil #\0))
       ((mv (the (unsigned-byte 8) b1) & &)
        (b64-bytes-from-vals val1 val2 0 0))
       (char1 (code-char b1)))
    (mv t char1))
  ///
  (defthm b64-dec1-of-b64-enc1
    (implies (characterp c1)
             (b* (((mv e1 e2)  (b64-enc1 c1))
                  ((mv okp x1) (b64-dec1 e1 e2)))
               (and okp
                    (equal x1 c1))))
    :hints(("Goal" :in-theory (enable b64-enc1)))))

(define b64-decode-last-group (c1 c2 c3 c4)
  (declare (type character c1 c2 c3 c4))
  :returns (mv (okp booleanp)
               (ans character-listp))
  :parents (base64-impl)
  :short "Decode the final group of base-64 encoded characters into 1-3 characters."
  (cond ((not (eql c4 #\=))
         ;; There was no pad, so the length was a multiple of three and
         ;; we really can go ahead and use the main decoder.
         (b* (((mv okp char1 char2 char3) (b64-dec3 c1 c2 c3 c4)))
           (mv okp (list char1 char2 char3))))
        ((not (eql c3 #\=))
         ;; There was exactly one pad, so two characters to decode.
         (b* (((mv okp char1 char2) (b64-dec2 c1 c2 c3)))
           (mv okp (list char1 char2))))
        (t
         ;; There were two pads, so there should just be one character to decode.
         (b* (((mv okp char1) (b64-dec1 c1 c2)))
           (mv okp (list char1)))))
  ///
  (local (defthm l1
           (not (equal (mv-nth 3 (b64-enc3 c1 c2 c3)) #\=))
           :hints(("Goal" :in-theory (enable b64-enc3)))))

  (local (defthm l2
           (not (equal (mv-nth 2 (b64-enc2 c1 c2)) #\=))
           :hints(("Goal" :in-theory (enable b64-enc2)))))

  (defthm b64-decode-last-group-of-b64-encode-last-group
    (implies (and (character-listp x)
                  (consp x)
                  (atom (cdddr x)))
             (b* (((mv c1 c2 c3 c4) (b64-encode-last-group x))
                  ((mv okp result)  (b64-decode-last-group c1 c2 c3 c4)))
               (and okp
                    (equal result x))))
    :hints(("Goal" :in-theory (enable b64-encode-last-group
                                      b64-decode-last-group)))))



(define b64-decode-list-impl ((x character-listp)
                              (acc))
  :returns (mv (okp booleanp :rule-classes :type-prescription)
               (acc character-listp :hyp (character-listp acc)))
  :parents (base64-impl)
  :short "Tail-recursive version of @(see base64-decode-list)."
  (b* (((when (atom x))
        (mv t acc))
       ((when (atom (cdddr x)))
        ;; Less than four characters, so that's not valid at all, just fail.
        (mv nil acc))
       (c1 (first x))
       (c2 (second x))
       (c3 (third x))
       (c4 (fourth x))
       (rest (cddddr x))
       ((when (atom rest))
        ;; Reached the very last group.  Have to think about padding.
        (b* (((mv okp last) (b64-decode-last-group c1 c2 c3 c4)))
          (mv okp (revappend last acc))))
       ;; Else, this is a normal group.
       ((mv okp x1 x2 x3) (b64-dec3 c1 c2 c3 c4))
       ((unless okp)
        (mv nil acc))
       (acc (list* x3 x2 x1 acc)))
    (b64-decode-list-impl (cddddr x) acc)))

(define base64-decode-list ((x character-listp "Character list to decode."))
  :returns (mv (okp booleanp
                    "Was decoding successful?  It can fail if we encounter non
                     Base-64 alphabetic characters in the input, or if the
                     input is not of the proper length (a multiple of 4), or if
                     there is incorrect padding."
                    :rule-classes :type-prescription)
               (ans character-listp
                    "On success, the decoded version of @('x').  On failure,
                     it is some nonsensical character list that should not be
                     relied on."))
  :parents (base64)
  :short "Base64 decode a character list."
  :verify-guards nil
  (mbe :logic
       (b* (((when (atom x))
             (mv t nil))
            ((when (atom (cdddr x)))
             ;; Less than four characters, so that's not valid at all, just fail.
             (mv nil nil))
            (c1 (first x))
            (c2 (second x))
            (c3 (third x))
            (c4 (fourth x))
            (rest (cddddr x))
            ((when (atom rest))
             ;; Reached the very last group.  Have to think about padding.
             (b64-decode-last-group c1 c2 c3 c4))
            ;; Else, this is a normal group.
            ((mv okp x1 x2 x3) (b64-dec3 c1 c2 c3 c4))
            ((unless okp)
             (mv nil nil))
            ((mv rest-ok rest-ans)
             (base64-decode-list (cddddr x))))
         (mv (and okp rest-ok)
             (list* x1 x2 x3 rest-ans)))
       :exec
       (b* (((mv okp acc) (b64-decode-list-impl x nil)))
         (mv okp (reverse acc))))
  ///
  (local (in-theory (enable b64-decode-list-impl)))

  (local (defthm l0
           (equal (mv-nth 0 (b64-decode-list-impl x acc))
                  (mv-nth 0 (base64-decode-list x)))))

  (local (defthm l1
           (equal (mv-nth 1 (b64-decode-list-impl x acc))
                  (revappend (mv-nth 1 (base64-decode-list x))
                             acc))))

  (defthm b64-decode-list-impl-removal
    (equal (b64-decode-list-impl x acc)
           (mv (mv-nth 0 (base64-decode-list x))
               (revappend (mv-nth 1 (base64-decode-list x))
                          acc))))

  (verify-guards base64-decode-list
    ;; bleh, stupid hint to know it returns two values
    :hints(("Goal" :in-theory (enable b64-decode-last-group))))

  (defthm base64-decode-list-of-base64-encode-list
    (implies (character-listp x)
             (b* ((encoded          (base64-encode-list x))
                  ((mv okp decoded) (base64-decode-list encoded)))
               (and okp
                    (equal decoded x))))
    :hints(("Goal"
            :induct (base64-encode-list x)
            :in-theory (enable base64-encode-list
                               base64-decode-list)))))



; ----------------------------------------------------------------------------
;
;                        String Encoding/Decoding
;
; ----------------------------------------------------------------------------

(local (defsection nthcdr-lemmas

         ;; These aren't generally things you'd want, they're sort of
         ;; specialized to accessing just the first few characters from the
         ;; list, as the string encoder/decoder need to do...

         (defthm cadr-of-nthcdr
           (equal (cadr (nthcdr n x))
                  (nth (+ 1 (nfix n)) x)))

         (local (defthm nth-of-inc2-and-list*
                  (implies (natp n)
                           (equal (nth (+ 2 n) (list* a b c))
                                  (nth n c)))
                  :hints(("Goal"
                          :in-theory (enable nth)
                          :expand (nth (+ 2 n) (list* a b c))))))

         (defthm caddr-of-nthcdr
           (equal (caddr (nthcdr n x))
                  (nth (+ 2 (nfix n)) x)))

         (defthm cadddr-of-nthcdr
           (equal (cadddr (nthcdr n x))
                  (nth (+ 3 (nfix n)) x)))

         (defthm cddr-nthcdr-under-iff
           (implies (and (true-listp x)
                         (natp n))
                    (iff (cddr (nthcdr n x))
                         (< (+ 2 n) (len x)))))

         (defthm cdddr-nthcdr-under-iff
           (implies (and (true-listp x)
                         (natp n))
                    (iff (cdddr (nthcdr n x))
                         (< (+ 3 n) (len x)))))

         (defthm cddddr-nthcdr-under-iff
           (implies (and (true-listp x)
                         (natp n))
                    (iff (cddddr (nthcdr n x))
                         (< (+ 4 n) (len x)))))

         (defthm cdr-nthcdr-under-iff
           (implies (and (true-listp x)
                         (natp n))
                    (iff (cdr (nthcdr n x))
                         (< (+ 1 n) (len x)))))

         (defthm cdr-nthcdr-inc2
           (implies (natp n)
                    (equal (cdr (nthcdr (+ 2 n) x))
                           (cdddr (nthcdr n x))))
           :hints(("Goal" :expand ((nthcdr (+ 2 n) x)))))

         (defthm cdr-nthcdr-inc3
           (implies (natp n)
                    (equal (cdr (nthcdr (+ 3 n) x))
                           (cddddr (nthcdr n x))))
           :hints(("Goal" :expand ((nthcdr (+ 3 n) x)))))

         (defthm nthcdr-of-len
           (implies (true-listp x)
                    (equal (nthcdr (len x) x)
                           nil)))))


(define b64-encode-last-group-str ((x stringp)
                                   (n  natp)
                                   (xl (eql xl (length x))))
  :guard (< n xl)
  :parents (base64-impl)
  :short "String-based version of @(see b64-encode-last-group)."
  (declare (type (integer 0 *) n xl)
           (type string x))
  (b* (((the (integer 0 *) left)
        (mbe :logic (nfix (- (nfix xl) (nfix n)))
             :exec (- xl n)))
       ((when (int= left 1))
        (b* (((mv c1 c2) (b64-enc1 (char x n))))
          (mv c1 c2 #\= #\=)))
       ((when (int= left 2))
        (b* (((mv c1 c2 c3)
              (b64-enc2 (char x n) (char x (+ 1 n)))))
          (mv c1 c2 c3 #\=))))
    (b64-enc3 (char x n)
              (char x (+ 1 n))
              (char x (+ 2 n))))
  ///
  (defthm b64-encode-last-group-str-correct
    (implies (and (force (stringp x))
                  (force (natp n))
                  (force (equal xl (length x)))
                  (force (< n xl)))
             (equal (b64-encode-last-group-str x n xl)
                    (b64-encode-last-group (nthcdr n (explode x)))))
    :hints(("Goal"
            :in-theory (e/d (b64-encode-last-group char)
                            (nthcdr nth))
            :do-not '(generalize fertilize)
            :do-not-induct t))))

(define b64-encode-str-impl ((x  stringp)
                             (n  natp)
                             (xl (eql xl (length x)))
                             (acc))
  :guard (<= n xl)
  :parents (base64-impl)
  :short "Efficient, string-based version of @(see b64-encode-list-impl)."
  :measure (nfix (- (nfix xl) (nfix n)))
  (declare (type (integer 0 *) n xl)
           (type string x))
  (b* (((the (integer 0 *) left)
        (mbe :logic (nfix (- (nfix xl) (nfix n)))
             :exec (- xl n)))
       ((when (zp left))
        acc)
       ((when (<= left 3))
        (b* (((mv c1 c2 c3 c4) (b64-encode-last-group-str x n xl)))
          (list* c4 c3 c2 c1 acc)))
       ((mv c1 c2 c3 c4)
        (b64-enc3 (char x n)
                  (char x (+ 1 n))
                  (char x (+ 2 n))))
       (acc (list* c4 c3 c2 c1 acc)))
    (b64-encode-str-impl x (+ 3 (lnfix n)) xl acc))
  ///
  (local (defthm l0
           (implies (and (stringp x)
                         (natp n)
                         (equal xl (length x))
                         (<= n xl))
                    (equal (b64-encode-str-impl x n xl acc)
                           (b64-encode-list-impl (nthcdr n (explode x)) acc)))
           :hints(("Goal"
                   :induct (b64-encode-str-impl x n xl acc)
                   :in-theory (e/d (b64-encode-list-impl
                                    char)
                                   (b64-encode-list-impl-removal))
                   :expand ((b64-encode-str-impl x n xl acc)
                            (b64-encode-list-impl (nthcdr n (explode x)) acc))
                   :do-not '(generalize fertilize)
                   :do-not-induct t))))
  (defthm b64-encode-str-impl-removal
    (implies (and (stringp x)
                  (natp n)
                  (equal xl (length x))
                  (<= n xl))
             (equal (b64-encode-str-impl x n xl acc)
                    (revappend (base64-encode-list (nthcdr n (explode x)))
                               acc)))
    :hints(("Goal" :in-theory (disable b64-encode-str-impl)))))

(define base64-encode ((x stringp "String to be encoded."))
  :returns (encoded stringp :rule-classes :type-prescription
                    "Encoded version of @('x').")
  :parents (base64)
  :short "Base64 encode a string."
  (declare (type string x))
  (mbe :logic (implode (base64-encode-list (explode x)))
       :exec (rchars-to-string (b64-encode-str-impl x 0 (length x) nil))))

(define base64-revappend-encode
  ((x   stringp "String to be encoded.")
   (acc         "Accumulator for encoded characters (in reverse order)."))
  :enabled t
  :parents (base64)
  :short "Efficient @('(revappend-chars (base64-encode x) acc)')."
  :long "<p>We leave this enabled; it would be odd to reason about it.</p>"
  :prepwork ((local (in-theory (enable base64-encode revappend-chars))))
  (declare (type string x))
  (mbe :logic (revappend-chars (base64-encode x) acc)
       :exec (b64-encode-str-impl x 0 (length x) acc)))



(define b64-decode-str-impl ((x stringp)
                             (n natp)
                             (xl (equal xl (length x)))
                             (acc))
  :guard (<= n xl)
  :measure (nfix (- (nfix xl) (nfix n)))
  :returns (mv (okp booleanp :rule-classes :type-prescription)
               (acc character-listp :hyp (character-listp acc)))
  :parents (base64-impl)
  :short "Efficient, string-based version of @(see b64-decode-list-impl)."
  (declare (type (integer 0 *) n xl)
           (type string x))
  (b* (((the (integer 0 *) left)
        (mbe :logic (nfix (- (nfix xl) (nfix n)))
             :exec (- xl n)))
       ((when (zp left))
        (mv t acc))
       ((when (< left 4))
        ;; Less than four characters, so that's not valid at all, just fail.
        (mv nil acc))
       (c1 (char x n))
       (c2 (char x (+ 1 n)))
       (c3 (char x (+ 2 n)))
       (c4 (char x (+ 3 n)))
       ((when (int= left 4))
        ;; Reached the very last group.  Have to think about padding.
        (b* (((mv okp last) (b64-decode-last-group c1 c2 c3 c4)))
          (mv okp (revappend last acc))))
       ;; Else, this is a normal group.
       ((mv okp x1 x2 x3) (b64-dec3 c1 c2 c3 c4))
       ((unless okp)
        (mv nil acc))
       (acc (list* x3 x2 x1 acc)))
    (b64-decode-str-impl x (+ 4 (lnfix n)) xl acc))
  ///
  (local (defthm l0
           (implies (and (stringp x)
                         (natp n)
                         (equal xl (length x))
                         (<= n xl))
                    (equal (b64-decode-str-impl x n xl acc)
                           (b64-decode-list-impl (nthcdr n (explode x)) acc)))
           :hints(("Goal"
                   :induct (b64-decode-str-impl x n xl acc)
                   :in-theory (e/d (b64-decode-list-impl char)
                                   (b64-decode-list-impl-removal))
                   :expand ((b64-decode-str-impl x n xl acc)
                            (b64-decode-list-impl (nthcdr n (explode x)) acc))
                   :do-not '(generalize fertilize)
                   :do-not-induct t))))
  (defthm b64-decode-str-impl-removal
    (implies (and (stringp x)
                  (natp n)
                  (equal xl (length x))
                  (<= n xl))
             (equal (b64-decode-str-impl x n xl acc)
                    (let ((chars (nthcdr n (explode x))))
                      (mv (mv-nth 0 (base64-decode-list chars))
                          (revappend (mv-nth 1 (base64-decode-list chars))
                                     acc)))))
    :hints(("Goal" :in-theory (disable b64-decode-str-impl)))))


(define base64-decode
  ((x stringp "String to be decoded."))
  :returns (mv (okp booleanp
                    "Was decoding successful?  It can fail if we encounter non
                     Base-64 alphabetic characters in the input, or if the
                     input is not of the proper length (a multiple of 4), or if
                     there is incorrect padding."
                    :rule-classes :type-prescription)
               (ans stringp
                    "On success, the decoded version of @('x').  On failure,
                     it is some nonsensical string that should not be relied
                     on."
                    :rule-classes :type-prescription))
  :parents (base64)
  :short "Base64 decode a string."
  (declare (type string x))
  (mbe :logic
       (b* (((mv okp chars)
             (base64-decode-list (explode x))))
         (mv okp (implode chars)))
       :exec
       (b* (((mv okp rchars)
             (b64-decode-str-impl x 0 (length x) nil)))
         (mv okp (rchars-to-string rchars))))
  ///
  (defthm base64-decode-of-base64-encode
    (equal (base64-decode (base64-encode x))
           (mv t (if (stringp x)
                     x
                   "")))
    :hints(("Goal" :in-theory (enable base64-encode
                                      base64-decode)))))


(define base64-revappend-decode
  ((x   stringp "String to be decoded.")
   (acc         "Accumulator for decoded characters (in reverse order)."))
  :returns (mv (okp "Was decoding successful?")
               (acc))
  :enabled t
  :parents (base64)
  :short "Efficiently revappend the characters from @(see base64-decode) onto
an accumulator."
  :long "<p>We leave this enabled; it would be odd to reason about it.</p>"
  :prepwork ((local (in-theory (enable base64-decode revappend-chars))))
  :guard-debug t
  (declare (type string x))
  (mbe :logic
       (b* (((mv okp str) (base64-decode x)))
         (mv okp (revappend-chars str acc)))
       :exec
       (b64-decode-str-impl x 0 (length x) acc)))
