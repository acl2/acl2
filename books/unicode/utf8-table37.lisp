; Processing Unicode Files with ACL2
; Copyright (C) 2005-2006 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "uchar")
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "std/typed-lists/signed-byte-listp" :dir :system))


(local (defthm signed-byte-p-resolver
         (implies (and (integerp n)
                       (<= 1 n)
                       (integerp x)
                       (<= (- (expt 2 (1- n))) x)
                       (< x (expt 2 (1- n))))
                  (signed-byte-p n x))
         :hints(("Goal" :in-theory (enable signed-byte-p)))))

;; UTF-8 sequences are also required to satisfy the informal constraints as
;; established in Table 3-7, which we recreate below:
;;
;;  Row   Code Points          1st Byte    2nd Byte    3rd Byte    4th Byte
;;  1     U+0000..U+007F       00..7F
;;  2     U+0080..U+07FF       C2..DF      80..BF
;;  3     U+0800..U+0FFF       E0          A0..BF      80..BF
;;  4     U+1000..U+CFFF       E1..EC      80..BF      80..BF
;;  5     U+D000..U+D7FF       ED          80..9F      80..BF
;;  6     U+E000..U+FFFF       EE..EF      80..BF      80..BF
;;  7     U+10000..U+3FFFF     F0          90..BF      80..BF      80..BF
;;  8     U+40000..U+FFFFF     F1..F3      80..BF      80..BF      80..BF
;;  9     U+100000..U+10FFFF   F4          80..8F      80..BF      80..BF
;;
;; To ensure that these constraints are respected by our UTF-8 functions, we
;; formalize the constraints of this table rigorously below.
;;
;; Because we are formalizing the Unicode specification here, the thorough
;; reader should check to ensure that our formalization is in agreement with
;; the Unicode standard.  In particular, one should check that our copy of
;; Table 3-7 above is an accurate copy of Table 3-7 from the Standard, and
;; should also convince themselves that the functions below accurately capture
;; the meaning of these ranges.


;; We begin by explaining what codepoints are acceptable entries for each row.
;; Note that the code points accepted by each row are subsumed by the later
;; rows, i.e., any codepoint which is acceptable under row 1 is also acceptable
;; under row 2 by simply letting yyyyy = 00000.  We do nothing to try to
;; require least row constraints, since these are handled by Table 3-7.

(defund utf8-table37-codepoint-1? (x)
  "Return true iff x matches U+0000..U+007F, i.e., if it could be a
   codepoint for Row 1 in Table 3-7."
  (declare (xargs :guard (uchar? x)))
  (and (mbt (uchar? x))
       (in-range? (the-fixnum x) 0 #x7F)))

(defund utf8-table37-codepoint-2? (x)
  "Return true iff x matches U+0080..U+07FF, i.e., if it could be a
   codepoint for Row 2 in Table 3-7."
  (declare (xargs :guard (uchar? x)))
  (and (mbt (uchar? x))
       (in-range? (the-fixnum x) #x80 #x7FF)))

(defund utf8-table37-codepoint-3? (x)
  "Return true iff x matches U+0800..U+0FFF, i.e., if it could be a
   codepoint for Row 3 in Table 3-7."
  (declare (xargs :guard (uchar? x)))
  (and (mbt (uchar? x))
       (in-range? (the-fixnum x) #x800 #xFFF)))

(defund utf8-table37-codepoint-4? (x)
  "Return true iff x matches U+1000..U+CFFF, i.e., if it could be a
   codepoint for Row 4 in Table 3-7."
  (declare (xargs :guard (uchar? x)))
  (and (mbt (uchar? x))
       (in-range? (the-fixnum x) #x1000 #xCFFF)))

(defund utf8-table37-codepoint-5? (x)
  "Return true iff x matches U+D000..U+D7FF, i.e., if it could be a
   codepoint for Row 5 in Table 3-7."
  (declare (xargs :guard (uchar? x)))
  (and (mbt (uchar? x))
       (in-range? (the-fixnum x) #xD000 #xD7FF)))

(defund utf8-table37-codepoint-6? (x)
  "Return true iff x matches U+E000..U+FFFF, i.e., if it could be a
   codepoint for Row 6 in Table 3-7."
  (declare (xargs :guard (uchar? x)))
  (and (mbt (uchar? x))
       (in-range? (the-fixnum x) #xE000 #xFFFF)))

(defund utf8-table37-codepoint-7? (x)
  "Return true iff x matches U+10000..U+3FFFF, i.e., if it could be a
   codepoint for Row 7 in Table 3-7."
  (declare (xargs :guard (uchar? x)))
  (and (mbt (uchar? x))
       (in-range? (the-fixnum x) #x10000 #x3FFFF)))

(defund utf8-table37-codepoint-8? (x)
  "Return true iff x matches U+40000..U+FFFFF, i.e., if it could be a
   codepoint for Row 8 in Table 3-7."
  (declare (xargs :guard (uchar? x)))
  (and (mbt (uchar? x))
       (in-range? (the-fixnum x) #x40000 #xFFFFF)))

(defund utf8-table37-codepoint-9? (x)
  "Return true iff x matches U+100000..U+10FFFF, i.e., if it could be a
   codepoint for Row 9 in Table 3-7."
  (declare (xargs :guard (uchar? x)))
  (and (mbt (uchar? x))
       (in-range? (the-fixnum x) #x100000 #x10FFFF)))

(deftheory utf8-table37-codepoints
  '(utf8-table37-codepoint-1?
    utf8-table37-codepoint-2?
    utf8-table37-codepoint-3?
    utf8-table37-codepoint-4?
    utf8-table37-codepoint-5?
    utf8-table37-codepoint-6?
    utf8-table37-codepoint-7?
    utf8-table37-codepoint-8?
    utf8-table37-codepoint-9?))



;; We now enumerate the valid entries for the bytes of each row in Table 3-7.
;; For example, utf8-table37-bytes-4? ensures that x is a sequence of bytes
;; which matches row 4 in Table 3-7.

(defund utf8-table37-bytes-1? (x)
  "Return true iff x matches the bytes in Row 1 of Table 3-7."
  (declare (xargs :guard (and (unsigned-byte-listp 8 x)
                              (equal (len x) 1))))
  (and (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 1))
       (<= (the-fixnum (first x)) #x7F)))

(defund utf8-table37-bytes-2? (x)
  "Return true iff x matches the bytes in Row 2 of Table 3-7."
  (declare (xargs :guard (and (unsigned-byte-listp 8 x)
                              (equal (len x) 2))))
  (and (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 2))
       (in-range? (the-fixnum (first x))  #xC2 #xDF)
       (in-range? (the-fixnum (second x)) #x80 #xBF)))

(defund utf8-table37-bytes-3? (x)
  "Return true iff x matches the bytes in Row 3 of Table 3-7."
  (declare (xargs :guard (and (unsigned-byte-listp 8 x)
                              (equal (len x) 3))))
  (and (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 3))
       (= (the-fixnum (first x)) #xE0)
       (in-range? (the-fixnum (second x)) #xA0 #xBF)
       (in-range? (the-fixnum (third x))  #x80 #xBF)))

(defund utf8-table37-bytes-4? (x)
  "Return true iff x matches the bytes in Row 4 of Table 3-7."
  (declare (xargs :guard (and (unsigned-byte-listp 8 x)
                              (equal (len x) 3))))
  (and (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 3))
       (in-range? (the-fixnum (first x))  #xE1 #xEC)
       (in-range? (the-fixnum (second x)) #x80 #xBF)
       (in-range? (the-fixnum (third x))  #x80 #xBF)))

(defund utf8-table37-bytes-5? (x)
  "Return true iff x matches the bytes in Row 5 of Table 3-7."
  (declare (xargs :guard (and (unsigned-byte-listp 8 x)
                              (equal (len x) 3))))
  (and (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 3))
       (= (the-fixnum (first x)) #xED)
       (in-range? (the-fixnum (second x)) #x80 #x9F)
       (in-range? (the-fixnum (third x))  #x80 #xBF)))

(defund utf8-table37-bytes-6? (x)
  "Return true iff x matches the bytes in Row 6 of Table 3-7."
  (declare (xargs :guard (and (unsigned-byte-listp 8 x)
                              (equal (len x) 3))))
  (and (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 3))
       (in-range? (the-fixnum (first x))  #xEE #xEF)
       (in-range? (the-fixnum (second x)) #x80 #xBF)
       (in-range? (the-fixnum (third x))  #x80 #xBF)))

(defund utf8-table37-bytes-7? (x)
  "Return true iff x matches the bytes in Row 7 of Table 3-7."
  (declare (xargs :guard (and (unsigned-byte-listp 8 x)
                              (equal (len x) 4))))
  (and (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 4))
       (= (the-fixnum (first x)) #xF0)
       (in-range? (the-fixnum (second x)) #x90 #xBF)
       (in-range? (the-fixnum (third x))  #x80 #xBF)
       (in-range? (the-fixnum (fourth x)) #x80 #xBF)))

(defund utf8-table37-bytes-8? (x)
  "Return true iff x matches the bytes in Row 8 of Table 3-7."
  (declare (xargs :guard (and (unsigned-byte-listp 8 x)
                              (equal (len x) 4))))
  (and (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 4))
       (in-range? (the-fixnum (first x))  #xF1 #xF3)
       (in-range? (the-fixnum (second x)) #x80 #xBF)
       (in-range? (the-fixnum (third x))  #x80 #xBF)
       (in-range? (the-fixnum (fourth x)) #x80 #xBF)))

(defund utf8-table37-bytes-9? (x)
  "Return true iff x matches the bytes in Row 9 of Table 3-7."
  (declare (xargs :guard (and (unsigned-byte-listp 8 x)
                              (equal (len x) 4))))
  (and (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 4))
       (= (the-fixnum (first x)) #xF4)
       (in-range? (the-fixnum (second x)) #x80 #x8F)
       (in-range? (the-fixnum (third x))  #x80 #xBF)
       (in-range? (the-fixnum (fourth x)) #x80 #xBF)))

(deftheory utf8-table37-bytes
  '(utf8-table37-bytes-1?
    utf8-table37-bytes-2?
    utf8-table37-bytes-3?
    utf8-table37-bytes-4?
    utf8-table37-bytes-5?
    utf8-table37-bytes-6?
    utf8-table37-bytes-7?
    utf8-table37-bytes-8?
    utf8-table37-bytes-9?))



;; We now merge our codepoint checking and byte-sequence checking functions, to
;; create complete checks for entire rows of Table 3-7.  For example,
;; utf8-table37-row-4? checks to ensure that a codepoint and byte sequence are
;; valid under Row 4 of Table 3-7.

(defund utf8-table37-row-1? (cp x)
  "True iff cp is a codepoint and x is a byte sequence which match the
   first row in Table 3-7."
  (declare (xargs :guard (and (uchar? cp)
                              (unsigned-byte-listp 8 x)
                              (equal (len x) 1))))
  (and (mbt (uchar? cp))
       (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 1))
       (utf8-table37-codepoint-1? cp)
       (utf8-table37-bytes-1? x)))

(defund utf8-table37-row-2? (cp x)
  "True iff cp is a codepoint and x is a byte sequence which match the
   second row in Table 3-7."
  (declare (xargs :guard (and (uchar? cp)
                              (unsigned-byte-listp 8 x)
                              (equal (len x) 2))))
  (and (mbt (uchar? cp))
       (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 2))
       (utf8-table37-codepoint-2? cp)
       (utf8-table37-bytes-2? x)))

(defund utf8-table37-row-3? (cp x)
  "True iff cp is a codepoint and x is a byte sequence which match the
   third row of Table 3-7."
  (declare (xargs :guard (and (uchar? cp)
                              (unsigned-byte-listp 8 x)
                              (equal (len x) 3))))
  (and (mbt (uchar? cp))
       (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 3))
       (utf8-table37-codepoint-3? cp)
       (utf8-table37-bytes-3? x)))

(defund utf8-table37-row-4? (cp x)
  "True iff cp is a codepoint and x is a byte sequence which match the
   fourth row of Table 3-7."
  (declare (xargs :guard (and (uchar? cp)
                              (unsigned-byte-listp 8 x)
                              (equal (len x) 3))))
  (and (mbt (uchar? cp))
       (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 3))
       (utf8-table37-codepoint-4? cp)
       (utf8-table37-bytes-4? x)))

(defund utf8-table37-row-5? (cp x)
  "True iff cp is a codepoint and x is a byte sequence which match the
   fifth row of Table 3-7."
  (declare (xargs :guard (and (uchar? cp)
                              (unsigned-byte-listp 8 x)
                              (equal (len x) 3))))
  (and (mbt (uchar? cp))
       (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 3))
       (utf8-table37-codepoint-5? cp)
       (utf8-table37-bytes-5? x)))

(defund utf8-table37-row-6? (cp x)
  "True iff cp is a codepoint and x is a byte sequence which match the
   sixth row of Table 3-7."
  (declare (xargs :guard (and (uchar? cp)
                              (unsigned-byte-listp 8 x)
                              (equal (len x) 3))))
  (and (mbt (uchar? cp))
       (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 3))
       (utf8-table37-codepoint-6? cp)
       (utf8-table37-bytes-6? x)))

(defund utf8-table37-row-7? (cp x)
  "True iff cp is a codepoint and x is a byte sequence which match the
   seventh row of Table 3-7."
  (declare (xargs :guard (and (uchar? cp)
                              (unsigned-byte-listp 8 x)
                              (equal (len x) 4))))
  (and (mbt (uchar? cp))
       (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 4))
       (utf8-table37-codepoint-7? cp)
       (utf8-table37-bytes-7? x)))

(defund utf8-table37-row-8? (cp x)
  "True iff cp is a codepoint and x is a byte sequence which match the
   eighth row of Table 3-7."
  (declare (xargs :guard (and (uchar? cp)
                              (unsigned-byte-listp 8 x)
                              (equal (len x) 4))))
  (and (mbt (uchar? cp))
       (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 4))
       (utf8-table37-codepoint-8? cp)
       (utf8-table37-bytes-8? x)))

(defund utf8-table37-row-9? (cp x)
  "True iff cp is a codepoint and x is a byte sequence which match the
   ninth row of Table 3-7."
  (declare (xargs :guard (and (uchar? cp)
                              (unsigned-byte-listp 8 x)
                              (equal (len x) 4))))
  (and (mbt (uchar? cp))
       (mbt (unsigned-byte-listp 8 x))
       (mbt (equal (len x) 4))
       (utf8-table37-codepoint-9? cp)
       (utf8-table37-bytes-9? x)))

(deftheory utf8-table37-rows
  '(utf8-table37-row-1?
    utf8-table37-row-2?
    utf8-table37-row-3?
    utf8-table37-row-4?
    utf8-table37-row-5?
    utf8-table37-row-6?
    utf8-table37-row-7?
    utf8-table37-row-8?
    utf8-table37-row-9?))

(local (defthm utf8-table37-length-lemmas
         (and (implies (utf8-table37-row-1? cp x) (equal (len x) 1))
              (implies (utf8-table37-row-2? cp x) (equal (len x) 2))
              (implies (utf8-table37-row-3? cp x) (equal (len x) 3))
              (implies (utf8-table37-row-4? cp x) (equal (len x) 3))
              (implies (utf8-table37-row-5? cp x) (equal (len x) 3))
              (implies (utf8-table37-row-6? cp x) (equal (len x) 3))
              (implies (utf8-table37-row-7? cp x) (equal (len x) 4))
              (implies (utf8-table37-row-8? cp x) (equal (len x) 4))
              (implies (utf8-table37-row-9? cp x) (equal (len x) 4)))
         :hints(("Goal" :in-theory (enable utf8-table37-rows)))))

(defund utf8-table37-ok? (cp x)
  "True iff cp is a codepoint and x is a byte sequence which match some
   row in Table 3-7."
  (declare (xargs :guard (and (uchar? cp)
                              (unsigned-byte-listp 8 x)
                              (<= 1 (len x))
                              (<= (len x) 4))))
  (mbe :logic (or (utf8-table37-row-1? cp x)
                  (utf8-table37-row-2? cp x)
                  (utf8-table37-row-3? cp x)
                  (utf8-table37-row-4? cp x)
                  (utf8-table37-row-5? cp x)
                  (utf8-table37-row-6? cp x)
                  (utf8-table37-row-7? cp x)
                  (utf8-table37-row-8? cp x)
                  (utf8-table37-row-9? cp x))
       :exec (case (len x)
               (1 (utf8-table37-row-1? cp x))
               (2 (utf8-table37-row-2? cp x))
               (3 (or (utf8-table37-row-3? cp x)
                      (utf8-table37-row-4? cp x)
                      (utf8-table37-row-5? cp x)
                      (utf8-table37-row-6? cp x)))
               (4 (or (utf8-table37-row-7? cp x)
                      (utf8-table37-row-8? cp x)
                      (utf8-table37-row-9? cp x)))
               (otherwise nil))))

(defthm len-of-bytes-when-utf8-table37-ok?
  (implies (utf8-table37-ok? cp x)
           (and (<= 1 (len x))
                (<= (len x) 4)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable utf8-table37-ok?))))

(defthm uchar?-of-codepoint-when-utf8-table37-ok?
  (implies (utf8-table37-ok? cp x)
           (uchar? cp))
  :hints(("Goal" :in-theory (enable utf8-table37-ok?
                                    utf8-table37-rows))))

(defthm unsigned-byte-listp-of-bytes-when-utf8-table37-ok?
  (implies (utf8-table37-ok? cp x)
           (unsigned-byte-listp 8 x))
  :hints(("Goal" :in-theory (enable utf8-table37-ok?
                                    utf8-table37-rows))))
