; Centaur Lexer Library
; Copyright (C) 2013 Centaur Technology
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

(in-package "CLEX")
(include-book "std/util/define" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(local (include-book "arithmetic"))


(defsection line-and-column-tracking
  :parents (sin$c)
  :short "Routines for tracking line and column numbers as we iterate through a
string."

  :long "<p>Keeping track of the line and column number is practically
important for producing good error messages.  The routines here are rather
specialized, and are mainly designed for use within our input stream
mechanism.</p>

<p>The normal convention used by, e.g., text editors like EMACS, is to show
line numbers starting at 1.  We adopt this convention in the interface to
our input streams.</p>

<p>However, <b>internally</b> we treat line numbers as starting at 0.  This
This has the good property that the line number never exceeds our current
character position in the file.  As a result, restricting ourselves to fixnum
positions automatically gives us fixnum line (and column) numbers.</p>")


(define line-after-nthcdr
  ((n    natp            "How many characters to cdr.")
   (x    character-listp "Characters we're processing.")
   (line natp            "Current line number."))
  :returns (new-line natp :rule-classes :type-prescription)
  :parents (line-and-column-tracking)
  :short "Determine what the new line number should be after we advance @('n')
characters."
  :long "<p>This is a logically simple way to express how the line number gets
updated.  It isn't really meant to be executed.</p>"
  (if (or (zp n)
          (atom x))
      (lnfix line)
    (line-after-nthcdr (- n 1) (cdr x) (if (eql (car x) #\Newline)
                                           (+ 1 (lnfix line))
                                         (lnfix line))))
  ///
  (defcong nat-equiv equal (line-after-nthcdr n x line) 1)
  (defcong nat-equiv equal (line-after-nthcdr n x line) 3)
  (defthm lower-bound-of-line-after-nthcdr
    (<= (nfix line) (line-after-nthcdr n x line))
    :rule-classes ((:rewrite) (:linear)))
  (defthm upper-bound-1-of-line-after-nthcdr
    (<= (line-after-nthcdr n x line)
        (+ (nfix line) (nfix n)))
    :rule-classes ((:rewrite) (:linear)))
  (defthm upper-bound-2-of-line-after-nthcdr
    (<= (line-after-nthcdr n x line)
        (+ (nfix line) (len x)))
    :rule-classes ((:rewrite) (:linear))))


(define col-after-nthcdr
  ((n    natp            "How many characters to cdr.")
   (x    character-listp "Characters we're processing.")
   (col  natp            "Current column number."))
  :returns (new-col natp :rule-classes :type-prescription)
  :parents (line-and-column-tracking)
  :short "Determine what the new column number should be after we advance
@('n') characters."
  :long "<p>This is a logically simple way to express how the column number
gets updated.  It isn't really meant to be executed.</p>"
  (if (or (zp n)
          (atom x))
      (lnfix col)
    (col-after-nthcdr (- n 1) (cdr x) (if (eql (car x) #\Newline)
                                          0
                                        (+ 1 (lnfix col)))))
  ///
  (defcong nat-equiv equal (col-after-nthcdr n x col) 1)
  (defcong nat-equiv equal (col-after-nthcdr n x col) 3)
  ;; No lower bound since it can get reset to zero
  (defthm upper-bound-1-of-col-after-nthcdr
    (<= (col-after-nthcdr n x col)
        (+ (nfix col) (nfix n)))
    :rule-classes ((:rewrite) (:linear)))
  (defthm upper-bound-2-of-col-after-nthcdr
    (<= (col-after-nthcdr n x col)
        (+ (nfix col) (len x)))
    :rule-classes ((:rewrite) (:linear))))


(define lc-nthcdr
  ((n    natp            "How many characters to advance.")
   (x    character-listp "Characters we're processing.")
   (line natp            "Current line number.")
   (col  natp            "Current column number."))
  :returns (mv (new-chars "Remaining characters after advancing.")
               (new-line  "Line number after advancing.")
               (new-col   "Column number after advancing."))
  :parents (line-and-column-tracking)
  :short "Like @(see nthcdr) into a character list, but simultaneously computes
the new line and column numbers."
  :enabled t
  :verify-guards nil
  (declare (type (integer 0 *) n line col))
  (mbe :logic
       (mv (nthcdr n x)
           (line-after-nthcdr n x line)
           (col-after-nthcdr n x col))
       :exec
       (b* (((when (or (zp n)
                       (atom x)))
             (mv x line col))
            ((the character char1) (car x))
            ((the (integer 0 *) n) (- (lnfix n) 1)))
         (if (eql char1 #\Newline)
             (lc-nthcdr n (cdr x) (+ 1 line) 0)
           (lc-nthcdr n (cdr x) line (+ 1 col)))))
  ///
  (verify-guards lc-nthcdr
    :hints(("Goal" :in-theory (enable line-after-nthcdr
                                      col-after-nthcdr)))))


(define lc-nthcdr-str
  ((n    natp                   "How many characters to advance.")
   (x    stringp                "String we're processing.")
   (pos  natp                   "Current index into x.")
   (xl   (equal xl (length x))  "Pre-computed length of x.")
   (line natp                   "Current line number.")
   (col  natp                   "Current column number."))
  :guard (<= pos xl)
  :returns (mv (new-pos  natp :rule-classes :type-prescription)
               (new-line natp :rule-classes :type-prescription)
               (new-col  natp :rule-classes :type-prescription))
  :parents (line-and-column-tracking)
  :short "String-based version of @(see lc-nthcdr)."
  :enabled t
  (declare (type (integer 0 *) n pos xl line col)
           (type string x))
  (mbe :logic
       (let ((chars (nthcdr pos (coerce x 'list))))
         (mv (min (+ (nfix pos) (nfix n)) (nfix xl))
             (line-after-nthcdr n chars line)
             (col-after-nthcdr n chars col)))
       :exec
       (b* (((when (or (zp n)
                       (eql pos xl)))
             (mv pos line col))
            ((the character char1)   (char x pos))
            ((the (integer 0 *) n)   (- n 1))
            ((the (integer 0 *) pos) (+ 1 pos)))
         (if (eql char1 #\Newline)
             (lc-nthcdr-str n x pos xl (+ 1 line) 0)
           (lc-nthcdr-str n x pos xl line (+ 1 col)))))
  :verify-guards nil
  ///
  (verify-guards lc-nthcdr-str
    :hints(("Goal" :in-theory (enable line-after-nthcdr
                                      col-after-nthcdr)))))



(define lc-nthcdr-str-fast
  ((n    natp                   "How many characters to advance.")
   (x    stringp                "String we're processing.")
   (pos  natp                   "Current index into x.")
   (xl   (equal xl (length x))  "Pre-computed length of x.")
   (line natp                   "Current line number.")
   (col  natp                   "Current column number."))
  :guard (and (<= pos xl)
              (<= line pos)
              (<= col pos))
  :parents (line-and-column-tracking)
  :short "Fixnum optimized version of @(see lc-nthcdr-str)."
  :enabled t
  (declare (type (unsigned-byte 60) pos xl line col n)
           (type string x))
  (mbe :logic
       (lc-nthcdr-str n x pos xl line col)
       :exec
       (b* (((when (or (zp n)
                       (eql pos xl)))
             (mv pos line col))
            ((the character char1)        (char x pos))
            ((the (unsigned-byte 60) n)   (- n 1))
            ((the (unsigned-byte 60) pos) (+ 1 pos)))
         (if (eql char1 #\Newline)
             (lc-nthcdr-str-fast n x pos xl
                                 (the (unsigned-byte 60) (+ 1 line))
                                 0)
           (lc-nthcdr-str-fast n x pos xl line
                               (the (unsigned-byte 60) (+ 1 col))))))
  :verify-guards nil
  ///
  (verify-guards lc-nthcdr-str-fast
    :hints(("Goal" :in-theory (enable line-after-nthcdr
                                      col-after-nthcdr)))))
