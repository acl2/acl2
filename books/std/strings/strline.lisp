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
(include-book "coerce")
(include-book "std/basic/defs" :dir :system)
(local (include-book "arithmetic"))


;; BOZO move these to arithmetic?  Depends, maybe we don't want them to be
;; local...

(defthm position-ac-lower-bound
  (implies (and (position-ac item x acc)
                (natp acc))
           (<= acc (position-ac item x acc)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable position-ac))))

(defthm position-ac-upper-bound
  (implies (natp acc)
           (<= (position-ac item x acc)
               (+ acc (len x))))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable position-ac))))


(defsection charpos-aux

  (defund charpos-aux (x n xl char)
    ;; Return the first index of character CHAR in X[n:_], or NIL if CHAR does
    ;; not occur in this range.
    (declare (type string x)
             (type integer n)
             (type integer xl)
             (type character char)
             (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (<= n xl)
                                (= xl (length x)))))
    (mbe :logic
         (position-ac char
                      (nthcdr n (explode x))
                      (nfix n))
         :exec
         (cond ((mbe :logic (zp (- (nfix xl) (nfix n)))
                     :exec (int= n xl))
                nil)
               ((eql (char x n) char)
                (lnfix n))
               (t
                (charpos-aux x (+ 1 (lnfix n)) xl char)))))

  (local (in-theory (enable charpos-aux position-equal-ac)))

  (defthm type-of-charpos-aux
    (implies (force (natp n))
             (or (natp (charpos-aux x n xl char))
                 (not (charpos-aux x n xl char))))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable charpos-aux)))))



(defsection go-to-line

  (defund go-to-line (x n xl curr goal)
    (declare (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (<= n xl)
                                (= xl (length x))
                                (natp curr)
                                (natp goal))
                    :measure (nfix (- (nfix xl) (nfix n))))
             (type string x)
             (type integer n xl curr goal))
    (cond ((mbe :logic (zp (- (nfix xl) (nfix n)))
                :exec (int= n xl))
           nil)
          ((int= curr goal)
           (lnfix n))
          (t
           (go-to-line x (+ 1 (lnfix n)) xl
                       (if (eql (char x n) #\Newline)
                           (+ 1 curr)
                         curr)
                       goal))))

  (local (in-theory (enable go-to-line)))

  (defthm type-of-go-to-line
    (or (not (go-to-line x n xl curr goal))
        (and (integerp (go-to-line x n xl curr goal))
             (<= 0 (go-to-line x n xl curr goal))))
    :rule-classes :type-prescription)

  (defthm go-to-line-lower-bound
    (implies (and (go-to-line x n xl curr goal)
                  (natp n))
             (<= n (go-to-line x n xl curr goal)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm go-to-line-upper-bound
    (implies (natp xl)
             (<= (go-to-line x n xl curr goal)
                 xl))
    :rule-classes ((:rewrite) (:linear))))



(defsection strline
  :parents (lines)
  :short "Extract a line from a string by its line number."

  :long "<p>@(call strline) extracts the @('n')th line from the string @('x')
and returns it as a string.  The string will <b>not</b> contain a newline
character.</p>

<p>Note that we consider the first line of the string to be 1, not 0.  This is
intended to agree with the convention followed by many text editors, where the
first line in a file is regarded as line 1 instead of line 0.  Accordingly, we
require @('n') to be a @(see posp).</p>

<p>If @('n') does not refer to a valid line number for @('x'), the empty string
is returned.</p>"

  (local (in-theory (enable charpos-aux)))

  (defund strline (n x)
    (declare (xargs :guard (and (posp n)
                                (stringp x))))
    (let* ((x     (mbe :logic (if (stringp x) x "")
                       :exec x))
           (xl    (length x))
           (start (go-to-line x 0 xl 1 n)))
      (if (not start)
          ""
        (let ((end (charpos-aux x start xl #\Newline)))
          (subseq x start end)))))

  (local (in-theory (enable strline)))

  (defthm stringp-of-strline
    (stringp (strline n x))
    :rule-classes :type-prescription))


(defsection strlines
  :parents (lines)
  :short "Extract a group of lines from a string by their line numbers."

  :long "<p>@(call strlines) extracts the lines between line number @('a') and
line number @('b') from the string @('x'), and returns them as a new
string.</p>

<p>The order of @('a') and @('b') is irrelevant; the extracted text will always
be a proper substring of @('x'), that is, the line with the smallest number
will come first.</p>

<p>Note that we consider the first line of the string to be 1, not 0.  This is
intended to agree with the convention followed by many text editors, where the
first line in a file is regarded as line 1 instead of line 0.  Accordingly, we
require @('a') and @('b') to be @(see posp)s.</p>

<p>Out of bounds conditions.  If the larger line number is past the end of the
text, the full text is obtained.  In other words, @('(strlines 0 100000 x)') is
likely to just be @('x') except for very large strings.  If both line numbers
are past the end of the text, the empty string is returned.</p>

<p>Newline behavior.  When both line numbers are in range and do not refer to
the last line in the string, the returned string will have a newline after
every line.  If the last line is to be included, then it will have a newline
exactly when @('x') ends with a newline.  In the out-of-bounds case where both
indices are too large, the empty string is returned so there are no
newlines.</p>

<p>Efficiency.  This function should be much faster than calling @(see strline)
repeatedly and concatenating the resulting lines.  Basically it figures out
where the text to extract should start and end, then extracts it all as a
single chunk.</p>"

  (defund strlines (a b x)
    (declare (type integer a)
             (type integer b)
             (type string x)
             (xargs :guard (and (posp a)
                                (posp b)
                                (stringp x))))
    (let* ((x  (mbe :logic (if (stringp x) x "")
                    :exec x))
           (xl (length x)))
      (mv-let
        (a b)
        (if (<= a b) (mv a b) (mv b a))
        (let ((start (go-to-line x 0 xl 1 a)))
          (if (not start)
              ""
            (let ((end (go-to-line x start xl a (+ 1 b))))
              (subseq x start end)))))))

  (local (in-theory (enable strlines)))

  (defthm stringp-of-strlines
    (stringp (strlines a b x))
    :rule-classes :type-prescription))
