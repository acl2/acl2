; ACL2 String Library
; Copyright (C) 2009-2014 Centaur Technology
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
(include-book "charset")
(local (include-book "arithmetic"))

(local (xdoc::set-default-parents charset-p))

(define count-leading-charset ((x   character-listp)
                               (set charset-p))
  :returns (num natp :rule-classes :type-prescription)
  :short "Count how many characters at the start of a list are members of a
particular character set."
  (cond ((atom x)
         0)
        ((char-in-charset-p (car x) set)
         (+ 1 (count-leading-charset (cdr x) set)))
        (t
         0))
  ///
  (defthm upper-bound-of-count-leading-charset
    (<= (count-leading-charset x set) (len x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm count-leading-charset-len
    (equal (equal (len x) (count-leading-charset x set))
           (chars-in-charset-p x set))
    :rule-classes ((:rewrite)
                   (:rewrite :corollary
                             (equal (< (count-leading-charset x set) (len x))
                                    (not (chars-in-charset-p x set))))
                   (:linear :corollary
                            (implies (not (chars-in-charset-p x set))
                                     (< (count-leading-charset x set) (len x))))))

  (defthm count-leading-charset-zero
    ;; A common paradigm is:
    ;;
    ;;  (1) check if the starting character is, e.g., a digit
    ;;  (2) if so, read as many digits as possible.
    ;;
    ;; This theorem basically shows that step 2 is sure to get at least some
    ;; characters when step 1 succeeds.
    (equal (equal 0 (count-leading-charset x set))
           (not (char-in-charset-p (car x) set)))
    :rule-classes ((:rewrite)
                   (:rewrite :corollary
                             (equal (< 0 (count-leading-charset x set))
                                    (char-in-charset-p (car x) set)))
                   (:linear :corollary
                            (implies (char-in-charset-p (car x) set)
                                     (< 0 (count-leading-charset x set))))))

  (defthm count-leading-charset-sound
    ;; Basic correctness property: all of the characters that were counted are
    ;; indeed in the desired character set.
    (let ((n (count-leading-charset x set)))
      (chars-in-charset-p (take n x) set)))

  (defthm count-leading-charset-complete
    ;; Basic correctness property: suppose we count and find that there are N
    ;; leading characters in the desired set.  Then, the next character (which,
    ;; due to zero indexing, is the one at index N), is NOT in the set; otherwise
    ;; we would have counted it, too.
    (b* ((n         (count-leading-charset x set))
         (next-char (nth n x)))
      (not (char-in-charset-p next-char set)))
    :hints(("Goal"
            :induct (count-leading-charset x set)
            :in-theory (enable nth)))))



(define str-count-leading-charset
  ((n   natp                 "Current position in the string.")
   (x   stringp              "String we're iterating through.")
   (xl  (eql xl (length x))  "Precomputed length of @('x').")
   (set charset-p            "Set of characters we're counting."))
  :guard (<= n xl)
  :returns (n natp :rule-classes :type-prescription)
  :short "String version of @(see count-leading-charset)."
  :enabled t
  (declare (type (integer 0 *) xl n)
           (type string x))
  (mbe :logic
       (let ((chars (nthcdr n (coerce x 'list))))
         (count-leading-charset chars set))
       :exec
       (b* (((when (eql n xl))
             0)
            ((the character char1) (char x n))
            ((when (char-in-charset-p char1 set))
             (+ 1 (str-count-leading-charset (+ 1 n) x xl set))))
         0))
  :verify-guards nil
  ///
  (verify-guards str-count-leading-charset
    :hints(("Goal" :in-theory (enable count-leading-charset)))))


(define str-count-leading-charset-fast
  ((n   natp                 "Current position in the string.")
   (x   stringp              "String we're iterating through.")
   (xl  (eql xl (length x))  "Precomputed length of @('x').")
   (set charset-p            "Set of characters we're counting."))
  :guard (<= n xl)
  :returns (n natp :rule-classes :type-prescription)
  :short "Fixnum optimized version of @(see str-count-leading-charset)."
  :enabled t
  (declare (type (unsigned-byte 60) n xl)
           (type string x))
  (mbe :logic
       (let ((chars (nthcdr n (coerce x 'list))))
         (count-leading-charset chars set))
       :exec
       (b* (((when (eql n xl))
             0)
            ((the character char1) (char x n))
            ((the (unsigned-byte 60) n) (+ 1 n))
            ((when (char-in-charset-p char1 set))
             (the (integer 0 *)
               ;; Blah, this one might not be an unsigned-byte 60
               ;; if X has length 2^60-1 and every character in it
               ;; is in the set.
               (+ 1 (str-count-leading-charset-fast n x xl set)))))
         0))
  :verify-guards nil
  ///
  (verify-guards str-count-leading-charset-fast
    :hints(("Goal" :in-theory (enable count-leading-charset)))))
