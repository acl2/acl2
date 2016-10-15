; VL Verilog Toolkit
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

(in-package "VL")
(include-book "defs")
(local (include-book "arithmetic"))

(deflist vl-maybe-integer-listp (x)
  (maybe-integerp x)
  :elementp-of-nil t
  :true-listp t
  :parents (utilities)
  :rest
  ((defrule integer-listp-when-no-nils-in-vl-maybe-integer-listp
     (implies (and (not (member-equal nil x))
                   (vl-maybe-integer-listp x))
              (integer-listp x)))))

(define vl-match-contiguous-indices ((n maybe-integerp         "Index to try to count up from.")
                                     (x vl-maybe-integer-listp "List whose elements we are to collect."))
  :returns (mv (range-end maybe-integerp         :hyp :fguard)
               (rest      vl-maybe-integer-listp :hyp :fguard))
  :parents (vl-merge-contiguous-indices)
  :short "Identify one strictly increasing segment of a @(see
vl-maybe-integer-listp)."
  :long "<p>We try to consume the leading portion of @('x') if it counts up
from @('n').  For example:</p>

@({
    (vl-match-contiguous-indices 1 '(2 3 4 5 10 11 12))
      -->
    (mv 5 (10 11 12))
})"
  :measure (len x)
  (if (or (not (integerp n))
          (atom x)
          (not (equal (car x) (+ n 1))))
      (mv n x)
    (vl-match-contiguous-indices (+ n 1) (cdr x)))
  ///
  (defthm len-of-vl-match-contiguous-indices
    (implies (not (equal n (mv-nth 0 (vl-match-contiguous-indices n x))))
             (< (len (mv-nth 1 (vl-match-contiguous-indices n x)))
                (len x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable |(< c2 (+ c1 a))|))))

  (defthm vl-match-contiguous-indices-fails-on-nil
    (equal (mv-nth 0 (vl-match-contiguous-indices nil x))
           nil))

  (defthm vl-match-contiguous-indices-monotonic-on-success
    (implies (and (not (equal n (mv-nth 0 (vl-match-contiguous-indices n x))))
                  (force (maybe-integerp n))
                  (force (vl-maybe-integer-listp x)))
             (< n (mv-nth 0 (vl-match-contiguous-indices n x))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm vl-match-contiguous-indices-exists-on-success
    (implies (and (not (equal n (mv-nth 0 (vl-match-contiguous-indices n x))))
                  (force (maybe-integerp n))
                  (force (vl-maybe-integer-listp x)))
             (integerp (mv-nth 0 (vl-match-contiguous-indices n x))))))

(define vl-merged-index-p (x)
  :parents (vl-merge-contiguous-indices)
  (or (not x)
      (integerp x)
      (and (consp x)
           (integerp (car x))
           (integerp (cdr x))
           (< (car x) (cdr x)))))

(deflist vl-merged-index-list-p (x)
  (vl-merged-index-p x)
  :elementp-of-nil t
  :parents (vl-merge-contiguous-indices))



(define vl-merge-contiguous-indices ((x vl-maybe-integer-listp))
  :parents (utilities)
  :short "Transform a @(see vl-maybe-integer-listp) by combining contiguous
sequences of indices into @('(low . high)') pairs."
  :long "<p>For example:</p>

@({
     (vl-merge-contiguous-indices '(1 2 3 5 6 7 8 9 10 15 17 18))
       -->
     ((1 . 3) (5 . 10) 15 (17 . 18))
})"
  :measure (len x)
  :returns (indices vl-merged-index-list-p :hyp :fguard
                    :hints(("Goal" :in-theory (enable vl-merged-index-p))))

  (b* (((when (atom x))
        nil)
       ((mv range-end rest) (vl-match-contiguous-indices (car x) (cdr x)))
       ((when (equal (car x) range-end))
        (cons (car x)
              (vl-merge-contiguous-indices (cdr x)))))
    (cons (cons (car x) range-end)
          (vl-merge-contiguous-indices rest))))
