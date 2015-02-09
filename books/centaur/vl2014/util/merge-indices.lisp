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
(include-book "defs")
(local (include-book "arithmetic"))

(defsection vl-match-contiguous-indices
  :parents (vl-verilogify-emodwirelist)
  :short "Identify one strictly increasing segment of a @(see
vl-maybe-nat-listp)."

  :long "<p>@(call vl-match-contiguous-indices) tries to consume the leading
portion of @('x') if it counts up from @('n').  It returns @('(mv range-end
rest)').  Here's an illustrative example:</p>

@({
 (vl-match-contiguous-indices 1 '(2 3 4 5 10 11 12))
   -->
 (mv 5 (10 11 12))
})

<p>We use when collapsing emod names into Verilog-style names; see @(see
vl-merge-contiguous-indices).</p>"

  (defund vl-match-contiguous-indices (n x)
    (declare (xargs :guard (and (maybe-natp n)
                                (vl-maybe-nat-listp x))
                    :measure (len x)))
    (if (or (not (natp n))
            (atom x)
            (not (equal (car x) (+ n 1))))
        (mv n x)
      (vl-match-contiguous-indices (+ n 1) (cdr x))))

  (local (in-theory (enable vl-match-contiguous-indices)))

  (defthm maybe-natp-of-vl-match-contiguous-indices
    (implies (and (force (maybe-natp n))
                  (force (vl-maybe-nat-listp x)))
             (maybe-natp (mv-nth 0 (vl-match-contiguous-indices n x)))))

  (defthm vl-maybe-nat-listp-of-vl-match-contiguous-indices
    (implies (and (force (maybe-natp n))
                  (force (vl-maybe-nat-listp x)))
             (vl-maybe-nat-listp (mv-nth 1 (vl-match-contiguous-indices n x)))))

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
                  (force (maybe-natp n))
                  (force (vl-maybe-nat-listp x)))
             (< n (mv-nth 0 (vl-match-contiguous-indices n x))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm vl-match-contiguous-indices-exists-on-success
    (implies (and (not (equal n (mv-nth 0 (vl-match-contiguous-indices n x))))
                  (force (maybe-natp n))
                  (force (vl-maybe-nat-listp x)))
             (natp (mv-nth 0 (vl-match-contiguous-indices n x))))))


(define vl-merged-index-p (x)
  :parents (vl-merge-contiguous-indices)
  (or (not x)
      (natp x)
      (and (consp x)
           (natp (car x))
           (natp (cdr x))
           (< (car x) (cdr x)))))

(deflist vl-merged-index-list-p (x)
  (vl-merged-index-p x)
  :elementp-of-nil t
  :parents (vl-merge-contiguous-indices))

(defsection vl-merge-contiguous-indices
  :parents (vl-verilogify-emodwirelist)
  :short "Transform a @(see vl-maybe-nat-listp) by combining contiguous
sequences of indices into @('(low . high)') pairs."

  :long "<p>For example:</p>

@({
 (vl-merge-contiguous-indices '(1 2 3 5 6 7 8 9 10 15 17 18))
  -->
 ((1 . 3) (5 . 10) 15 (17 . 18))
})"

  (defund vl-merge-contiguous-indices (x)
    (declare (xargs :guard (vl-maybe-nat-listp x)
                    :measure (len x)))
    (if (atom x)
        nil
      (mv-let (range-end rest)
        (vl-match-contiguous-indices (car x) (cdr x))
        (if (equal (car x) range-end)
            (cons (car x)
                  (vl-merge-contiguous-indices (cdr x)))
          (cons (cons (car x) range-end)
                (vl-merge-contiguous-indices rest))))))

  (local (in-theory (enable vl-merge-contiguous-indices
                            vl-merged-index-p)))

  (defthm vl-merged-index-list-p-of-vl-merge-contiguous-indices
    (implies (force (vl-maybe-nat-listp x))
             (vl-merged-index-list-p (vl-merge-contiguous-indices x)))))
