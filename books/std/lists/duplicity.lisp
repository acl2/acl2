; Duplicity -- Count how many times an element occurs in a list
; Copyright (C) 2008 Centaur Technology
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

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "equiv")
(include-book "rev")
(include-book "flatten")

(defsection duplicity
  :parents (std/lists count no-duplicatesp)
  :short "@(call duplicity) counts how many times the element @('a') occurs
within the list @('x')."

  :long "<p>This function is much nicer to reason about than ACL2's built-in
@(see count) function because it is much more limited:</p>

<ul>

<li>@('count') can operate on either strings or lists; @('duplicity') only
works on lists.</li>

<li>@('count') can consider only some particular sub-range of its input;
@('duplicity') always considers the whole list.</li>

</ul>

<p>Reasoning about duplicity is useful when trying to show two lists are
permutations of one another (sometimes called multiset- or bag-equivalence).  A
classic exercise for new ACL2 users is to prove that a permutation function is
symmetric.  Hint: a duplicity-based argument may compare quite favorably to
induction on the definition of permutation.</p>

<p>This function can also be useful when trying to establish @(see
no-duplicatesp), e.g., see @(see no-duplicatesp-equal-same-by-duplicity).</p>"

  (defund duplicity-exec (a x n)
    (declare (xargs :guard (natp n)))
    (if (atom x)
        n
      (duplicity-exec a (cdr x)
                      (if (equal (car x) a)
                          (+ 1 n)
                        n))))

  (defund duplicity (a x)
    (declare (xargs :guard t
                    :verify-guards nil))
    (mbe :logic (cond ((atom x)
                       0)
                      ((equal (car x) a)
                       (+ 1 (duplicity a (cdr x))))
                      (t
                       (duplicity a (cdr x))))
         :exec (duplicity-exec a x 0)))

  (defthm duplicity-exec-removal
    (implies (natp n)
             (equal (duplicity-exec a x n)
                    (+ (duplicity a x) n)))
    :hints(("Goal" :in-theory (enable duplicity duplicity-exec))))

  (verify-guards duplicity
    :hints(("Goal" :in-theory (enable duplicity))))

  (defthm duplicity-when-not-consp
    (implies (not (consp x))
             (equal (duplicity a x)
                    0))
    :hints(("Goal" :in-theory (enable duplicity))))

  (defthm duplicity-of-cons
    (equal (duplicity a (cons b x))
           (if (equal a b)
               (+ 1 (duplicity a x))
             (duplicity a x)))
    :hints(("Goal" :in-theory (enable duplicity))))

  (defthm duplicity-of-list-fix
    (equal (duplicity a (list-fix x))
           (duplicity a x))
    :hints(("Goal" :induct (len x))))

  (defcong list-equiv equal (duplicity a x) 2
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (duplicity-of-list-fix))
            :use ((:instance duplicity-of-list-fix)
                  (:instance duplicity-of-list-fix (x x-equiv))))))

  (defthm duplicity-of-append
    (equal (duplicity a (append x y))
           (+ (duplicity a x)
              (duplicity a y)))
    :hints(("Goal" :induct (len x))))

  (defthm duplicity-of-rev
    (equal (duplicity a (rev x))
           (duplicity a x))
    :hints(("Goal" :induct (len x))))

  (defthm duplicity-of-revappend
    (equal (duplicity a (revappend x y))
           (+ (duplicity a x)
              (duplicity a y)))
    :hints(("Goal" :induct (revappend x y))))

  (defthm duplicity-of-reverse
    (equal (duplicity a (reverse x))
           (duplicity a x)))

  (defthm duplicity-when-non-member-equal
    (implies (not (member-equal a x))
             (equal (duplicity a x)
                    0)))

  (defthm duplicity-when-member-equal
    ;; New lemma by Keshav Kini to complement the nonmember lemma above
    (implies (member-equal a x)
             (< 0 (duplicity a x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm duplicity-zero-to-member-equal
    ;; This also seems like a solid rule for normalizing nonzero duplicity into
    ;; membership.  It's potentially expensive since it targets equal, but I
    ;; think we are generally okay with that.
    (iff (equal 0 (duplicity a x))
         (not (member-equal a x))))

  (defthm no-duplicatesp-equal-when-high-duplicity
    (implies (> (duplicity a x) 1)
             (not (no-duplicatesp-equal x))))

  (defthm duplicity-of-flatten-of-rev
    (equal (duplicity a (flatten (rev x)))
           (duplicity a (flatten x)))
    :hints(("Goal" :induct (len x)))))
