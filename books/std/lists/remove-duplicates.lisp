; Removing Duplicates
; Copyright (C) 2014 Centaur Technology
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
;
; Additional copyright notice.
;
; Some of the definitions in this book were adapted from the file
; misc/hons-help.lisp, Copyright (C) 2013 the Regents of the University of
; Texas, which was originally written by Bob Boyer and Warren Hunt and is
; available under a 3-clause BSD license.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "list-defuns")
(local (include-book "equiv"))
(local (include-book "sets"))
(local (include-book "duplicity"))
(local (include-book "no-duplicatesp"))

(defsection std/lists/remove-duplicates-equal
  :parents (std/lists remove-duplicates)
  :short "Lemmas about @(see remove-duplicates-equal) available in the @(see
std/lists) library."

  (defthm remove-duplicates-equal-when-atom
    (implies (atom x)
             (equal (remove-duplicates-equal x)
                    nil)))

  (defthm remove-duplicates-equal-of-cons
    (equal (remove-duplicates-equal (cons a x))
           (if (member a x)
               (remove-duplicates-equal x)
             (cons a (remove-duplicates-equal x)))))

  (defthm consp-of-remove-duplicates-equal
    (equal (consp (remove-duplicates-equal x))
           (consp x)))

  (defthm len-of-remove-duplicates-equal
    (<= (len (remove-duplicates-equal x))
        (len x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm remove-duplicates-equal-of-list-fix
    (equal (remove-duplicates-equal (list-fix x))
           (remove-duplicates-equal x)))

  (defcong list-equiv equal (remove-duplicates-equal x) 1
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (remove-duplicates-equal-of-list-fix))
            :use ((:instance remove-duplicates-equal-of-list-fix)
                  (:instance remove-duplicates-equal-of-list-fix (x x-equiv))))))

  (defthm member-of-remove-duplicates-equal
    (iff (member a (remove-duplicates-equal x))
         (member a x)))

  (defthm remove-duplicates-equal-under-set-equiv
    (set-equiv (remove-duplicates-equal x)
               x)
    :hints(("Goal" :in-theory (enable set-equiv))))

  (defcong set-equiv set-equiv (remove-duplicates-equal x) 1)

  (defthm no-duplicatesp-equal-of-remove-duplicates-equal
    (no-duplicatesp-equal (remove-duplicates-equal x)))

  (defthm duplicity-in-of-remove-duplicates-equal
    (equal (duplicity a (remove-duplicates-equal x))
           (if (member a x)
               1
             0)))

  (defthm remove-duplicates-equal-of-remove
    (equal (remove-duplicates-equal (remove a x))
           (remove a (remove-duplicates-equal x)))))


(defsection hons-remove-duplicates
  :parents (std/lists remove-duplicates)
  :short "@(call hons-remove-duplicates) removes duplicate elements from a
list, and is implemented using @(see fast-alists)."

  :long "<p>This operation is similar to the built-in ACL2 function @(see
remove-duplicates-equal), but it has different performance characteristics and
the answer it produces is in an oddly different order.</p>

<p>ACL2's @(see remove-duplicates) function preserves the order of
non-duplicated elements but has a rather inefficient @('O(n^2)')
implementation: it walks down the list, checking for each element whether there
are any more occurrences of the element in the tail of the list.</p>

<p>In contrast, @('hons-remove-duplicates') is a tail-recursive function that
uses a fast alist to record the elements that have been seen so far.  This is
effectively @('O(n)') if we assume that hashing is constant time.  Note,
however.  that this approach requires us to @(see hons) the elements in the
list, which may be quite expensive if the list contains large structures.</p>

<p>Another reasonably efficient way to remove duplicate elements from a list
include sorting the elements, e.g., via @(see set::mergesort).</p>

<p>In the special case of removing duplicates from lists of natural numbers,
@(see nat-list-remove-duplicates) may be offer superior performance.</p>

<p>Even though @('hons-remove-duplicates') has a reasonably nice logical
definition that is merely in terms of @(see remove-duplicates-equal) and @(see
rev), we leave it disabled by default and go ahead and prove various theorems
about it.  These theorems are perhaps best regarded as a back-up plan.  In
general, you may often be able to avoid reasoning about
@('hons-remove-duplicates') via the following, strong @(see set-equiv)
rule:</p>

@(def hons-remove-duplicates-under-set-equiv)"

  (defund hons-remove-duplicates1 (l tab)
    (declare (xargs :guard t))
    (cond ((atom l)
           ;; BOZO a bit unfortunate to free this table here.  Better would be
           ;; to move the freeing to the :exec part of hons-remove-duplicates,
           ;; except that we might be depending on this freeing somewhere else?
           (progn$ (fast-alist-free tab)
                   nil))
          ((hons-get (car l) tab)
           (hons-remove-duplicates1 (cdr l) tab))
          (t
           (cons (car l)
                 (hons-remove-duplicates1 (cdr l)
                                          (hons-acons (car l) t tab))))))

  (defund hons-remove-duplicates (l)
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic (rev (remove-duplicates-equal (rev l)))
         :exec (hons-remove-duplicates1 l (len l))))

  (local (in-theory (enable hons-remove-duplicates1
                            hons-remove-duplicates)))

  (defthm hons-remove-duplicates-when-atom
    (implies (atom x)
             (equal (hons-remove-duplicates x)
                    nil)))

  (defthm hons-remove-duplicates-of-list-fix
    (equal (hons-remove-duplicates (list-fix x))
           (hons-remove-duplicates x)))

  (defcong list-equiv equal (hons-remove-duplicates x) 1
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (hons-remove-duplicates
                             hons-remove-duplicates-of-list-fix))
            :use ((:instance hons-remove-duplicates-of-list-fix)
                  (:instance hons-remove-duplicates-of-list-fix (x x-equiv))))))

  (defcong set-equiv set-equiv (hons-remove-duplicates x) 1)

  (defthm hons-remove-duplicates-under-set-equiv
    (set-equiv (hons-remove-duplicates x)
               (remove-duplicates-equal x)))

  (defthm no-duplicatesp-equal-of-hons-remove-duplicates
    (no-duplicatesp-equal (hons-remove-duplicates x)))

  (defthm duplicity-in-of-hons-remove-duplicates
    (equal (duplicity a (hons-remove-duplicates x))
           (if (member a x)
               1
             0)))

  (encapsulate
    ()
    (local (include-book "remove"))
    (local (include-book "../alists/alist-keys"))

    ;; BOZO we should have these lemmas about set-difference somewhere decent
    (local (defthm set-difference-equal-of-cons-right
             (equal (set-difference-equal x (cons a y))
                    (remove a (set-difference-equal x y)))))

    (local (defthm set-difference-equal-of-list-fix-left
             (equal (set-difference-equal (list-fix x) y)
                    (set-difference-equal x y))))

    (local (defthm set-difference-equal-of-append-left
             (equal (set-difference-equal (append a b) c)
                    (append (set-difference-equal a c)
                            (set-difference-equal b c)))))

    (local (defthm set-difference-equal-of-remove-left
             (equal (set-difference-equal (remove a x) y)
                    (remove a (set-difference-equal x y)))))

    (local (defthm rev-of-remove-equal
             (equal (rev (remove-equal a x))
                    (remove-equal a (rev x)))))

    (local (in-theory (disable remove-of-rev
                               remove-of-set-difference-equal)))

    (local (defthm l0
             (implies (not (hons-assoc-equal x1 tab))
                      (equal (cons x1 (remove-equal x1 (rev (remove-duplicates-equal x2))))
                             (rev (remove-duplicates-equal (append x2 (list x1))))))))

    (local (defthm hons-remove-duplicates1-redef
             (equal (hons-remove-duplicates1 x tab)
                    (rev (remove-duplicates-equal
                          (set-difference-equal (rev x)
                                                (alist-keys tab)))))
             :hints(("Goal" :induct (hons-remove-duplicates1 x tab)))))

    (local (defthm set-difference-equal-of-nil-right
             (equal (set-difference-equal a nil)
                    (list-fix a))))

    (defthmd hons-remove-duplicates1-of-nil
      (equal (hons-remove-duplicates1 x nil)
             (hons-remove-duplicates x)))

    (verify-guards hons-remove-duplicates))

  (local (defthm hons-remove-duplicates1-acl2-count
           (<= (acl2-count (hons-remove-duplicates1 x y))
               (acl2-count x))
           :hints(("Goal" :in-theory (e/d (hons-remove-duplicates1 acl2-count))))
           :rule-classes :linear))

  (defthm acl2-count-of-hons-remove-duplicates
    (<= (acl2-count (hons-remove-duplicates x))
        (acl2-count x))
    :hints(("Goal"
            :in-theory (disable hons-remove-duplicates1
                                hons-remove-duplicates)
            :use ((:instance hons-remove-duplicates1-of-nil))))
    :rule-classes ((:rewrite) (:linear))))

