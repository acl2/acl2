; List Equivalence
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "list-fix")
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "append"))

; [Jared]: I split these out of centaur/misc/lists.lisp.  I tried to mainly
; keep the rules about list-equiv and how it relates to built-in functions.
; But this omits things like arith-equivs, list-defthms, and rewrite rules to
; rewrite various functions.

(defsection list-equiv
  :parents (std/lists)
  :short "@(call list-equiv) is an @(see equivalence) relation that determines
whether @('x') and @('y') are identical except perhaps in their @(see
final-cdr)s."

  :long "<p>This is a very common equivalence relation for functions that
process lists.  See also @(see list-fix) for more discussion.</p>"

  (defund fast-list-equiv (x y)
    (declare (xargs :guard t))
    (if (consp x)
        (and (consp y)
             (equal (car x) (car y))
             (fast-list-equiv (cdr x) (cdr y)))
      (atom y)))

  (local (defthm fast-list-equiv-removal
           (equal (fast-list-equiv x y)
                  (equal (list-fix x) (list-fix y)))
           :hints(("Goal" :in-theory (enable fast-list-equiv)))))

  (defund list-equiv (x y)
    (mbe :logic (equal (list-fix x) (list-fix y))
         :exec (fast-list-equiv x y)))

  (verify-guards list-equiv)

  (local (in-theory (enable list-equiv)))

  (defequiv list-equiv)

  (defthm list-equiv-when-atom-left
    (implies (atom x)
             (equal (list-equiv x y)
                    (atom y)))
    :hints(("Goal" :in-theory (enable list-equiv))))

  (defthm list-equiv-when-atom-right
    (implies (atom y)
             (equal (list-equiv x y)
                    (atom x)))
    :hints(("Goal" :in-theory (enable list-equiv))))

  (defthm list-equiv-of-nil-left
    (equal (list-equiv nil y)
           (not (consp y))))

  (defthm list-equiv-of-nil-right
    (equal (list-equiv x nil)
           (not (consp x))))

  (defthm list-fix-under-list-equiv
    (list-equiv (list-fix x) x))

  (defthm list-fix-equal-forward-to-list-equiv
    (implies (equal (list-fix x) (list-fix y))
             (list-equiv x y))
    :rule-classes :forward-chaining)

  (defthm append-atom-under-list-equiv
    (implies (atom y)
             (list-equiv (append x y)
                         x))))


(local (in-theory (enable list-equiv)))


(defsection basic-list-equiv-congruences
  :parents (list-equiv)
  :short "Basic @(see list-equiv) @(see congruence) theorems for built-in
functions."

  (defcong list-equiv equal (list-fix x) 1)
  (defcong list-equiv equal      (car x) 1)
  (defcong list-equiv list-equiv (cdr x) 1)
  (defcong list-equiv list-equiv (cons x y) 2)

  (defcong list-equiv equal      (nth n x) 2)
  (defcong list-equiv list-equiv (nthcdr n x) 2)
  (defcong list-equiv list-equiv (update-nth n v x) 3)

  (defcong list-equiv equal      (consp x)     1 :hints (("Goal" :induct (cdr-cdr-induct x x-equiv))))
  (defcong list-equiv equal      (len x)       1 :hints (("Goal" :induct (cdr-cdr-induct x x-equiv))))
  (defcong list-equiv equal      (append x y)  1 :hints (("Goal" :induct (cdr-cdr-induct x x-equiv))))
  (defcong list-equiv list-equiv (append x y)  2)
  (defcong list-equiv list-equiv (member k x)  2 :hints(("Goal" :induct (cdr-cdr-induct x x-equiv))))
  (defcong list-equiv iff        (member k x)  2 :hints(("Goal" :induct (cdr-cdr-induct x x-equiv))))
  (defcong list-equiv equal      (subsetp x y) 1 :hints(("Goal" :induct (cdr-cdr-induct x x-equiv))))
  (defcong list-equiv equal      (subsetp x y) 2 :hints(("Goal" :induct (cdr-cdr-induct x x-equiv))))
  (defcong list-equiv equal      (remove a x)  2 :hints (("Goal" :induct (cdr-cdr-induct x x-equiv))))
  (defcong list-equiv equal      (resize-list lst n default) 1)

  (defcong list-equiv equal (revappend x y) 1
    :hints (("Goal" :induct (and (cdr-cdr-induct x x-equiv)
                                 (revappend x y)))))

  (defcong list-equiv list-equiv (revappend x y) 2)

  (defcong list-equiv list-equiv (last x) 1
    :hints(("Goal" :induct (cdr-cdr-induct x x-equiv))))

  (defcong list-equiv list-equiv (make-list-ac n val ac) 3)

  (defcong list-equiv equal (no-duplicatesp-equal x) 1
    :hints(("Goal" :induct (cdr-cdr-induct x x-equiv))))

  (defcong list-equiv equal (string-append-lst x) 1
    :hints(("Goal" :induct (cdr-cdr-induct x x-equiv))))

  ;; Mihir M. mod: four congruence rules for assoc, strip-cars, remove-assoc
  ;; and put-assoc are added. These four functions are generally associated
  ;; with an alist context, so congruence on list-equiv may seem to be a
  ;; surprising choice. However, remove-assoc always returns a true list, even
  ;; when it doesn't remove anything, and so true-list-fix sometimes appears
  ;; unexpectedly in an argument to the above four functions during
  ;; alist-related proofs; that's where these congruences help.

  (defcong list-equiv equal (assoc-equal x l) 2
    :hints(("Goal" :induct (cdr-cdr-induct l l-equiv))))

  (defcong list-equiv equal (strip-cars x) 1
    :hints(("Goal" :induct (cdr-cdr-induct x x-equiv))))

  (defcong list-equiv equal (remove-assoc-equal x l) 2
    :hints(("Goal" :induct (cdr-cdr-induct l l-equiv))))

  (defcong list-equiv list-equiv (put-assoc-equal name val alist) 3
    :hints(("Goal" :induct (cdr-cdr-induct alist alist-equiv)))))

(defsection list-equiv-reductions
  :parents (list-equiv)
  :short "Lemmas for reducing @(see list-equiv) terms involving basic functions."

   (defthm list-equiv-of-cons-and-cons
     (equal (list-equiv (cons a x) (cons a y))
            (list-equiv x y)))

   (defthm list-equiv-of-append-and-append
     (equal (list-equiv (append a x) (append a y))
            (list-equiv x y)))

   (defthm list-equiv-of-revappend-and-revappend
     (equal (list-equiv (revappend a x) (revappend a y))
            (list-equiv x y))))
