; Prefixp function and lemmas
; Copyright (C) 2005-2013 Kookamara LLC
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
;
; prefixp.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "equiv")
(local (include-book "take"))
(local (include-book "sets"))

(defsection prefixp
  :parents (std/lists)
  :short "@(call prefixp) determines if the list @('x') occurs at the front of
the list @('y')."

  (defund prefixp (x y)
    (declare (xargs :guard t))
    (if (consp x)
        (and (consp y)
             (equal (car x) (car y))
             (prefixp (cdr x) (cdr y)))
      t))

  (defthm prefixp-when-not-consp-left
    (implies (not (consp x))
             (prefixp x y))
    :hints(("Goal" :in-theory (enable prefixp))))

  (defthm prefixp-of-cons-left
    (equal (prefixp (cons a x) y)
           (and (consp y)
                (equal a (car y))
                (prefixp x (cdr y))))
    :hints(("Goal" :in-theory (enable prefixp))))

  (defthm prefixp-when-not-consp-right
    (implies (not (consp y))
             (equal (prefixp x y)
                    (not (consp x))))
    :hints(("Goal" :induct (len x))))

  (defthm prefixp-of-cons-right
    (equal (prefixp x (cons a y))
           (if (consp x)
               (and (equal (car x) a)
                    (prefixp (cdr x) y))
             t)))

  (defthm prefixp-of-list-fix-left
    (equal (prefixp (list-fix x) y)
           (prefixp x y))
    :hints(("Goal" :in-theory (enable prefixp))))

  (defthm prefixp-of-list-fix-right
    (equal (prefixp x (list-fix y))
           (prefixp x y))
    :hints(("Goal" :in-theory (enable prefixp))))

  (defcong list-equiv equal (prefixp x y) 1
    :hints(("Goal"
            :in-theory (disable prefixp-of-list-fix-left)
            :use ((:instance prefixp-of-list-fix-left)
                  (:instance prefixp-of-list-fix-left (x x-equiv))))))

  (defcong list-equiv equal (prefixp x y) 2
    :hints(("Goal"
            :in-theory (disable prefixp-of-list-fix-right)
            :use ((:instance prefixp-of-list-fix-right)
                  (:instance prefixp-of-list-fix-right (y y-equiv))))))

  (defthm len-when-prefixp
    (implies (prefixp x y)
             (equal (< (len y) (len x))
                    nil))
    :rule-classes ((:rewrite)
                   (:linear :corollary (implies (prefixp x y)
                                                (<= (len x) (len y)))))
    :hints(("Goal" :in-theory (enable (:induction prefixp)))))

  (defthm take-when-prefixp
    (implies (prefixp x y)
             (equal (take (len x) y)
                    (list-fix x)))
    :hints(("Goal" :in-theory (enable (:induction prefixp)))))

  (defthm prefixp-of-take
    (equal (prefixp (take n x) x)
           (<= (nfix n) (len x)))
    :hints(("Goal" :in-theory (enable take))))

  (defthm prefixp-reflexive
    (prefixp x x)
    :hints(("Goal" :induct (len x))))

  (defthm prefixp-of-append-arg2
    (equal (prefixp x (append y z))
           (or (prefixp x y)
               (and (equal (true-list-fix y)
                           (take (len y) x))
                    (prefixp (nthcdr (len y) x) z))))
    :hints (("goal" :in-theory (enable prefixp nthcdr))))

  (local (defthm equal-len-0
           (equal (equal (len x) 0)
                  (atom x))))

  (defthm prefixp-of-append-when-same-length
    (implies (<= (len x) (len y))
             (equal (prefixp x (append y z))
                    (prefixp x y)))
    :hints(("Goal"
            :induct (prefixp x y)
            :in-theory (enable prefixp list-equiv))))

  (defthm prefixp-when-equal-lengths
    (implies (>= (len x) (len y))
             (equal (prefixp x y)
                    (list-equiv x y)))
    :hints(("Goal" :in-theory (enable prefixp list-equiv))))

  ;; Mihir M. mod: Nine lemmas are added below. prefixp-transitive generates
  ;; two rewrite rules which are identical except in how they bind the free
  ;; variable y; it is similar with prefixp-one-way-or-another and the free
  ;; variable z. In nth-when-prefixp, the rewrite rule is a little less general
  ;; than the theorem in order to avoid endless rewriting.
  (defthm
    prefixp-transitive
    (implies (and (prefixp x y) (prefixp y z))
             (prefixp x z))
    :hints (("goal" :in-theory (enable prefixp)))
    :rule-classes
    (:rewrite (:rewrite :corollary (implies (and (prefixp y z) (prefixp x y))
                                            (prefixp x z)))))

  (defthm prefixp-append-append
    (equal (prefixp (append x1 x2) (append x1 y))
           (prefixp x2 y))
    :hints (("goal" :in-theory (enable prefixp))))

  (defthm prefixp-nthcdr-nthcdr
    (implies (and (>= (len l2) n)
                  (equal (take n l1) (take n l2)))
             (equal (prefixp (nthcdr n l1) (nthcdr n l2))
                    (prefixp l1 l2)))
    :hints (("goal" :in-theory (enable prefixp))))

  (defthm prefixp-one-way-or-another
    (implies (and (prefixp x z)
                  (prefixp y z)
                  (not (prefixp x y)))
             (prefixp y x))
    :hints (("goal" :in-theory (enable prefixp)))
    :rule-classes
    (:rewrite (:rewrite :corollary (implies (and (prefixp y z)
                                                 (prefixp x z)
                                                 (not (prefixp x y)))
                                            (prefixp y x)))))

  (defthm
    nth-when-prefixp
    (implies (and (prefixp x y) (< (nfix n) (len x)))
             (equal (nth n y) (nth n x)))
    :hints (("goal" :in-theory (enable prefixp)))
    :rule-classes ((:rewrite :corollary (implies (and (prefixp x y)
                                                      (not (list-equiv x y))
                                                      (< (nfix n) (len x)))
                                                 (equal (nth n y) (nth n x))))))

  (defthm
    append-when-prefixp
    (implies (prefixp x y)
             (equal (append x (nthcdr (len x) y)) y))
    :hints (("Goal" :induct (prefixp x y)
             :in-theory (enable prefixp)) ))

  (defthmd subsetp-when-prefixp
    (implies (prefixp x y)
             (subsetp-equal x y))
    :hints (("goal" :in-theory (enable prefixp)
             :induct (prefixp x y))))

  (defthm prefixp-of-append-arg1
    (equal (prefixp (append x y) z)
           (and (<= (+ (len x) (len y)) (len z))
                (equal (true-list-fix x)
                       (take (len x) z))
                (prefixp y (nthcdr (len x) z))))
    :hints (("goal" :in-theory (enable prefixp)
             :induct (prefixp x z))))

  (defthm prefixp-when-prefixp
    (implies (prefixp y x)
             (equal (prefixp x y) (list-equiv x y)))
    :hints (("goal" :in-theory (enable prefixp)))))

(encapsulate
  ()

  (local (in-theory (enable element-list-p true-list-fix prefixp)))

  (def-listp-rule element-list-p-when-prefixp
    (implies (and (prefixp x y)
                  (element-list-p y)
                  (not (element-list-final-cdr-p t)))
             (element-list-p (true-list-fix x)))
    :name element-list-p-when-prefixp
    :requirement (and true-listp (not single-var))
    :body
    (implies (and (prefixp x y)
                  (element-list-p y))
             (element-list-p (true-list-fix x)))))
