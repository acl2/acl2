; List Equivalence
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "list-fix")
(local (include-book "take"))
(local (include-book "arithmetic/top" :dir :system))

; [Jared]: I split these out of centaur/misc/lists.lisp.  I tried to mainly
; keep the rules about list-equiv and how it relates to built-in functions.
; But this omits things like arith-equivs, list-defthms, and rewrite rules to
; rewrite various functions.

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

(local (in-theory (enable list-equiv)))

(defequiv list-equiv)

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

(defcong list-equiv equal      (list-fix x) 1)
(defcong list-equiv equal      (car x) 1)
(defcong list-equiv list-equiv (cdr x) 1)
(defcong list-equiv list-equiv (cons x y) 2)

(defcong list-equiv equal      (nth n x) 2)
(defcong list-equiv list-equiv (nthcdr n x) 2)
(defcong list-equiv list-equiv (update-nth n v x) 3)

(local (defun cdr-cdr-ind (x y)
         (declare (xargs :measure (+ (len x) (len y))))
         (if (and (atom x) (atom y))
             nil
           (cdr-cdr-ind (cdr x) (cdr y)))))

(defcong list-equiv equal      (consp x)     1 :hints (("Goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv equal      (len x)       1 :hints (("Goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv equal      (append x y)  1 :hints (("Goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv list-equiv (append x y)  2)
(defcong list-equiv list-equiv (member k x)  2 :hints(("Goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv iff        (member k x)  2 :hints(("Goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv equal      (subsetp x y) 1 :hints(("Goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv equal      (subsetp x y) 2 :hints(("Goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv equal      (remove k x)  2 :hints (("Goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv equal      (resize-list lst n default) 1)


(defcong list-equiv equal (revappend x y) 1
  :hints (("Goal" :induct (and (cdr-cdr-ind x x-equiv)
                               (revappend x y)))))

(defcong list-equiv list-equiv (revappend x y) 2)

(defcong list-equiv equal (butlast lst n) 1
  :hints(("Goal" :induct (cdr-cdr-ind lst lst-equiv))))

(defcong list-equiv list-equiv (make-list-ac n val ac) 3)


(defund simpler-take (n xs)
  ;; Redundant with take.lisp
  (declare (xargs :guard (and (natp n)
                              (true-listp xs))))
  (if (zp n)
      nil
    (cons (car xs)
          (simpler-take (1- n) (cdr xs)))))

(defcong list-equiv equal (simpler-take n x) 2
  :hints(("Goal"
          :in-theory (enable simpler-take)
          :induct (and (simpler-take n x)
                       (cdr-cdr-ind x x-equiv)))))

(defcong list-equiv equal (take n x) 2)

(defthm append-nil-under-list-equiv
  (list-equiv (append x nil) x))



(defcong list-equiv equal (no-duplicatesp-equal x) 1
  :hints(("Goal" :induct (cdr-cdr-ind x x-equiv))))
