; Centaur Miscellaneous Books
; Copyright (C) 2008-2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "universal-equiv")
(include-book "std/lists/equiv" :dir :system)

(def-universal-equiv nth-equiv
  :qvars n
  :equiv-terms ((equal (nth n x))))

(defcong nth-equiv equal (nth n x) 2
  :hints(("Goal" :in-theory (enable nth-equiv-necc))))

(defcong nth-equiv nth-equiv (update-nth n v x) 3
  :hints(("Goal" :in-theory (enable nth-equiv-necc)
          :expand ((:free (n v x y)
                    (nth-equiv (update-nth n v x) y))))))

(defthm update-nth-of-same-under-nth-equiv
  (nth-equiv (update-nth n (nth n x) x)
             x)
  :hints(("Goal" :in-theory (enable nth-equiv))))

(local (defthm +-cancel-consts
         (implies (syntaxp (and (quotep x) (quotep y)))
                  (equal (+ x y z) (+ (+ x y) z)))))

(defcong nth-equiv equal (car x) 1
  :hints (("goal" :use ((:instance nth-equiv-necc
                         (n 0) (y x-equiv)))
           :in-theory (e/d (nth) (nth-equiv-implies-equal-nth-2)))))

(defcong nth-equiv nth-equiv (cdr x) 1
  :hints (("goal" :use ((:instance nth-equiv-necc
                         (n (+ 1 (nfix (nth-equiv-witness (cdr x) (cdr
                                                                   x-equiv)))))
                         (y x-equiv)))
           :expand ((nth-equiv (cdr x) (cdr x-equiv))
                    (nth-equiv (cdr x) nil)
                    (nth-equiv nil (cdr x-equiv)))
           :in-theory (disable nth-equiv-implies-equal-nth-2))))

(defthmd nth-equiv-recursive
  (equal (nth-equiv x y)
         (or (and (atom x) (atom y))
             (and (equal (car x) (car y))
                  (nth-equiv (cdr x) (cdr y)))))
  :hints ((and stable-under-simplificationp
               '(:cases ((nth-equiv x y))))
          (and stable-under-simplificationp
               (cond ((equal (car clause) '(nth-equiv x y))
                      '(:expand ((nth-equiv x y)
                                 (:free (n) (nth n x))
                                 (:free (n) (nth n y))))))))
  :rule-classes ((:definition :install-body nil
                  :clique (nth-equiv)
                  :controller-alist ((nth-equiv t t)))))

(defun cdr2-ind (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (if (and (atom x) (atom y))
      nil
    (cdr2-ind (cdr x) (cdr y))))

(defthmd nth-equiv-ind
  t
  :rule-classes ((:induction
                  :pattern (nth-equiv x y)
                  :scheme (cdr2-ind x y))))




(defrefinement list-equiv  nth-equiv
  :hints (("goal" :in-theory (enable nth-equiv-recursive
                                     nth-equiv-ind
                                     list-equiv
                                     true-list-fix))))



(defthm true-list-fix-under-nth-equiv
  (nth-equiv (true-list-fix x) x))


(defcong list-equiv equal (nth-equiv x y) 1)

(defcong list-equiv equal (nth-equiv x y) 2)

(defcong nth-equiv nth-equiv (cons x y) 2
  :hints(("Goal" :in-theory (enable nth-equiv-recursive))))

(defcong nth-equiv nth-equiv (cdr x) 1
  :hints(("Goal" :in-theory (enable nth-equiv-recursive))))

(defcong nth-equiv nth-equiv (nthcdr n x) 2
  :hints(("Goal" :in-theory (enable nth-equiv-recursive))))

(defcong nth-equiv nth-equiv (update-nth n v x) 3
  :hints(("Goal" :in-theory (enable nth-equiv-recursive))))

(defthm true-list-fix-under-nth-equiv
  (nth-equiv (true-list-fix x) x))

(defun nth-equiv-exec (x y)
  (declare (xargs :guard (and (true-listp x) (true-listp y))
                  :guard-hints (("goal" :in-theory (enable nth-equiv-recursive nth-equiv-exec)))))
  (mbe :logic (nth-equiv x y)
       :exec (or (and (atom x) (atom y))
                 (and (equal (car x) (car y))
                      (nth-equiv-exec (cdr x) (cdr y))))))

(defsection nth-equiv-fix
  (defund nth-equiv-fix (x)
    (declare (xargs :guard (true-listp x)))
    (if (atom (remove nil x))
        nil
      (cons (car x)
            (nth-equiv-fix (cdr x)))))

  (local (in-theory (enable nth-equiv-fix)))
  
  (local (defthm nth-when-remove-nil
           (implies (not (consp (remove nil x)))
                    (not (nth n x)))))

  (defthm nth-of-nth-equiv-fix
    (equal (nth n (nth-equiv-fix x)) (nth n x)))

  (defthm nth-equiv-fix-under-nth-equiv
    (nth-equiv (nth-equiv-fix x) x)
    :hints(("Goal" :in-theory (enable nth-equiv))))

  (defthm nth-equiv-fix-self
    (equal (nth-equiv-fix (nth-equiv-fix x)) (nth-equiv-fix x)))

  (local (defthm consp-remove-equal-of-true-list-fix
           (equal (consp (remove-equal k (true-list-fix x)))
                  (consp (remove-equal k x)))))

  (defcong nth-equiv equal (nth-equiv-fix x) 1
    :hints (("goal" :in-theory (enable nth-equiv-recursive nth-equiv-ind)
             :induct (nth-equiv x x-equiv))))

  (defthmd nth-equiv-is-equal-of-fixes
    (equal (nth-equiv x y)
           (equal (nth-equiv-fix x) (nth-equiv-fix y)))
    :hints (("goal" :use ((:instance nth-equiv-fix-under-nth-equiv)
                          (:instance nth-equiv-fix-under-nth-equiv (x y)))
             :in-theory (disable nth-equiv-fix-under-nth-equiv nth-equiv-fix)))))

