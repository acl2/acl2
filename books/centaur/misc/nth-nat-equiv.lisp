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
(include-book "std/basic/arith-equiv-defs" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))

(def-universal-equiv nth-nat-equiv
  :qvars n
  :equiv-terms ((nat-equiv (nth n x))))

(defcong nth-nat-equiv nat-equiv (nth n x) 2
  :hints(("Goal" :in-theory (e/d (nth-nat-equiv-necc)
                                 (nat-equiv))
          :do-not-induct t)))

(defcong nth-nat-equiv nth-nat-equiv (update-nth n v x) 3
  :hints(("Goal" :in-theory (e/d (nth-nat-equiv-necc)
                                 (nat-equiv))
          :expand ((:free (n v x y)
                    (nth-nat-equiv (update-nth n v x) y))))))

(defthm update-nth-of-same-under-nth-nat-equiv
  (nth-nat-equiv (update-nth n (nth n x) x)
                 x)
  :hints(("Goal" :in-theory (enable nth-nat-equiv))))

(local (defthm +-cancel-consts
         (implies (syntaxp (and (quotep x) (quotep y)))
                  (equal (+ x y z) (+ (+ x y) z)))))

(defcong nth-nat-equiv nat-equiv (car x) 1
  :hints (("goal" :use ((:instance nth-nat-equiv-necc
                         (n 0) (y x-equiv)))
           :in-theory (e/d (nth) (nth-nat-equiv-implies-nat-equiv-nth-2)))))

(defcong nth-nat-equiv nth-nat-equiv (cdr x) 1
  :hints (("goal" :use ((:instance nth-nat-equiv-necc
                         (n (+ 1 (nfix (nth-nat-equiv-witness (cdr x) (cdr
                                                                   x-equiv)))))
                         (y x-equiv)))
           :expand ((nth-nat-equiv (cdr x) (cdr x-equiv))
                    (nth-nat-equiv (cdr x) nil)
                    (nth-nat-equiv nil (cdr x-equiv)))
           :in-theory (disable nth-nat-equiv-implies-nat-equiv-nth-2))))

(defthmd nth-nat-equiv-recursive
  (equal (nth-nat-equiv x y)
         (or (and (atom x) (atom y))
             (and (nat-equiv (car x) (car y))
                  (nth-nat-equiv (cdr x) (cdr y)))))
  :hints ((and stable-under-simplificationp
               '(:cases ((nth-nat-equiv x y))))
          (and stable-under-simplificationp
               (cond ((equal (car clause) '(nth-nat-equiv x y))
                      '(:expand ((nth-nat-equiv x y)
                                 (:free (n) (nth n x))
                                 (:free (n) (nth n y))))))))
  :rule-classes ((:definition :install-body nil
                  :clique (nth-nat-equiv)
                  :controller-alist ((nth-nat-equiv t t)))))

(defun cdr2-ind (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (if (and (atom x) (atom y))
      nil
    (cdr2-ind (cdr x) (cdr y))))

(defthmd nth-nat-equiv-ind
  t
  :rule-classes ((:induction
                  :pattern (nth-nat-equiv x y)
                  :scheme (cdr2-ind x y))))
