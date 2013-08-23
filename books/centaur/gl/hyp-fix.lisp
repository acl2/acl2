; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "bfr")

;; determines whether x, a non-negated aig, is trivially necessarily true or
;; false assuming hyp.  Just traverses the top-level ANDs of hyp.  Returns (mv
;; known val).
(defund aig-under-hyp1 (x hyp)
  (declare (xargs :guard t))
  (b* (((when (hqual hyp x)) (mv t t))
       ((when (atom hyp))    (mv nil nil))
       ((when (eq (cdr hyp) nil))
        (mv (hqual (car hyp) x) nil))
       ((mv known1 val1) (aig-under-hyp1 x (car hyp)))
       ((when known1) (mv known1 val1)))
    (aig-under-hyp1 x (cdr hyp))))

(defthm aig-under-hyp1-correct
  (b* (((mv known val) (aig-under-hyp1 x hyp)))
    (implies (and known
                  (acl2::aig-eval hyp env))
             (equal (acl2::aig-eval x env) val)))
  :hints (("Goal" :induct (aig-under-hyp1 x hyp)
           :in-theory (e/d ((:i aig-under-hyp1))
                           ((:d aig-under-hyp1) acl2::aig-eval))
           :expand ((aig-under-hyp1 x hyp)
                    (aig-under-hyp1 hyp hyp)))
          (and stable-under-simplificationp
               '(:expand ((acl2::aig-eval hyp env))))))

(defthm booleanp-of-aig-under-hyp1-val
  (booleanp (mv-nth 1 (aig-under-hyp1 x hyp)))
  :hints(("Goal" :in-theory (enable aig-under-hyp1)))
  :rule-classes :type-prescription)

(defund aig-under-hyp (x hyp)
  (declare (xargs :guard t))
  (cond ((booleanp x) (mv t x))
        ((atom x) (aig-under-hyp1 x hyp))
        ((eq (cdr x) nil)
         (b* (((mv known val) (aig-under-hyp1 (car x) hyp)))
           (mv known (not val))))
        (t (b* (((mv known1 val1)
                 (aig-under-hyp (car x) hyp))
                ((when (and known1 (not val1)))
                 (mv t nil))
                ((mv known2 val2)
                 (aig-under-hyp (cdr x) hyp))
                ((when (and known2 (not val2)))
                 (mv t nil)))
             (mv (and known1 known2) t)))))

(defthm aig-under-hyp-correct
  (b* (((mv known val) (aig-under-hyp x hyp)))
    (implies (and known
                  (acl2::aig-eval hyp env))
             (equal (acl2::aig-eval x env) val)))
  :hints(("Goal" :in-theory (enable aig-under-hyp))))

(defthm aig-under-hyp-of-booleans
  (implies (booleanp x)
           (equal (aig-under-hyp x hyp)
                  (mv t x)))
  :hints(("Goal" :in-theory (enable aig-under-hyp)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm booleanp-of-aig-under-hyp-val
  (booleanp (mv-nth 1 (aig-under-hyp x hyp)))
  :hints(("Goal" :in-theory (enable aig-under-hyp)))
  :rule-classes :type-prescription)



(defun hyp-fix (x hyp)
  (declare (xargs :guard t))
  (bfr-case
   :bdd (let ((and (bfr-and x hyp)))
          (if and
              (if (hqual and hyp)
                  t
                x)
            nil))
   :aig (b* (((mv known val) (aig-under-hyp x hyp)))
          (if known
              val
            x))))

;; (prove-congruences (bfr-equiv bfr-equiv) hyp-fix)

(defn hyp-fixedp (x hyp)
  (declare (xargs :guard t))
  (hqual (hyp-fix x hyp) x))

;; (prove-congruences (bfr-equiv bfr-equiv) hyp-fixedp)

(defn true-under-hyp (x hyp)
  (declare (ignorable hyp))
  (eq x t))

(defn false-under-hyp (x hyp)
  (declare (ignorable hyp))
  (eq x nil))


(defmacro hf (x)
  `(hyp-fix ,x hyp))

(defmacro th (x)
  `(true-under-hyp ,x hyp))

(defmacro fh (x)
  `(false-under-hyp ,x hyp))

(add-untranslate-pattern (true-under-hyp ?x hyp) (th ?x))
(add-untranslate-pattern (false-under-hyp ?x hyp) (fh ?x))
(add-untranslate-pattern (hyp-fix ?x hyp) (hf ?x))
