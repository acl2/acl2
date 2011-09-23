; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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


(in-package "ACL2")

(include-book "misc/hons-help2" :dir :system)
(include-book "equal-sets")

(defun is-prefix (x y)
  (or (atom x)
      (and (equal (car x) (car y))
           (is-prefix (cdr x) (cdr y)))))

(defun subgoal-of (goal id)
  (declare (xargs :mode :program))
  (let ((goal (parse-clause-id goal)))
       (and (is-prefix (car goal) (car id))
            (or (not (equal (car goal) (car id)))
                (and (is-prefix (cadr goal) (cadr id))
                     (or (not (equal (cadr goal) (cadr id)))
                         (< (cddr goal) (cddr id))))))))



(defthm hons-member-equal-member-equal
  (equal (hons-member-equal a b)
         (member-equal a b)))

(defthm hons-assoc-equal-hons-put-list-iff
  (iff (hons-assoc-equal x (hons-put-list a b c))
       (or (member-equal x a)
           (hons-assoc-equal x c)))
  :hints (("goal" :induct (hons-put-list a b c))))


;; Hons-union interaction with member-equal
(defthm hons-union2-member
  (iff (member-equal x (hons-union2 a b c))
       (or (and (member-equal x a)
                (not (member-equal x b)))
           (member-equal x c))))

(defthm hons-union1-member
  (iff (member-equal x (hons-union1 a b c))
       (or (and (member-equal x a)
                (not (hons-get x b)))
           (member-equal x c))))

(defthm hons-union-member
  (iff (member-equal x (hons-union a b))
       (or (member-equal x a)
           (member-equal x b))))


;; ;; Hons-intersection interaction with member-equal
;; (defthm hons-intersection2-member
;;   (iff (member-equal x (hons-intersection2 a b))
;;        (and (member-equal x a)
;;             (member-equal x b))))

(defthm hons-int1-is-intersection-equal
  (implies (atom atom)
           (equal (hons-int1 x (hons-put-list y t atom))
                  (intersection-equal x y)))
  :hints(("Goal" :in-theory (enable intersection-equal))))

(defthm hons-intersection2-is-intersection-equal
  (equal (hons-intersection2 x y)
         (intersection-equal x y))
  :hints(("Goal" :in-theory (enable intersection-equal))))

;; (defthm hons-int1-member
;;   (iff (member-equal x (hons-int1 a b))
;;        (and (member-equal x a)
;;             (hons-assoc-equal x b))))

;; Hons-intersection interaction with member-equal
(defthm hons-set-diff2-member
  (iff (member-equal x (hons-set-diff2 a b))
       (and (member-equal x a)
            (not (member-equal x b)))))

(defthm hons-sd1-member
  (iff (member-equal x (hons-sd1 a b))
       (and (member-equal x a)
            (not (hons-assoc-equal x b)))))

(defthm hons-set-diff-member
  (iff (member-equal x (hons-set-diff a b))
       (and (member-equal x a)
            (not (member-equal x b)))))



(in-theory (disable hons-union hons-intersection hons-set-diff))

(local (set-default-hints '((set-reasoning))))

(defthm hons-union-set-equiv-union-equal
  (set-equivp (hons-union x y)
                   (union-equal x y)))


(defthm hons-set-diff-set-equiv-set-diff-equal
  (set-equivp (hons-set-diff x y)
                   (set-difference-equal x y)))

(defcong set-equivp iff (hons-member-equal a b) 2)

(defcong set-equivp set-equivp (hons-union x y) 1)
(defcong set-equivp set-equivp (hons-union x y) 2)

(defcong set-equivp set-equivp (hons-intersection x y) 1)
(defcong set-equivp set-equivp (hons-intersection x y) 2)

(defcong set-equivp set-equivp (hons-set-diff x y) 1)
(defcong set-equivp set-equivp (hons-set-diff x y) 2)




(defthmd hons-subset1-member-inv
  (implies (and (hons-subset1 l al)
                (not (hons-assoc-equal x al)))
           (not (member-equal x l))))

(defthmd hons-subset2-member
  (implies (and (hons-subset2 l l2)
                (member-equal x l))
           (member-equal x l2)))

(defthmd hons-subset-member
  (implies (and (hons-subset l l2)
                (member-equal x l))
           (member-equal x l2))
  :hints (("goal" :in-theory (enable hons-subset1-member-inv
                                     hons-subset2-member))))

(in-theory (disable hons-subset))




(defthmd hons-subset-implies-subset
  (implies (hons-subset x y)
           (subsetp-equal x y))
  :hints (("goal" :expand (subsetp-equal x y)
           :in-theory (enable hons-subset-member))))


(defthm subset-implies-hons-subset1
  (implies (subsetp-equal x y)
           (hons-subset1 x (hons-put-list y a z)))
  :hints (("Goal" :induct (len x))))

(defthm subset-implies-hons-subset2
  (implies (subsetp-equal x y)
           (hons-subset2 x y))
  :hints (("Goal" :induct (len x))))

(defthm hons-subset-is-subset
  (equal (hons-subset x y)
         (subsetp-equal x y))
  :hints (("goal" :expand (hons-subset x y)
           :cases ((hons-subset x y))
           :use hons-subset-implies-subset)))



(local
 (defthm equal-of-booleans-rewrite
   (implies (and (booleanp x)
                 (booleanp y))
            (equal (equal x y)
                   (iff x y)))
   :rule-classes ((:rewrite :backchain-limit-lst 1))))

(defcong set-equivp equal (hons-subset x y) 1)
(defcong set-equivp equal (hons-subset x y) 2)




(defun list-intersects-fal (x fal)
  (and (consp x)
       (or (hons-get (car x) fal)
           (list-intersects-fal (cdr x) fal))))


(defthm list-does-not-intersect-fal-atom
  (implies (atom fal)
           (not (list-intersects-fal x fal))))

(defthm list-intersects-fal-cons-fal
  (iff (list-intersects-fal x (cons (cons k v) fal))
       (or (member-equal k x)
           (list-intersects-fal x fal)))
  :hints(("Goal" :in-theory (enable hons-assoc-equal))))

(defthm hons-dups-p1-iff-no-dups-and-not-in-tab
  (iff (hons-dups-p1 l tab)
       (or (list-intersects-fal l tab)
           (not (no-duplicatesp-equal l))))
  :hints(("Goal" :in-theory (enable hons-dups-p1)
          :induct (hons-dups-p1 l tab))))

(defthm hons-dupsp-to-no-duplicatesp-equal
  (iff (hons-dups-p x)
       (not (no-duplicatesp-equal x))))

(in-theory (disable hons-dups-p))




(defthm hons-intersect-p1-iff-intersect
  (iff (hons-intersect-p1 l tab)
       (list-intersects-fal l tab)))

(defthm hons-intersect-p2-is-intersectp-equal
  (iff (hons-intersect-p2 x y)
       (intersectp-equal x y)))

(defthm list-intersects-fal-intersectp-equal
  (iff (list-intersects-fal x (hons-put-list y z acc))
       (or (intersectp-equal x y)
           (list-intersects-fal x acc)))
  :hints (("goal" :induct (len x))))

(defthm hons-intersect-p-is-intersectp-equal
  (iff (hons-intersect-p x y)
       (intersectp-equal x y)))

(in-theory (disable hons-intersect-p))




(defthm member-hons-remove-duplicates1
  (iff (member-equal x (hons-remove-duplicates1 lst al))
       (and (member-equal x lst)
            (not (hons-assoc-equal x al))))
  :hints(("Goal" :in-theory (enable hons-assoc-equal))))

(defthm no-duplicatesp-equal-hons-remove-duplicates1
  (no-duplicatesp-equal (hons-remove-duplicates1 lst al))
  :hints(("Goal" :in-theory (enable hons-assoc-equal))))

(defthm no-duplicatesp-equal-hons-remove-duplicates
  (no-duplicatesp-equal (hons-remove-duplicates lst)))

(defthm member-hons-remove-duplicates
  (iff (member-equal x (hons-remove-duplicates lst))
       (member-equal x lst))
  :hints(("Goal" :in-theory (enable hons-assoc-equal))))


(defthm set-equivp-hons-remove-duplicates
  (set-equivp (hons-remove-duplicates lst) lst)
  :hints (("goal" :in-theory (Disable set-equivp))))




(encapsulate
  ()
  (local (include-book "alist-defs"))

  (local (defthm l0
           (iff (hons-assoc-equal key alist)
                (member-equal key (alist-keys alist)))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthm l1
           (iff (member-equal a (alist-keys (hons-put-list x y z)))
                (member-equal a (append x (alist-keys z))))
           :hints(("Goal" :in-theory (enable hons-put-list alist-keys)))))

  (local (defthm l2
           (set-equivp (alist-keys (hons-put-list x y z))
                       (append x (alist-keys z)))
           :hints((witness))))

  (local (defthm l3
           (equal (hons-sd1 x (hons-put-list y t acc))
                  (set-difference-equal x (append y (alist-keys acc))))
           :hints(("Goal"
                   :induct (len x)
                   :in-theory (enable hons-sd1 set-difference-equal)))))

  (local (defthm l4
           (equal (hons-set-diff2 x y)
                  (set-difference-equal x y))
           :hints(("Goal" :in-theory (enable hons-set-diff2 set-difference-equal)))))

  (defthm hons-set-diff-removal
    (equal (hons-set-diff x y)
           (set-difference-equal x y))
    :hints(("Goal" :in-theory (enable hons-set-diff)))))
