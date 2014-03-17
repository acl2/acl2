; FTY type support library
; Copyright (C) 2014 Centaur Technology
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

(in-package "FTY")

(include-book "fixequiv")
(include-book "std/basic/defs" :dir :System)
(include-book "centaur/misc/arith-equivs" :dir :system)
(include-book "std/misc/two-nats-measure" :dir :system)
(include-book "std/lists/acl2-count" :dir :system)
(include-book "centaur/misc/universal-equiv" :dir :System)

(deffixtype nat
  :pred natp
  :fix nfix
  :equiv acl2::nat-equiv)

(deffixtype int
  :pred integerp
  :fix ifix
  :equiv acl2::int-equiv)

(defines int-tree
  (define int-tree-p (x)
    :measure (two-nats-measure (acl2-count x) 1)
    (if (atom x)
        (integerp x)
      (int-treelist-p x)))
  (define int-treelist-p (x)
    :measure (two-nats-measure (acl2-count x) 0)
    (if (atom x)
        (eq x nil)
      (and (int-tree-p (car x))
           (int-treelist-p (cdr x)))))
  ///
  (defthm int-treelist-p-of-cons
    (equal (int-treelist-p (cons a b))
           (and (int-tree-p a)
                (int-treelist-p b))))

  (defthm int-tree-p-when-consp
    (implies (consp x)
             (equal (int-tree-p x)
                    (int-treelist-p x)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm int-tree-p-when-atom
    (implies (not (consp x))
             (equal (int-tree-p x)
                    (integerp x)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm int-treelist-p-when-consp
    (implies (consp x)
             (equal (int-treelist-p x)
                    (and (int-tree-p (car x))
                         (int-treelist-p (cdr x)))))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm int-treelist-p-when-atom
    (implies (not (consp x))
             (equal (int-treelist-p x)
                    (equal x nil)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))

(defines int-tree-fix
  (define int-tree-fix (x)
    :returns (itree int-tree-p
                    :hints ('(:expand ((int-tree-fix x)
                                       (int-treelist-fix x)))))
    :measure (two-nats-measure (acl2-count x) 1)
    (if (atom x)
        (ifix x)
      (int-treelist-fix x)))
  (define int-treelist-fix (x)
    :returns (itree int-treelist-p
                    :hints ('(:expand ((int-treelist-fix x)))))
    :measure (two-nats-measure (acl2-count x) 0)
    (if (atom x)
        nil
      (cons (int-tree-fix (car x))
            (int-treelist-fix (cdr x)))))
  ///
  (defthm-int-tree-fix-flag
    (defthm int-tree-fix-when-int-tree-p
      (implies (int-tree-p x)
               (equal (int-tree-fix x) x))
      :flag int-tree-fix)
    (defthm int-treelist-fix-when-int-treelist-p
      (implies (int-treelist-p x)
               (equal (int-treelist-fix x) x))
      :flag int-treelist-fix))

  (acl2::def-universal-equiv int-tree-equiv
    :equiv-terms ((equal (int-tree-fix acl2::x))))

  (deffixtype int-tree
    :pred int-tree-p
    :fix int-tree-fix
    :equiv int-tree-equiv
    :hints (("goal" :in-theory (enable int-tree-equiv))))

  (deffixtype int-treelist
    :pred int-treelist-p
    :fix int-treelist-fix
    :equiv int-treelist-equiv :define t)

  (local (in-theory (e/d (int-treelist-equiv int-tree-equiv)
                         (int-tree-fix))))

  (deffixcong int-treelist-equiv int-treelist-equiv (cdr x) x
    :hints (("goal" :expand ((int-treelist-fix x)))))
  (deffixcong int-treelist-equiv int-treelist-equiv (cons x y) y)
  (deffixcong int-tree-equiv int-treelist-equiv (cons x y) x
    :hints (("goal" :expand ((int-treelist-fix x)))))
  (deffixcong int-treelist-equiv int-tree-equiv (car x) x
    :hints (("goal" :expand ((int-treelist-fix x))))))


(defines count-leaves
  (define count-leaves ((x int-tree-p))
    :returns (n natp :rule-classes :type-prescription)
    :measure (two-nats-measure (acl2-count x) 1)
    (if (atom x)
        1
      (count-leaves-list x)))
  (define count-leaves-list ((x int-treelist-p))
    :returns (n natp :rule-classes :type-prescription)
    :measure (two-nats-measure (acl2-count x) 0)
    (if (atom x)
        0
      (+ (count-leaves (car x))
         (count-leaves-list (cdr x)))))
  ///
  (deffixequiv-mutual count-leaves
    :hints(("Goal" :expand ((int-tree-fix x)
                            (int-treelist-fix x))))))

(defines nth-leaf
  :guard-hints (("goal" :expand ((count-leaves-list x)
                                 (count-leaves x))))
  (define nth-leaf ((n natp)
                    (x int-tree-p))
    :measure (two-nats-measure (acl2-count x) 1)
    :guard (< n (count-leaves x))
    :returns (leaf integerp :rule-classes :type-prescription)
    (if (atom x)
        (acl2::lifix x)
      (nth-leaf-list n x)))
  (define nth-leaf-list ((n natp) (x int-treelist-p))
    :guard (< n (count-leaves-list x))
    :measure (two-nats-measure (acl2-count x) 0)
    :returns (leaf integerp :rule-classes :type-prescription)
    (if (mbt (consp x))
        (let ((first-count (count-leaves (car x))))
          (if (< (acl2::lnfix n) first-count)
              (nth-leaf n (car x))
            (nth-leaf-list (- (acl2::lnfix n) first-count)
                           (cdr x))))
      0))
  ///
  (deffixequiv-mutual nth-leaf :args (n))
  (deffixequiv-mutual nth-leaf :omit (n)
    :hints ((and stable-under-simplificationp
                 '(:expand ((int-treelist-fix x)
                            (int-tree-fix x)))))))

(defines update-nth-leaf
  :guard-hints (("goal" :expand ((count-leaves-list x)
                                 (count-leaves x))))
  (define update-nth-leaf ((n natp)
                           (v integerp)
                           (x int-tree-p))
    :measure (two-nats-measure (acl2-count x) 1)
    :guard (<= n (count-leaves x))
    :returns (tree int-tree-p)
    (if (atom x)
        (acl2::lifix v)
      (update-nth-leaf-list n v x)))
  (define update-nth-leaf-list ((n natp)
                                (v integerp)
                                (x int-treelist-p))
    :guard (<= n (count-leaves-list x))
    :measure (two-nats-measure (acl2-count x) 0)
    :returns (tree int-treelist-p)
    (if (atom x)
        (list (acl2::lifix v))
      (let ((first-count (count-leaves (car x))))
        (if (< (acl2::lnfix n) first-count)
            (cons (update-nth-leaf n v (car x))
                  (mbe :logic (int-treelist-fix (cdr x)) :exec (cdr x)))
          (cons (mbe :logic (int-tree-fix (car x)) :exec (car x))
                (update-nth-leaf-list
                 (- (acl2::lnfix n) first-count)
                 v (cdr x)))))))
  ///
  (deffixequiv-mutual update-nth-leaf :args (n))
  (deffixequiv-mutual update-nth-leaf
    :args ((update-nth-leaf
            (x int-tree-p :hints ('(:expand ((int-tree-fix x)
                                             (int-treelist-fix x))))))
           (update-nth-leaf-list
            (x int-treelist-p :hints ('(:expand ((int-treelist-fix x))))))))
  (deffixequiv-mutual update-nth-leaf :omit (n x)))
