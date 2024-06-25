;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "coi/types/types" :dir :system)
(include-book "coi/pattern-hint/pattern-hint" :dir :system)
(include-book "coi/util/linear" :dir :system)
(include-book "coi/quantification/quantified-congruence" :dir :system)
(include-book "coi/util/deffix" :dir :system)

(defmacro stable-p (&rest args)
  `(and stable-under-simplificationp
        '(,@args)))

(defmacro with-arithmetic (&rest args)
  `(encapsulate
       ()
     (local (include-book "arithmetic-5/top" :dir :system))
     (local (in-theory (disable DEFAULT-PLUS-2
                                |(* -1 x)|
                                NOT-INTEGERP-4A
                                SIMPLIFY-SUMS-<)))
     ,@args
     ))

(defmacro include-arithmetic ()
  `(progn
     (include-book "arithmetic-5/top" :dir :system)
     (in-theory (disable DEFAULT-PLUS-2
                         |(* -1 x)|
                         NOT-INTEGERP-4A
                         SIMPLIFY-SUMS-<))
     ))

(defthm nfix-natp
  (implies
   (natp x)
   (equal (nfix x) x))
  :rule-classes (:rewrite :linear))

(in-theory (disable nfix))

(defthm implies-nat-equiv
  (implies
   (equal (nfix x) y)
   (nat-equiv x y))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable nat-equiv))))

(defthm nat-equiv-type-alist
  (implies
   (nat-equiv x (nfix y))
   (nat-equiv x y))
  :rule-classes (:forward-chaining))

(defthm implies-int-equiv
  (implies
   (equal (ifix x) y)
   (int-equiv x y))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable int-equiv))))

(defthm int-equiv-type-alist
  (implies
   (int-equiv x (ifix y))
   (int-equiv x y))
  :rule-classes (:forward-chaining))

(defthm rfix-rationalp
  (implies
   (rationalp x)
   (equal (rfix x) x))
  :hints (("Goal" :in-theory (enable rfix)))
  :rule-classes (:rewrite :linear))

(defthm nfix-with-negative-ifix
  (implies
   (< (ifix i) 0)
   (equal (nfix i) 0))
  :hints (("Goal" :in-theory (enable ifix nfix)))
  :rule-classes (:rewrite :linear))

(defthm equal-ifix-zero
  (implies
   (equal (ifix x) 0)
   (int-equiv x 0))
  :hints (("Goal" :in-theory (enable int-equiv)))
  :rule-classes (:forward-chaining))

(defthm nfix-ifix-equiv
  (implies
   (<= 0 (ifix x))
   (equal (ifix x) (nfix x)))
  :hints (("Goal" :in-theory (enable ifix nfix)))
  :rule-classes (:rewrite :linear))

(defthm nfix-int-equiv-x
  (implies
   (<= 0 (ifix x))
   (int-equiv (nfix x) x))
  :hints (("Goal" :in-theory (enable int-equiv ifix nfix))))

(defthm natp-nfix
  (implies
   (natp x)
   (and (equal (nfix x) x)
        (equal (ifix x) x)))
  :rule-classes (:rewrite :linear))

(defthm integerp-ifix
  (implies
   (integerp x)
   (equal (ifix x) x))
  :rule-classes (:rewrite :linear))

(defthm zp-ifix
  (implies
   (zp x)
   (<= (ifix x) 0))
  :hints (("Goal" :in-theory (enable nfix zp)))
  :rule-classes (:linear))

(defthm zp-nfix
  (implies
   (zp x)
   (equal (nfix x) 0))
  :hints (("Goal" :in-theory (enable nfix zp)))
  :rule-classes (:rewrite :linear))

(defthm ifix-nfix-linear-relation
  (<= (ifix x) (nfix x))
  :rule-classes :linear)

(in-theory (disable ifix nfix))
(in-theory (disable rfix))

(def::type nnrat (x)
  :body (and (rationalp x) (<= 0 x))
  :type-witness 0)

(def::type prat (x)
  :body (and (rationalp x) (< 0 x))
  :type-witness 1)

(defthm prat-fix-unfix
  (implies
   (< 0 (rfix x))
   (equal (prat-fix x) (rfix x)))
  :hints (("Goal" :in-theory (enable rfix prat-p prat-fix))))

(in-theory (disable rational-equiv int-equiv nat-equiv NAT-EQUIV$INLINE))

;; nth

(defthm list-equiv-true-list-fix
  (list-equiv (true-list-fix x) x)
  :hints (("Goal" :in-theory (enable list-equiv true-list-fix))))

(defcong list-equiv equal (true-list-fix x) 1
  :hints (("Goal" :in-theory (enable list-equiv))))

(local
 (defthm len-true-list-fix
   (implies
    (syntaxp (symbolp x))
    (equal (len x)
           (len (true-list-fix x))))
   :hints (("Goal" :in-theory (enable true-list-fix)))))

(defcong list-equiv equal (len x) 1)

(local
 (defthmd nth-list-fix
   (implies
    (syntaxp (symbolp x))
    (equal (nth i x)
           (nth i (true-list-fix x))))
   :hints (("Goal" :in-theory (enable nth true-list-fix)))))

(defcong list-equiv equal (nth i x) 2
  :hints (("Goal" :in-theory (enable nth-list-fix list-equiv))))

(defthmd nth-nfix
  (implies
   (syntaxp (symbolp i))
   (equal (nth i ens)
          (nth (nfix i) ens)))
  :hints (("Goal" :in-theory (enable nfix))))

(defcong nat-equiv equal (nth i ens) 1
  :hints (("Goal" :in-theory (enable nth-nfix))))

(in-theory (disable nth))

(encapsulate
    (
     ((branch-witness * *) => *)
     )
  (local (defun branch-witness (name args) (declare (ignore name args)) t))

  (defthm booleanp-branch-witness
    (booleanp (branch-witness name args))
    :rule-classes (:type-prescription))
  
  (defthm not-branch-witness
    (implies
     (not (branch-witness name args))
     nil)
    :rule-classes (:forward-chaining))
  
  )


(encapsulate
    ()

  (set-tau-auto-mode nil)
  
  (defun branch (name args)
    (branch-witness name args))
  
  (defthm not-branch
    (implies
     (not (branch name args))
     nil)
    :rule-classes (:forward-chaining))
  
  (defthm branch-is-true
    (branch name args))
  
  (in-theory (disable branch))

  )
  
(defmacro and-mark (spec &rest body)
  (declare (xargs :guard (and (true-listp spec) (symbolp (car spec)) (< 0 (len spec)))))
  (let ((name  (car spec)))
    (let ((pre  (packn-pos (list name '-pre)  :keyword))
          (post (packn-pos (list name '-post) :keyword)))
      `(and
        (branch ,pre (list ,@(cdr spec)))
        (implies
         (branch ,post (list ,@(cdr spec)))
         (and ,@body))))))

(defthm and-mark-property
  (iff (and-mark (:hi 'x) a b)
       (and a b t)))

(def::un average (x y)
  (declare (xargs :fty ((rational rational) rational)))
  (/ (+ x y) 2))

(defthm rationalp-average
  (rationalp (average x y))
  :rule-classes (:type-prescription))

(defthm average-same
  (equal (average x x) (rfix x)))

(defthm average-bounds-1
  (implies
   (<= (rfix x) (rfix y))
   (and (<= (average x y) (rfix y))
        (<= (rfix x) (average x y))))
  :rule-classes (:linear))

(defthm average-bounds-2
  (implies
   (<= (rfix x) (rfix y))
   (and (<= (average y x) (rfix y))
        (<= (rfix x) (average y x))))
  :rule-classes (:linear))

(defthm average-difference-linear-rule
  (equal (+ (- (rfix x)) (average x y))
         (+ (rfix y) (- (average x y))))
  :rule-classes ((:linear :trigger-terms ((average x y))))
  :hints (("Goal" :in-theory (enable average))))

(in-theory (disable average))

(defmacro implies* (x y)
  `(or (not ,x) ,y))
