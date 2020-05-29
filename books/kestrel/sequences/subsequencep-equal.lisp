; The mathematical subsequence predicate for lists.
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Stephen Westfold (westfold@kestrel.edu)
; Contributing Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;;; subsequencep-equal is the mathematical subsequence predicate for lists.
;;; It is the relationship between a filtered list and the original list,

(include-book "std/lists/list-defuns" :dir :system) ;for suffixp and list-equiv
(include-book "kestrel/lists-light/firstn-def" :dir :system)
(include-book "kestrel/lists-light/subsequencep-equal-def" :dir :system)
(local (include-book "std/lists/take" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;; TODO: Consider disabling some rules below if they seem expensive.

;;
;; library stuff (TODO: Some of these must be already proved elsewhere):
;;

(defthm not-member-equal-of-cdr
  (implies (not (member-equal item z))
           (not (member-equal item (cdr z)))))

(defthm not-member-equal-of-member-equal
  (implies (not (member-equal item z))
           (not (member-equal item (member-equal item2 z)))))

(defthm member-append-1
  (implies (member-equal x y)
           (member-equal x (append y z))))

(defthm member-append-1-true
  (implies (member-equal x y)
           (equal (member-equal x (append y z))
                  (append (member-equal x y) z))))

;; TODO: suffixp does not handle non-true-lists nicely, so we use this variant
;; instead:
(defund suffixp$ (x y)
  (declare (xargs :guard t))
  (or (equal (true-list-fix x) (true-list-fix y))
      (and (consp y) (suffixp$ x (cdr y)))))

(defthm suffixp$-of-cdr-and-cdr
  (implies (and (suffixp$ x y)
                (consp x))
           (suffixp$ (cdr x) (cdr y)))
  :hints (("Goal" :in-theory (enable suffixp$))))

(defthm suffixp$-of-member-equal
  (suffixp$ (member-equal item x) x)
  :hints (("Goal" :in-theory (enable suffixp$ member-equal))))

(defcong list-equiv equal (suffixp$ x y) 1
  :hints (("Goal" :in-theory (enable suffixp$))))

(local
 (defun ind (x y y-equiv)
   (if (equal (true-list-fix x) (true-list-fix y))
       (list x y y-equiv)
       (and (consp y) (ind x (cdr y) (cdr y-equiv))))))

(defcong list-equiv equal (suffixp$ x y) 2
  :hints (("Goal" :expand (SUFFIXP$ X Y-EQUIV)
           :induct (ind x y y-equiv)
           :in-theory (enable SUFFIXP$))))
(local
 (defun ind2 (a x x-equiv)
   (cond ((endp x) (list a x x-equiv))
         ((equal a (car x)) x)
         (t (ind2 a (cdr x) (cdr x-equiv))))))

(defcong list-equiv list-equiv (member-equal a x) 2
  :hints (("Goal" :induct (ind2 a x x-equiv))))

(defcong list-equiv iff (member-equal a x) 2
  :hints (("Goal" :induct (ind2 a x x-equiv))))

(defcong list-equiv list-equiv (cdr x) 1)

(defthm suffixp$-of-member-equal-gen
  (implies (suffixp$ y x)
           (suffixp$ (member-equal item y) x))
  :hints (("Goal"
           :in-theory (enable suffixp$ member-equal))))

(defthm suffixp$-of-cdr
  (implies (suffixp$ y x)
           (suffixp$ (cdr y) x))
  :hints (("Goal" :in-theory (enable suffixp$ member-equal))))

(defthm suffixp$-reflexive
  (suffixp$ x x)
  :hints (("Goal" :in-theory (enable suffixp$ member-equal))))

(defthm suffixp$-transitive
  (implies (and (suffixp$ x y)
                (suffixp$ y z))
           (suffixp$ x z))
  :hints (("Goal" :in-theory (enable suffixp$))))

(defthm suffixp$-transitive-2
  (implies (and (suffixp$ y z)
                (suffixp$ x y))
           (suffixp$ x z))
  :hints (("Goal" :in-theory (enable suffixp$))))

(defthm suffixp$-of-member-equal-and-member-equal
  (implies (suffixp$ x y)
           (suffixp$ (member-equal item x) (member-equal item y)))
  :hints (("Goal" :in-theory (enable suffixp$))))

(defthm not-suffixp$-when-differ-on-member-equal
  (implies (and (not (member-equal item y))
                (member-equal item z))
           (not (suffixp$ z y)))
  :hints (("Goal" :expand (MEMBER-EQUAL ITEM Z)
           :in-theory (enable suffixp$ member-equal))))

(defthm true-listp-of-cdr-0
  (implies (true-listp x)
           (true-listp (cdr x))))

(defthm len-of-member-equal
  (<= (len (member-equal item x)) (len x))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable member-equal))))

;move (this must already exist)
(defthm +-cancel-lemma
  (equal (EQUAL (+ a x)
                (+ a y))
         (equal (fix x) (fix y))))

(defthm equal-of-len-and-member-equal
  (equal (equal (len x) (len (member-equal a x)))
         (or (not (consp x))
             (equal (car x) a))))
;;
;; end of library stuff
;;

;;
;; subsequencep-equal
;;

(defthm not-subsequencep-equal-when-differ-on-member
  (implies (and (not (member-equal item z))
                (member-equal item y))
           (not (subsequencep-equal y z)))
  :hints (("Goal" :in-theory (enable subsequencep-equal))))

(defthm subsequencep-equal-when-subsequencep-equal-and-suffixp$
  (implies (and (subsequencep-equal x z)
                (suffixp$ z y))
           (subsequencep-equal x y))
  :hints (("Goal" :in-theory (enable subsequencep-equal suffixp$))))

(defthm subsequencep-equal-when-subsequencep-equal-of-cdr-of-member-equal
  (implies (subsequencep-equal x (cdr (member-equal item y)))
           (subsequencep-equal x y))
  :hints (("Goal" :use (:instance subsequencep-equal-when-subsequencep-equal-and-suffixp$ (z (cdr (member-equal item y))))
           :in-theory (disable subsequencep-equal-when-subsequencep-equal-and-suffixp$))))

(defthm subsequencep-equal-lemma
  (implies (and (subsequencep-equal x y)
                (member-equal item x))
           (subsequencep-equal (cdr (member-equal item x))
                      (cdr (member-equal item y))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable subsequencep-equal member-equal))))

(defthm subsequencep-equal-transitive
  (implies (and (subsequencep-equal x y)
                (subsequencep-equal y z))
           (subsequencep-equal x z))
  :hints (("Goal" :in-theory (enable subsequencep-equal))))

;; stephen's properties:

(include-book "std/lists/equiv" :dir :system)
(include-book "kestrel/library-wrappers/sublistp" :dir :system)

(local (in-theory (enable subsequencep-equal)))

(defthm subsequencep-equal-when-atom-left
  (implies (atom x)
           (equal (subsequencep-equal x y)
                  t)))

(defthm subsequencep-equal-when-atom-right
  (implies (atom y)
           (equal (subsequencep-equal x y)
                  (atom x))))

(defthm subsequencep-equal-of-cdr-right
  (implies (subsequencep-equal x y)
           (subsequencep-equal (cdr x) y)))

(defthm subsequencep-equal-of-cons-right1
  (implies (subsequencep-equal x y)
           (subsequencep-equal x (cons a y))))

(defthm subsequencep-equal-of-cons-right2
  (implies (and (equal (car x) a)
                (subsequencep-equal (cdr x) y))
           (subsequencep-equal x (cons a y))))

(defthm subsequencep-equal-length12
  (implies (and ;(listp x)
                (> (len x) (len y))) ;changed length to len
           (not (subsequencep-equal x y)))
  :hints (("Goal" :in-theory (enable len-of-cdr))))

(defthm subsequencep-equal-of-cdr
  (implies (subsequencep-equal x (cdr y))
           (subsequencep-equal x y)))

(defthm subsequencep-equal-of-cons-cons
  (equal (subsequencep-equal (cons a x) (cons b y))
         (if (equal a b)
             (subsequencep-equal x y)
           (subsequencep-equal (cons a x) y))))

(defthm subsequencep-equal-implies-subsequencep-equal-of-cons-cons
  (implies (subsequencep-equal x y)
           (subsequencep-equal (cons a x) (cons a y))))

(defthm subsequencep-equal-of-append-append
  (equal (subsequencep-equal (append a x) (append a y))
         (subsequencep-equal x y))
  :hints (("Goal" :in-theory (enable append))))

(defthm subsequencep-equal-reflexive
  (subsequencep-equal x x))

(defthm subsequencep-equal-equal-len
  (implies (and (true-listp x) (true-listp y)
                (equal (len x) (len y)))
           (iff (subsequencep-equal x y)
                (equal x y)))
  :hints (("Goal" :in-theory (e/d (len-of-cdr) (len)))))

(defthm subsequencep-equal-of-cons-right
  (equal (subsequencep-equal x (cons a y))
         (or (and (equal (car x) a)
                  (subsequencep-equal (cdr x) y))
             (subsequencep-equal x y))))

(defthm subsequencep-equal-when-sublistp
  (implies (sublistp x y)
           (subsequencep-equal x y))
  :hints (("Goal" :in-theory (enable sublistp))))

(defthm subsequencep-equal-append-empty
  (equal (subsequencep-equal (append x y) y)
         (atom x))
  :hints (("Goal" :in-theory (enable append))))

(defthm subsequencep-equal-append-1
  (implies (subsequencep-equal x y)
           (subsequencep-equal x (append y z))))

(defthm subsequencep-equal-append-2
  (implies (subsequencep-equal x z)
           (subsequencep-equal x (append y z)))
  :hints (("Goal" :in-theory (e/d (append) (subsequencep-equal)))))

(defthm subsequencep-equal-append-append
  (implies (and (subsequencep-equal x1 y1) (subsequencep-equal x2 y2))
           (subsequencep-equal (append x1 x2) (append y1 y2)))
  :hints (("Goal" :in-theory (e/d (append) (len subsequencep-equal-of-cdr)))))

(defthm subsequencep-equal-of-true-list-fix-left
  (equal (subsequencep-equal (true-list-fix x) y)
         (subsequencep-equal x y))
  :hints (("Goal" :in-theory (disable len subsequencep-equal-of-cdr))))

(defthm subsequencep-equal-of-true-list-fix-right
  (equal (subsequencep-equal x (true-list-fix y))
         (subsequencep-equal x y))
  :hints (("Goal" :in-theory (enable sublistp-when-prefixp ;why?
                                     ))))

(defcong list-equiv equal (subsequencep-equal x y) 1
  :hints (("Goal" :in-theory (disable subsequencep-equal
                                      subsequencep-equal-of-true-list-fix-left)
           :use ((:instance subsequencep-equal-of-true-list-fix-left (x x))
                 (:instance subsequencep-equal-of-true-list-fix-left (x x-equiv))))))

(defcong list-equiv equal (subsequencep-equal x y) 2
  :hints (("Goal" :in-theory (disable subsequencep-equal
                                      subsequencep-equal-of-true-list-fix-right)
           :use ((:instance subsequencep-equal-of-true-list-fix-right (y y))
                 (:instance subsequencep-equal-of-true-list-fix-right (y y-equiv))))))

(defthm lower-bound-of-len-when-subsequencep-equal
  (implies (subsequencep-equal x y)
           (<= (len x) (len y)))
  :rule-classes ((:rewrite) (:linear)))

(defthmd subsequencep-equal-antisymmetric
  (implies (and (true-listp x) (true-listp y)
                (subsequencep-equal x y)
                (subsequencep-equal y x))
           (equal (equal x y)
                  t))
  :hints (("Goal" :cases ((< (len x) (len y))
                          (< (len y) (len x))))))

;; Disabling this, since it seemed slow
(defthmd subsequencep-equal-subsetp-equal
  (implies (subsequencep-equal x y)
           (subsetp-equal x y))
  :hints (("Goal" :in-theory (enable subsequencep-equal subsetp-equal))))

;;; prefixp theorems
(defthm prefixp-take
  (implies (and (true-listp l) (<= i (length l)) )
           (prefixp (take i l) l))
  :hints (("Goal" :in-theory (enable take prefixp))))

(defthm prefixp-firstn
  (implies (and (true-listp l) (<= i (length l)) )
           (prefixp (firstn i l) l))
  :hints (("Goal" :in-theory (enable firstn prefixp))))

(defthmd prefixp-antisymmetric
  (implies (and (true-listp x) (true-listp y)
                (prefixp x y)
                (prefixp y x))
           (equal (equal x y)
                  t))
  :hints (("Goal" :in-theory (enable sublistp-when-prefixp
                                     subsequencep-equal-antisymmetric))))

(defthm prefixp-transitive-1
  (implies (and (prefixp x y)
                (prefixp y z))
           (prefixp x z))
  :hints (("Goal" :in-theory (enable prefixp))))


;;; sublistp theorems
(defthm suffixp$-sublistp
  (implies (suffixp$ x y)
           (sublistp x y))
  :hints (("Goal" :in-theory (e/d (suffixp$ sublistp-when-prefixp)
                                  (len subsequencep-equal-antisymmetric)))))

(defthm suffixp-sublistp
  (implies (suffixp x y)
           (sublistp x y))
  :hints (("Goal" :in-theory (enable suffixp))))

(defthmd sublistp-antisymmetric
  (implies (and (true-listp x) (true-listp y)
                (sublistp x y)
                (sublistp y x))
           (equal (equal x y)
                  t))
  :hints (("Goal" :in-theory (enable subsequencep-equal-antisymmetric))))

(defthm sublistp-not-prefixp
  (implies (and (sublistp x y)
                (not (prefixp x y)))
           (sublistp x (cdr y))))

(defthm sublistp-nthcdr
  (sublistp (nthcdr i l) l)
  :hints (("Goal" :in-theory (enable nthcdr sublistp))))

;; (defthm sublistp-nthcdr-1
;;   (implies (sublistp l1 (nthcdr i l2))
;;            (sublistp l1 l2))
;;   :hints (("Goal" :in-theory (enable nthcdr sublistp))))

(defthm sublistp-when-sublistp-and-prefixp
  (implies (and (sublistp x y)
                (prefixp y z))
           (sublistp x z))
  :hints (("Goal" :in-theory (enable sublistp prefixp))))

(defthm sublistp-transitive
  (implies (and (sublistp x y)
                (sublistp y z))
           (sublistp x z))
  :hints (("Goal" :in-theory (enable sublistp))))

;; (defthm sublistp-nthcdr-trans
;;   (implies (sublistp l1 l2)
;;            (sublistp (nthcdr i l1) l2))
;;   :hints (("Goal" :in-theory (enable nthcdr sublistp))))

(defthm sublistp-subseq
  (implies (and (natp i)
                (natp j)
                (<= j (length l))
                (<= i j))
           (sublistp (subseq l i j) l))
  :hints (("Goal" :in-theory (enable subseq subseq-list sublistp-when-prefixp)
                  :use (:instance sublistp-transitive
                                  (x (take (+ (- i) j) (nthcdr i l)))
                                  (y (nthcdr i l))
                                  (z l)) )))

;; (defstub p (*) => *)

;; (defun filter-p (l)
;;   (if (endp l)
;;       ()
;;     (if (p (car l))
;;         (cons (car l) (filter-p (cdr l)))
;;       (filter-p (cdr l)))))

;; (defthm subsequencep-equal-filter-p
;;   (subsequencep-equal (filter-p l) l))

(include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system)

(defthm not-member-equal-when-subsequencep-equal-and-member-equal
  (implies (and (subsequencep-equal x y)
                (not (member-equal a y)))
           (not (member-equal a x))))

(defthm no-duplicatesp-equal-when-subsequencep-equal
  (implies (and (subsequencep-equal x y)
                (no-duplicatesp y))
           (no-duplicatesp-equal x))
  :hints (("Goal" :expand ((no-duplicatesp-equal x))
           :in-theory (e/d (subsequencep-equal) (no-duplicatesp)))))
