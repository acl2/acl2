; Test of propagate-iso. Isomorphism between (integer-range-p 0 10 x) and (integer-range-p 8 18 x)
; Tests case where defiso uses :unconditional option. I.e. isomorphism is total on all ACL2 values.
;
; Copyright (C) 2018-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Stephen Westfold (westfold@kestrel.edu)
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(in-package "ACL2")

(include-book "kestrel/apt/propagate-iso" :dir :system)
;(include-book "kestrel/apt/isodata" :dir :system)
;(include-book "kestrel/utilities/testing" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

; test isomorphism between {0, ..., 9} and {8, ..., 17}:

;(must-succeed*
(define int10 (x)
  :returns (b booleanp)
  :no-function t
  (integer-range-p 0 10 x)
  ///
  (defthm int10-natp
    (implies (int10 x)
             (natp x))))

(define add-int10 ((x int10) (y int10))
  :returns (z int10
              :hints (("Goal" :in-theory (enable int10))))
  :no-function t
  (if  (mbt (and (int10 x)
                 (int10 y)))
      (mod (+ x y) 10)
    0)
  ///
  (defthmd add-int10-comm
    (equal (add-int10 x y)
           (add-int10 y x))))

(define double-int10 ((x int10))
  :returns (z int10)
  (add-int10 x x))

(define triple-int10 ((x int10))
  :returns (z int10)
  (add-int10 x (double-int10 x)))

(defforall int10-list-p (l) (int10 l) :true-listp t :guard t)

(defmap map-double-int10 (l) (double-int10 l)
  :declares ((xargs :guard (int10-list-p l))))

(defthm int10-list-p-of-map-double-int10
  (implies (int10-list-p l)
           (int10-list-p (map-double-int10 l)))
  :hints (("Goal" :in-theory (enable map-double-int10))))


(define int10-list-p-alias (l)
  :guard t
  (int10-list-p l))

(defmap map-double-int10-alias (l) (double-int10 l)
  :declares ((xargs :guard (int10-list-p l))))

(defthm int10-list-p-alias-of-map-double-int10-alias
  (implies (int10-list-p-alias l)
           (int10-list-p-alias (map-double-int10-alias l)))
  :hints (("Goal" :in-theory (enable map-double-int10-alias int10-list-p-alias))))


;; Isomorphic types
(define int18 (x)
  :returns (b booleanp)
  (integer-range-p 8 18 x)
  ///
  (defthm int18-natp
    (implies (int18 x)
             (natp x))))

(define int10-to-int18 ((x int10))
  ;; :returns (z int18
  ;;             :hints (("Goal" :in-theory (enable int10 int18))))
  (if (mbt (int10 x))
      (+ 8 x)
    (if (int18 x)
        (+ -10 x)
      x)))

(define int18-to-int10 ((x int18))
  ;; :returns (z int10
  ;;             :hints (("Goal" :in-theory (enable int10 int18))))
  (if (mbt (int18 x))
      (+ -8 x)
    (if (int10 x)
        (+ 10 x)
      x)))

(defiso int10-iso-int18
  int10 int18 int10-to-int18 int18-to-int10
  :thm-enable :all-nonguard
  :hints (:beta-of-alpha (("Goal" :in-theory (enable int10-to-int18 int18-to-int10 int10 int18)))
          :alpha-of-beta (("Goal" :in-theory (enable int10-to-int18 int18-to-int10 int10 int18)))
          :alpha-image (("Goal" :in-theory (enable int10-to-int18 int10 int18)))
          :beta-image (("Goal" :in-theory (enable int18-to-int10 int10 int18))))
  :unconditional t)

(defforall int18-list-p (l) (int18 l) :true-listp t :guard t)

(defmap int10-list-p-to-int18-list-p0 (l) (int10-to-int18 l)
  :declares ((xargs :guard (int10-list-p l))))
(defmap int18-list-p-to-int10-list-p0 (l) (int18-to-int10 l)
  :declares ((xargs :guard (int18-list-p l))))

(defiso int10-list-p-iso-int18-list-p0
  int10-list-p int18-list-p int10-list-p-to-int18-list-p0 int18-list-p-to-int10-list-p0
  :thm-enable :all-nonguard
  :hints (:beta-of-alpha (("Goal" :in-theory (enable int10-list-p int18-list-p)))
          :alpha-of-beta (("Goal" :in-theory (enable int10-list-p int18-list-p)))
          :alpha-image (("Goal" :in-theory (enable int10-list-p int18-list-p)))
          :beta-image (("Goal" :in-theory (enable int10-list-p int18-list-p)))))

(define int10-list-p-to-int18-list-p ((l int10-list-p))
  :enabled t
  (if (mbt (true-listp l))   ; (mbt (true-listp l))
      (int10-list-p-to-int18-list-p0 l)
    l))

(define int18-list-p-to-int10-list-p ((l int18-list-p))
  :enabled t
  (if (mbt (true-listp l))  ; (mbt (true-listp l))
      (int18-list-p-to-int10-list-p0 l)
    l))

(defiso int10-list-p-iso-int18-list-p
  int10-list-p int18-list-p int10-list-p-to-int18-list-p int18-list-p-to-int10-list-p
  :thm-enable :all-nonguard
  :hints (:beta-of-alpha (("Goal" :in-theory (enable int10-list-p int18-list-p)))
          :alpha-of-beta (("Goal" :in-theory (enable int10-list-p int18-list-p)))
          :alpha-image (("Goal" :in-theory (enable int10-list-p int18-list-p)))
          :beta-image (("Goal" :in-theory (enable int10-list-p int18-list-p))))
  :unconditional t)

(define add-int18 ((x int18) (y int18))
  :returns (z int18
              :hints (("Goal" :in-theory (enable int18))))
  :guard-hints (("Goal" :in-theory (enable int18)))
  :no-function t
  (if (mbt (and (int18 x)
                (int18 y)))
       (+ 8 (mod (+ x -8 y -8) 10))
    8))

(defthm add-int10-->add-int18
  (equal (add-int10 x y)
         (int18-to-int10 (add-int18 (int10-to-int18 x)
                                    (int10-to-int18 y))))
  :hints (("Goal" :in-theory (enable add-int10 add-int18 int10-to-int18 int18-to-int10
                                     int10 int18)
           :cases ((int10 x) (int10 y)))))

(defthmd add-int18-->add-int10
  (equal (add-int18 x y)
         (int10-to-int18 (add-int10 (int18-to-int10 x)
                                    (int18-to-int10 y)))))

(apt::propagate-iso (int10-iso-int18 int10-list-p-iso-int18-list-p)
  ((add-int10 add-int18 add-int10-->add-int18 add-int18-->add-int10
              (int10 int10) => int10))
  :first-event add-int10-comm
  :last-event int10-list-p-alias-of-map-double-int10-alias)


;; Too specific?: will fail on inconsequential changes.
(must-be-redundant
 (defthmd add-int18-comm (equal (add-int18 x y) (add-int18 y x)) :rule-classes ((:rewrite)))
 (defun double-int18 (x) (declare (xargs :guard (int18 x))) (add-int18 x x))
 (defthmd double-int18-is-iso-double-int10
   (implies (force (int18 x))
            (equal (double-int18 x)
                   (int10-to-int18 (double-int10 (int18-to-int10 x))))))
 (defthm double-int10-is-iso-double-int18
   (implies (force (int10 x))
            (equal (double-int10 x)
                   (int18-to-int10 (double-int18 (int10-to-int18 x))))))
 (defthm int18-of-double-int18 (let ((z (double-int18 x))) (int18 z)) :rule-classes ((:rewrite)))
 (defun triple-int18 (x) (declare (xargs :guard (int18 x))) (add-int18 x (double-int18 x)))
 (defthmd triple-int18-is-iso-triple-int10
   (implies (force (int18 x))
            (equal (triple-int18 x)
                   (int10-to-int18 (triple-int10 (int18-to-int10 x))))))
 (defthm triple-int10-is-iso-triple-int18
   (implies (force (int10 x))
            (equal (triple-int10 x)
                   (int18-to-int10 (triple-int18 (int10-to-int18 x))))))
 (defthm int18-of-triple-int18 (let ((z (triple-int18 x))) (int18 z)) :rule-classes ((:rewrite)))
 (defthm int18-list-p-of-cons
   (equal (int18-list-p (cons l0 l))
          (and (int18 l0) (int18-list-p l)))
   :rule-classes ((:rewrite)))
 (defthm use-int18-list-p-for-car
   (implies (and (int18-list-p l)
                 (consp (double-rewrite l)))
            (int18 (car l)))
   :rule-classes ((:rewrite)))
 (defthm use-int18-list-p-for-car-of-last
   (implies (and (int18-list-p l)
                 (consp (double-rewrite l)))
            (int18 (car (last l))))
   :rule-classes ((:rewrite)))
 (defthm int18-list-p-of-append
   (equal (int18-list-p (append l l0))
          (and (int18-list-p (true-list-fix l))
               (int18-list-p l0)))
   :rule-classes ((:rewrite)))
 (defthm int18-list-p-of-union-equal
   (equal (int18-list-p (union-equal l l0))
          (and (int18-list-p (true-list-fix l))
               (int18-list-p l0)))
   :rule-classes ((:rewrite)))
 (defthm int18-list-p-when-not-consp
   (implies (not (consp (double-rewrite l)))
            (equal (int18-list-p l) (equal nil l)))
   :rule-classes ((:rewrite)))
 (defthm int18-list-p-when-not-consp-cheap
   (implies (not (consp (double-rewrite l)))
            (equal (int18-list-p l) (equal nil l)))
   :rule-classes ((:rewrite :backchain-limit-lst (0))))
 (defthm int18-list-p-of-revappend
   (implies (and (int18-list-p l) (int18-list-p l0))
            (int18-list-p (revappend l l0)))
   :rule-classes ((:rewrite)))
 (defthm int18-list-p-of-cdr (implies (int18-list-p l) (equal (int18-list-p (cdr l)) t)) :rule-classes ((:rewrite)))
 (defthm int18-list-p-of-nthcdr
   (implies (int18-list-p l)
            (equal (int18-list-p (nthcdr l0 l)) t))
   :rule-classes ((:rewrite)))
 (defthm int18-list-p-of-firstn
   (implies (int18-list-p l)
            (equal (int18-list-p (firstn l0 l)) t))
   :rule-classes ((:rewrite)))
 (defthm int18-list-p-of-remove1-equal
   (implies (int18-list-p l)
            (int18-list-p (remove1-equal l0 l)))
   :rule-classes ((:rewrite)))
 (defthm int18-list-p-of-remove-equal
   (implies (int18-list-p l)
            (int18-list-p (remove-equal l0 l)))
   :rule-classes ((:rewrite)))
 (defthm int18-list-p-of-last (implies (int18-list-p l) (int18-list-p (last l))) :rule-classes ((:rewrite)))
 (defthm int18-list-p-of-take
   (implies (and (int18-list-p l)
                 (<= l0 (len (double-rewrite l))))
            (equal (int18-list-p (take l0 l)) t))
   :rule-classes ((:rewrite)))
 (defthmd true-listp-when-int18-list-p (implies (int18-list-p l) (true-listp l)) :rule-classes ((:rewrite)))
 (defthm true-listp-when-int18-list-p-forward
   (implies (int18-list-p l)
            (true-listp l))
   :rule-classes ((:forward-chaining :trigger-terms ((int18-list-p l)))))
 (defthmd int18-list-p-when-perm
   (implies (perm l l0)
            (equal (int18-list-p l)
                   (and (true-listp l)
                        (int18-list-p (true-list-fix l0)))))
   :rule-classes ((:rewrite)))
 (defthm int18-list-p-of-true-list-fix
   (implies (int18-list-p l)
            (int18-list-p (true-list-fix l)))
   :rule-classes ((:rewrite)))
 (defthm use-int18-list-p (implies (and (int18-list-p free-l) (memberp x free-l)) (int18 x)) :rule-classes ((:rewrite)))
 (defthm use-int18-list-p-2
   (implies (and (memberp x free-l)
                 (int18-list-p free-l))
            (int18 x))
   :rule-classes ((:rewrite)))
 (defthm int18-list-p-of-add-to-set-equal
   (equal (int18-list-p (add-to-set-equal l0 l))
          (and (int18 l0) (int18-list-p l)))
   :rule-classes ((:rewrite)))
 (defun map-double-int18 (l)
   (declare (xargs :measure (acl2-count l)
                   :guard (int18-list-p l)))
   (if (atom l)
       nil
     (cons (double-int18 (car l))
           (map-double-int18 (cdr l)))))
 (defthmd map-double-int18-is-iso-map-double-int10
   (implies (force (int18-list-p l))
            (equal (map-double-int18 l)
                   (int10-list-p-to-int18-list-p (map-double-int10 (int18-list-p-to-int10-list-p l))))))
 (defthm map-double-int10-is-iso-map-double-int18
   (implies (force (int10-list-p l))
            (equal (map-double-int10 l)
                   (int18-list-p-to-int10-list-p (map-double-int18 (int10-list-p-to-int18-list-p l))))))
 (defthm map-double-int18-of-nil (equal (map-double-int18 nil) nil) :rule-classes ((:rewrite)))
 (defthm map-double-int18-of-cons
   (equal (map-double-int18 (cons l0 l))
          (cons (double-int18 l0)
                (map-double-int18 l)))
   :rule-classes ((:rewrite)))
 (defthm map-double-int18-of-true-list-fix
   (equal (map-double-int18 (true-list-fix l))
          (map-double-int18 l))
   :rule-classes ((:rewrite)))
 (defthmd map-double-int18-opener
   (implies (consp (double-rewrite l))
            (equal (map-double-int18 l)
                   (cons (double-int18 (car (double-rewrite l)))
                         (map-double-int18 (cdr l)))))
   :rule-classes ((:rewrite)))
 (defthm map-double-int18-of-append
   (equal (map-double-int18 (append l l0))
          (append (map-double-int18 l)
                  (map-double-int18 l0)))
   :rule-classes ((:rewrite)))
 (defthm car-of-map-double-int18
   (equal (car (map-double-int18 l))
          (and (consp (double-rewrite l))
               (double-int18 (car (double-rewrite l)))))
   :rule-classes ((:rewrite)))
 (defthm cdr-of-map-double-int18
   (equal (cdr (map-double-int18 l))
          (map-double-int18 (cdr l)))
   :rule-classes ((:rewrite)))
 (defthm len-of-map-double-int18 (equal (len (map-double-int18 l)) (len (double-rewrite l))) :rule-classes ((:rewrite)))
 (defthm consp-of-map-double-int18
   (equal (consp (map-double-int18 l))
          (consp (double-rewrite l)))
   :rule-classes ((:rewrite)))
 (defthm map-double-int18-iff (iff (map-double-int18 l) (consp (double-rewrite l))) :rule-classes ((:rewrite)))
 (defthm true-listp-of-map-double-int18 (equal (true-listp (map-double-int18 l)) t) :rule-classes ((:rewrite)))
 (defthm firstn-of-map-double-int18
   (equal (firstn l0 (map-double-int18 l))
          (map-double-int18 (firstn l0 (double-rewrite l))))
   :rule-classes ((:rewrite)))
 (defthm take-of-map-double-int18
   (implies (<= l0 (len (double-rewrite l)))
            (equal (take l0 (map-double-int18 l))
                   (map-double-int18 (take l0 (double-rewrite l)))))
   :rule-classes ((:rewrite)))
 (defthm nth-of-map-double-int18
   (implies (natp l0)
            (equal (nth l0 (map-double-int18 l))
                   (and (< l0 (len (double-rewrite l)))
                        (double-int18 (nth l0 (double-rewrite l))))))
   :rule-classes ((:rewrite)))
 (defthm nthcdr-of-map-double-int18
   (equal (nthcdr l0 (map-double-int18 l))
          (map-double-int18 (nthcdr l0 l)))
   :rule-classes ((:rewrite)))
 (defthm int18-list-p-of-map-double-int18
   (implies (int18-list-p l)
            (int18-list-p (map-double-int18 l)))
   :rule-classes ((:rewrite)))
 (defun int18-list-p-alias (l) (declare (xargs :guard t)) (int18-list-p l))
 (defiso int10-list-p-alias-iso-int18-list-p-alias
   int10-list-p-alias int18-list-p-alias
   int10-list-p-to-int18-list-p
   int18-list-p-to-int10-list-p
   :thm-enable :all-nonguard
   :hints (:beta-of-alpha (("Goal" :in-theory (enable int10-list-p-alias int18-list-p-alias
                                                      int10-list-p-to-int18-list-p
                                                      int18-list-p-to-int10-list-p)))
           :alpha-of-beta (("Goal" :in-theory (enable int10-list-p-alias int18-list-p-alias
                                                      int10-list-p-to-int18-list-p
                                                      int18-list-p-to-int10-list-p)))
           :alpha-image (("Goal" :in-theory (enable int10-list-p-alias int18-list-p-alias
                                                    int10-list-p-to-int18-list-p)))
           :beta-image (("Goal" :in-theory (enable int10-list-p-alias int18-list-p-alias
                                                   int18-list-p-to-int10-list-p)))
           :alpha-guard (("Goal" :in-theory (enable int10-list-p-alias int18-list-p-alias)))
           :beta-guard (("Goal" :in-theory (enable int10-list-p-alias
                                                   int18-list-p-alias)))))
 (defthm int10-list-p-alias-int10-list-p-to-int18-list-p-int18-list-p
   (implies (and (int10-list-p-alias l))
            (int18-list-p (int10-list-p-to-int18-list-p l))))
 (defthm int18-list-p-alias-int18-list-p-to-int10-list-p-int10-list-p
   (implies (and (int18-list-p-alias l))
            (int10-list-p (int18-list-p-to-int10-list-p l))))
 (defun map-double-int18-alias (l)
   (declare (xargs :measure (acl2-count l)
                   :guard (int18-list-p l)))
   (if (atom l)
       nil
     (cons (double-int18 (car l))
           (map-double-int18-alias (cdr l)))))
 (defthmd map-double-int18-alias-is-iso-map-double-int10-alias
   (implies (force (int18-list-p l))
            (equal (map-double-int18-alias l)
                   (int10-list-p-to-int18-list-p (map-double-int10-alias (int18-list-p-to-int10-list-p l))))))
 (defthm map-double-int10-alias-is-iso-map-double-int18-alias
   (implies (force (int10-list-p l))
            (equal (map-double-int10-alias l)
                   (int18-list-p-to-int10-list-p (map-double-int18-alias (int10-list-p-to-int18-list-p l))))))
 (defthm map-double-int18-alias-of-nil (equal (map-double-int18-alias nil) nil) :rule-classes ((:rewrite)))
 (defthm map-double-int18-alias-of-cons
   (equal (map-double-int18-alias (cons l0 l))
          (cons (double-int18 l0)
                (map-double-int18-alias l)))
   :rule-classes ((:rewrite)))
 (defthm map-double-int18-alias-of-true-list-fix
   (equal (map-double-int18-alias (true-list-fix l))
          (map-double-int18-alias l))
   :rule-classes ((:rewrite)))
 (defthmd map-double-int18-alias-opener
   (implies (consp (double-rewrite l))
            (equal (map-double-int18-alias l)
                   (cons (double-int18 (car (double-rewrite l)))
                         (map-double-int18-alias (cdr l)))))
   :rule-classes ((:rewrite)))
 (defthm map-double-int18-alias-of-append
   (equal (map-double-int18-alias (append l l0))
          (append (map-double-int18-alias l)
                  (map-double-int18-alias l0)))
   :rule-classes ((:rewrite)))
 (defthm car-of-map-double-int18-alias
   (equal (car (map-double-int18-alias l))
          (and (consp (double-rewrite l))
               (double-int18 (car (double-rewrite l)))))
   :rule-classes ((:rewrite)))
 (defthm cdr-of-map-double-int18-alias
   (equal (cdr (map-double-int18-alias l))
          (map-double-int18-alias (cdr l)))
   :rule-classes ((:rewrite)))
 (defthm len-of-map-double-int18-alias
   (equal (len (map-double-int18-alias l))
          (len (double-rewrite l)))
   :rule-classes ((:rewrite)))
 (defthm consp-of-map-double-int18-alias
   (equal (consp (map-double-int18-alias l))
          (consp (double-rewrite l)))
   :rule-classes ((:rewrite)))
 (defthm map-double-int18-alias-iff
   (iff (map-double-int18-alias l)
        (consp (double-rewrite l)))
   :rule-classes ((:rewrite)))
 (defthm true-listp-of-map-double-int18-alias
   (equal (true-listp (map-double-int18-alias l))
          t)
   :rule-classes ((:rewrite)))
 (defthm firstn-of-map-double-int18-alias
   (equal (firstn l0 (map-double-int18-alias l))
          (map-double-int18-alias (firstn l0 (double-rewrite l))))
   :rule-classes ((:rewrite)))
 (defthm take-of-map-double-int18-alias
   (implies (<= l0 (len (double-rewrite l)))
            (equal (take l0 (map-double-int18-alias l))
                   (map-double-int18-alias (take l0 (double-rewrite l)))))
   :rule-classes ((:rewrite)))
 (defthm nth-of-map-double-int18-alias
   (implies (natp l0)
            (equal (nth l0 (map-double-int18-alias l))
                   (and (< l0 (len (double-rewrite l)))
                        (double-int18 (nth l0 (double-rewrite l))))))
   :rule-classes ((:rewrite)))
 (defthm nthcdr-of-map-double-int18-alias
   (equal (nthcdr l0 (map-double-int18-alias l))
          (map-double-int18-alias (nthcdr l0 l)))
   :rule-classes ((:rewrite)))
 (defthm int18-list-p-alias-of-map-double-int18-alias
   (implies (int18-list-p-alias l)
            (int18-list-p-alias (map-double-int18-alias l)))
   :rule-classes ((:rewrite)))
 )
