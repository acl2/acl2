; Test of propagate-iso. Isomorphism between (integer-range-p 0 10 x) and (integer-range-p 10 20 x)
; Like propagate-iso-tests.lisp but generates isomorphisms for types depending on primary isomorphism type.
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

; test isomorphism between {0, ..., 9} and {10, ..., 19}:

(define int10 (x)
  :returns (b booleanp)
  :no-function t
  (integer-range-p 0 10 x)
  ///
  (defthm int10-natp
    (implies (int10 x)
             (natp x))))

(define add-int10 ((x int10) (y int10))
  :returns (z int10 :hyp :guard
              :hints (("Goal" :in-theory (enable int10))))
  :no-function t
  (mod (+ x y) 10)
  ///
  (defthmd add-int10-comm
    (implies (and (int10 x) (int10 y))
             (equal (add-int10 x y)
                    (add-int10 y x)))))

(define double-int10 ((x int10))
  :returns (z int10 :hyp :guard)
  (add-int10 x x))

(define triple-int10 ((x int10))
  :returns (z int10 :hyp :guard)
  (add-int10 x (double-int10 x)))

(defforall int10-list-p (l) (int10 l) :true-listp t :guard t)

(defmap map-double-int10 (l) (double-int10 l)
  :declares ((xargs :guard (int10-list-p l))))

(defthm int10-list-p-of-map-double-int10
  (implies (int10-list-p l)
           (int10-list-p (map-double-int10 l)))
  :hints (("Goal" :in-theory (enable map-double-int10))))

(define int10* (x)
  :returns (b booleanp)
  :enabled t
  :no-function t
  (or (null x)
      (int10 x)))

(define pair-int10-bool-p (pr)
  :returns (v booleanp)
  :enabled t
  (and (consp pr)
       (int10 (car pr))
       (booleanp (cdr pr))))

(define pair-int10-bool->val ((pr pair-int10-bool-p))
  :returns (v int10 :hyp :guard)
  :no-function t
  :enabled t
  (car pr))

(define pair-int10-bool->flag ((pr pair-int10-bool-p))
  :returns (v booleanp :hyp :guard)
  :no-function t
  :enabled t
  (cdr pr))

(defforall pair-int10-bool-listp (l) (pair-int10-bool-p l) :true-listp t :guard t)

(define filter-double ((l pair-int10-bool-listp))
  :returns (l int10-list-p :hyp :guard)
  (if (atom l)
      ()
    (let ((rl (filter-double (cdr l)))
          (pr (car l)))
      (if (pair-int10-bool->flag pr)
          (cons (pair-int10-bool->val pr)
                rl)
        rl))))

(define int10-map-p (m)
  :returns (b booleanp)
  (if (atom m)
      (null m)
    (and (consp (car m))
         (int10 (caar m))
         (int10 (cdar m))
         (int10-map-p (cdr m))))
  ///
  (defthm int10-map-p-nil
    (int10-map-p nil))

  (defthm int10-map-p-cdr
    (implies (int10-map-p m)
             (int10-map-p (cdr m))))
  (defthm int10-map-p-car
    (implies (and (consp m)
                  (int10-map-p m))
             (consp (car m))))
  (defthm int10-map-p-caar
    (implies (and (int10-map-p m)
                  (consp m))
             (int10 (caar m))))
  (defthm int10-map-p-cdar
    (implies (and (int10-map-p m)
                  (consp m))
             (int10 (cdar m))))
  (defthm int10-map-p-cons
    (equal (int10-map-p (cons x y))
           (and (consp x)
                (int10 (car x))
                (int10 (cdr x))
                (int10-map-p y))))
) ; int10-map-p

(define lookup-int10-map ((x int10) (m int10-map-p))
  :returns (val int10* :hyp (int10-map-p m))
  (if (atom m)
      nil
    (if (and (consp (car m))
             (equal (caar m) x))
        (cdar m)
      (lookup-int10-map x (cdr m)))))

(define int10-map2-p (m)
  :returns (b booleanp)
  (if (atom m)
      (null m)
    (if (consp (car m))
        (if (int10 (caar m))
            (if (int10 (cdar m))
                (if (int10-map2-p (cdr m))
                    t
                  nil)
              nil)
          nil)
      nil))
  ///
  (defthm int10-map2-p-nil
    (int10-map2-p nil))

  (defthm int10-map2-p-cdr
    (implies (int10-map2-p m)
             (int10-map2-p (cdr m))))
  (defthm int10-map2-p-car
    (implies (and (consp m)
                  (int10-map2-p m))
             (consp (car m))))
  (defthm int10-map2-p-caar
    (implies (and (int10-map2-p m)
                  (consp m))
             (int10 (caar m))))
  (defthm int10-map2-p-cdar
    (implies (and (int10-map2-p m)
                  (consp m))
             (int10 (cdar m))))
  (defthm int10-map2-p-cons
    (equal (int10-map2-p (cons x y))
           (and (consp x)
                (int10 (car x))
                (int10 (cdr x))
                (int10-map2-p y))))
)

;; Isomorphic types
(define int20 (x)
  :returns (b booleanp)
  (integer-range-p 10 20 x)
  ///
  (defthm int20-natp
    (implies (int20 x)
             (natp x))))

(define int10-to-int20 ((x int10))
  ;; :returns (z int20 :hyp :guard
  ;;             :hints (("Goal" :in-theory (enable int10 int20))))
  (+ 10 x))

(define int20-to-int10 ((x int20))
  ;; :returns (z int10 :hyp :guard
  ;;             :hints (("Goal" :in-theory (enable int10 int20))))
  (+ -10 x))

(defiso int10-iso-int20
  int10 int20 int10-to-int20 int20-to-int10
  :thm-enable :all-nonguard
  :hints (:beta-of-alpha (("Goal" :in-theory (enable int10-to-int20 int20-to-int10 int10 int20)))
          :alpha-of-beta (("Goal" :in-theory (enable int10-to-int20 int20-to-int10 int10 int20)))
          :alpha-image (("Goal" :in-theory (enable int10-to-int20 int10 int20)))
          :beta-image (("Goal" :in-theory (enable int20-to-int10 int10 int20)))))

(define add-int20 ((x int20) (y int20))
  :returns (z int20 :hyp :guard
              :hints (("Goal" :in-theory (enable int20))))
  :guard-hints (("Goal" :in-theory (enable int20)))
  (+ 10 (mod (+ x y) 10)))

(defthm add-int10-->add-int20
  (implies (and (int10 x) (int10 y))
           (equal (add-int10 x y)
                  (int20-to-int10 (add-int20 (int10-to-int20 x)
                                             (int10-to-int20 y)))))
  :hints (("Goal" :in-theory (enable add-int10 add-int20 int10-to-int20 int20-to-int10
                                     int10 int20))))

(defthmd add-int20-->add-int10
  (implies (and (int20 x) (int20 y))
           (equal (add-int20 x y)
                  (int10-to-int20 (add-int10 (int20-to-int10 x)
                                             (int20-to-int10 y)))))
  :hints (("Goal" :in-theory (enable add-int10 add-int20 int10-to-int20 int20-to-int10
                                     int10 int20))))

(apt::propagate-iso int10-iso-int20
  ((add-int10 add-int20 add-int10-->add-int20 add-int20-->add-int10
              (int10 int10) => int10))
  :first-event add-int10-comm
  :last-event int20)

;; Too specific?: will fail on inconsequential changes.
(must-be-redundant
 (defthmd add-int20-comm
   (implies (and (int20 x) (int20 y))
            (equal (add-int20 x y) (add-int20 y x)))
   :rule-classes ((:rewrite)))
 (defun double-int20 (x) (declare (xargs :guard (int20 x))) (add-int20 x x))
 (defthmd double-int20-is-iso-double-int10
   (implies (force (int20 x))
            (equal (double-int20 x)
                   (int10-to-int20 (double-int10 (int20-to-int10 x))))))
 (defthm double-int10-is-iso-double-int20
   (implies (force (int10 x))
            (equal (double-int10 x)
                   (int20-to-int10 (double-int20 (int10-to-int20 x))))))
 (defthm int20-of-double-int20 (implies (int20 x) (let ((z (double-int20 x))) (int20 z))) :rule-classes ((:rewrite)))
 (defun triple-int20 (x) (declare (xargs :guard (int20 x))) (add-int20 x (double-int20 x)))
 (defthmd triple-int20-is-iso-triple-int10
   (implies (force (int20 x))
            (equal (triple-int20 x)
                   (int10-to-int20 (triple-int10 (int20-to-int10 x))))))
 (defthm triple-int10-is-iso-triple-int20
   (implies (force (int10 x))
            (equal (triple-int10 x)
                   (int20-to-int10 (triple-int20 (int10-to-int20 x))))))
 (defthm int20-of-triple-int20 (implies (int20 x) (let ((z (triple-int20 x))) (int20 z))) :rule-classes ((:rewrite)))
 (defun int20-list-p (l)
   (declare (xargs :measure (acl2-count l)
                   :guard t))
   (if (atom l)
       (null l)
     (and (int20 (first l))
          (int20-list-p (rest l)))))
 (defun int10-list-p-->-int20-list-p (l)
   (declare (xargs :guard (int10-list-p l)))
   (if (atom l)
       nil
     (cons (int10-to-int20 (first l))
           (int10-list-p-->-int20-list-p (rest l)))))
 (defun int20-list-p-->-int10-list-p (l)
   (declare (xargs :guard (int20-list-p l)))
   (if (atom l)
       nil
     (cons (int20-to-int10 (first l))
           (int20-list-p-->-int10-list-p (rest l)))))
 (defiso int10-list-p-iso-int20-list-p
   int10-list-p int20-list-p
   int10-list-p-->-int20-list-p
   int20-list-p-->-int10-list-p
   :thm-enable :all-nonguard
   :hints (:beta-of-alpha (("Goal" :in-theory (enable int10-list-p int20-list-p
                                                      int10-list-p-->-int20-list-p
                                                      int20-list-p-->-int10-list-p)))
                          :alpha-of-beta (("Goal" :in-theory (enable int10-list-p int20-list-p
                                                                     int10-list-p-->-int20-list-p
                                                                     int20-list-p-->-int10-list-p)))
                          :alpha-image (("Goal" :in-theory (enable int10-list-p int20-list-p
                                                                   int10-list-p-->-int20-list-p)))
                          :beta-image (("Goal" :in-theory (enable int10-list-p int20-list-p
                                                                  int20-list-p-->-int10-list-p)))))
 (defthm int10-list-p-->-int20-list-p-null
   (implies (and (int10-list-p l) (atom l))
            (null (int10-list-p-->-int20-list-p l))))
 (defthm int10-list-p-->-int20-list-p-int20--consp
   (implies (and (int10-list-p l) (not (atom l)))
            (consp (int10-list-p-->-int20-list-p l))))
 (defthm int10-list-p-->-int20-list-p-int20-first
   (implies (and (int10-list-p l) (not (atom l)))
            (int20 (first (int10-list-p-->-int20-list-p l)))))
 (defthm int10-list-p-->-int20-list-p-int20-list-p-rest
   (implies (and (int10-list-p l) (not (atom l)))
            (int20-list-p (rest (int10-list-p-->-int20-list-p l)))))
 (defthm int20-list-p-->-int10-list-p-null
   (implies (and (int20-list-p l) (atom l))
            (null (int20-list-p-->-int10-list-p l))))
 (defthm int20-list-p-->-int10-list-p-int10--consp
   (implies (and (int20-list-p l) (not (atom l)))
            (consp (int20-list-p-->-int10-list-p l))))
 (defthm int20-list-p-->-int10-list-p-int10-first
   (implies (and (int20-list-p l) (not (atom l)))
            (int10 (first (int20-list-p-->-int10-list-p l)))))
 (defthm int20-list-p-->-int10-list-p-int10-list-p-rest
   (implies (and (int20-list-p l) (not (atom l)))
            (int10-list-p (rest (int20-list-p-->-int10-list-p l)))))
 (defthm int20-list-p-of-cons
   (equal (int20-list-p (cons l0 l))
          (and (int20 l0) (int20-list-p l)))
   :rule-classes ((:rewrite)))
 (defthm use-int20-list-p-for-car
   (implies (and (int20-list-p l)
                 (consp (double-rewrite l)))
            (int20 (car l)))
   :rule-classes ((:rewrite)))
 (defthm use-int20-list-p-for-car-of-last
   (implies (and (int20-list-p l)
                 (consp (double-rewrite l)))
            (int20 (car (last l))))
   :rule-classes ((:rewrite)))
 (defthm int20-list-p-of-append
   (equal (int20-list-p (append l l0))
          (and (int20-list-p (true-list-fix l))
               (int20-list-p l0)))
   :rule-classes ((:rewrite)))
 (defthm int20-list-p-of-union-equal
   (equal (int20-list-p (union-equal l l0))
          (and (int20-list-p (true-list-fix l))
               (int20-list-p l0)))
   :rule-classes ((:rewrite)))
 (defthm int20-list-p-when-not-consp
   (implies (not (consp (double-rewrite l)))
            (equal (int20-list-p l) (equal nil l)))
   :rule-classes ((:rewrite)))
 (defthm int20-list-p-when-not-consp-cheap
   (implies (not (consp (double-rewrite l)))
            (equal (int20-list-p l) (equal nil l)))
   :rule-classes ((:rewrite :backchain-limit-lst (0))))
 (defthm int20-list-p-of-revappend
   (implies (and (int20-list-p l) (int20-list-p l0))
            (int20-list-p (revappend l l0)))
   :rule-classes ((:rewrite)))
 (defthm int20-list-p-of-cdr (implies (int20-list-p l) (equal (int20-list-p (cdr l)) t)) :rule-classes ((:rewrite)))
 (defthm int20-list-p-of-nthcdr
   (implies (int20-list-p l)
            (equal (int20-list-p (nthcdr l0 l)) t))
   :rule-classes ((:rewrite)))
 (defthm int20-list-p-of-firstn
   (implies (int20-list-p l)
            (equal (int20-list-p (firstn l0 l)) t))
   :rule-classes ((:rewrite)))
 (defthm int20-list-p-of-remove1-equal
   (implies (int20-list-p l)
            (int20-list-p (remove1-equal l0 l)))
   :rule-classes ((:rewrite)))
 (defthm int20-list-p-of-remove-equal
   (implies (int20-list-p l)
            (int20-list-p (remove-equal l0 l)))
   :rule-classes ((:rewrite)))
 (defthm int20-list-p-of-last (implies (int20-list-p l) (int20-list-p (last l))) :rule-classes ((:rewrite)))
 (defthm int20-list-p-of-take
   (implies (and (int20-list-p l)
                 (<= l0 (len (double-rewrite l))))
            (equal (int20-list-p (take l0 l)) t))
   :rule-classes ((:rewrite)))
 (defthmd true-listp-when-int20-list-p (implies (int20-list-p l) (true-listp l)) :rule-classes ((:rewrite)))
 (defthm true-listp-when-int20-list-p-forward
   (implies (int20-list-p l)
            (true-listp l))
   :rule-classes ((:forward-chaining :trigger-terms ((int20-list-p l)))))
 (defthmd int20-list-p-when-perm
   (implies (perm l l0)
            (equal (int20-list-p l)
                   (and (true-listp l)
                        (int20-list-p (true-list-fix l0)))))
   :rule-classes ((:rewrite)))
 (defthm int20-list-p-of-true-list-fix
   (implies (int20-list-p l)
            (int20-list-p (true-list-fix l)))
   :rule-classes ((:rewrite)))
 (defthm use-int20-list-p (implies (and (int20-list-p free-l) (memberp x free-l)) (int20 x)) :rule-classes ((:rewrite)))
 (defthm use-int20-list-p-2
   (implies (and (memberp x free-l)
                 (int20-list-p free-l))
            (int20 x))
   :rule-classes ((:rewrite)))
 (defthm int20-list-p-of-add-to-set-equal
   (equal (int20-list-p (add-to-set-equal l0 l))
          (and (int20 l0) (int20-list-p l)))
   :rule-classes ((:rewrite)))
 (defun map-double-int20 (l)
   (declare (xargs :measure (acl2-count l)
                   :guard (int20-list-p l)))
   (if (atom l)
       nil
     (cons (double-int20 (car l))
           (map-double-int20 (cdr l)))))
 (defthmd map-double-int20-is-iso-map-double-int10
   (implies (force (int20-list-p l))
            (equal (map-double-int20 l)
                   (int10-list-p-->-int20-list-p (map-double-int10 (int20-list-p-->-int10-list-p l))))))
 (defthm map-double-int10-is-iso-map-double-int20
   (implies (force (int10-list-p l))
            (equal (map-double-int10 l)
                   (int20-list-p-->-int10-list-p (map-double-int20 (int10-list-p-->-int20-list-p l))))))
 (defthm map-double-int20-of-nil (equal (map-double-int20 nil) nil) :rule-classes ((:rewrite)))
 (defthm map-double-int20-of-cons
   (equal (map-double-int20 (cons l0 l))
          (cons (double-int20 l0)
                (map-double-int20 l)))
   :rule-classes ((:rewrite)))
 (defthm map-double-int20-of-true-list-fix
   (equal (map-double-int20 (true-list-fix l))
          (map-double-int20 l))
   :rule-classes ((:rewrite)))
 (defthmd map-double-int20-opener
   (implies (consp (double-rewrite l))
            (equal (map-double-int20 l)
                   (cons (double-int20 (car (double-rewrite l)))
                         (map-double-int20 (cdr l)))))
   :rule-classes ((:rewrite)))
 (defthm map-double-int20-of-append
   (equal (map-double-int20 (append l l0))
          (append (map-double-int20 l)
                  (map-double-int20 l0)))
   :rule-classes ((:rewrite)))
 (defthm car-of-map-double-int20
   (equal (car (map-double-int20 l))
          (and (consp (double-rewrite l))
               (double-int20 (car (double-rewrite l)))))
   :rule-classes ((:rewrite)))
 (defthm cdr-of-map-double-int20
   (equal (cdr (map-double-int20 l))
          (map-double-int20 (cdr l)))
   :rule-classes ((:rewrite)))
 (defthm len-of-map-double-int20 (equal (len (map-double-int20 l)) (len (double-rewrite l))) :rule-classes ((:rewrite)))
 (defthm consp-of-map-double-int20
   (equal (consp (map-double-int20 l))
          (consp (double-rewrite l)))
   :rule-classes ((:rewrite)))
 (defthm map-double-int20-iff (iff (map-double-int20 l) (consp (double-rewrite l))) :rule-classes ((:rewrite)))
 (defthm true-listp-of-map-double-int20 (equal (true-listp (map-double-int20 l)) t) :rule-classes ((:rewrite)))
 (defthm firstn-of-map-double-int20
   (equal (firstn l0 (map-double-int20 l))
          (map-double-int20 (firstn l0 (double-rewrite l))))
   :rule-classes ((:rewrite)))
 (defthm take-of-map-double-int20
   (implies (<= l0 (len (double-rewrite l)))
            (equal (take l0 (map-double-int20 l))
                   (map-double-int20 (take l0 (double-rewrite l)))))
   :rule-classes ((:rewrite)))
 (defthm nth-of-map-double-int20
   (implies (natp l0)
            (equal (nth l0 (map-double-int20 l))
                   (and (< l0 (len (double-rewrite l)))
                        (double-int20 (nth l0 (double-rewrite l))))))
   :rule-classes ((:rewrite)))
 (defthm nthcdr-of-map-double-int20
   (equal (nthcdr l0 (map-double-int20 l))
          (map-double-int20 (nthcdr l0 l)))
   :rule-classes ((:rewrite)))
 (defthm int20-list-p-of-map-double-int20
   (implies (int20-list-p l)
            (int20-list-p (map-double-int20 l)))
   :rule-classes ((:rewrite)))
 (defun int20* (x) (declare (xargs :guard t)) (or (null x) (int20 x)))
 (defun int10*-->-int20* (x) (declare (xargs :guard (int10* x))) (if (null x) nil (int10-to-int20 x)))
 (defun int20*-->-int10* (x) (declare (xargs :guard (int20* x))) (if (null x) nil (int20-to-int10 x)))
 (defiso int10*-iso-int20* int10*
   int20* int10*-->-int20* int20*-->-int10*
   :thm-enable :all-nonguard
   :hints (:beta-of-alpha (("Goal" :in-theory (enable int10* int20*
                                                      int10*-->-int20* int20*-->-int10*)))
                          :alpha-of-beta (("Goal" :in-theory (enable int10* int20*
                                                                     int10*-->-int20* int20*-->-int10*)))
                          :alpha-image (("Goal" :in-theory (enable int10* int20* int10*-->-int20*)))
                          :beta-image (("Goal" :in-theory (enable int10* int20* int20*-->-int10*)))))
 (defthm booleanp-of-int20* (let ((b (int20* x))) (booleanp b)) :rule-classes ((:rewrite)))
 (defun pair-int20-bool-p (pr) (declare (xargs :guard t)) (and (consp pr) (int20 (car pr)) (booleanp (cdr pr))))
 (defun pair-int10-bool-p-->-pair-int20-bool-p
     (pr)
   (declare (xargs :guard (pair-int10-bool-p pr)))
   (cons (int10-to-int20 (car pr))
         (cdr pr)))
 (defun pair-int20-bool-p-->-pair-int10-bool-p
     (pr)
   (declare (xargs :guard (pair-int20-bool-p pr)))
   (cons (int20-to-int10 (car pr))
         (cdr pr)))
 (defiso pair-int10-bool-p-iso-pair-int20-bool-p
   pair-int10-bool-p pair-int20-bool-p
   pair-int10-bool-p-->-pair-int20-bool-p
   pair-int20-bool-p-->-pair-int10-bool-p
   :thm-enable :all-nonguard
   :hints (:beta-of-alpha (("Goal" :in-theory (enable pair-int10-bool-p pair-int20-bool-p
                                                      pair-int10-bool-p-->-pair-int20-bool-p
                                                      pair-int20-bool-p-->-pair-int10-bool-p)))
                          :alpha-of-beta (("Goal" :in-theory (enable pair-int10-bool-p pair-int20-bool-p
                                                                     pair-int10-bool-p-->-pair-int20-bool-p
                                                                     pair-int20-bool-p-->-pair-int10-bool-p)))
                          :alpha-image (("Goal" :in-theory (enable pair-int10-bool-p pair-int20-bool-p
                                                                   pair-int10-bool-p-->-pair-int20-bool-p)))
                          :beta-image (("Goal" :in-theory (enable pair-int10-bool-p pair-int20-bool-p
                                                                  pair-int20-bool-p-->-pair-int10-bool-p)))))
 (defthm pair-int10-bool-p-->-pair-int20-bool-p-consp
   (implies (and (pair-int10-bool-p pr))
            (consp (pair-int10-bool-p-->-pair-int20-bool-p pr))))
 (defthm pair-int10-bool-p-->-pair-int20-bool-p-int20--consp
   (implies (and (pair-int10-bool-p pr))
            (consp (pair-int10-bool-p-->-pair-int20-bool-p pr))))
 (defthm pair-int10-bool-p-->-pair-int20-bool-p-int20-car
   (implies (and (pair-int10-bool-p pr))
            (int20 (car (pair-int10-bool-p-->-pair-int20-bool-p pr)))))
 (defthm pair-int10-bool-p-->-pair-int20-bool-p-booleanp-cdr
   (implies (and (pair-int10-bool-p pr))
            (booleanp (cdr (pair-int10-bool-p-->-pair-int20-bool-p pr)))))
 (defthm pair-int20-bool-p-->-pair-int10-bool-p-consp
   (implies (and (pair-int20-bool-p pr))
            (consp (pair-int20-bool-p-->-pair-int10-bool-p pr))))
 (defthm pair-int20-bool-p-->-pair-int10-bool-p-int10--consp
   (implies (and (pair-int20-bool-p pr))
            (consp (pair-int20-bool-p-->-pair-int10-bool-p pr))))
 (defthm pair-int20-bool-p-->-pair-int10-bool-p-int10-car
   (implies (and (pair-int20-bool-p pr))
            (int10 (car (pair-int20-bool-p-->-pair-int10-bool-p pr)))))
 (defthm pair-int20-bool-p-->-pair-int10-bool-p-booleanp-cdr
   (implies (and (pair-int20-bool-p pr))
            (booleanp (cdr (pair-int20-bool-p-->-pair-int10-bool-p pr)))))
 (defthm booleanp-of-pair-int20-bool-p (let ((v (pair-int20-bool-p pr))) (booleanp v)) :rule-classes ((:rewrite)))
 (defun pair-int20-bool->val (pr) (declare (xargs :guard (pair-int20-bool-p pr))) (car pr))
 (defthmd pair-int20-bool->val-is-iso-pair-int10-bool->val
   (implies (force (pair-int20-bool-p pr))
            (equal (pair-int20-bool->val pr)
                   (int10-to-int20 (pair-int10-bool->val (pair-int20-bool-p-->-pair-int10-bool-p pr))))))
 (defthm pair-int10-bool->val-is-iso-pair-int20-bool->val
   (implies (force (pair-int10-bool-p pr))
            (equal (pair-int10-bool->val pr)
                   (int20-to-int10 (pair-int20-bool->val (pair-int10-bool-p-->-pair-int20-bool-p pr))))))
 (defthm int20-of-pair-int20-bool->val
   (implies (pair-int20-bool-p pr)
            (let ((v (pair-int20-bool->val pr)))
              (int20 v)))
   :rule-classes ((:rewrite)))
 (defun pair-int20-bool->flag (pr) (declare (xargs :guard (pair-int20-bool-p pr))) (cdr pr))
 (defthmd pair-int20-bool->flag-is-iso-pair-int10-bool->flag
   (implies (force (pair-int20-bool-p pr))
            (equal (pair-int20-bool->flag pr)
                   (pair-int10-bool->flag (pair-int20-bool-p-->-pair-int10-bool-p pr)))))
 (defthm pair-int10-bool->flag-is-iso-pair-int20-bool->flag
   (implies (force (pair-int10-bool-p pr))
            (equal (pair-int10-bool->flag pr)
                   (pair-int20-bool->flag (pair-int10-bool-p-->-pair-int20-bool-p pr)))))
 (defthm booleanp-of-pair-int20-bool->flag
   (implies (pair-int20-bool-p pr)
            (let ((v (pair-int20-bool->flag pr)))
              (booleanp v)))
   :rule-classes ((:rewrite)))
 (defun pair-int20-bool-listp (l)
   (declare (xargs :measure (acl2-count l)
                   :guard t))
   (if (atom l)
       (null l)
     (and (pair-int20-bool-p (first l))
          (pair-int20-bool-listp (rest l)))))
 (defun pair-int10-bool-listp-->-pair-int20-bool-listp
     (l)
   (declare (xargs :guard (pair-int10-bool-listp l)))
   (if (atom l)
       nil
     (cons (pair-int10-bool-p-->-pair-int20-bool-p (first l))
           (pair-int10-bool-listp-->-pair-int20-bool-listp (rest l)))))
 (defun pair-int20-bool-listp-->-pair-int10-bool-listp
     (l)
   (declare (xargs :guard (pair-int20-bool-listp l)))
   (if (atom l)
       nil
     (cons (pair-int20-bool-p-->-pair-int10-bool-p (first l))
           (pair-int20-bool-listp-->-pair-int10-bool-listp (rest l)))))
 (defiso
   pair-int10-bool-listp-iso-pair-int20-bool-listp
   pair-int10-bool-listp
   pair-int20-bool-listp
   pair-int10-bool-listp-->-pair-int20-bool-listp
   pair-int20-bool-listp-->-pair-int10-bool-listp
   :thm-enable :all-nonguard
   :hints (:beta-of-alpha (("Goal" :in-theory (enable pair-int10-bool-listp
                                                      pair-int20-bool-listp
                                                      pair-int10-bool-listp-->-pair-int20-bool-listp
                                                      pair-int20-bool-listp-->-pair-int10-bool-listp)))
                          :alpha-of-beta (("Goal" :in-theory (enable pair-int10-bool-listp
                                                                     pair-int20-bool-listp
                                                                     pair-int10-bool-listp-->-pair-int20-bool-listp
                                                                     pair-int20-bool-listp-->-pair-int10-bool-listp)))
                          :alpha-image (("Goal" :in-theory (enable pair-int10-bool-listp
                                                                   pair-int20-bool-listp
                                                                   pair-int10-bool-listp-->-pair-int20-bool-listp)))
                          :beta-image (("Goal" :in-theory (enable pair-int10-bool-listp
                                                                  pair-int20-bool-listp
                                                                  pair-int20-bool-listp-->-pair-int10-bool-listp)))))
 (defthm pair-int10-bool-listp-->-pair-int20-bool-listp-null
   (implies (and (pair-int10-bool-listp l) (atom l))
            (null (pair-int10-bool-listp-->-pair-int20-bool-listp l))))
 (defthm pair-int10-bool-listp-->-pair-int20-bool-listp-pair-int20-bool-p--consp
   (implies (and (pair-int10-bool-listp l)
                 (not (atom l)))
            (consp (pair-int10-bool-listp-->-pair-int20-bool-listp l))))
 (defthm pair-int10-bool-listp-->-pair-int20-bool-listp-pair-int20-bool-p-first
   (implies (and (pair-int10-bool-listp l)
                 (not (atom l)))
            (pair-int20-bool-p (first (pair-int10-bool-listp-->-pair-int20-bool-listp l)))))
 (defthm pair-int10-bool-listp-->-pair-int20-bool-listp-pair-int20-bool-listp-rest
   (implies (and (pair-int10-bool-listp l)
                 (not (atom l)))
            (pair-int20-bool-listp (rest (pair-int10-bool-listp-->-pair-int20-bool-listp l)))))
 (defthm pair-int20-bool-listp-->-pair-int10-bool-listp-null
   (implies (and (pair-int20-bool-listp l) (atom l))
            (null (pair-int20-bool-listp-->-pair-int10-bool-listp l))))
 (defthm pair-int20-bool-listp-->-pair-int10-bool-listp-pair-int10-bool-p--consp
   (implies (and (pair-int20-bool-listp l)
                 (not (atom l)))
            (consp (pair-int20-bool-listp-->-pair-int10-bool-listp l))))
 (defthm pair-int20-bool-listp-->-pair-int10-bool-listp-pair-int10-bool-p-first
   (implies (and (pair-int20-bool-listp l)
                 (not (atom l)))
            (pair-int10-bool-p (first (pair-int20-bool-listp-->-pair-int10-bool-listp l)))))
 (defthm pair-int20-bool-listp-->-pair-int10-bool-listp-pair-int10-bool-listp-rest
   (implies (and (pair-int20-bool-listp l)
                 (not (atom l)))
            (pair-int10-bool-listp (rest (pair-int20-bool-listp-->-pair-int10-bool-listp l)))))
 (defthm pair-int20-bool-listp-of-cons
   (equal (pair-int20-bool-listp (cons l0 l))
          (and (pair-int20-bool-p l0)
               (pair-int20-bool-listp l)))
   :rule-classes ((:rewrite)))
 (defthm use-pair-int20-bool-listp-for-car
   (implies (and (pair-int20-bool-listp l)
                 (consp (double-rewrite l)))
            (pair-int20-bool-p (car l)))
   :rule-classes ((:rewrite)))
 (defthm use-pair-int20-bool-listp-for-car-of-last
   (implies (and (pair-int20-bool-listp l)
                 (consp (double-rewrite l)))
            (pair-int20-bool-p (car (last l))))
   :rule-classes ((:rewrite)))
 (defthm pair-int20-bool-listp-of-append
   (equal (pair-int20-bool-listp (append l l0))
          (and (pair-int20-bool-listp (true-list-fix l))
               (pair-int20-bool-listp l0)))
   :rule-classes ((:rewrite)))
 (defthm pair-int20-bool-listp-of-union-equal
   (equal (pair-int20-bool-listp (union-equal l l0))
          (and (pair-int20-bool-listp (true-list-fix l))
               (pair-int20-bool-listp l0)))
   :rule-classes ((:rewrite)))
 (defthm pair-int20-bool-listp-when-not-consp
   (implies (not (consp (double-rewrite l)))
            (equal (pair-int20-bool-listp l)
                   (equal nil l)))
   :rule-classes ((:rewrite)))
 (defthm pair-int20-bool-listp-when-not-consp-cheap
   (implies (not (consp (double-rewrite l)))
            (equal (pair-int20-bool-listp l)
                   (equal nil l)))
   :rule-classes ((:rewrite :backchain-limit-lst (0))))
 (defthm pair-int20-bool-listp-of-revappend
   (implies (and (pair-int20-bool-listp l)
                 (pair-int20-bool-listp l0))
            (pair-int20-bool-listp (revappend l l0)))
   :rule-classes ((:rewrite)))
 (defthm pair-int20-bool-listp-of-cdr
   (implies (pair-int20-bool-listp l)
            (equal (pair-int20-bool-listp (cdr l))
                   t))
   :rule-classes ((:rewrite)))
 (defthm pair-int20-bool-listp-of-nthcdr
   (implies (pair-int20-bool-listp l)
            (equal (pair-int20-bool-listp (nthcdr l0 l))
                   t))
   :rule-classes ((:rewrite)))
 (defthm pair-int20-bool-listp-of-firstn
   (implies (pair-int20-bool-listp l)
            (equal (pair-int20-bool-listp (firstn l0 l))
                   t))
   :rule-classes ((:rewrite)))
 (defthm pair-int20-bool-listp-of-remove1-equal
   (implies (pair-int20-bool-listp l)
            (pair-int20-bool-listp (remove1-equal l0 l)))
   :rule-classes ((:rewrite)))
 (defthm pair-int20-bool-listp-of-remove-equal
   (implies (pair-int20-bool-listp l)
            (pair-int20-bool-listp (remove-equal l0 l)))
   :rule-classes ((:rewrite)))
 (defthm pair-int20-bool-listp-of-last
   (implies (pair-int20-bool-listp l)
            (pair-int20-bool-listp (last l)))
   :rule-classes ((:rewrite)))
 (defthm pair-int20-bool-listp-of-take
   (implies (and (pair-int20-bool-listp l)
                 (<= l0 (len (double-rewrite l))))
            (equal (pair-int20-bool-listp (take l0 l))
                   t))
   :rule-classes ((:rewrite)))
 (defthmd true-listp-when-pair-int20-bool-listp
   (implies (pair-int20-bool-listp l)
            (true-listp l))
   :rule-classes ((:rewrite)))
 (defthm true-listp-when-pair-int20-bool-listp-forward
   (implies (pair-int20-bool-listp l)
            (true-listp l))
   :rule-classes ((:forward-chaining :trigger-terms ((pair-int20-bool-listp l)))))
 (defthmd pair-int20-bool-listp-when-perm
   (implies (perm l l0)
            (equal (pair-int20-bool-listp l)
                   (and (true-listp l)
                        (pair-int20-bool-listp (true-list-fix l0)))))
   :rule-classes ((:rewrite)))
 (defthm pair-int20-bool-listp-of-true-list-fix
   (implies (pair-int20-bool-listp l)
            (pair-int20-bool-listp (true-list-fix l)))
   :rule-classes ((:rewrite)))
 (defthm use-pair-int20-bool-listp
   (implies (and (pair-int20-bool-listp free-l)
                 (memberp x free-l))
            (pair-int20-bool-p x))
   :rule-classes ((:rewrite)))
 (defthm use-pair-int20-bool-listp-2
   (implies (and (memberp x free-l)
                 (pair-int20-bool-listp free-l))
            (pair-int20-bool-p x))
   :rule-classes ((:rewrite)))
 (defthm pair-int20-bool-listp-of-add-to-set-equal
   (equal (pair-int20-bool-listp (add-to-set-equal l0 l))
          (and (pair-int20-bool-p l0)
               (pair-int20-bool-listp l)))
   :rule-classes ((:rewrite)))
 (defun filter-double$1 (l)
   (declare (xargs :measure (acl2-count l)
                   :guard (pair-int20-bool-listp l)))
   (if (atom l)
       nil
     (let ((rl (filter-double$1 (cdr l)))
           (pr (car l)))
       (if (pair-int20-bool->flag pr)
           (cons (pair-int20-bool->val pr) rl)
         rl))))
 (defthmd
   filter-double$1-is-iso-filter-double
   (implies (force (pair-int20-bool-listp l))
            (equal (filter-double$1 l)
                   (int10-list-p-->-int20-list-p (filter-double (pair-int20-bool-listp-->-pair-int10-bool-listp l))))))
 (defthm
   filter-double-is-iso-filter-double$1
   (implies (force (pair-int10-bool-listp l))
            (equal (filter-double l)
                   (int20-list-p-->-int10-list-p (filter-double$1 (pair-int10-bool-listp-->-pair-int20-bool-listp l))))))
 (defthm int20-list-p-of-filter-double
   (implies (pair-int20-bool-listp l)
            (let ((l (filter-double$1 l)))
              (int20-list-p l)))
   :rule-classes ((:rewrite)))
 (defun int20-map-p (m)
   (declare (xargs :measure (acl2-count m)
                   :guard t))
   (if (atom m)
       (null m)
     (and (consp (car m))
          (int20 (caar m))
          (int20 (cdar m))
          (int20-map-p (cdr m)))))
 (defun int10-map-p-->-int20-map-p (m)
   (declare (xargs :guard (int10-map-p m)))
   (if (atom m)
       nil
     (cons (cons (int10-to-int20 (caar m))
                 (int10-to-int20 (cdar m)))
           (int10-map-p-->-int20-map-p (cdr m)))))
 (defun int20-map-p-->-int10-map-p (m)
   (declare (xargs :guard (int20-map-p m)))
   (if (atom m)
       nil
     (cons (cons (int20-to-int10 (caar m))
                 (int20-to-int10 (cdar m)))
           (int20-map-p-->-int10-map-p (cdr m)))))
 (defiso int10-map-p-iso-int20-map-p int10-map-p
   int20-map-p int10-map-p-->-int20-map-p
   int20-map-p-->-int10-map-p
   :thm-enable :all-nonguard
   :hints (:beta-of-alpha (("Goal" :in-theory (enable int10-map-p
                                                      int20-map-p int10-map-p-->-int20-map-p
                                                      int20-map-p-->-int10-map-p)))
                          :alpha-of-beta (("Goal" :in-theory (enable int10-map-p
                                                                     int20-map-p int10-map-p-->-int20-map-p
                                                                     int20-map-p-->-int10-map-p)))
                          :alpha-image (("Goal" :in-theory (enable int10-map-p int20-map-p
                                                                   int10-map-p-->-int20-map-p)))
                          :beta-image (("Goal" :in-theory (enable int10-map-p int20-map-p
                                                                  int20-map-p-->-int10-map-p)))))
 (defthm int10-map-p-->-int20-map-p-null (implies (and (int10-map-p m) (atom m)) (null (int10-map-p-->-int20-map-p m))))
 (defthm int10-map-p-->-int20-map-p-consp--consp
   (implies (and (int10-map-p m) (not (atom m)))
            (consp (int10-map-p-->-int20-map-p m))))
 (defthm int10-map-p-->-int20-map-p-consp-car
   (implies (and (int10-map-p m) (not (atom m)))
            (consp (car (int10-map-p-->-int20-map-p m)))))
 (defthm int10-map-p-->-int20-map-p-int20-caar
   (implies (and (int10-map-p m) (not (atom m)))
            (int20 (caar (int10-map-p-->-int20-map-p m)))))
 (defthm int10-map-p-->-int20-map-p-int20-cdar
   (implies (and (int10-map-p m) (not (atom m)))
            (int20 (cdar (int10-map-p-->-int20-map-p m)))))
 (defthm int10-map-p-->-int20-map-p-int20-map-p-cdr
   (implies (and (int10-map-p m) (not (atom m)))
            (int20-map-p (cdr (int10-map-p-->-int20-map-p m)))))
 (defthm int20-map-p-->-int10-map-p-null (implies (and (int20-map-p m) (atom m)) (null (int20-map-p-->-int10-map-p m))))
 (defthm int20-map-p-->-int10-map-p-consp--consp
   (implies (and (int20-map-p m) (not (atom m)))
            (consp (int20-map-p-->-int10-map-p m))))
 (defthm int20-map-p-->-int10-map-p-consp-car
   (implies (and (int20-map-p m) (not (atom m)))
            (consp (car (int20-map-p-->-int10-map-p m)))))
 (defthm int20-map-p-->-int10-map-p-int10-caar
   (implies (and (int20-map-p m) (not (atom m)))
            (int10 (caar (int20-map-p-->-int10-map-p m)))))
 (defthm int20-map-p-->-int10-map-p-int10-cdar
   (implies (and (int20-map-p m) (not (atom m)))
            (int10 (cdar (int20-map-p-->-int10-map-p m)))))
 (defthm int20-map-p-->-int10-map-p-int10-map-p-cdr
   (implies (and (int20-map-p m) (not (atom m)))
            (int10-map-p (cdr (int20-map-p-->-int10-map-p m)))))
 (defthm booleanp-of-int20-map-p (let ((b (int20-map-p m))) (booleanp b)) :rule-classes ((:rewrite)))
 (defthm int20-map-p-nil (int20-map-p nil) :rule-classes ((:rewrite)))
 (defthm int20-map-p-cdr (implies (int20-map-p m) (int20-map-p (cdr m))) :rule-classes ((:rewrite)))
 (defthm int20-map-p-car (implies (and (consp m) (int20-map-p m)) (consp (car m))) :rule-classes ((:rewrite)))
 (defthm int20-map-p-caar (implies (and (int20-map-p m) (consp m)) (int20 (car (car m)))) :rule-classes ((:rewrite)))
 (defthm int20-map-p-cdar (implies (and (int20-map-p m) (consp m)) (int20 (cdr (car m)))) :rule-classes ((:rewrite)))
 (defthm int20-map-p-cons
   (equal (int20-map-p (cons x y))
          (and (consp x)
               (int20 (car x))
               (int20 (cdr x))
               (int20-map-p y)))
   :rule-classes ((:rewrite)))
 (defun lookup-int20-map (x m)
   (declare (xargs :measure (acl2-count m)
                   :guard (and (int20 x) (int20-map-p m))))
   (if (atom m)
       nil
     (if (and (consp (car m)) (equal (caar m) x))
         (cdar m)
       (lookup-int20-map x (cdr m)))))
 (defthmd lookup-int20-map-is-iso-lookup-int10-map
   (implies (and (force (int20 x))
                 (force (int20-map-p m)))
            (equal (lookup-int20-map x m)
                   (int10*-->-int20* (lookup-int10-map (int20-to-int10 x)
                                                       (int20-map-p-->-int10-map-p m))))))
 (defthm lookup-int10-map-is-iso-lookup-int20-map
   (implies (and (force (int10 x))
                 (force (int10-map-p m)))
            (equal (lookup-int10-map x m)
                   (int20*-->-int10* (lookup-int20-map (int10-to-int20 x)
                                                       (int10-map-p-->-int20-map-p m))))))
 (defthm int20*-of-lookup-int20-map
   (implies (int20-map-p m)
            (let ((val (lookup-int20-map x m)))
              (int20* val)))
   :rule-classes ((:rewrite)))
 (defun int20-map2-p (m)
   (declare (xargs :measure (acl2-count m)
                   :guard t))
   (if (atom m)
       (null m)
     (if (consp (car m))
         (if (int20 (caar m))
             (if (int20 (cdar m))
                 (if (int20-map2-p (cdr m)) t nil)
               nil)
           nil)
       nil)))
 (defiso int10-map2-p-iso-int20-map2-p
   int10-map2-p
   int20-map2-p int10-map-p-->-int20-map-p
   int20-map-p-->-int10-map-p
   :thm-enable :all-nonguard
   :hints (:beta-of-alpha (("Goal" :in-theory (enable int10-map2-p
                                                      int20-map2-p int10-map-p-->-int20-map-p
                                                      int20-map-p-->-int10-map-p)))
                          :alpha-of-beta (("Goal" :in-theory (enable int10-map2-p
                                                                     int20-map2-p int10-map-p-->-int20-map-p
                                                                     int20-map-p-->-int10-map-p)))
                          :alpha-image (("Goal" :in-theory (enable int10-map2-p int20-map2-p
                                                                   int10-map-p-->-int20-map-p)))
                          :beta-image (("Goal" :in-theory (enable int10-map2-p int20-map2-p
                                                                  int20-map-p-->-int10-map-p)))
                          :alpha-guard (("Goal" :in-theory (enable int10-map2-p int20-map2-p)))
                          :beta-guard (("Goal" :in-theory (enable int10-map2-p int20-map2-p)))))
 (defthm int10-map2-p-int10-map-p-->-int20-map-p-null
   (implies (and (int10-map2-p m) (atom m))
            (null (int10-map-p-->-int20-map-p m))))
 (defthm int20-map2-p-int20-map-p-->-int10-map-p-null
   (implies (and (int20-map2-p m) (atom m))
            (null (int20-map-p-->-int10-map-p m))))
 (defthm booleanp-of-int20-map2-p (let ((b (int20-map2-p m))) (booleanp b)) :rule-classes ((:rewrite)))
 (defthm int20-map2-p-nil (int20-map2-p nil) :rule-classes ((:rewrite)))
 (defthm int20-map2-p-cdr (implies (int20-map2-p m) (int20-map2-p (cdr m))) :rule-classes ((:rewrite)))
 (defthm int20-map2-p-car (implies (and (consp m) (int20-map2-p m)) (consp (car m))) :rule-classes ((:rewrite)))
 (defthm int20-map2-p-caar (implies (and (int20-map2-p m) (consp m)) (int20 (car (car m)))) :rule-classes ((:rewrite)))
 (defthm int20-map2-p-cdar (implies (and (int20-map2-p m) (consp m)) (int20 (cdr (car m)))) :rule-classes ((:rewrite)))
 (defthm int20-map2-p-cons
   (equal (int20-map2-p (cons x y))
          (and (consp x)
               (int20 (car x))
               (int20 (cdr x))
               (int20-map2-p y)))
   :rule-classes ((:rewrite))))
