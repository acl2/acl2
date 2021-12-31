; Small test of propagate-iso. Isomorphism between (integer-range-p 0 10 x) and (integer-range-p 10 20 x)
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
(include-book "kestrel/apt/isodata" :dir :system)
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

(defforall int20-list-p (l) (int20 l) :true-listp t :guard t)

(defmap int10-list-p-to-int20-list-p (l) (int10-to-int20 l)
  :declares ((xargs :guard (int10-list-p l))))
(defmap int20-list-p-to-int10-list-p (l) (int20-to-int10 l)
  :declares ((xargs :guard (int20-list-p l))))

(defiso int10-list-p-iso-int20-list-p
  int10-list-p int20-list-p int10-list-p-to-int20-list-p int20-list-p-to-int10-list-p
  :thm-enable :all-nonguard
  :hints (:beta-of-alpha (("Goal" :in-theory (enable int10-list-p int20-list-p)))
          :alpha-of-beta (("Goal" :in-theory (enable int10-list-p int20-list-p)))
          :alpha-image (("Goal" :in-theory (enable int10-list-p int20-list-p)))
          :beta-image (("Goal" :in-theory (enable int10-list-p int20-list-p)))))

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

(apt::propagate-iso (int10-iso-int20 int10-list-p-iso-int20-list-p)
  ((add-int10 add-int20 add-int10-->add-int20 add-int20-->add-int10
              (int10 int10) => int10))
  :first-event add-int10-comm
  :last-event int10-list-p-of-map-double-int10)


;; Too specific?: will fail inconsequential changes.
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
                   (int10-list-p-to-int20-list-p (map-double-int10 (int20-list-p-to-int10-list-p l))))))
 (defthm map-double-int10-is-iso-map-double-int20
   (implies (force (int10-list-p l))
            (equal (map-double-int10 l)
                   (int20-list-p-to-int10-list-p (map-double-int20 (int10-list-p-to-int20-list-p l))))))
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
   :rule-classes ((:rewrite))))
