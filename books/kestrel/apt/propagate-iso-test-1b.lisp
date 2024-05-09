; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(in-package "ACL2")

(include-book "kestrel/apt/propagate-iso" :dir :system)
(include-book "kestrel/apt/isodata" :dir :system)
;(include-book "kestrel/utilities/testing" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(include-book "std/util/defaggregate" :dir :system)


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


(std::defaggregate test-int10-pair
  ((name "Symbol" symbolp)
   (int10-val "Must be int10" int10))
  :layout :list)
(in-theory (enable test-int10-pair))

;; (defthm test-int10-pair-p-implies-int10-cdadr
;;   (implies (test-int10-pair-p x)
;;            (int10 (cdr (cadr x))))
;;   :hints (("Goal" :in-theory (enable test-int10-pair-p))))

(define inc-int10-val ((pr test-int10-pair-p))
  (change-test-int10-pair pr :int10-val (add-int10 1 (test-int10-pair->int10-val pr))))



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
    int10-list-p int20-list-p
    int10-list-p-to-int20-list-p int20-list-p-to-int10-list-p
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
  :last-event return-type-of-test-int10-pair->int10-val ;inc-int10-val
  :hints-map ((test-int10-pair-is-iso-test-int20-pair (enable test-int10-pair))
              (honsed-test-int10-pair-is-iso-honsed-test-int20-pair (("Goal")))
              (test-int20-pair->int20-val$inline-is-iso-test-int10-pair->int10-val$inline
                (("Goal" :in-theory (enable int10-to-int20 test-int10-pair->int10-val$inline int20-to-int10 test-int20-pair-p))))))



#|
(define test-int10-pair-->test-int10-pair ((pr test-int10-pair-p))
  :returns (new-pr test-int20-pair-p)
  (list (cons 'name (cdr (car x))) (list 'int10-val (cdr (cadr x))))
)
(cons ? ?)
(cons (cons ? ?) ?)
(cons (cons 'name ?) ?)
(cons (cons ? ?) (cons ? ?))
(cons ? (cons 'int10-val ?))
(cons ? (cons ? nil))
(cons (cons ? (cdr (car x))) ?)
(cons ? (cons (int10->int20 (cdr (cadr x))) ?))
|#
