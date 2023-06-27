; Tests for lift-iso
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(in-package "ACL2")


(include-book "lift-iso")
(include-book "../sequences/defforall")

(include-book "arithmetic-5/top" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

;; Define a simple isomorphism so it can be lifted
(define int10 (x)
  :returns (b booleanp)
  :no-function t
  (integer-range-p 0 10 x)
  ///
  (defthm int10-natp
    (implies (int10 x)
             (natp x))))

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


(defforall int10-list-p (l) (int10 l) :true-listp t :guard t)
(apt::lift-iso int10-list-p int10-iso-int20)

;; (include-book "propagate-iso")
;; (apt::propagate-iso int10-iso-int20 ()
;;   :first-event int10-list-p
;;   :last-event int10-list-p-of-add-to-set-equal)

(define all-int10 (x)
  :returns (b booleanp)
  (or (null x)
      (and (consp x)
           (int10 (car x))
           (all-int10 (cdr x)))))
(apt::lift-iso all-int10 int10-iso-int20)
;; (apt::propagate-iso int10-iso-int20 ()
;;   :first-event all-int10
;;   :last-event all-int10)


(define all-int10a (x)
  :returns (b booleanp)
  (cond ((null x) t)
        ((and (consp x)
              (int10 (car x))
              (all-int10a (cdr x)))
         t)))
(apt::lift-iso all-int10a int10-iso-int20)

(define all-int10b (x)
  :returns (b booleanp)
  (cond ((null x) t)
        ((atom x) nil)
        ((not (int10 (car x))) nil) 
        ((all-int10b (cdr x))
         t)))
(apt::lift-iso all-int10b int10-iso-int20)

