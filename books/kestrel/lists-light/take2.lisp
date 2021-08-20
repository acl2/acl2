; More rules about take
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
;; (local (include-book "kestrel/lists-light/nth" :dir :system))
;; (local (include-book "kestrel/lists-light/len" :dir :system))
;; (local (include-book "kestrel/lists-light/cdr" :dir :system))

;; Not in the take book because this mentions repeat.
(defthm take-of-nil
  (equal (take n nil)
         (repeat n nil))
  :hints (("Goal" :in-theory (enable take))))

;; Not in the take book because this mentions repeat.
(defthm take-when-not-consp
  (implies (not (consp x))
           (equal (take n x)
                  (repeat n nil)))
  :hints (("Goal" :in-theory (enable take))))

;; Not in the take book because this mentions repeat.
;nested inductions
(defthm take-of-take
  (implies (and; (natp n)
            (integerp n)
                (natp m))
           (equal (take n (take m lst))
                  (if (< m n)
                      (append (take m lst)
                              (repeat (- n m) nil))
                    (take n lst))))
  :hints (("Goal" :in-theory (e/d (take) (TAKE-OF-TAKE-WHEN-<=)))))

;move
(defthmd take-plus-one-equal-rewrite
  (IMPLIES (AND (EQUAL (NTH N LST1) (NTH N LST2))
;                (< 0 N)
                (INTEGERP N)
                (< n (len lst1))
                (< n (len lst2))
                )
           (equal (EQUAL (take (+ 1 N) LST1)
                         (take (+ 1 N) LST2))
                  (EQUAL (take N LST1)
                         (take N LST2))))
  :hints (("Goal" :in-theory (e/d (take nth) ())
           :induct t
           :do-not '(generalize eliminate-destructors))))

;bozo might loop?
(defthmd take-equal-lenghten
  (implies (and (EQUAL (NTH n lst1)
                       (NTH n lst2))
                (< n (len lst1)) ;drop?
                (< n (len lst2)) ;drop?
                (<= 0 n)
                (integerp n)
                )
           (equal (EQUAL (TAKE n lst1)
                         (TAKE n lst2))
                  (EQUAL (TAKE (+ 1 n) lst1)
                         (TAKE (+ 1 n) lst2))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (take nth) ()))))

;move
(defthm take-of-update-nth-irrel
  (implies (and; (< m (len lst)) ;drop?
                (<= n m)
                (integerp n)
                (integerp m))
           (EQUAL (take N (UPDATE-NTH m VAL LST))
                  (take N LST)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable take update-nth))))

;; (DEFTHM TAKE-1-REWRITE-better
;;   (EQUAL (TAKE 1 X)
;;          (if (consp x)
;;              (LIST (CAR X))
;;            nil))
;;   :HINTS (("Goal" :IN-THEORY (ENABLE TAKE))))

(defthm cons-of-car-and-cdr-of-take
  (equal (cons (car lst) (cdr (take n lst)))
         (if (zp n)
             (list (car lst))
           (take n lst)))
  :hints (("Goal" :in-theory (enable take))))

;rename
(defthm cdr-take-nthcdr
  (implies (and (natp n)
                (< 0 n)
                (natp m))
           (equal (cdr (take n (nthcdr m x)))
                  (take (+ -1 n) (nthcdr (+ 1 m) x))))
  :hints (("Goal" :in-theory (enable ))))

;drop rewrite part?
(defthm consp-of-take-tp
  (implies (and (integerp n)
                (< 0 n))
           (consp (take n lst)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable take))))

(local
 (defun double-sub1-induct (n m)
   (if (zp m)
       (list n m)
     (double-sub1-induct (+ -1 n) (+ -1 m)))))

;todo: combine with the one from std
(defthm take-of-repeat-2
  (implies (and (<= n1 n2)
                (natp n1)
                (natp n2))
           (equal (take n1 (repeat n2 x))
                  (repeat n1 x)))
  :hints (("Goal" :induct (double-sub1-induct n1 n2)
           :in-theory (enable take))))

;move
(defthm take-cons-2
  (implies (not (zp n))
           (equal (take n (cons a b))
                  (cons a (take (1- n) b)))))

(defthm take-when-equal-of-takes
  (implies (and (equal (take n x) (take n free))
                (syntaxp (smaller-termp free x))
                (<= m n)
                (natp m)
                (natp n))
           (equal (take m x)
                  (take m free)))
  :hints (("Goal" :in-theory (enable take))))
