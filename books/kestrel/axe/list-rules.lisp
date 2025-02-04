; Mixed rules about lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: These should be moved to lists-light

(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "kestrel/lists-light/finalcdr" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/lists-light/subrange" :dir :system)
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

(defun sub1-cdr-cdr-induct (n x y)
  (if (zp n)
      (list n x y)
    (sub1-cdr-cdr-induct (+ -1 n) (cdr x) (cdr y))))

;; todo: rephrase using take?
;; ;could also phrase this using clear-nth
(defthmd equal-of-update-nth
  (implies (and (natp n)
                (< n (len x)) ;todo
;                (true-listp y)
 ;               (true-listp x)
                )
           (equal (equal y (update-nth n val x))
                  (and (<= (+ 1 n) (len y))
                       (equal (nth n y) val)
                       (equal (firstn n y) ;todo: use take
                              (firstn n x))
                       (equal (nthcdr (+ 1 n) x)
                              (nthcdr (+ 1 n) y)))))
  :hints (("Goal" :induct (sub1-cdr-cdr-induct n x y)
           :in-theory (enable update-nth))))

(defthmd take-differs-hack
  (implies (and (not (equal (take n lst1) ;binds n
                            (take n lst2)))
                (not (equal (take n x)
                            (take n y))))
           (not (equal x y))))

(defthmd nthcdr-differs-hack
  (implies (and (not (equal (nthcdr n lst1) ;binds n
                            (nthcdr n lst2)))
                (not (equal (nthcdr n x)
                            (nthcdr n y))))
           (not (equal x y))))

(defthmd nth-differs-hack
  (implies (and (not (equal (nth n lst1) ;binds n
                            (nth n lst2)))
                (not (equal (nth n x)
                            (nth n y))))
           (not (equal x y))))

(defthmd nth-differs-hack2
  (implies (not (equal (nth n x)
                       (nth n y)))
           (not (equal x y))))

;problems happen when n is a huge constant...
(defthm take-plus-1-hack
  (implies (and (syntaxp (not (quotep n))) ;BOZO
                (equal (take n x)
                       (take n y))
                (equal (len x) (len y))
                (natp n))
           (equal (equal (take (+ 1 n) x)
                         (take (+ 1 n) y))
                  (equal (nth n x)
                         (nth n y))))
  :hints (("Goal" :in-theory (enable take))))

(defthm nthcdrs-differ-when-nths-differ
  (implies (and (NOT (EQUAL (NTH m lst1) (NTH m lst2))) ;binds m
                (<= n m)
                (natp n)
                (natp m)
                )
           (NOT (EQUAL (NTHCDR n lst1) (NTHCDR n lst2))))
  :hints (("Goal" :use (:instance nth-differs-hack2 (n (- m n)) (x (NTHCDR n lst1)) (y (NTHCDR n lst2))))))

(defthmd nthcdr-when-its-just-the-last-elem
  (implies (and (equal n (+ -1 (len x)))
                (natp n))
           (equal (nthcdr n x)
                  (cons (nth n x) (finalcdr x)))))

(DEFTHM UPDATE-NTH-WITH-LAST-VAL-gen
  (IMPLIES (AND; (SYNTAXP (AND (QUOTEP N)))
                (EQUAL (+ N 1) (LEN LST))
                (TRUE-LISTP LST)
                (NATP N))
           (EQUAL (UPDATE-NTH N VAL LST)
                  (APPEND (TAKE N LST) (LIST VAL))))
  :RULE-CLASSES ((:REWRITE :BACKCHAIN-LIMIT-LST (1 NIL NIL)))
  :hints (("Goal" :in-theory (enable equal-of-append))))

(defthm equal-cons-nth-0-self
  (equal (equal x (cons (nth 0 x) y))
         (and (consp x)
              (equal (cdr x) y))))

(defthm consp-from-len-bound
  (implies (and (< free (len x)) ;add a syntaxp hyp
                (natp free))
           (consp x)))

;dup?
(defthm len-when-not-consp-cheap
  (implies (not (consp x))
           (equal (len x) 0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable ;list::len-of-non-consp
                              ))))

;; (defthm memberp-caar-strip-cars
;;   (equal (memberp (caar pairs) (strip-cars pairs))
;;          (consp pairs))
;;   :hints (("Goal" :in-theory (enable strip-cars))))

(defthm nth-equal-car-hack
  (implies (equal y (nthcdr n x))
           (equal (equal (nth n x) (car y))
                  t)))

;move
;maybe this doesn't loop like the other one does?
(DEFTHM TAKE-EQUAL-LENGTHEN-cheap
  (IMPLIES (AND (EQUAL (NTH N LST1) (NTH N LST2))
                (< N (LEN LST1))
                (< N (LEN LST2))
                (<= 0 N)
                (INTEGERP N))
           (EQUAL (EQUAL (TAKE N LST1)
                         (TAKE N LST2))
                  (EQUAL (TAKE (+ 1 N) LST1)
                         (TAKE (+ 1 N) LST2))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil nil)))
  :HINTS (("Goal" :IN-THEORY (E/d (TAKE NTH) ()))))

;move?
(theory-invariant (incompatible (:rewrite TAKE-EQUAL-LENGTHEN) (:rewrite NTHS-EQUAL-WHEN-TAKES-EQUAL)))

(defthmd nths-equal-when-takes-equal
  (implies (and (equal (take n lst1) (take n lst2))
                (< 0 n)
                (integerp n))
           (EQUAL (NTH 0 lst1)
                  (NTH 0 lst2)))
  :hints (("Goal" :in-theory (enable take))))

(defthm take-when-<-of-len
  (implies (< (len x) n) ;could be expensive?
           (equal (take n x)
                  (if (zp n)
                      nil
                    (append x
                            (repeat (- (nfix n) (len x))
                                    nil)))))
  :hints (("Goal" :in-theory (e/d (take; list::nth-append
                                   ) ()))))


;gen
(defthm subsetp-equal-of-subrange-and-subrange
  (implies (and (<= high high2)
                (natp low)
                (natp high)
                (natp high2))
           (subsetp-equal (SUBRANGE low high X) (SUBRANGE low high2 X)))
  :hints (("Goal" :in-theory (e/d (subrange) (;anti-subrange
                                              )))))
