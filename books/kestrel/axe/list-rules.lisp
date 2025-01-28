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

(defthmd nth-differs-hack2
  (implies (not (equal (nth n x)
                       (nth n y)))
           (equal (equal x y)
                  nil)))

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
           (equal (NTHCDR n x)
                  (cons (nth n x) (FINALCDR X))))
  :hints (("Goal" :in-theory (enable))))

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
