; Theorems about merge-sort-<
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "merge-sort-less-than")
(include-book "all-less-than-or-equal")
(include-book "less-than-or-equal-all")
(include-book "all-less-than-or-equal-all")
(include-book "sortedp-less-than-or-equal")
(include-book "kestrel/typed-lists-light/all-natp" :dir :system)
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;move
(defthm all-<-of-+-of-1
  (implies (and (syntaxp (not (quotep y)))
                (all-integerp x)
                (integerp y))
           (equal (all-< x (+ 1 y))
                  (all-<= x y)))
  :hints (("Goal" :in-theory (enable all-<= all-<))))

;; this one actually uses perm as the equiv
(DEFTHM PERM-OF-MERGE-SORT-<-2
  (PERM (MERGE-SORT-< X)
        X))

(defthm all-<=-all-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (all-<=-all x lst)
                ;;(all-<=-all x tail)
                (<= (len tail) (len lst))
                (all-<=-all x acc))
           (all-<=-all x (mv-nth 0 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux all-<=-all))))

(defthm all-<=-all-of-mv-nth-0-of-split-list-fast-aux-arg2
  (implies (and (all-<=-all lst y)
                (all-<=-all tail y)
                (<= (len tail) (len lst))
                (all-<=-all acc y))
           (all-<=-all (mv-nth 0 (split-list-fast-aux lst tail acc)) y))
  :hints (("Goal" :in-theory (enable split-list-fast-aux all-<=-all))))

(defthm all-<=-all-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (all-<=-all x lst)
                ;;(all-<=-all x tail)
                (<= (len tail) (len lst))
                (all-<=-all x acc))
           (all-<=-all x (mv-nth 1 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux all-<=-all))))

(defthm all-<=-all-of-mv-nth-1-of-split-list-fast-aux-arg1
  (implies (and (all-<=-all lst y)
                (all-<=-all tail y)
;                (<= (len tail) (len lst))
                (all-<=-all acc y))
           (all-<=-all (mv-nth 1 (split-list-fast-aux lst tail acc)) y))
  :hints (("Goal" :in-theory (enable split-list-fast-aux all-<=-all))))

(defthm all-<=-all-of-mv-nth-0-of-split-list-fast
  (implies (all-<=-all x l)
           (all-<=-all x (mv-nth 0 (split-list-fast l))))
  :hints (("Goal" :in-theory (enable split-list-fast all-<=-all))))

(defthm all-<=-all-of-mv-nth-1-of-split-list-fast
  (implies (all-<=-all x l)
           (all-<=-all x (mv-nth 1 (split-list-fast l))))
  :hints (("Goal" :in-theory (enable split-list-fast all-<=-all))))

(defthm all-<=-all-of-mv-nth-0-of-split-list-fast-arg1
  (implies (all-<=-all x y)
           (all-<=-all (mv-nth 0 (split-list-fast x)) y))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm all-<=-all-of-mv-nth-1-of-split-list-fast-arg1
  (implies (all-<=-all x y)
           (all-<=-all (mv-nth 1 (split-list-fast x)) y))
  :hints (("Goal" :in-theory (enable split-list-fast all-<=-all))))

(defthm all-<=-all-of-merge-<
  (implies (and (all-<=-all x l1)
                (all-<=-all x l2)
                (all-<=-all x acc))
           (all-<=-all x (merge-< l1 l2 acc)))
  :hints (("Goal" :in-theory (enable merge-<
                                     revappend-lemma
                                     all-<=-all))))

(defthm all-<=-of-merge-<-arg1
  (equal (all-<= (merge-< l1 l2 acc) x)
         (and (all-<= l1 x)
              (all-<= l2 x)
              (all-<= acc x)))
  :hints (("Goal" :in-theory (enable merge-<
                                     ;;revappend-lemma
                                     all-<=))))

(defthm all-<=-all-of-merge-<-arg1
  (equal (all-<=-all (merge-< l1 l2 acc) x)
         (and (all-<=-all l1 x)
              (all-<=-all l2 x)
              (all-<=-all acc x)))
  :hints (("Goal" :in-theory (enable merge-<
                                     ;;revappend-lemma
                                     all-<=-all))))

(defthm all-<=-all-of-merge-sort-<
  (implies (all-<=-all x l)
           (all-<=-all x (merge-sort-< l)))
  :hints (("Goal" :in-theory (enable merge-sort-< all-<=-all))))



;todo: nested induction
(defthm all-<=-of-car-of-last-when-sortedp-<=
  (implies (sortedp-<= x)
           (all-<= x (car (last x))))
  :hints (("Goal" :in-theory (enable all-<= sortedp-<=))))



(defthmd all-<=-all-redef
  (implies (consp x)
           (equal (all-<=-all x y)
                  (and (all-<=-all (cdr x) y)
                       (<=-all (car x) y))))
  :hints (("Goal" :in-theory (enable ALL-<=-ALL <=-all))))

(defthm <=-all-trans-1
  (implies (and (<=-all x2 lst)
                (<= x x2))
           (<=-all x lst))
  :hints (("Goal" :in-theory (enable <=-all))))

(defthm all-<=-all-when-not-consp-arg1
  (implies (not (consp x))
           (all-<=-all x y))
  :hints (("Goal" :in-theory (enable all-<=-all))))

(defthm ALL-<=-ALL-when-not-consp-arg2
  (implies (not (consp y))
           (ALL-<=-ALL x y))
  :hints (("Goal" :in-theory (enable ALL-<=-ALL))))

(defthm sortedp-<=-of-append
  (equal (sortedp-<= (append x y))
         (and (sortedp-<= x)
              (sortedp-<= y)
              (all-<=-all x y)))
  :hints (("Goal" :in-theory (enable all-<=-all-redef
                                     all-<=
                                     <=-all
                                     append
                                     sortedp-<=))))

(defthm all-<=-of-reverse-list-arg1
  (equal (all-<= (reverse-list x) y)
         (all-<= x y))
  :hints (("Goal" :in-theory (enable all-<=))))

(defthm all-<=-all-of-reverse-list-arg1
  (equal (all-<=-all (reverse-list x) y)
         (all-<=-all x y))
  :hints (("Goal" :in-theory (enable all-<=-all))))

(defthm all-<=-all-of-cons-arg1
  (equal (all-<=-all (cons x1 x2) lst)
         (and (<=-all x1 lst)
              (all-<=-all x2 lst)))
  :hints (("Goal" :in-theory (enable all-<=-all <=-all))))

(defthm <=-all-when-sortedp-<=-and-<=-of-car
  (implies (and (SORTEDP-<= lst)
                (<= x (CAR lst)))
           (<=-ALL x lst))
  :hints (("Goal" :in-theory (enable <=-ALL
                                     sortedp-<=))))

(defthm ALL-<=-ALL-of-cdr-arg2
  (implies (ALL-<=-ALL ACC L2)
           (ALL-<=-ALL ACC (CDR L2)))
  :hints (("Goal" :in-theory (enable ALL-<=-ALL))))

(defthm ALL-<=-ALL-of-cons-arg2
  (equal (ALL-<=-ALL x (cons a lst))
         (and (ALL-<= x a)
              (ALL-<=-ALL x lst)))
  :hints (("Goal" :in-theory (enable ALL-<=-ALL))))

;rename
;todo: nested induction
(defthm sorted-of-merge-<
  (implies (and (sortedp-<= l1)
                (sortedp-<= l2)
                (sortedp-<= (reverse-list acc))
                (all-<=-all acc l1)
                (all-<=-all acc l2)
                )
           (sortedp-<= (merge-< l1 l2 acc)))
  :hints (("Goal" :in-theory (enable merge-<
                                     sortedp-<=
                                     SORTEDP-<=
                                     <=-all
                                     revappend-lemma
                                     ))))

(defthm sortedp-<=-of-merge-sort-<
  (sortedp-<= (merge-sort-< x))
  :hints (("Goal" :in-theory (enable merge-sort-<
                                     sortedp-<=))))

(defthm nat-listp-of-merge-<
  (implies (and (nat-listp l1)
                (nat-listp l2)
                (nat-listp acc))
           (nat-listp (merge-< l1 l2 acc)))
  :hints (("Goal" :in-theory (enable merge-< revappend-lemma))))

(defthm nat-listp-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (nat-listp lst)
                (nat-listp tail)
                (nat-listp acc)
                (<= (len tail) (len lst)))
           (nat-listp (mv-nth 0 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (e/d (split-list-fast-aux nat-listp) (natp)))))

(defthm nat-listp-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (nat-listp lst)
                (nat-listp tail)
                (nat-listp acc)
                (<= (len tail) (len lst)))
           (nat-listp (mv-nth 1 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux nat-listp))))

(defthm nat-listp-of-mv-nth-0-of-split-list-fast
  (implies (nat-listp l)
           (nat-listp (mv-nth 0 (split-list-fast l))))
  :hints (("Goal" :in-theory (enable split-list-fast nat-listp))))

(defthm nat-listp-of-mv-nth-1-of-split-list-fast
  (implies (nat-listp l)
           (nat-listp (mv-nth 1 (split-list-fast l))))
  :hints (("Goal" :in-theory (enable split-list-fast nat-listp))))

(defthm nat-listp-of-merge-sort-<
  (implies (nat-listp x)
           (nat-listp (merge-sort-< x)))
  :hints (("Goal" :in-theory (enable merge-sort-<))))

(defcong perm equal (all-<=-all x y) 1
  :hints (("Goal" :in-theory (enable all-<=-all))))

;; (defcong perm equal (all-<=-all x y) 2
;;    :hints (("Goal" :in-theory (enable all-<=-all))))

(defthm all-<=-all-of-merge-sort-<-strong
  (equal (all-<=-all (merge-sort-< x) y)
         (all-<=-all x y))
  ;; todo: why doesn't the congruence rule fire?  because PERM-OF-MERGE-SORT uses equal, not perm, as the equiv?
  :hints (("Goal" :use (:instance perm-implies-equal-all-<=-all-1
                                  (x-equiv (merge-sort-< x)))
           :in-theory (disable perm-implies-equal-all-<=-all-1))))

;defforall could do these too?
(defthm all-natp-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (all-natp lst)
                (all-natp acc)
                (<= (len tail) (len lst)))
           (all-natp (mv-nth 0 (split-list-fast-aux lst tail acc)))))

(defthm all-natp-of-mv-nth-0-of-split-list-fast
  (implies (all-natp lst)
           (all-natp (mv-nth 0 (split-list-fast lst))))
  :hints (("Goal" :in-theory (e/d (split-list-fast) ()))))

(defthm all-natp-of-mv-nth-1-of-split-list-fast-aux
  (implies (all-natp lst)
           (all-natp (mv-nth 1 (split-list-fast-aux lst tail acc)))))

(defthm all-natp-of-mv-nth-1-split-list-fast
  (implies (all-natp lst)
           (all-natp (mv-nth 1 (split-list-fast lst))))
  :hints (("Goal" :in-theory (e/d (split-list-fast) (SPLIT-LIST-FAST-AUX)))))

;move
(defthmd all-integerp-when-all-natp
  (implies (all-natp x)
           (all-integerp x))
  :hints (("Goal" :in-theory (enable all-natp))))

(defthm <-of-+-of-1-and-car-of-last-when-<=-all
  (implies (and (<=-all x lst)
                (consp lst))
           (< x (+ 1 (car (last lst)))))
  :hints (("Goal" :in-theory (enable <=-all))))

;todo: nested induction
(defthm <=-all-of-merge-<
  (implies (and (<=-all a x)
                (<=-all a y)
                (<=-all a acc))
           (<=-all a (merge-< x y acc)))
  :hints (("Goal" :in-theory (enable merge-< <=-all
                                     revappend-lemma))))

(defthm <=-all-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (<=-all a lst)
                (<=-all a tail)
                (<=-all a acc)
                (<= (len tail) (len lst))
                )
           (<=-all a (mv-nth 0 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux <=-all))))

(defthm <=-all-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (<=-all a lst)
                (<=-all a tail)
                (<=-all a acc)
                (<= (len tail) (len lst))
                )
           (<=-all a (mv-nth 1 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux <=-all))))

(defthm <=-all-of-mv-nth-0-of-split-list-fast
  (implies (<=-all a x)
           (<=-all a (mv-nth 0 (split-list-fast x))))
  :hints (("Goal" :in-theory (enable split-list-fast <=-all))))

(defthm <=-all-of-mv-nth-1-of-split-list-fast
  (implies (<=-all a x)
           (<=-all a (mv-nth 1 (split-list-fast x))))
  :hints (("Goal" :in-theory (enable split-list-fast <=-all))))

(defthm <=-all-of-merge-sort-<
  (implies (<=-all a x)
           (<=-all a (merge-sort-< x)))
  :hints (("Goal" :in-theory (enable merge-sort-< <=-all))))

;todo: have defforall do this too
(defthm not-all-natp-when-not-natp-and-member-equal
  (implies (and (not (natp a))
                (member-equal a x))
           (not (all-natp x)))
  :hints (("Goal" :in-theory (e/d (all-natp) (natp)))))

;todo: have defforall do this too
(DEFTHM ALL-NATP-OF-REVAPPEND-strong
  (equal (ALL-NATP (REVAPPEND LST LST0))
         (AND (ALL-NATP LST) (ALL-NATP LST0)))
  :hints (("Goal" :in-theory (e/d (all-natp
                                   revappend-lemma)
                                  (natp)))))

(defthm all-natp-of-merge-<
  (equal (all-natp (merge-< l1 l2 acc))
         (and (all-natp l1)
              (all-natp l2)
              (all-natp acc)))
  :hints (("Goal" :in-theory (enable merge-<))))

(defthm eqlable-listp-of-merge-<
  (implies (and (eqlable-listp l1)
                (eqlable-listp l2)
                (eqlable-listp acc))
           (eqlable-listp (merge-< l1 l2 acc)))
  :hints (("Goal" :in-theory (enable merge-< revappend-lemma))))

(defthm eqlable-listp-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (eqlable-listp acc)
                (eqlable-listp lst))
           (eqlable-listp (mv-nth 0 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm eqlable-listp-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (eqlable-listp acc)
                (eqlable-listp lst))
           (eqlable-listp (mv-nth 1 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm eqlable-listp-of-mv-nth-0-of-split-list-fast
  (Implies (EQLABLE-LISTP LST)
           (EQLABLE-LISTP (MV-NTH 0 (SPLIT-LIST-FAST LST))))
  :hints (("Goal" :in-theory (enable SPLIT-LIST-FAST))))

(defthm eqlable-listp-of-mv-nth-1-of-split-list-fast
  (implies (eqlable-listp lst)
           (eqlable-listp (mv-nth 1 (split-list-fast lst))))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm eqlable-listp-of-merge-sort-<
  (implies (and (eqlable-listp lst)
                (true-listp lst))
           (eqlable-listp (merge-sort-< lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-sort-<) ()))))

(defthm eqlable-listp-when-all-natp
  (implies (and (all-natp x)
                (true-listp x))
           (eqlable-listp x)))

(defthm all-natp-of-merge-sort-<
  (equal (all-natp (merge-sort-< lst))
         (all-natp lst))
  :hints (("Goal" :in-theory (enable))))

(defthm all-<-of-merge-sort-<
  (equal (all-< (merge-sort-< lst) val)
         (all-< lst val))
  :hints (("Goal" :in-theory (enable merge-sort-<))))

(defthm all-<=-of-car-of-last-when-sortedp-<=-2
  (implies (and (sortedp-<= x)
                (subsetp-equal y x))
           (all-<= y (car (last x))))
  :hints (("Goal" :in-theory (enable ALL-<=
                                     SUBSETP-EQUAL
                                     sortedp-<=))))

(encapsulate ()
  (local (include-book "kestrel/lists-light/memberp" :dir :system))
;move
  (defcong perm iff (member-equal x y) 2
    :hints (("Goal" :in-theory (enable member-equal perm)))))

;move
(defcong perm equal (subsetp-equal x y) 2
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-merge-sort-<
  (equal (subsetp-equal x (merge-sort-< x))
         (subsetp-equal x x)))

(defthm all-<=-of-car-of-last-of-merge-sort-<
  (all-<= x (car (last (merge-sort-< x))))
  :hints (("Goal" :use (:instance all-<=-of-car-of-last-when-sortedp-<=-2
                                  (x (merge-sort-< x))
                                  (y x))
           :in-theory (disable all-<=-of-car-of-last-when-sortedp-<=-2))))

(defthm all-integerp-of-merge-sort-<-when-nat-listp
  (implies (nat-listp x) ;gen
           (all-integerp (merge-sort-< x))))

(defthm all-<-of-+-of-1-and-car-of-last-of-merge-sort-<
  (implies (and (nat-listp x) ;(all-integerp x)
                (consp x))
           (all-< x (+ 1 (car (last (merge-sort-< x))))))
  :hints (("Goal" :in-theory (e/d (integerp-of-car-of-last-when-all-integerp ALL-INTEGERP-WHEN-NAT-LISTP)
                                  (NAT-LISTP)))))
