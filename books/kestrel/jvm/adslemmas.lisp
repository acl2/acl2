; Lemmas about addresses
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ads")
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
;(include-book "utilities")
;(include-book "coi/osets/set-order" :dir :system)

(defthm insert-new-ad-insert-2nd-new-ad
  (implies (set::setp dom)
           (equal (set::insert (new-ad dom)
                               (set::insert (nth-new-ad 2 dom)
                                            dom))
                  (set::union (list::2set (n-new-ads 2 dom))
                              dom)))
  :otf-flg t
  :hints (("Goal"
;          :use (:instance set::union (x (list (new-ad dom) (nth-new-ad 2 dom))) (y dom))
           :expand ((nth-new-ad 1 dom) ;bozo turn this into new-ad (or do the reverse!)
                    (n-new-ads-aux 1 dom)
                    (n-new-ads-aux 2 dom)
                    (n-new-ads 2 dom)))))

;BOZO gen
(defthm new-ad-of-union-n-new-ads
  (equal (NEW-AD (SET::UNION dom (list::2set (N-NEW-ADS 2 dom))))
         (nth-new-ad 3 dom))
  :hints (("Goal" :in-theory (disable NTH-NEW-AD-OF-INSERT-NEW-AD)
           :expand ((N-NEW-ADS 2 DOM)
                    (N-NEW-ADS-AUX 1 DOM)
                    (N-NEW-ADS-AUX 2 DOM)
                    (NTH-NEW-AD 2 (SET::INSERT (NEW-AD DOM) DOM))
                    (nth-new-ad 3 dom)))))

;if x is a small term, acl2 has to wait for substitution without this rule...
(defthm new-ad-not-equal-nth-new-ad-helper
  (implies (and (EQUAL (NTH-NEW-AD n dom) x)
                (< 1 n)
                (force (integerp n)))
           (equal (EQUAL x (NEW-AD dom))
                  nil)))

(in-theory (disable N-NEW-ADS-AUX)) ;new

;move?
(defthm union-of-2set-and-2set
  (equal (set::union (list::2set lst1) (list::2set lst2))
         (list::2set (append lst1 lst2)))
  :hints (("Goal" :in-theory (enable list::2set))))

(defthm union-of-2set-and-2set-alt
  (equal (set::union (list::2set lst1) (set::union (list::2set lst2) x))
         (set::union (list::2set (append lst1 lst2)) x))
  :hints (("Goal" :in-theory (enable list::2set))))

(defthmd UNION-OF-2SET-AND-2SET-back
 (equal (LIST::|2SET| (APPEND l1 l2))
        (set::union (LIST::|2SET| l1)
                    (LIST::|2SET| l2)))
 :hints (("Goal" :in-theory (enable append))))

(theory-invariant (incompatible (:rewrite  UNION-OF-2SET-AND-2SET) (:rewrite UNION-OF-2SET-AND-2SET-back)))

(defthm insert-of-next-ad-onto-union-of-dom-and-n-new-ads
  (implies (and (equal m (+ 1 n))
                (natp n)
                (< 0 n))
           (equal (SET::INSERT (NTH-NEW-AD m dom) (SET::UNION dom (LIST::|2SET| (N-NEW-ADS n dom))))
                  (SET::UNION dom (LIST::|2SET| (N-NEW-ADS m dom)))))
  :hints (("Goal" :in-theory (e/d (UNION-OF-2SET-AND-2SET-back) (UNION-OF-2SET-AND-2SET
                                                                 ))
           :expand ((N-NEW-ADS-AUX (+ 1 N) DOM)
                    (N-NEW-ADS N DOM)
                    (N-NEW-ADS (+ 1 N) DOM)))))

;gen the 1?
(defthm memberp-new-ad-n-new-ads-aux-1
  (MEMBERP (NEW-AD DOM)
                 (N-NEW-ADS-AUX 1 DOM))
  :hints (("Goal" :expand (N-NEW-ADS-AUX 1 DOM)
           :in-theory (enable N-NEW-ADS-AUX))))


;; (defthm NTH-NEW-AD-of-insert-new-ad
;;   (implies (and (natp n)
;;                 (< 0 n))
;;            (equal (NTH-NEW-AD n (SET::INSERT (NEW-AD DOM) DOM))
;;                   (NTH-NEW-AD (+ 1 n) DOM)))
;;   :hints (("Goal" :in-theory (e/d (NTH-NEW-AD) (NTH-NEW-AD-OF-INSERT-NEW-AD)))))


;bozo gen?
;i've seen this loop with something
(defthm insert-nth-new-ad-2-union-new-ads-slice-3
  (implies (and (natp n)
                (< 1 n))
           (equal (SET::INSERT (NTH-NEW-AD 2 DOM) (SET::UNION DOM (LIST::|2SET| (NEW-ADS-SLICE 3 N DOM))))
                  (SET::UNION DOM (LIST::|2SET| (NEW-ADS-SLICE 2 N DOM)))))
  :otf-flg t
  :hints (("Goal" :expand ((LIST::|2SET| (NTHCDR 2 (N-NEW-ADS N DOM)))
                           (LIST::|2SET| (CDR (N-NEW-ADS N DOM))))
           :in-theory (e/d (NEW-ADS-SLICE)
                           (;CDR-OF-N-NEW-ADS ;bozo
                            )))))

(defthm n-new-ads-aux-of-0
  (equal (N-NEW-ADS-AUX 0 DOM)
         nil)
  :hints (("Goal" :in-theory (enable N-NEW-ADS-AUX))))

(defthm insert-car-2set-cdr
  (IMPLIES (consp x)
           (EQUAL (SET::INSERT (car x)
                               (LIST::|2SET| (CDR x)))
                  (LIST::|2SET| x))))

(defthm insert-new-ad-union-new-ads-slice-2-helper
  (implies (and (natp n)
                (< 0 n)
                )
           (equal (SET::INSERT (NEW-AD DOM) (LIST::|2SET| (NEW-ADS-SLICE 2 N DOM)))
                  (LIST::|2SET| (n-NEW-ADS N DOM))))
  :otf-flg t
  :hints (("Goal" :expand (;(N-NEW-ADS N DOM)
;                           (N-NEW-ADS-AUX (+ -1 N) DOM)
;                          (N-NEW-ADS-AUX (+ -2 N) DOM)
                           )
           :use (:instance insert-car-2set-cdr (x (n-NEW-ADS N DOM)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (NEW-ADS-SLICE
                            ;N-NEW-ADS-AUX
                            ;LIST::CDR-APPEND
                            UNION-OF-2SET-AND-2SET-back)
                           (insert-car-2set-cdr
                            NEW-ADS-SLICE-OPENER
                            CDR-OF-N-NEW-ADS ;bozo
                            UNION-OF-2SET-AND-2SET
                            )))))

(defthm insert-new-ad-union-new-ads-slice-2
  (implies (and (natp n)
                (< 0 n))
           (equal (SET::INSERT (NEW-AD DOM) (SET::UNION DOM (LIST::|2SET| (NEW-ADS-SLICE 2 N DOM))))
                  (SET::UNION DOM (LIST::|2SET| (n-NEW-ADS N DOM)))))
  :hints (("Goal" :use (:instance insert-new-ad-union-new-ads-slice-2-helper)
           :in-theory (disable insert-new-ad-union-new-ads-slice-2-helper))))

(defthm new-ad-of-union-dom-and-n-new-ads
  (implies (and (natp n)
                (<= 0 n)
                )
           (equal (NEW-AD (SET::UNION dom (LIST::|2SET| (N-NEW-ADS n dom))))
                  (nth-new-ad (+ 1 n) dom)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (nth-new-ad n dom)
           :do-not-induct t
           :expand ((N-NEW-ADS 1 DOM))
           :in-theory (e/d ((:induction NTH-NEW-AD)
;n-new-ads
                            N-NEW-ADS-AUX UNION-OF-2SET-AND-2SET-back)
                           (NEW-ADS-SLICE
                            NEW-ADS-SLICE-OPENER
                            SET::USE-WEAK-INSERT-INDUCTION
                            UNION-OF-2SET-AND-2SET
                            SET::WEAK-INSERT-INDUCTION
;NTH-NEW-AD-OF-INSERT-NEW-AD
                            )))))

(defthm nth-new-ad-of-sfix
  (equal (nth-new-ad m (set::sfix dom))
         (nth-new-ad m dom))
  :hints (("Goal" :in-theory (e/d (nth-new-ad) (nth-new-ad-of-insert-new-ad NTH-NEW-AD-COLLECT)))))

(defthm NTH-NEW-AD-of-union-dom-n-new-ads
  (implies (and (natp m)
                (< 0 m)
                (natp n))
           (equal (NTH-NEW-AD m (SET::UNION dom (LIST::|2SET| (N-NEW-ADS n dom))))
                  (NTH-NEW-AD (+ m n) dom)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (nth-new-ad n dom)
           :do-not-induct t
           :expand ((N-NEW-ADS 1 DOM))
           :in-theory (e/d ((:induction NTH-NEW-AD)
;n-new-ads
                            N-NEW-ADS-AUX UNION-OF-2SET-AND-2SET-back)
                           (NEW-ADS-SLICE
                            NEW-ADS-SLICE-OPENER
                            SET::USE-WEAK-INSERT-INDUCTION
                            UNION-OF-2SET-AND-2SET
                            SET::WEAK-INSERT-INDUCTION
;NTH-NEW-AD-OF-INSERT-NEW-AD
                            )))))

(defthm nth-new-ad-of-union-dom-n-new-ads-alt
  (implies (and (natp m) (< 0 m) (natp n))
           (equal (nth-new-ad m (set::union (list::2set (n-new-ads n dom)) dom))
                  (nth-new-ad (+ m n) dom))))

(defthm insert-nth-new-ad-insert-nth-new-ad-adjacent
  (implies (and (equal n (+ 1 m))
                (< 0 m)
                (natp m))
           (equal (SET::INSERT (NTH-NEW-AD m dom) (SET::INSERT (NTH-NEW-AD n dom) dom2))
                  (set::union (list::2set (NEW-ADS-SLICE m (+ 1 m) dom)) dom2)))
  :hints (("Goal" :in-theory (disable set::WEAK-INSERT-INDUCTION))))

(in-theory (disable NEW-ADS-SLICE-OPENER))

(defthmd n-new-ads-opener-high
  (implies (and (< 0 n)
                (integerp n))
           (equal (n-new-ads n dom)
                  (append (n-new-ads (+ -1 n) dom)
                          (list (nth-new-ad n dom)))))
  :hints (("Goal" :in-theory (enable n-new-ads N-NEW-ADS-AUX))))

(DEFTHMd NEW-ADS-SLICE-OPENER2
  (IMPLIES (AND (NATP M)
                (< 0 M)
                (NATP N)
                (<= M N))
           (EQUAL (NEW-ADS-SLICE M N DOM)
                  (append (NEW-ADS-SLICE M (+ -1 N) DOM)
                          (list (NTH-NEW-AD n DOM)
                                ))))
  :HINTS
  (("Goal" :use (:instance n-new-ads-opener-high)
    :IN-THEORY (E/d (NEW-ADS-slice ;EQUAL-CONS-CASES2
                     )
                    (CDR-OF-N-NEW-ADS ;looped
                     )))))

(defthm insert-nth-new-ad-union-new-ads-slice
  (implies (and (equal nplus1 (+ 1 n))
                (natp n)
                (<= m n)
                (< 0 m)
                (natp m))
           (equal (SET::INSERT (NTH-NEW-AD nplus1 dom) (SET::UNION dom2 (LIST::|2SET| (NEW-ADS-SLICE m n dom))))
                  (SET::UNION dom2 (LIST::|2SET| (NEW-ADS-SLICE m nplus1 dom)))))
  :hints (("Goal" :use (:instance NEW-ADS-SLICE-OPENER2
                                  (n nplus1))
           :in-theory (e/d (UNION-OF-2SET-AND-2SET-BACK)
                           (SET::PICK-A-POINT-SUBSET-STRATEGY ;trying..
                            NEW-ADS-SLICE-OPENER
;                             LIST::EQUAL-APPEND-REDUCTION!
 ;                            LIST::EQUAL-APPEND-REDUCTION!-alt
                            IN-OF-2SET
                             UNION-OF-2SET-AND-2SET)))))


(defthm nth-0-n-new-ads-aux
  (implies (and (natp n)
                (< 0 n))
           (equal (NTH 0 (N-NEW-ADS-AUX N X))
                  (nth-new-ad n x)))
  :hints (("Goal" :in-theory (enable N-NEW-ADS-AUX))))

;;fixme move these after moving axe/seq
(defthm take-of-n-new-ads
  (implies (and (<= n m)
                (natp n)
                (natp m))
           (equal (TAKE N (N-NEW-ADS m X))
                  (N-NEW-ADS n X)))
  :hints (("Goal" ; :induct (N-NEW-ADS-AUX M X)
           :in-theory (e/d (N-NEW-ADS N-NEW-ADS-AUX) (TAKE)))))

(defthm append-n-new-ads-new-ads-slice
  (implies (and (equal m (+ 1 n))
                (<= n p)
                (natp n)
                (natp p))
           (equal (APPEND (N-NEW-ADS n X) (NEW-ADS-SLICE m p X))
                  (N-NEW-ADS p x)))
  :hints (("Goal" :in-theory (e/d (NEW-ADS-SLICE equal-of-append) (CDR-OF-N-NEW-ADS)))))

(defthm union-2set-n-new-ads-2set-new-ads-slice
  (implies (and (equal m (+ 1 n))
                (<= n p)
                (natp n)
                (natp p))
           (equal (SET::UNION (LIST::|2SET| (N-NEW-ADS n x)) (LIST::|2SET| (NEW-ADS-SLICE m p x)))
                  (LIST::|2SET| (N-NEW-ADS p x)))))

(defthm union-2set-new-ads-slice-2set-n-new-ads
  (implies (and (equal m (+ 1 n))
                (<= n p)
                (natp n)
                (natp p))
           (equal (SET::UNION (LIST::|2SET| (NEW-ADS-SLICE m p x)) (LIST::|2SET| (N-NEW-ADS n x)))
                  (LIST::|2SET| (N-NEW-ADS p x))))
  :hints (("Goal" :use (:instance union-2set-n-new-ads-2set-new-ads-slice)
           :in-theory (disable union-2set-n-new-ads-2set-new-ads-slice UNION-OF-2SET-AND-2SET))))
