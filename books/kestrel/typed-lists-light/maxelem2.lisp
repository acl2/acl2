; More theorems about maxelem
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "maxelem")
(include-book "kestrel/lists-light/memberp-def" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(local (include-book "kestrel/lists-light/remove1-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; This book mixes maxelem with other non-built-in functions.

;rename
(defthm maxelem-of-member
  (implies (memberp a x)
           (<= a (maxelem x)))
  :hints (("Goal" :in-theory (enable maxelem))))


;; (IMPLIES (AND (CONSP X)
;;               (CONSP (CDR X))
;;               (MEMBERP (CAR X) BAG::X-EQUIV)
;;               (BAG::PERM (CDR X)
;;                          (BAG::REMOVE-1 (CAR X) BAG::X-EQUIV))
;;               (< (MAXELEM (BAG::REMOVE-1 (CAR X) BAG::X-EQUIV))
;;                  (CAR X)))
;;          (EQUAL (CAR X) (MAXELEM BAG::X-EQUIV))).

;; (defcong bag::perm equal (maxelem x) 1
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable maxelem bag::perm))))

(defthm maxelem-of-remove1
  (implies (<= 2 (len lst)) ;bozo, so maxelem is well-defined after we remove a
           (<= (maxelem (remove1-equal a lst))
               (maxelem lst)))
  :hints (("Goal" :expand ((REMOVE1-EQUAL A LST)
                           (REMOVE1-EQUAL A (CDR LST)))
           :in-theory (enable maxelem ;consp-cdr
                                     ))))

(defthmd maxelem-when-subbagp-helper
  (implies (and (subsetp-equal lst1 lst2)
                (consp lst1) ;handle..
                )
           (equal (< (MAXELEM lst2) (MAXELEM lst1))
                  nil))
  :hints (("Subgoal *1/5.1" :use (:instance maxelem-of-remove1 (lst lst2) (a (car lst1)))
           :in-theory (e/d (maxelem ;len-less-than-2-rewrite
                            ) ( maxelem-of-remove1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (maxelem (:definition maxelem)
                            ;bag::subbagp
                                    ;;BAG::PERM-OF-REMOVE1-ONE
                            ;len-less-than-2-rewrite
                            )
                           (;BAG::LEN-1-AND-MEMBERP-MEANS-YOU-KNOW-X ;eff
                            ;BAG::CONSP-REMOVE1-REWRITE ;eff
                            ;BAG::SUBBAGP-CDR-REMOVE1-REWRITE
                            )))))

(defthm maxelem-when-subbagp
  (implies (subsetp-equal lst1 lst2)
           (equal (< (MAXELEM lst2) (MAXELEM lst1))
                  (if (consp lst1)
                      nil
                    (< (MAXELEM lst2) (negative-infinity)))))
  :hints (("Goal" :in-theory (enable maxelem-when-subbagp-helper))))

(defthm not-<-car-when->=maxelem-free
  (implies (and (<= (maxelem free) x)
                (subsetp-equal lst free)
                (consp lst))
           (not (< x (car lst))))
  :hints (("Goal" :use ((:instance not-<-car-when->=maxelem)
                        (:instance maxelem-when-subbagp (lst1 lst) (lst2 free)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (disable not-<-car-when->=maxelem MAXELEM-WHEN-SUBBAGP))))

(defthm not-less-than-maxelem-of-small-range-lemma
  (implies (and (<= (MAXELEM bigrange) k) ;bigrange is a free var
                (subsetp-equal smallrange bigrange))
           (equal (< k (MAXELEM smallrange))
                  (if (consp smallrange)
                      nil
                    (< k (negative-infinity)))))
  :hints (("Goal" :use (:instance maxelem-when-subbagp (lst1 smallrange) (lst2 bigrange))
           :in-theory (disable maxelem-when-subbagp))))

(defthm maxelem-of-reverse-list
  (implies (rational-listp lst)
           (equal (maxelem (reverse-list lst))
                  (maxelem lst)))
  :hints (("Goal" :in-theory (enable reverse-list maxelem))))

(defthm maxelem-of-strip-cars-bound
  (implies (consp dag)
           (<= (car (car dag)) (maxelem (strip-cars dag))))
  :rule-classes ((:linear :trigger-terms ((maxelem (strip-cars dag)))))
  :hints (("Goal" :expand (strip-cars dag))))

(defthmd maxelem-of-strip-cars-bound-2
  (implies (consp dag)
           (<= (car (car dag)) (maxelem (strip-cars dag))))
  :rule-classes ((:linear :trigger-terms ((car (car dag)))))
  :hints (("Goal" :expand (strip-cars dag))))

(defthm maxelem-of-reverse-list
  (implies (rational-listp lst)
           (equal (maxelem (reverse-list lst))
                  (maxelem lst)))
  :hints (("Goal" :in-theory (enable reverse-list maxelem))))
