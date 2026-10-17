; More theorems about maxelem
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
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
;(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/memberp" :dir :system))
;(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; This book mixes maxelem with other non-built-in functions.

;rename
;drop?
(defthmd maxelem-of-member
  (implies (memberp a x)
           (<= a (maxelem x))))

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

;move to main book
(defthm maxelem-of-remove1
  (implies (<= 2 (len lst)) ;bozo, so maxelem is well-defined after we remove a
           (<= (maxelem (remove1-equal a lst))
               (maxelem lst)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(local
  (defthmd maxelem-when-subsetp-equal-helper
    (implies (and (subsetp-equal lst1 lst2)
                  (consp lst1) ;handle..
                  )
             (not (< (maxelem lst2) (maxelem lst1))))
    :hints (("Goal" :in-theory (enable maxelem)))))

(defthm maxelem-when-subsetp-equal
  (implies (subsetp-equal lst1 lst2)
           (equal (< (maxelem lst2) (maxelem lst1))
                  (if (consp lst1)
                      nil
                    (< (maxelem lst2) (negative-infinity)))))
  :hints (("Goal" :in-theory (enable maxelem-when-subsetp-equal-helper))))

(defthm not-<-car-when->=maxelem-free
  (implies (and (<= (maxelem free) x)
                (subsetp-equal lst free)
                (consp lst))
           (not (< x (car lst))))
  :hints (("Goal" :use (not-<-car-when->=maxelem
                        (:instance maxelem-when-subsetp-equal (lst1 lst) (lst2 free)))
           :in-theory (disable not-<-car-when->=maxelem MAXELEM-WHEN-SUBSETP-EQUAL))))

(defthm not-less-than-maxelem-of-small-range-lemma
  (implies (and (<= (MAXELEM bigrange) k) ;bigrange is a free var
                (subsetp-equal smallrange bigrange))
           (equal (< k (MAXELEM smallrange))
                  (if (consp smallrange)
                      nil
                    (< k (negative-infinity)))))
  :hints (("Goal" :use (:instance maxelem-when-subsetp-equal (lst1 smallrange) (lst2 bigrange))
           :in-theory (disable maxelem-when-subsetp-equal))))

(defthm maxelem-of-reverse-list
  (implies (rational-listp lst)
           (equal (maxelem (reverse-list lst))
                  (maxelem lst)))
  :hints (("Goal" :in-theory (enable reverse-list maxelem))))
