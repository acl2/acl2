(in-package "ACL2")

; A lightweight book about the built-in functions evens and odds
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

(in-theory (disable evens odds))

(defthm symbol-listp-of-evens
  (implies (symbol-listp l)
           (symbol-listp (evens l)))
  :hints (("Goal" :induct (evens l)
           :in-theory (enable evens))))

(defthm cons-of-evens
  (equal (consp (evens l))
         (consp l))
  :hints (("Goal" ;:induct (evens l)
           :in-theory (enable evens))))

(defthm symbol-listp-of-odds
  (implies (symbol-listp l)
           (symbol-listp (odds l)))
  :hints (("Goal" ;:induct (odds l)
           :in-theory (enable odds))))

(defthm cons-of-odds
  (equal (consp (odds l))
         (<= 2 (len l)))
  :hints (("Goal" :in-theory (enable odds))))

(defthmd intersection-equal-when-intersection-equal-of-evens
  (implies (intersection-equal (evens l1) l2)
           (intersection-equal l1 l2))
  :hints (("Goal" :in-theory (enable evens))))

(defthmd intersection-equal-when-intersection-equal-of-odds
  (implies (intersection-equal (odds l1) l2)
           (intersection-equal l1 l2))
  :hints (("Goal" :in-theory (enable odds
                                     intersection-equal-when-intersection-equal-of-evens
                                     intersection-equal))))

;; not sure which is better
(defthmd evens-of-cddr
  (equal (evens (cddr x))
         (cdr (evens x)))
  :hints (("Goal" :in-theory (enable evens))))

(defthm not-intersection-equal-when-not-intersection-equal-of-evens-and-intersection-equal-of-odds
  (implies (and (not (intersection-equal (evens x) y))
                (not (intersection-equal (odds x) y)))
           (not (intersection-equal x y)))
  :hints (("Goal" :expand (evens x)
           :in-theory (enable intersection-equal odds))))

(defthm not-member-equal-of-evens-when-not-member-equal
  (implies (not (member-equal a l))
           (not (member-equal a (evens l))))
  :hints (("Goal" :in-theory (enable evens))))

(defthm not-intersection-equal-of-evens-and-odds-when-no-duplicatesp-equal
  (implies (no-duplicatesp-equal l)
           (not (intersection-equal (evens l) (odds l))))
  :hints (("Goal" :expand (EVENS L)
           :in-theory (enable evens odds no-duplicatesp-equal))))

(defthm not-member-equal-of-odds-when-not-member-equal
  (implies (not (member-equal a l))
           (not (member-equal a (evens l))))
  :hints (("Goal" :in-theory (enable odds))))

(defthm no-duplicatesp-equal-of-evens
  (implies (no-duplicatesp-equal l)
           (no-duplicatesp-equal (evens l)))
  :hints (("Goal" :expand (evens l)
           :induct (evens l)
           :in-theory (e/d (evens no-duplicatesp-equal) (evens-of-cddr)))))

(defthm no-duplicatesp-equal-of-odds
  (implies (no-duplicatesp-equal l)
           (no-duplicatesp-equal (odds l)))
  :hints (("Goal" :in-theory (enable odds))))
