; Rules about sets
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/sets/sets" :dir :system)
(include-book "kestrel/lists-light/subrange" :dir :system) ;todo: just include the def?
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (in-theory (disable SET::PICK-A-POINT-SUBSET-STRATEGY SET::DOUBLE-CONTAINMENT SET::DOUBLE-CONTAINMENT-expensive)))

;trying
(in-theory (disable SET::DIFFERENCE-OVER-UNION))
(in-theory (disable DIFFERENCE-OF-UNION))
(in-theory (disable DIFFENCE-OF-UNION-LEMMA-ALT))
(in-theory (disable DIFFERENCE-OF-DIFFERENCE))

;; (thm
;;  (implies (and (equal (set::insert a x) (set::insert a y))
;;                (set::setp x)
;;                (set::setp y))
;;           (or (equal x y)
;;               (equal x (set::insert a y))
;;               (equal x (set::delete a y)))))

;move
(defthm 2set-when-not-consp
  (IMPLIES (NOT (CONSP ADDRS))
           (equal (LIST::2SET ADDRS)
                  nil))
  :hints (("Goal" :in-theory (enable LIST::2SET))))

;rephrase? ;expensive?
(defthmd setp-hack
  (implies (and s (set::setp s))
           (consp s))
  :hints (("Goal" :in-theory (enable set::setp))))

;seems expensive
(defthmd consp-set-hack
  (implies (not (set::empty s))
           (consp s))
  :hints (("Goal" :in-theory (enable setp-hack set::empty))))

;bad to mix sets and lists?
(defthm consp-of-insert
  (consp (set::insert a s))
  :hints (("Goal" :in-theory (enable set::insert consp-set-hack))))

;; (defthm subset-union-helper
;;   (implies (set::subset x y)
;;            (set::subset x (set::union a y))))

;trying...
(in-theory (disable list::2set))

;make an non-alt version?
;really this mixes sets and sequences
(defthm insert-of-insert-adjacent
  (implies (and (equal m (+ -1 n))
                (natp n)
                (< 0 n)
                (< n (len lst)))
           (equal (SET::INSERT (NTH m lst) (SET::INSERT (NTH n lst ) set))
                  (SET::union (list::2set (subrange (+ -1 n) n lst)) set)))
  :hints (("Goal" :expand ((TAKE 2 (NTHCDR (+ -1 N) LST))
                           (SUBRANGE (+ -1 N) N LST) (NTH 1 LST))
           :in-theory (e/d (nth
                            nthcdr
                            CDR-OF-NTHCDR
                            )
                           (NTH-OF-CDR
                            NTHCDR-OF-CONS
                               ;;LIST::NTH-OF-CDR
                            ))
           :do-not '(generalize eliminate-destructors))))

;bozo prove an equivalence?
(defthm 2set-of-true-list-fix
  (equal (list::2set (true-list-fix lst))
         (list::2set lst))
  :hints (("Goal" :in-theory (enable list::2set true-list-fix))))
