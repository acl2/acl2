; More theorems about minelem
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "minelem")
(include-book "kestrel/lists-light/subrange" :dir :system)
(include-book "kestrel/lists-light/memberp-def" :dir :system)
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))

;; This book mixes maxelem with other non-built-in functions.

(defthm <=-of-minelem-when-memberp
  (implies (memberp a x)
           (<= (minelem x) a))
  :hints (("Goal" :in-theory (enable minelem))))

;more generally, minelem of a subbag...
(defthm minelem-of-subrange-and-subrange-hack
  (implies (and (integerp start)
                (integerp end)
                (< start end) ;not <=
                (<= 0 start)
                (< end (len lst)))
           (<= (MINELEM (SUBRANGE start end lst))
               (MINELEM (SUBRANGE (+ 1 start) end lst))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (TAKE-OF-NTHCDR ;subrange
                                   subrange-opener
                                   )
                                  (NTHCDR-OF-TAKE
                                   minelem-of-cons
                                   nth
                                   minelem-when-subsetp-equal))
           :use (:instance minelem-when-subsetp-equal
                           (lst1 (CONS (NTH (+ 1 START) LST)
                                       (SUBRANGE (+ 2 START) END LST)))
                           (lst2 (LIST* (NTH START LST)
                             (NTH (+ 1 START) LST)
                             (SUBRANGE (+ 2 START) END LST))))
           :do-not-induct t)))


(defthm minelem-of-subrange-tighten
  (implies (and (< end (len lst))
                (<= k (nth i lst))
                (<= i end)
                (natp i)
                (natp k)
                (integerp end)
                )
           (equal (< (minelem (subrange i end lst)) k)
                  (if (equal i end) ;unusual case
                      (< (nth i lst) k)
                    (< (minelem (subrange (+ 1 i) end lst)) k))))
  :hints (("Goal" :use (:instance subrange-opener (start i))
           :in-theory (e/d (;LIST::NTH-0-BECOMES-CAR
                            subrange
                            take
                            ;consp-cdr
                            )
                           (len ;take-of-nthcdr-becomes-subrange
                            ;CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER
;NTHCDR-OF-TAKE-BECOMES-SUBRANGE
                            ))
           :do-not '(generalize eliminate-destructors))))

(defthm minelem-of-subrange-peel-off-one
  (implies (and (<= k (nth n lst))
                (<= n end)
                (natp end)
                (< end (len lst))
                (natp n)
                (<= k (minelem (subrange (+ 1 n) end lst))))
           (<= k (minelem (subrange n end lst))))
  :hints (("Goal" :in-theory (e/d (subrange minelem)
                                  (;CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER
                                   ;NTHCDR-OF-TAKE-BECOMES-SUBRANGE
                                   ;TAKE-OF-NTHCDR-BECOMES-SUBRANGE
;list::equal-cons-cases
                                   ))
           :use (:instance subrange-opener (start n)))))
