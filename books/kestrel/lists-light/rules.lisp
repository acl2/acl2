; Mixed rules about lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Organize these rules into simpler books.

(include-book "repeat")
(include-book "all-equal-dollar")
(include-book "count-occs")
(include-book "kestrel/utilities/polarity" :dir :system)
;(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;rewrite (EQUAL (LEN L) 1) ?

(defthm len-of-remove-equal
  (equal (len (remove-equal x l))
         (- (len l) (count-occs x l)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;           :induct (true-listp l)
           :in-theory (e/d (remove (:induction true-listp))
                           (;REMOVE-CAR-FROM-CDR-2
                            ;LEN-CDR-BOTH len-cdr
                            )))))

;do we have a congruence rule for true-list-fix?

;what is open-small-nthcdr?
(theory-invariant (incompatible (:rewrite 3-cdrs) (:rewrite open-small-nthcdr)))

;; ;BOZO gen! see NTH-OF-SUBRANGE-GEN
;; (defthm nth-of-subrange
;;   (implies (and (integerp n)
;;                 (<= 0 n))
;;            (equal (nth n (SUBRANGE 0 n lst))
;;                   (nth n lst))))

;(in-theory (disable list::fix-of-update-nth)) ;bozo remove in favor of mine

;yuck?
(defthmd cons-equal-rewrite-constant-version
  (implies (and (syntaxp (quotep k))
                (consp k))
           (equal (equal k z)
                  (and (consp z)
                       (equal (car k) (car z))
                       (equal (cdr k) (cdr z))))))

;; Turns a hyp of (<= (len x) 0) into (equal (len x) 0).
(defthm len->-0-weaken
  (implies (syntaxp (want-to-weaken (< 0 (len x))))
           (equal (< 0 (len x))
                  (not (equal 0 (len x))))))

;; ;;TODO: These also loop with consp-cdr?
;; (theory-invariant (incompatible (:rewrite consp-to-len-bound) (:rewrite list::len-pos-rewrite)))
;; (theory-invariant (incompatible (:rewrite consp-to-len-bound) (:rewrite list::len-when-at-most-1)))
;; (theory-invariant (incompatible (:rewrite consp-to-len-bound) (:rewrite list::len-equal-0-rewrite)))
;; (theory-invariant (incompatible (:rewrite consp-to-len-bound) (:rewrite len-equal-0-rewrite-alt)))

;; (defthm nthcdr-when-equal-of-len-gen
;;   (implies (and (equal (len x) k) ; k is a free var
;;                 (syntaxp (quotep k))
;;                 (<= k n)
;;                 (integerp n)
;;                 (natp k))
;;            (equal (nthcdr n x)
;;                   (list::finalcdr x)))
;;   :hints (("Goal" :in-theory (enable nthcdr))))

;; (in-theory (disable nthcdr-when-equal-of-len))
