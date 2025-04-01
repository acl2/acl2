; Recognizing strictly decreasing lists
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

(include-book "all-natp")
(include-book "all-integerp")
(include-book "all-less")
(include-book "all-less-than-or-equal")

;; Check that NUMS are strictly decreasing.
;; Note that this implies that NUMS contains no duplicates.
(defund decreasingp (nums)
  (declare (xargs :guard (rational-listp nums)))
  (if (or (endp nums)
          (endp (cdr nums)))
      t
    (and (> (first nums) (second nums))
         (decreasingp (rest nums)))))

(defthm decreasingp-of-cdr
  (implies (decreasingp nums)
           (decreasingp (cdr nums)))
  :hints (("Goal" :in-theory (enable decreasingp))))

(defthm decreasingp-of-singleton
  (decreasingp (list num))
  :hints (("Goal" :in-theory (enable decreasingp))))

;; (defthmd maxelem-when-decreasingp
;;   (implies (decreasingp nums)
;;            (equal (maxelem nums)
;;                   (if (consp nums)
;;                       (car nums)
;;                     (negative-infinity))))
;;   :hints (("Goal" :in-theory (enable decreasingp))))

;; (local (in-theory (enable maxelem-when-decreasingp)))

(defthmd <-of-nth-1-and-nth-0-when-decreasingp
  (implies (and (decreasingp nums)
                (consp (cdr nums)))
           (< (nth 1 nums) (nth 0 nums)))
  :hints (("Goal" :in-theory (enable decreasingp))))

(defthmd <-of-nth-1-and-nth-0-when-decreasingp-alt
  (implies (and (decreasingp nums)
                (< 1 (len nums)))
           (< (nth 1 nums) (nth 0 nums)))
  :hints (("Goal" :in-theory (enable decreasingp))))

(defthmd not-<-of-nth-0-and-nth-1-when-decreasingp
  (implies (and (decreasingp nums)
                (all-natp nums) ; (nat-listp nums) ; gen?
                (consp nums)
                ;; (consp (cdr nums))
                )
           (not (< (nth 0 nums) (nth 1 nums))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable decreasingp))))

; try this instead
(defthmd not-<-of-nth-0-and-nth-1-when-decreasingp2
  (implies (and (decreasingp nums)
                ;(all-natp nums) ; (nat-listp nums) ; gen?
                ;(consp nums)
                (consp (cdr nums))
                )
           (not (< (nth 0 nums) (nth 1 nums))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable decreasingp))))

(defthm all-<-of-cdr-and-nth-0-when-decreasingp
  (implies (decreasingp nums)
           (all-< (cdr nums) (nth 0 nums)))
  :hints (("Goal" :in-theory (e/d (decreasingp nth all-<) ()))))

(defthm all-<=of-cdr-and-nth-0-when-decreasingp
  (implies (decreasingp nums)
           (all-<= (cdr nums) (nth 0 nums)))
  :hints (("Goal" :in-theory (enable decreasingp all-<=))))

(defthmd all-<=-when-<=-and-decreasingp ; add of-car to name
  (implies (and (<= (car nums) bound)
                (decreasingp nums))
           (all-<= nums bound))
  :hints (("Goal" :in-theory (enable all-<= decreasingp))))

(defthmd all-<-when-<-of-car-and-decreasingp
  (implies (and (< (car nums) bound)
                (decreasingp nums))
           (all-< nums bound))
  :hints (("Goal" :in-theory (enable all-< decreasingp))))

(local
  (defthm not-equal-of-nth-0-and-nth-1-when-decreasingp
    (implies (and (decreasingp nums)
                  (all-integerp nums)
                  (consp nums))
             (not (equal (nth 1 nums) (nth 0 nums))))
    :hints (("Goal" :in-theory (enable decreasingp all-integerp)))))
