; A simple random number generator
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See https://en.wikipedia.org/wiki/Linear_congruential_generator
;; This is the generator that that article calls minstd_rand0.

(in-package "ACL2")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(in-theory (disable mv-nth))

;; The Mersenne prime M_31, used as the modulus of the generator.
(defconst *m31* (- (expt 2 31) 1))

;; The multipler of the generator, equal to 7^5.
(defconst *minstd-rand0-multiplier* 16807)

;; Recognize a (pseudo-random) value.
;; TODO: Exclude 0?
(defund minstd-rand0p (rand)
  (declare (xargs :guard t))
  (and (natp rand)
       (< rand *m31*)))

(defthm minstd-rand0p-forward
  (implies (minstd-rand0p rand)
           (and (natp rand)
                (< rand *m31*)))
  :rule-classes :forward-chaining)

;; Compute the next pseudo-random value from the current value, RAND.
;; TODO: Consider optimizing this.
(defund minstd-rand0-next (rand)
  (declare (xargs :guard (minstd-rand0p rand)))
  (mod (* *minstd-rand0-multiplier* rand) *m31*))

;; TODO: Prove the we can never generate 0 (and thus get stuck), given a
;; current value that satisfies minstd-randp.

(defthm minstd-rand0p-of-minstd-rand0-next
  (implies (minstd-rand0p rand)
           (minstd-rand0p (minstd-rand0-next rand)))
  :hints (("Goal" :in-theory (enable minstd-rand0-next minstd-rand0p))))

;; Returns (mv val next) where VAL is a pseudo-random number in the interval
;; [0, max] and NEXT is the next random value produced by the generator.
(defund extract-bounded-val-using-minstd-rand0 (max rand)
  (declare (xargs :guard (and (natp max)
                              (< max *m31*)
                              (minstd-rand0p rand))))
  (mv (mod rand (+ 1 max))
      (minstd-rand0-next rand)))

(defthm natp-of-mv-nth-0-of-extract-bounded-val-using-minstd-rand0
  (implies (and (natp max)
                (minstd-rand0p rand))
           (natp (mv-nth 0 (extract-bounded-val-using-minstd-rand0 max rand))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable extract-bounded-val-using-minstd-rand0))))

(defthm <=-of-mv-nth-0-of-extract-bounded-val-using-minstd-rand0
  (implies (and (natp max)
                (minstd-rand0p rand))
           (<= (mv-nth 0 (extract-bounded-val-using-minstd-rand0 max rand)) max))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable extract-bounded-val-using-minstd-rand0))))

(defthm minstd-rand0p-of-mv-nth-1-of-extract-bounded-val-using-minstd-rand0
  (implies (and (natp max)
                (minstd-rand0p rand))
           (minstd-rand0p (mv-nth 1 (extract-bounded-val-using-minstd-rand0 max rand))))
  :hints (("Goal" :in-theory (enable extract-bounded-val-using-minstd-rand0))))
