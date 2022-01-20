; A simple random number generator
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See https://en.wikipedia.org/wiki/Linear_congruential_generator
;; This is the generator that that article calls minstd_rand.

(in-package "ACL2")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(in-theory (disable mv-nth))

;; The Mersenne prime M_31, used as the modulus of the generator.
(defconst *m31* (- (expt 2 31) 1))

;; The multipler of the generator.
(defconst *minstd-rand-multiplier* 48271)

;; Recognize a (pseudo-random) value.
;; TODO: Exclude 0?
(defund minstd-randp (rand)
  (declare (xargs :guard t))
  (and (natp rand)
       (< rand *m31*)))

(defthm minstd-randp-forward
  (implies (minstd-randp rand)
           (and (natp rand)
                (< rand *m31*)))
  :rule-classes :forward-chaining)

;; Compute the next pseudo-random value from the current value, RAND.
;; TODO: Consider optimizing this.
(defund minstd-rand-next (rand)
  (declare (xargs :guard (minstd-randp rand)))
  (mod (* *minstd-rand-multiplier* rand) *m31*))

;; TODO: Prove the we can never generate 0 (and thus get stuck), given a
;; current value that satisfies minstd-randp.

(defthm minstd-randp-of-minstd-rand-next
  (implies (minstd-randp rand)
           (minstd-randp (minstd-rand-next rand)))
  :hints (("Goal" :in-theory (enable minstd-rand-next minstd-randp))))

;; Returns (mv val next) where VAL is a pseudo-random number in the interval
;; [0, max] and NEXT is the next random value produced by the generator.
(defund extract-bounded-val-using-minstd-rand (max rand)
  (declare (xargs :guard (and (natp max)
                              (< max *m31*)
                              (minstd-randp rand))))
  (mv (mod rand (+ 1 max))
      (minstd-rand-next rand)))

(defthm natp-of-mv-nth-0-of-extract-bounded-val-using-minstd-rand
  (implies (and (natp max)
                (minstd-randp rand))
           (natp (mv-nth 0 (extract-bounded-val-using-minstd-rand max rand))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable extract-bounded-val-using-minstd-rand))))

(defthm <=-of-mv-nth-0-of-extract-bounded-val-using-minstd-rand
  (implies (and (natp max)
                (minstd-randp rand))
           (<= (mv-nth 0 (extract-bounded-val-using-minstd-rand max rand)) max))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable extract-bounded-val-using-minstd-rand))))

(defthm minstd-randp-of-mv-nth-1-of-extract-bounded-val-using-minstd-rand
  (implies (and (natp max)
                (minstd-randp rand))
           (minstd-randp (mv-nth 1 (extract-bounded-val-using-minstd-rand max rand))))
  :hints (("Goal" :in-theory (enable extract-bounded-val-using-minstd-rand))))
