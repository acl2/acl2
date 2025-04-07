; BV Library: leftrotate
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat-def")
(include-book "slice-def")
(include-book "getbit-def")
(include-book "../arithmetic-light/power-of-2p")
(include-book "../arithmetic-light/lg-def")
(local (include-book "../arithmetic-light/lg"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/plus-and-minus"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "bvcat"))
(local (include-book "unsigned-byte-p"))

(local (in-theory (disable expt)))

;; Rotate VAL to the left by AMT positions within a field of width WIDTH.  We
;; reduce the rotation amount modulo the width.
(defund leftrotate (width amt val)
  (declare (xargs :guard (and (natp width)
                              (natp amt)
                              (integerp val))
                  :split-types t)
           (type integer val amt)
           (type (integer 0 *) width))
  (if (= 0 width)
      0
    (let* ((amt (mod (ifix amt) width)))
      (bvcat (- width amt)
             (slice (+ -1 width (- amt)) 0 val)
             amt
             (slice (+ -1 width) (+ width (- amt)) val)))))

(defthm unsigned-byte-p-of-leftrotate-same
  (implies (natp size)
           (unsigned-byte-p size (leftrotate size x y)))
  :hints (("Goal" :in-theory (enable leftrotate natp))))

(defthm unsigned-byte-p-of-leftrotate
  (implies (and (<= size2 size1)
                (integerp size1)
                (natp size2))
           (unsigned-byte-p size1 (leftrotate size2 x y)))
  :hints (("Goal" :in-theory (enable leftrotate natp))))

(defthm leftrotate-of-0-arg1
  (equal (leftrotate 0 amt val)
         0)
  :hints (("Goal" :in-theory (enable leftrotate))))

(defthm leftrotate-of-0-arg2
  (equal (leftrotate width 0 val)
         (bvchop width val))
  :hints (("Goal" :in-theory (enable leftrotate))))

(defthm leftrotate-of-0-arg3
  (equal (leftrotate width amt 0)
         0)
  :hints (("Goal" :in-theory (enable leftrotate))))

(defthm leftrotate-of-plus-same
  (implies (and (integerp amt)
                (natp size))
           (equal (leftrotate size (+ size amt) val)
                  (leftrotate size amt val)))
  :hints (("Goal" :in-theory (enable leftrotate))))

(defthm leftrotate-when-not-integerp-arg2
  (implies (not (integerp amt))
           (equal (leftrotate width amt val)
                  (leftrotate width 0 val)))
  :hints (("Goal" :in-theory (enable leftrotate))))

(defthm leftrotate-same
  (implies (natp size)
           (equal (leftrotate size size val)
                  (bvchop size val)))
  :hints (("Goal" :in-theory (enable leftrotate))))

(defthm leftrotate-of-mod-same
  (implies (and (natp width)
                (integerp amt))
           (equal (leftrotate width (mod amt width) val)
                  (leftrotate width amt val)))
  :hints (("Goal" :in-theory (enable leftrotate))))

(defthm leftrotate-of-leftrotate
  (implies (and (natp width)
                (integerp amt1)
                (integerp amt2))
           (equal (leftrotate width amt1 (leftrotate width amt2 val))
                  (leftrotate width (+ amt1 amt2) val)))
  :hints (("Goal" :in-theory (enable leftrotate mod-sum-cases))))

(defthmd leftrotate-open-when-constant-shift-amount
  (implies (syntaxp (and (quotep amt)
                         (quotep width)))
           (equal (leftrotate width amt val)
                  (if (equal width 0)
                      0
                    (let* ((amt (mod (ifix amt) width) ;(bvchop (integer-length (+ -1 width)) amt)
                                ))
                      (bvcat (- width amt)
                             (slice (+ -1 width (- amt)) 0 val)
                             amt
                             (slice (+ -1 width)
                                    (+ width (- amt))
                                    val))))))
  :hints (("Goal" :in-theory (enable leftrotate))))

(defthm bvchop-of-leftrotate-low
  (implies (and (<= size amount) ;this case
                (<= amount width)
                (natp size)
                (posp width)
                (natp amount))
           (equal (bvchop size (leftrotate width amount val))
                  (slice (+ -1 (- amount) size width)
                         (+ (- amount) width)
                         val)))
  :hints (("Goal" :cases ((equal amount width))
           :in-theory (enable leftrotate))))

;combine the cases?
(defthm bvchop-of-leftrotate-not-low
  (implies (and (< amount size)  ;this case
                (<= size width)
                (natp size)
                (posp width)
                (natp amount))
           (equal (bvchop size (leftrotate width amount val))
                  (bvcat (- size amount)
                         val
                         amount
                         (slice (+ -1 width)
                                (+ (- amount) width)
                                val) )))
  :hints (("Goal" ;:cases ((equal amount width))
           :in-theory (enable leftrotate))))

;; is there a nicer way to comvine the cases?
(defthm bvchop-of-leftrotate-both
  (implies (and (<= size width)
                (<= amount width)
                (natp size)
                (posp width)
                (natp amount))
           (equal (bvchop size (leftrotate width amount val))
                  (if (< amount size)
                      (bvcat (- size amount)
                             val
                             amount
                             (slice (+ -1 width)
                                    (+ (- amount) width)
                                    val) )
                    (slice (+ -1 (- amount) size width)
                           (+ (- amount) width)
                           val))))
  :hints (("Goal" :cases ((< amount size)))))

(defthm slice-of-leftrotate
  (implies (and (< highbit width) ;otherwise we can tighten the slice
                (<= lowbit highbit) ;otherwise we get 0?
                (natp lowbit)
                (natp highbit)
                (posp width)
                (natp amt))
           (equal (slice highbit lowbit (leftrotate width amt val))
                  (if (< highbit (mod amt width))
                      (slice (+ highbit width (- (mod amt width)))
                             (+ lowbit width (- (mod amt width)))
                             val)
                    (if (< lowbit (mod amt width))
                        (bvcat (+ highbit (- (mod amt width)) 1)
                               (slice (+ -1 width (- (mod amt width))) 0 val)
                               (- (mod amt width) lowbit)
                               (slice (+ -1 width)
                                      (+ lowbit width (- (mod amt width)))
                                      val))
                      (slice (+ highbit (- (mod amt width)))
                             (+ lowbit (- (mod amt width)))
                             val)))))
  :hints (("Goal" :in-theory (enable leftrotate natp))))

(local
 (defthm getbit-of-leftrotate-high
   (implies (and (<= amt n) ; this case
                 (< n width)
                 (< amt width)
                 (natp n)
                 (natp amt)
                 (natp width))
            (equal (getbit n (leftrotate width amt x))
                   (getbit (- n amt) x)))
   :hints (("Goal" :in-theory (e/d (getbit leftrotate) (
                                                        ))))))

(local
 (defthm getbit-of-leftrotate-low
   (implies (and (< n amt) ; this case
                 (< n width)
                 (< amt width)
                 (natp n)
                 (natp amt)
                 (natp width))
            (equal (getbit n (leftrotate width amt x))
                   (getbit (+ width (- amt) n) x)))
   :hints (("Goal" :in-theory (e/d (getbit leftrotate) (
                                                        ))))))

;; todo: restrict to the case when we can resolve the (< n width) test?
(defthm getbit-of-leftrotate
  (implies (and ;(< amt width) ;gen?
            (natp n)
            (natp amt)
            (natp width))
           (equal (getbit n (leftrotate width amt x))
                  (if (< n width)
                      (if (< n (mod amt width)) ; this case
                          (getbit (+ width (- (mod amt width)) n) x)
                        (getbit (- n (mod amt width)) x))
                    0)))
  :hints (("Goal" :in-theory (e/d (getbit leftrotate) (
                                                       )))))

;; no mod in rhs
;; todo: restrict to the case when we can resolve the (< n width) test?
;; "Simple" because there is no mod in the RHS.
(defthmd getbit-of-leftrotate-simple
  (implies (and (< amt width) ; avoids mod in rhs
                (natp n)
                (natp amt)
                (natp width))
           (equal (getbit n (leftrotate width amt x))
                  (if (< n width)
                      (if (< n amt)
                          (getbit (+ width (- amt) n) x)
                        (getbit (- n amt) x))
                    0)))
  :hints (("Goal" :in-theory (e/d (getbit leftrotate) ()))))

(defthm equal-of-leftrotate-and-leftrotate
  (implies (natp size)
           (equal (equal (leftrotate size n x) (leftrotate size n y))
                  (equal (bvchop size x) (bvchop size y))))
  :hints (("Goal" :cases ((equal 0 size))
           :in-theory (enable leftrotate))))

;; This may fail to match if the first mention of X has been chopped down.
(defthmd bvcat-of-slice-becomes-leftrotate
  (implies (and (equal high (+ -1 highsize lowsize))
                (natp lowsize)
                (posp highsize))
           (equal (bvcat highsize x lowsize (slice high highsize x))
                  (leftrotate (+ highsize lowsize) lowsize x)))
  :hints (("Goal" :in-theory (enable leftrotate))))

(theory-invariant (incompatible (:definition leftrotate)
                                (:rewrite bvcat-of-slice-becomes-leftrotate)))

;; special case when the slice is a single bit so we have getbit instead
(defthmd bvcat-of-getbit-becomes-leftrotate
  (implies (and (natp lowsize)
                (posp highsize))
           (equal (bvcat highsize x 1 (getbit highsize x))
                  (leftrotate (+ highsize 1) 1 x)))
  :hints (("Goal" :in-theory (enable leftrotate))))

(theory-invariant (incompatible (:definition leftrotate)
                                (:rewrite bvcat-of-getbit-becomes-leftrotate)))

(defthm leftrotate-of-bvchop-arg2-core
  (implies (power-of-2p width)
           (equal (leftrotate width (bvchop (lg width) amt) x)
                  (leftrotate width amt x)))
  :hints (("Goal" :in-theory (enable leftrotate bvchop))))

(defthm leftrotate-of-bvchop-arg2
  (implies (and (syntaxp (and (quotep width)
                              (quotep size)))
                (equal size (lg width))
                (power-of-2p width))
           (equal (leftrotate width (bvchop size amt) x)
                  (leftrotate width amt x)))
  :hints (("Goal" :use (:instance leftrotate-of-bvchop-arg2-core (amt amt))
           :in-theory (disable leftrotate-of-bvchop-arg2-core))))

(defthm leftrotate-of-bvchop-arg3
  (implies (natp width)
           (equal (leftrotate width amt (bvchop width x))
                  (leftrotate width amt x)))
  :hints (("Goal" :in-theory (enable leftrotate))))

(defthm leftrotate-subst-arg2
  (implies (and (equal (bvchop size amt) k)
                (syntaxp (and (quotep k)
                              (not (quotep amt))))
                (equal size (lg width))
                (power-of-2p width))
           (equal (leftrotate width amt x)
                  (leftrotate width k x)))
  :hints (("Goal" :in-theory (enable leftrotate BVCHOP))))
