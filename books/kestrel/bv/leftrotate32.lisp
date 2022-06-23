; BV Library: leftrotate for size 32
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "leftrotate")
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/plus-and-minus"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "bvcat"))

(local (in-theory (disable unsigned-byte-p)))

(defund leftrotate32 (amt val)
  (declare (type integer amt val))
  (leftrotate 32 amt val))

(defthm leftrotate32-of-0-arg1
  (equal (leftrotate32 0 val)
         (bvchop 32 val))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthm leftrotate32-of-0-arg2
  (equal (leftrotate32 amt 0)
         0)
  :hints (("Goal" :in-theory (enable leftrotate32))))

;todo gen the 5 and move
(defthm leftrotate-32-of-bvchop-5
  (implies (natp amt)
           (equal (leftrotate 32 (bvchop 5 amt) val)
                  (leftrotate 32 (ifix amt) val)))
  :hints (("Goal" :in-theory (enable bvchop))))

;todo gen the 5
(defthm leftrotate32-of-bvchop-5
  (implies (natp amt)
           (equal (leftrotate32 (bvchop 5 amt) val)
                  (leftrotate32 amt val)))
  :hints (("Goal" :in-theory (enable leftrotate32))))

;justifies the correctness of some operations performed by Axe
(defthm unsigned-byte-p-32-of-leftrotate32
  (unsigned-byte-p 32 (leftrotate32 x y))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthm unsigned-byte-p-of-leftrotate32
  (implies (and (<= 32 size)
                (integerp size))
           (unsigned-byte-p size (leftrotate32 x y)))
  :hints (("Goal" :in-theory (enable leftrotate32 leftrotate))))

;or should leftrotate32 be among the functions we can take the size of?
(defthm bvchop-of-leftrotate32-does-nothing
  (implies (and (<= 32 size)
                (integerp size))
           (equal (bvchop size (leftrotate32 x y))
                  (leftrotate32 x y))))

(defthm leftrotate32-of-bvchop-arg2
  (implies (and (<= 32 size)
                (integerp size))
           (equal (leftrotate32 amt (bvchop size x))
                  (leftrotate32 amt x)))
  :hints (("Goal" :in-theory (enable leftrotate32 leftrotate))))

(defthm leftrotate32-of-bvchop
  (implies (natp amt)
           (equal (leftrotate32 (bvchop 32 amt) val)
                  (leftrotate32 amt val)))
  :hints (("Goal" :in-theory (disable leftrotate32 leftrotate32-of-bvchop-5)
           :use ((:instance leftrotate32-of-bvchop-5 (amt amt))
                 (:instance leftrotate32-of-bvchop-5 (amt (bvchop 32 amt)))))))

;do not remove.  this helps justify how Axe translates leftrotate32 to STP:
(defthm leftrotate32-of-mod
  (implies (natp amt)
           (equal (leftrotate32 (mod amt 32) val)
                  (leftrotate32 amt val)))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthmd leftrotate-becomes-leftrotate32
  (equal (leftrotate 32 amt val)
         (leftrotate32 amt val))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(theory-invariant (incompatible (:rewrite leftrotate-becomes-leftrotate32) (:definition leftrotate32)))

(defthmd leftrotate32-open-when-constant-shift-amount
  (implies (syntaxp (quotep amt))
           (equal (leftrotate32 amt val)
                  (let* ((amt (mod (nfix amt) 32) ;(bvchop 5 amt)
                              ))
                    (bvcat (- 32 amt)
                           (slice (- 31 amt) 0 val)
                           amt (slice 31 (+ 32 (- amt)) val)))))
  :hints (("Goal" :expand (leftrotate32 amt val)
           :in-theory (enable leftrotate))))

(defthm slice-of-leftrotate32-high
  (implies (and (<= amt low)
                (<= low high)
                (<= high 31)
                (unsigned-byte-p 5 amt) ;drop
                (natp high)
                (natp low)
                (natp amt))
           (equal (slice high low (leftrotate32 amt x))
                  (slice (- high amt) (- low amt) x)))
  :hints (("Goal" :in-theory (e/d (leftrotate leftrotate32) ()))))

(defthmd bvchop-of-leftrotate32-both
  (implies (and (<= size 32)
                (<= amount 32)
                (natp size)
                (natp amount))
           (equal (bvchop size (leftrotate32 amount val))
                  (if (< amount size)
                      (bvcat (- size amount)
                             val
                             amount
                             (SLICE (+ -1 32)
                                    (+ (- AMOUNT) 32)
                                    VAL) )
                    (slice (+ -1 (- AMOUNT) SIZE 32)
                           (+ (- AMOUNT) 32)
                           val))))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthm slice-of-leftrotate32
  (implies (and (< highbit 32) ;otherwise we can tighten the slice
                (<= lowbit highbit) ;otherwise we get 0?
                (natp lowbit)
                (natp highbit)
                (natp amt))
           (equal (slice highbit lowbit (leftrotate32 amt val))
                  (if (< highbit (mod amt 32))
                      (slice (+ highbit 32 (- (mod amt 32)))
                             (+ lowbit 32 (- (mod amt 32)))
                             val)
                    (if (< lowbit (mod amt 32))
                        (bvcat (+ highbit (- (mod amt 32)) 1)
                               (slice (+ -1 32 (- (mod amt 32))) 0 val)
                               (- (mod amt 32) lowbit)
                               (slice (+ -1 32)
                                      (+ lowbit 32 (- (mod amt 32)))
                                      val))
                      (slice (+ highbit (- (mod amt 32)))
                             (+ lowbit (- (mod amt 32)))
                             val)))))
  :hints (("Goal" :in-theory (enable leftrotate32 natp))))

(defthm equal-of-leftrotate32-and-leftrotate32
  (equal (equal (leftrotate32 n x) (leftrotate32 n y))
         (equal (bvchop 32 x) (bvchop 32 y)))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthm getbit-of-leftrotate32-low
  (implies (and (< n amt)
                (<= n 31)
                (unsigned-byte-p 5 amt)
                (natp n)
                (natp amt))
           (equal (getbit n (leftrotate32 amt x))
                  (getbit (+ 32 (- amt) n) x)))
  :hints (("Goal" :in-theory (e/d (getbit unsigned-byte-p)
                                  (bvchop-1-becomes-getbit
                                   leftrotate32
                                   slice-becomes-getbit)))))

(defthm getbit-of-leftrotate32-high
  (implies (and (<= amt n) ;todo: other case! see rules for leftrotate
                (<= n 31)
                (unsigned-byte-p 5 amt)
                (natp n)
                (natp amt))
           (equal (getbit n (leftrotate32 amt x))
                  (getbit (- n amt) x)))
  :hints (("Goal" :in-theory (e/d (getbit) (bvchop-1-becomes-getbit
                                            leftrotate32
                                            slice-becomes-getbit)))))

;drop the syntap hyp?
(defthmd getbit-of-leftrotate32
  (implies (and (syntaxp (and (quotep amt)
                              (quotep n)))
                (natp n)
                (natp amt))
           (equal (getbit n (leftrotate32 amt x))
                  (if (< n 32)
                      (if (< n (mod amt 32))
                          (getbit (+ 32 (- (mod amt 32)) n) x)
                        (getbit (- n (mod amt 32)) x))
                    0)))
  :hints (("Goal" :in-theory (enable leftrotate32))))

;; "Simple" because there is no mod in the RHS.
;drop the syntap hyp?
(defthmd getbit-of-leftrotate32-simple
  (implies (and (syntaxp (and (quotep amt)
                              (quotep n)))
                (< amt 32) ; avoids mod in rhs
                (natp n)
                (natp amt))
           (equal (getbit n (leftrotate32 amt x))
                  (if (< n 32)
                      (if (< n amt)
                          (getbit (+ 32 (- amt) n) x)
                        (getbit (- n amt) x))
                    0)))
  :hints (("Goal" :in-theory (enable leftrotate32))))
