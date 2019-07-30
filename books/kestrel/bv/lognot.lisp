; BV Library: lognot
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(in-package "ACL2")

(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "../arithmetic-light/integerp"))
(local (include-book "../arithmetic-light/plus-and-times"))

(in-theory (disable lognot))

;move?
;rename
(defthm integerp-all-ones
  (implies (and (rationalp i)
                (posp j))
           (equal (integerp (+ (/ j)
                               (* i (/ j))))
                  (equal 0 (mod (+ 1 i) j))))
  :hints (("Goal" :in-theory (e/d (equal-of-0-and-mod) (mod-sum-cases)))))

(defthm lognot-when-not-integerp
  (implies (not (integerp i))
           (equal (lognot i)
                  -1))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-of-lognot
  (equal (lognot (lognot i))
         (ifix i))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm <-of-lognot-and-0
  (equal (< (lognot i) 0)
         (if (integerp i)
             (<= 0 i)
           t))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-of-all-ones
  (implies (natp n)
           (equal (lognot (+ -1 (expt 2 n)))
                  (- (expt 2 n))))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-of---of-expt
  (implies (natp size)
           (equal (lognot (- (expt 2 size)))
                  (+ -1 (expt 2 size))))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm equal-of-lognot-and-constant
  (implies (syntaxp (quotep k))
           (equal (equal k (lognot i))
                  (and (equal (ifix i) (lognot k))
                       (integerp k))))
  :hints (("Goal" :in-theory (enable lognot))))

(defthmd lognot-of-floor-of-2
  (implies (integerp i)
           (equal (lognot (floor i 2))
                  (floor (lognot i) 2)))
  :hints (("Goal" :cases ((equal 0 (mod i 2)))
           :in-theory (enable lognot))))

(defthmd floor-of-lognot-and-2
  (implies (integerp i)
           (equal (floor (lognot i) 2)
                  (lognot (floor i 2))))
  :hints (("Goal" :by lognot-of-floor-of-2)))

(defthm lognot-of-*-of-2
  (implies (integerp i)
           (equal (lognot (* 2 i))
                  (+ 1 (* 2 (lognot i)))))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-of-+-1-of-*-2
  (implies (integerp i)
           (equal (lognot (+ 1 (* 2 i)))
                  (* 2 (lognot i))))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm integerp-of-*-1/2-of-lognot
  (implies (integerp i)
           (equal (integerp (* 1/2 (lognot i)))
                  (not (integerp (* 1/2 i)))))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm mod-of-lognot-of-2
  (implies (integerp i)
           (equal (mod (lognot i) 2)
                  (- 1 (mod i 2))))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm <-of-lognot-and-expt
  (implies (and (natp n)
                (integerp i))
           (equal (< (lognot i) (expt 2 n))
                  (< (+ -1 (- (expt 2 n))) i)))
  :hints (("Goal"
           :cases ((< (lognot i) (expt 2 n)))
           :in-theory (enable lognot))))

(defthm mod-of-lognot-and-expt
  (implies (and (integerp i)
                (natp n))
           (equal (mod (lognot i) (expt 2 n))
                  (+ (expt 2 n) (lognot (mod i (expt 2 n))))))
  :hints (("Goal" :in-theory (enable lognot mod-sum-cases))))

(defthm floor-of-lognot-and-expt
  (implies (and (integerp i)
                (natp n))
           (equal (floor (lognot i) (expt 2 n))
                  (lognot (floor i (expt 2 n)))))
  :hints (("Goal" :in-theory (e/d (lognot
                                   floor-of-sum)
                                  (floor-minus-arg1-hack)))))

(defthm <-of---and-lognot
  (implies (and (integerp i)
                (integerp j))
           (equal (< (- j) (lognot i))
                  (< i (+ -1 j))))
  :hints (("Goal" :cases ((< i (+ -1 j)))
           :in-theory (enable lognot))))

;gen?
(defthm <-of-lognot-and---of-expt
  (implies (and (natp n)
                (integerp i))
           (equal (< (lognot i) (- (expt 2 n)))
                  (<= (expt 2 n) i)))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-of-+-of-expt
  (implies (and (integerp i)
                (natp n))
           (equal (lognot (+ (expt 2 n) i))
                  (+ (- (expt 2 n)) (lognot i))))
  :hints (("Goal" :in-theory (enable lognot))))
