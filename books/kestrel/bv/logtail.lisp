; BV Library: theorems about logtail
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "logtail-def")
(local (include-book "../library-wrappers/ihs-logops-lemmas"))
(local (include-book "unsigned-byte-p"))
(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/times-and-divides"))
(local (include-book "../arithmetic-light/divides"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "../arithmetic-light/floor-and-expt"))

(in-theory (disable logtail))

(defthm logtail-of-0-arg1
  (equal (logtail 0 x)
         (ifix x))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-of-0-arg2
  (equal (logtail pos 0)
         0)
   :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-when-not-integerp-arg2
  (implies (not (integerp i))
           (equal (logtail pos i)
                  0))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-becomes-0
  (implies (unsigned-byte-p n x)
           (equal (logtail n x)
                  0))
  :hints (("Goal" :in-theory (enable logtail unsigned-byte-p))))

(defthm logtail-when-not-posp-arg1
  (implies (not (posp size))
           (equal (logtail size x)
                  (ifix x)))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-shift
  (implies (and (integerp x)
                (natp n))
           (equal (logtail n (* x (expt 2 n)))
                  x))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-shift-alt
  (implies (and (integerp x)
                (natp n))
           (equal (logtail n (* (expt 2 n) x))
                  (ifix x)))
  :hints (("Goal" :use (:instance logtail-shift)
           :in-theory (disable logtail-shift))))

(defthm logtail-of-sum
  (implies (and (integerp (/ a (expt 2 m)))
                (integerp a)
                (integerp b)
                (integerp m)
                (<= 0 m))
           (equal (logtail m (+ a b))
                  (+ (logtail m a)
                     (logtail m b))))
  :hints (("Goal" :in-theory (enable logtail
                                     floor-when-multiple))))

;; (defthm logtail-of-logtail-worse
;;   (implies (and (natp i)
;;                 (integerp x)
;;                 (natp j))
;;            (equal (logtail j (logtail i x))
;;                   (logtail (+ i j) x)))
;;   :hints (("Goal" :in-theory (enable logtail expt-of-+))))

(defthm floor-of-logtail-and-expt
  (implies (and (natp n)
                (natp m)
                (integerp x)
                )
           (equal (floor (logtail m x) (expt 2 n))
                  (floor x (expt 2 (+ m n)))))
  :hints (("Goal" :in-theory (enable logtail expt-of-+))))

(defthm logtail-0-i-better
  (equal (logtail 0 i)
         (ifix i))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-of-minus-one
  (implies (natp n)
           (equal (logtail n -1)
                  -1))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-of-times-2
  (implies (and (natp n)
                (integerp x))
           (equal (logtail n (* 2 x))
                  (if (equal 0 n)
                      (* 2 x)
                    (logtail (+ -1 n) x))))
  :hints (("Goal" :in-theory (enable logtail))))

;; (defthm natp-of-logtail
;;   (implies (NATP X)
;;            (NATP (LOGTAIL HIGH X))))

(defthm logtail-of-logtail
  (implies (and (natp pos1)
                (natp pos))
           (equal (logtail pos1 (logtail pos i))
                  (logtail (+ pos pos1) i)))
  :hints (("Goal" :use (:instance logtail-logtail)
           :in-theory (disable logtail-logtail))))

(defthm logtail-of-minus-expt
  (implies (natp size)
           (equal (logtail size (- (expt 2 size)))
                  -1))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-non-neg
  (implies (<= 0 x)
           (equal (< (logtail n x) 0)
                  nil))
  :hints (("Goal"
           :use (:instance LOGTAIL-LESSP (pos n) (i x) (j 0))
           :in-theory (e/d (expt-of-+)
                           (LOGTAIL-LESSP)))))

(defthm logtail-shift-gen
  (implies (and (<= n size)
                (natp size)
                (natp n)
                (integerp x)
                )
           (equal (logtail size (* x (expt 2 n)))
                  (logtail (- size n) x)))
  :hints (("Goal" :in-theory (e/d (logtail expt-of-+
                                           floor-normalize-denominator)
                                  (floor-of-*-of-/-and-1)))))

(defthm logtail-shift-gen-alt
  (implies (and (<= n size)
                (natp size)
                (natp n)
                (integerp x)
                )
           (equal (logtail size (* (expt 2 n) x))
                  (logtail (- size n) x)))
  :hints (("Goal" :use (:instance logtail-shift-gen)
           :in-theory (disable logtail-shift-gen))))

(defthm logtail-of-expt
  (implies (and
            (natp n)
            (integerp size))
           (equal (logtail n (expt 2 size))
                  (if (<= n size)
                      (expt 2 (- size n))
                    0)))
  :hints (("Goal" :in-theory (enable logtail expt-of-+
                                     floor-when-multiple))))

(defthm logtail-monotone
  (implies (and (<= x y) ;expensive?
                (integerp y)
                (integerp x))
           ;rephrase?
           (<= (logtail n x)
               (logtail n y)))
  :hints (("Goal" :in-theory (e/d (logtail) (logtail-lessp)))))

;better than LOGTAIL-UNSIGNED-BYTE-P and UNSIGNED-BYTE-P-OF-LOGTAIL (from
;centaur/bitops/ihsext-basics.lisp)
(defthm unsigned-byte-p-of-logtail-strong
  (equal (unsigned-byte-p n (logtail pos i))
         (and (natp n)
              (unsigned-byte-p (+ n (nfix pos)) (ifix i))))
  :hints (("Goal" :cases ((integerp x)))))

(defthm logtail-of-sum2
  (implies (and (integerp (/ b (expt 2 m)))
                (integerp a)
                (integerp b)
                (integerp m)
                (<= 0 m))
           (equal (logtail m (+ a b))
                  (+ (logtail m a) (logtail m b))))
  :hints (("Goal" :use (:instance logtail-of-sum (a b) (b a))
           :in-theory (disable logtail-of-sum))))

(defthm logtail-shift-gen2
  (implies (and (<= size n) ;this case
                (natp size)
                (natp n)
                (integerp x)
                )
           (equal (logtail size (* x (expt 2 n)))
                  (* (expt 2 (- n size)) x)))
  :hints (("Goal" :in-theory (enable logtail expt-of-+))))

(defthm logtail-shift-gen2-alt
  (implies (and (<= size n) ;this case
                (natp size)
                (natp n)
                (integerp x)
                )
           (equal (logtail size (* (expt 2 n) x))
                  (* (expt 2 (- n size)) x)))
  :hints (("Goal" :in-theory (enable logtail expt-of-+))))

(defthm <-of-logtail-same
  (implies (and (natp x)
                (posp n))
           (equal (< (logtail n x) x)
                  (not (equal x 0))))
  :hints (("Goal" :in-theory (e/d (expt logtail <-of-floor-arg1)
                                  (expt-hack)))))

(defthm <=-of-logtail-same
  (implies (natp x)
           (<= (logtail n x) x))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm <=-of-logtail-same-linear
  (implies (natp x)
           (<= (logtail n x) x))
  :rule-classes ((:linear))
  :hints (("Goal" :in-theory (enable logtail <-of-floor-arg1))))

;can loop with REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER
(defthmd equal-of-logtail-and-0
  (implies (and (integerp x)
                (natp n))
           (equal (equal (logtail n x) 0)
                  (unsigned-byte-p n x)))
  :hints (("Goal" :cases ((unsigned-byte-p n x))
           :in-theory (enable LOGTAIL))))

;improve the rewrite version?
(defthm logtail-non-positive
  (implies (<= x 0)
           (<= (logtail n x) 0))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable logtail))))

(defthm equal-of-logtail-and-i
  (implies (and (natp i)
                (posp pos))
           (equal (equal (logtail pos i) i)
                  (equal i 0)))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm equal-of-logtail-self
  (implies (and (natp x) ;gen?
                (integerp n))
           (equal (equal (logtail n x) x)
                  (or (equal 0 x)
                      (zp n))))
  :hints (("Goal" :in-theory (enable logtail zip zp))))

(defthm logtail-of-1
  (equal (logtail size 1)
         (if (zp size)
             1
           0))
  :hints (("Goal" :in-theory (enable logtail zp))))

;move
(defthm logtail-non-negative-linear
  (implies (<= 0 x)
           (<= 0 (logtail n x)))
  :rule-classes ((:linear)))
