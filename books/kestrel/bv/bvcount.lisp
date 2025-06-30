; Counting the number of 1 bits
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "getbit")
(include-book "bvplus")
(include-book "bvcat-def")
(local (include-book "unsigned-byte-p"))
(local (include-book "bvcat"))
(local (include-book "getbit"))
(local (include-book "kestrel/arithmetic-light/numerator" :dir :system))
(local (include-book "kestrel/arithmetic-light/denominator" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/nonnegative-integer-quotient" :dir :system))
(local (include-book "kestrel/arithmetic-light/evenp" :dir :system))

(local (in-theory (disable expt)))

;; Count the number of 1 bits in X, which should be SIZE bits wide.  The result
;; fits in B bits where B is (integer-length SIZE).
(defund bvcount (size x)
  (declare (xargs :guard (and (natp size)
                              (integerp x))))
  (if (zp size)
      0
    (+ (getbit (+ -1 size) x)
       (bvcount (+ -1 size) x))))

(defthm bvcount-of-0-arg1
  (equal (bvcount 0 x)
         0)
  :hints (("Goal" :in-theory (enable bvcount))))

(defthm bvcount-of-0-arg2
  (equal (bvcount x 0)
         0)
  :hints (("Goal" :in-theory (enable bvcount))))

;; (defthm logcount-bound
;;   (implies (and (natp x)
;;                 (natp n)
;;                 (< x (expt 2 n)))
;;            (<= (logcount x) n))
;;   :hints (("Goal" :induct (logcount-induct x n)
;;            :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable expt expt-of-+))))

(local
  (defun ind (x i)
    (cond ((zip x) (list x i))
          ((< x 0) (ind (lognot x) (+ -1 i)))
          ((evenp x)
           (ind (nonnegative-integer-quotient x 2) (+ -1 i)))
          (t (1+ (ind (nonnegative-integer-quotient x 2) (+ -1 i)))))))

(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;move
(defthm logcount-of-nonnegative-integer-quotient
  (implies (natp x)
           (equal (logcount (nonnegative-integer-quotient x 2))
                  (if (evenp x)
                      (logcount x)
                    (+ -1 (logcount x))))))

;(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;; (thm
;;   (implies (and (unsigned-byte-p size x)
;;                 ;(posp size)
;;                 )
;;            (equal (logcount x)
;;                   (+ (logcount (slice (+ -1 size) 1 x))
;;                      (getbit 0 x))))
;;   :hints (("Goal" :induct (ind x size)
;;            :in-theory (enable logcount))))

;; (thm
;;   (implies (and (natp highval)
;;                 (natp small)
;;                 ;(< small (expt 2 size))
;;                 (natp size))
;;            (equal (logcount (+ (mod small (expt 2 size)) (* (expt 2 size) highval)))
;;                   (+ (logcount (mod small (expt 2 size)))
;;                      (logcount highval))))
;;   :hints (("Goal" ;:induct (ind highval size)
;;            :expand (logcount (+ (* highval (expt 2 size))
;;                                 (mod small (expt 2 size))))

;;            :in-theory (disable logcount-of-nonnegative-integer-quotient)
;;            )))


;; (thm
;;   (equal (logcount (bvcat highsize highval lowsize lowval))
;;          (+ (logcount (bvchop highsize highval))
;;             (logcount (bvchop lowsize lowval))))
;;   :hints (("Goal" :in-theory (enable logcount bvcat))))

;; (thm
;;   (implies (and (posp size)
;;                 (unsigned-byte-p size x))
;;            (equal (logcount x)
;;                   (+ (getbit (+ -1 size) x)
;;                      (logcount (bvchop (+ -1 size) x)))))
;;   :hints (("Goal" :induct (ind x size)
;;            :in-theory (enable logcount
;;                               nonnegative-integer-quotient-becomes-floor))))

;; ;; ;;sanity check
;; (defthmd bvcount-is-logcount
;;   (implies t;(unsigned-byte-p size x)
;;            (equal (bvcount size x)
;;                   (logcount (bvchop size x))))
;;   :hints (("Goal" ;:use (:instance logcount-bound (n size))
;;            :in-theory (e/d (unsigned-byte-p bvcount)
;;                            (;logcount-bound
;;                             )))))

;; (defthm evenp-of-bvchop
;;   (implies (posp size)
;;            (equal (evenp (bvchop size x))
;;                   (equal 0 (getbit 0 x))))
;;   :hints (("Goal" :in-theory (e/d (bvchop EVENP-BECOMES-EQUAL-OF-0-AND-MOD getbit)
;;                                   ()))))

(defthm bvcount-bound
  (implies (natp size)
           (<= (bvcount size x) size))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable bvcount))))

;;(in-theory (disable logcount))

;; (defthm unsigned-byte-p-of-logcount
;;   (implies (unsigned-byte-p size x)
;;            (unsigned-byte-p (integer-length size)
;;                             (logcount x)))
;;   :hints (("Goal"
;;            :use (:instance logcount-bound (n (+ -1 (expt 2 (integer-length size)))))
;;            :in-theory (e/d (unsigned-byte-p) (logcount-bound)))))

;;Disabled because we have unsigned-byte-p-of-bvcountg-gen.
(defthmd unsigned-byte-p-of-bvcount
  (implies (natp size)
           (unsigned-byte-p (integer-length size) (bvcount size x)))
  :hints (("Goal" :induct (BVCOUNT SIZE X)
           :in-theory (enable bvcount))))

(defthm unsigned-byte-p-of-bvcount-gen
  (implies (and (<= (integer-length size) size2)
                (natp size)
                (integerp size2))
           (unsigned-byte-p size2 (bvcount size x)))
  :hints (("Goal" :use unsigned-byte-p-of-bvcount
           :in-theory (disable unsigned-byte-p-of-bvcount))))

(defthm bvcount-of-bvchop
  (implies (and (<= size size2)
                (integerp size2)
                (natp size))
           (equal (bvcount size (bvchop size2 x))
                  (bvcount size x)))
  :hints (("Goal" :induct t
           :in-theory (enable bvcount))))

;gen
(defthm bvcount-of-slice-of-0
  (implies (and (<= (+ -1 size) high)
                (natp high)
                (natp size))
           (equal (bvcount size (slice high 0 x))
                  (bvcount size x)))
  :hints (("Goal" :induct t
           :in-theory (enable bvcount))))

;; (defthmd bvcount-unroll
;;   (implies (posp size)
;;            (equal (bvcount size x)
;;                   (bvplus (integer-length size)
;;                           (getbit 0 x)
;;                           (bvcount (+ -1 size) (slice (+ -1 size) 1 x)))))
;;   :hints (("Goal" :induct (bvcount size x)
;;            :in-theory (enable bvcount))))

;;   :hints (("Goal" ;:expand ((LOGCOUNT (BVCHOP SIZE X)))
;;            :in-theory (e/d (slice bvplus BVCHOP-OF-LOGTAIL floor-by-2
;;                                   bvcount)
;;                            ()))))

;; (defthmd bvcount-unroll2
;;   (implies (posp size)
;;            (equal (bvcount size x)
;;                   (+ (getbit 0 x)
;;                      (bvcount (+ -1 size) (slice (+ -1 size) 1 x)))))
;;   :hints (("Goal" :induct (bvcount size x)
;;            :in-theory (enable bvcount))))

;; This version has a bvplus in the conclusion so we can use the SMT solver on
;; it.
(defthmd bvcount-unroll
  (implies (posp size)
           (equal (bvcount size x)
                  (bvplus (integer-length size)
                          (getbit (+ -1 size) x)
                          (bvcount (+ -1 size) x))))
  :hints (("Goal" :in-theory (enable bvcount bvplus bvchop-of-sum-cases))))

(defthmd bvcount-unroll2
  (implies (posp size)
           (equal (bvcount size x)
                  (+ (getbit (+ -1 size) x)
                     (bvcount (+ -1 size) x))))
  :hints (("Goal" :in-theory (enable bvcount bvplus bvchop-of-sum-cases))))

(defthm bvcount-of-1
  (equal (bvcount size 1)
         (if (posp size)
             1
           0))
  :hints (("Goal" :in-theory (enable bvcount))))

(defthm bvcount-when-unsigned-byte-p-1
  (implies (unsigned-byte-p 1 x)
           (equal (bvcount size x)
                  (if (posp size)
                      x
                    0)))
  :hints (("Goal" :cases ((equal 0 x))
           :in-theory (enable BVCOUNT))))

(defthm bvcount-of-1-arg1
  (equal (bvcount 1 x)
         (getbit 0 x))
  :hints (("Goal" :in-theory (enable bvcount))))

(defthm bvcount-of-bvcat-irrel
  (implies (and (<= size lowsize)
                (integerp lowsize)
                (natp size))
           (equal (bvcount size (bvcat highsize highval lowsize lowval))
                  (bvcount size lowval)))
  :hints (("Goal" :in-theory (enable bvcount))))

(defthm bvcount-of-bvcat-of-1-arg1
  (implies (and (equal (+ 1 lowsize) size) ;gen
                (natp lowsize))
           (equal (bvcount size (bvcat 1 bit lowsize lowval))
                  (+ (getbit 0 bit)
                     (bvcount lowsize lowval))))
  :hints (("Goal" :expand (BVCOUNT (+ 1 lowsize) (BVCAT 1 BIT LOWSIZE LOWVAL)))))

(defthm bvcount-of-bvchop-when-unsigned-byte-p
  (implies (and (unsigned-byte-p xsize x)
                (natp size))
           (equal (bvcount size (bvchop xsize x))
                  (bvcount size x)))
  :hints (("Goal" :use (:instance split-bv
                                  (x (bvchop size x))
                                  (n size)
                                  (m xsize))
           :in-theory (disable bvcat-of-getbit-and-x-adjacent
                               bvcat-equal-rewrite-alt
                               bvcat-equal-rewrite))))

(defthm bvcount-tighten-size
  (implies (and (unsigned-byte-p xsize x)
                (< xsize size) ;not <= to avoid loops
                (natp size))
           (equal (bvcount size x)
                  (bvcount xsize x)))
  :hints (("subgoal *1/5" :use (:instance GETBIT-TOO-HIGH (n (+ -1 SIZE)))
           :expand (BVCOUNT SIZE X)
           :in-theory (disable GETBIT-TOO-HIGH-CHEAP-2))
          ("Goal" :in-theory (e/d (bvcount zp) (INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM)))))

(defthm bvcount-of-bvchop-gen
  (implies (and (natp size1)
                ;;(posp size1)
                (natp size2))
           (equal (bvcount size1 (bvchop size2 x))
                  (bvcount (min size1 size2) x)))
  :hints (("Goal" :use (:instance bvcount-tighten-size
                                  (x (BVCHOP SIZE2 X))
                                  (xsize size2)
                                  (size size1))
           :in-theory (disable bvcount-tighten-size))))

(defthm bvcount-of-bvcat
  (implies (and (equal (+ highsize lowsize) size) ;gen?
                (natp highsize)
                (natp lowsize)
                ;;(natp size)
                )
           (equal (bvcount size (bvcat highsize highval lowsize lowval))
                  (+ (bvcount highsize highval)
                     (bvcount lowsize lowval))))
  :hints (("subgoal *1/4" :in-theory (e/d (bvcount) ( bvcount-of-bvchop))
           :use (:instance bvcount-of-bvchop
                           (size (+ -1 HIGHSIZE LOWSIZE))
                           (size2 (+ -1 HIGHSIZE LOWSIZE))
                           (x (BVCAT HIGHSIZE HIGHVAL LOWSIZE LOWVAL))))
          ("Goal" :in-theory (enable bvcount))))
