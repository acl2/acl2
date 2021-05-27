; BV Library: theorems about logapp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "logapp-def")
(include-book "logtail-def")
(local (include-book "../library-wrappers/ihs-logops-lemmas"))
(local (include-book "../library-wrappers/ihs-quotient-remainder-lemmas")) ;drop
(local (include-book "../utilities/equal-of-booleans"))
(local (include-book "../../meta/meta-plus-equal"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "../arithmetic-light/mod-and-expt"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/times-and-divides"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/plus"))

(in-theory (disable logapp))

(defthm logapp-when-not-integerp-arg2
  (implies (not (integerp i))
           (equal (logapp size i j)
                  (logapp size 0 j)))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm logapp-when-not-integerp-arg3
  (implies (not (integerp j))
           (equal (logapp size i j)
                  (bvchop size i)))
  :hints (("Goal" :in-theory (enable logapp bvchop))))

(defthm logapp-when-not-natp-arg1
  (implies (not (natp size))
           (equal (logapp size i j)
                  (ifix j)))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm <-of-logapp-and-0
  (equal (< (logapp size i j) 0)
         (< (ifix j) 0))
  :hints (("Goal"
           :in-theory (enable logapp)
           :cases ((and (integerp i) (integerp j))
                   (and (integerp i) (not (integerp j)))
                   (and (not (integerp i)) (integerp j))))))

(defthm natp-of-logapp
  (implies (natp j)
           (natp (logapp size i j)))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm floor-of-logapp-same
  (implies (natp size)
           (equal (floor (logapp size i j) (expt 2 size))
                  (ifix j)))
  :hints (("Goal" :in-theory (enable logapp))))

(defthmd logapp-onto-self-hack
  (implies (and (natp size)
                (integerp i))
           (equal (logapp size i (floor i (expt 2 size)))
                  i))
  :hints (("Goal" :in-theory (enable logapp bvchop))))

(defthm logapp-of-bvchop-same ;see also logapp-of-bvchop
  (equal (logapp size (bvchop size i) j)
         (logapp size i j))
  :hints (("Goal" :in-theory (enable logapp bvchop))))

(defthm logapp-of-0-arg1
  (equal (logapp 0 i j)
         (ifix j))
  :hints (("Goal" :in-theory (enable logapp))))

;; rewrite to a shift?
(defthm logapp-of-0-arg2
  (equal (logapp size 0 i)
         (* (ifix i) (expt 2 (nfix size))))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm logapp-of-0-arg3
  (equal (logapp size i 0)
         (bvchop size i))
  :hints (("Goal" :in-theory (enable logapp bvchop))))

(defthm mod-of-logapp-1
  (implies (and (<= size2 size) ;this case
                (integerp i)
                (natp size)
                (natp size2))
           (equal (mod (logapp size i j) (expt 2 size2))
                  (mod i (expt 2 size2))))
  :hints (("Goal" :in-theory (e/d (logapp) (EQUAL-OF-MOD-OF-+-AND-MOD-CANCEL)))))

(defthm mod-of-logapp-2
  (implies (and (< size size2) ;this case
                (integerp i)
                (natp size)
                (natp size2))
           (equal (mod (logapp size i j) (expt 2 size2))
                  (logapp size i (mod j (expt 2 (+ (- size) size2))))))
  :hints (("Goal"
           :use (:instance mod-of-*-of-expt-and-expt-bound (i j))
           :in-theory (e/d (logapp expt-of-+)
                           ( ;MOD-SUM-CASES
                            mod-of-*-of-expt-and-expt-bound
                            MOD-X-I*J-OF-POSITIVES)))))

(defthm bvchop-of-logapp
  (implies (and (natp size)
                (integerp size2))
           (equal (bvchop size2 (logapp size i j))
                  (if (<= size2 size)
                      (bvchop size2 i)
                    (logapp size i (bvchop (- size2 size) j)))))
  :hints (("Goal" :cases ((integerp i))
           :in-theory (enable bvchop))))

;no hyps on size
(defthm bvchop-of-logapp-same
  (equal (bvchop size (logapp size i j))
         (bvchop size i))
  :hints (("Goal" :cases ((natp size)))))

(defthm logapp-of-bvchop
  (implies (and (<= size size2)
                (integerp size)
                (integerp size2))
           (equal (logapp size (bvchop size2 i) j)
                  (logapp size i j)))
  :hints (("Goal" :in-theory (enable bvchop logapp))))

(defthm logapp-equal-rewrite
  (equal (equal (logapp size i j) x)
         (and (integerp x)
              (equal (bvchop size x)
                     (bvchop size i))
              (equal (logtail size x)
                     (ifix j))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :cases ((natp size))
           :use ((:instance logapp-onto-self-hack (size size) (i x))
                 (:instance logapp-of-bvchop-same (size size) (i i) (j (floor x (expt 2 size))))
                 (:instance logapp-of-bvchop-same (size size) (i x) (j (floor x (expt 2 size)))))
           :in-theory (disable logapp-of-bvchop-same
                               logapp-of-bvchop))))

(defthm logapp-equal-0-rewrite-gen
  (implies (and (integerp x)
                (natp n))
           (equal (equal (logapp n 0 x) 0)
                  (equal x 0)))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm unsigned-byte-p-of-logapp-small-case
  (implies (and (<= n size)
                (natp size)
                (natp j))
           (equal (unsigned-byte-p n (logapp size i j))
                  (and (equal 0 j)
                       (unsigned-byte-p n (bvchop size i)))))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
           :use ((:instance expt-bound-linear-weak (free size) (size n))
                 (:instance <-of-*-cancel-2 (x j) (y (expt 2 size))))
           :in-theory (e/d (logapp unsigned-byte-p bvchop)
                           (<-of-*-cancel-2
                            expt-bound-linear-weak)))))

(defthm logtail-of-logapp-same
  (equal (logtail size (logapp size i j))
         (ifix j))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm logapp-associative
  (implies (and (natp size1)
                (natp size))
           (equal (logapp size i (logapp size1 j k))
                  (logapp (+ size size1)
                          (logapp size i j)
                          k)))
  :hints (("Goal" :in-theory (disable associativity-of-logapp logapp-equal-rewrite)
           :use (:instance associativity-of-logapp (j (ifix j)) (i (ifix i)) (k (ifix k))))))

(defthm unsigned-byte-p-of-logapp-large-case
  (implies (and (<= size size1)
                (natp size)
                (integerp size1))
           (equal (unsigned-byte-p size1 (logapp size i j))
                  (unsigned-byte-p (- size1 size) (ifix j))))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (unsigned-byte-p-logapp))
           :use (:instance unsigned-byte-p-logapp (size size1) (size1 size) (i (ifix i)) (j (ifix j))))))

(defthm logapp-of-constant-negative-linear
  (implies (and (syntaxp (quotep j))
                (< j 0) ;gets computed
                (integerp j) ;gets computed
                )
           (< (logapp size i j) 0))
  :rule-classes :linear)

;since logapp calls loghead
(defthm loghead-becomes-bvchop
  (equal (loghead n x)
         (bvchop n x))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm logapp-minus-1-negative
  (implies (integerp x)
           (< (logapp n x -1) 0))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable logapp))))
