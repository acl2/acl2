; BV Library: Theorems about bvcat
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat-def")
(include-book "logapp")
(include-book "slice")
(include-book "getbit")
(include-book "bvchop")
(local (include-book "unsigned-byte-p"))
(local (include-book "../arithmetic-light/denominator"))
(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "../arithmetic-light/plus-and-minus"))
(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/times-and-divides"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/floor")) ;drop?
(local (include-book "../library-wrappers/ihs-logops-lemmas"))

(defthm unsigned-byte-p-of-bvcat
  (implies (and (equal n (+ lowsize highsize))
                (natp lowsize)
                (natp highsize))
           (unsigned-byte-p n (BVCAT HIGHSIZE HIGHVAL LOWSIZE LOWVAL)))
  :hints (("Goal" :do-not '(preprocess generalize eliminate-destructors)
           :cases ((integerp lowval))
           :in-theory (enable bvcat))))

(defthm unsigned-byte-p-of-bvcat-gen
  (implies (and (>= n (+ lowsize highsize))
                (natp n)
                (natp lowsize)
                (natp highsize))
           (unsigned-byte-p n (bvcat highsize highval lowsize lowval)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvcat (n (+ lowsize highsize)))
           :in-theory (disable unsigned-byte-p-of-bvcat))))

(defthm bvchop-of-bvcat-same
  (implies (and (equal n (+ n2 xsize))
                (natp n2)
                (natp xsize))
           (equal (bvchop n (bvcat xsize x n2 y))
                  (bvcat xsize x n2 y))))

(defthm bvchop-of-bvcat-low
  (implies (and (<= n lowsize)
                (natp n)
                (natp lowsize))
           (equal (bvchop n (bvcat highsize highval lowsize lowval))
                  (bvchop n lowval)))
  :hints (("Goal" :cases ((integerp lowval))
           :in-theory (enable bvcat))))

(defthmd unsigned-byte-p-of-+-when-<-of-logtail-and-expt
  (implies (and (< (logtail size x) (expt 2 size2))
                (natp size)
                (natp size2)
                (natp x))
           (unsigned-byte-p (+ size size2) x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p expt-of-+))))

(encapsulate
 ()
 (local (defthm bvcat-equal-rewrite-fw
          (implies (and (natp lowsize)
                        (natp highsize))
                   (implies (equal (bvcat highsize highval lowsize lowval) x)
                            (and (unsigned-byte-p (+ lowsize highsize) x)
                                 (equal (bvchop lowsize x)
                                        (bvchop lowsize lowval))
                                 (equal (slice (+ -1 lowsize highsize) lowsize x)
                                        (bvchop highsize highval)))))
          :hints (("Goal" :cases ((integerp lowval))
                   :use (:instance unsigned-byte-p-of-+-when-<-of-logtail-and-expt
                                   (size lowsize)
                                   (size2 highsize)
                                   (x x))
                   :in-theory (e/d (bvcat slice)
                                   (bvchop-of-logtail-becomes-slice
                                    LOGTAIL-LESSP
                                    unsigned-byte-p-of-+-when-<-of-logtail-and-expt))))))

 (local (defthm bvcat-equal-rewrite-bk
          (implies (and (natp lowsize)
                        (natp highsize))
                   (implies (and (unsigned-byte-p (+ lowsize highsize) x)
                                 (equal (bvchop lowsize x)
                                        (bvchop lowsize lowval))
                                 (equal (slice (+ -1 lowsize highsize) lowsize x)
                                        (bvchop highsize highval)))
                            (EQUAL (BVCAT HIGHSIZE HIGHVAL LOWSIZE LOWVAL) x)))
          :hints (("Goal" :in-theory (e/d (bvcat slice)
                                          (BVCHOP-OF-LOGTAIL-BECOMES-SLICE))))))

 (defthm bvcat-equal-rewrite
   (implies (and (natp lowsize)
                 (natp highsize))
            (equal (equal (bvcat highsize highval lowsize lowval) x)
                   (and (unsigned-byte-p (+ lowsize highsize) x)
                        (equal (bvchop lowsize x)
                               (bvchop lowsize lowval))
                        (equal (slice (+ -1 lowsize highsize) lowsize x)
                               (bvchop highsize highval)))))
   :hints (("Goal" :use (bvcat-equal-rewrite-fw bvcat-equal-rewrite-bk)
            :in-theory (disable bvcat-equal-rewrite-bk bvcat-equal-rewrite-fw)))))

(defthm bvcat-equal-rewrite-alt
  (implies (and (natp lowsize)
                (natp highsize))
           (equal (equal x (bvcat highsize highval lowsize lowval))
                  (and (unsigned-byte-p (+ lowsize highsize) x)
                       (equal (bvchop lowsize x)
                              (bvchop lowsize lowval))
                       (equal (slice (+ -1 lowsize highsize) lowsize x)
                              (bvchop highsize highval)))))
  :hints (("Goal" :in-theory (disable bvcat-equal-rewrite)
           :use (:instance bvcat-equal-rewrite))))

;dup?
(defthm bvcat-of-bvchop-high
  (implies (and (<= highsize size2)
                (natp highsize)
                (natp size2)
                (natp lowsize))
           (equal(bvcat highsize (bvchop size2 highval) lowsize lowval)
                 (bvcat highsize highval lowsize lowval)))
  :hints (("Goal"
           :cases ((integerp lowval))
           :in-theory (enable bvcat ;bvchop-logapp
                            ))))

(defthm slice-of-bvcat
  (implies (and (<= lowsize lowindex) ;todo handle other case
                (natp lowsize)
                (natp lowindex)
                (natp highsize)
                (natp highindex)
                )
           (equal (slice highindex lowindex (BVCAT HIGHSIZE HIGHVAL LOWSIZE LOWVAL))
                  (slice (- highindex lowsize) (- lowindex lowsize) (bvchop highsize highval))))
  :hints (("Goal" :cases ((and (integerp lowval) (integerp highval))
                          (and (not (integerp lowval)) (integerp highval))
                          (and (integerp lowval) (not (integerp highval)))
                          (and (not (integerp lowval)) (not (integerp highval))))
           :in-theory (e/d (bvcat slice bvchop-when-i-is-not-an-integer logtail-logapp)
                           (bvchop-of-logtail-becomes-slice)))))

;fixme rename?
;causes case split (due to the IF and the MIN).
;prove other rules for each case (many may exist already).
(defthm bvchop-of-bvcat-cases
  (implies (and (natp n)
                (natp lowsize)
                (natp highsize))
           (equal (bvchop n (bvcat highsize highval lowsize lowval))
                  (if (<= n lowsize) ;use min or max instead of this if?
                      (bvchop n lowval)
                    (bvcat (min (binary-+ n (unary-- lowsize))
                                highsize)
                           highval lowsize lowval))))
  :hints (("Goal" :cases ((natp (+ (- lowsize) n))))))

(defthm bvcat-when-lowval-is-not-an-integer
  (implies (not (integerp lowval))
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize highval lowsize 0)))
  :hints (("Goal" :in-theory (enable bvcat logapp))))

(defthm bvcat-when-highval-is-not-an-integer
  (implies (not (integerp highval))
           (equal (bvcat highsize highval LOWSIZE LOWVAL)
                  (bvcat highsize 0 LOWSIZE lowval)))
  :hints (("Goal" :in-theory (enable bvcat))))

(defthm bvcat-of-ifix-arg2
  (equal (bvcat highsize (ifix highval) lowsize lowval)
         (bvcat highsize highval lowsize lowval))
  :hints (("Goal" :in-theory (enable bvcat-when-highval-is-not-an-integer))))

(defthm bvcat-of-ifix-arg4
  (equal (bvcat highsize highval lowsize (ifix lowval))
         (bvcat highsize highval lowsize lowval))
  :hints (("Goal" :in-theory (enable bvcat-when-lowval-is-not-an-integer))))

(defthm bvcat-recombine
  (equal (logapp lowsize lowval (bvchop highsize highval))
         (bvcat highsize highval lowsize lowval))
  :hints (("Goal" :in-theory (enable bvcat))))

(theory-invariant (incompatible (:definition bvcat) (:rewrite bvcat-recombine)))

(defthm unsigned-byte-p-of-bvcat2
  (implies (and (equal n (+ lowsize highsize))
                (natp lowsize)
                (natp highsize))
           (unsigned-byte-p n(bvcat highsize highval lowsize lowval)))
  :hints
  (("Goal"
    :cases ((integerp lowval))
    :do-not '(preprocess generalize eliminate-destructors)
    :in-theory (e/d (bvcat) (bvcat-recombine)))))

;drop?
(defthm bvcat-equal-0-rewrite
  (implies (and (integerp x)
                (equal 7 size))
           (equal (equal (bvcat 1 x size 0) 0)
                  (equal (getbit 0 x) 0)))
  :hints (("Goal"   :do-not '(preprocess)
           :in-theory (e/d (;getbit bvcat slice
                            )
                           (BVCHOP-OF-LOGTAIL-BECOMES-SLICE BVCAT-RECOMBINE)))))

(defthm bvcat-when-lowsize-is-0
  (equal (bvcat highsize highval 0 lowval)
         (bvchop highsize highval))
  :hints (("Goal" :cases ((integerp lowval))
           :in-theory (e/d (bvcat) (bvcat-recombine)))))

(defthm bvcat-of-bvchop-low
  (implies (and (<= lowsize n)
                (natp lowsize)
                (natp n)
                ;(integerp lowval)
                )
           (equal (bvcat highsize highval lowsize (bvchop n lowval))
                  (bvcat highsize highval lowsize lowval)))
  :hints (("Goal" :cases ((integerp lowval))
           :in-theory (e/d (bvcat) (BVCAT-RECOMBINE)))))

;rename
(defthm bvcat-slice-same
  (implies (and (natp n)
                (equal n (+ 1 k (- m)))
                (natp m)
                (natp k))
           (equal (bvcat m (slice k n x) n x)
                  (slice k 0 x))))

(defthm bvcat-of-getbit-arg4
   (equal (bvcat n x 1 (getbit 0 y))
          (bvcat n x 1 y))
   :hints (("Goal" :in-theory (e/d (getbit bvcat) (bvcat-recombine BVCHOP-1-BECOMES-GETBIT SLICE-BECOMES-GETBIT)))))

(defthm bvcat-of-getbit-arg2
  (equal (bvcat 1 (getbit 0 x) n y)
         (bvcat 1 x n y))
   :hints (("Goal" :in-theory (e/d (getbit bvcat) (bvcat-recombine BVCHOP-1-BECOMES-GETBIT SLICE-BECOMES-GETBIT)))))

(encapsulate
 ()

 (local (defthm unsigned-byte-p-of-bvcat-all-cases-helper
          (implies (and (integerp lowval) ;todo
                        (natp lowsize)
                        (natp highsize)
                        )
                   (equal (unsigned-byte-p n (bvcat highsize highval lowsize lowval))
                          (if (natp n)
                              (if (< n (+ highsize lowsize))
                                  (if (<= n lowsize)
                                      (and (equal 0 (bvchop highsize highval))
                                           (unsigned-byte-p n (bvchop lowsize lowval)))
                                    (unsigned-byte-p (- n lowsize) (bvchop highsize highval)))
                                t)
                            nil)))
          :otf-flg t
          :hints (("Goal" :cases ((not (natp n))
                                  (and (natp n) (integerp lowval))
                                  (and (natp n) (not (integerp lowval))))
                   :in-theory (e/d (bvcat LOGAPP-0
                                          unsigned-byte-p-when-n-is-not-natp
                                          BVCHOP-WHEN-I-IS-NOT-AN-INTEGER
                                          BVCHOP-WITH-N-NOT-AN-INTEGER
                                          )
                                   (bvcat-recombine ;hide-bvcat
                                    NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG ;why?
                                    SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))))))

 (defthm unsigned-byte-p-of-bvcat-all-cases
   (implies (and (natp lowsize)
                 (natp highsize))
            (equal (unsigned-byte-p n (bvcat highsize highval lowsize lowval))
                   (if (natp n)
                       (if (< n (+ highsize lowsize))
                           (if (<= n lowsize)
                               (and (equal 0 (bvchop highsize highval))
                                    (unsigned-byte-p n (bvchop lowsize lowval)))
                             (unsigned-byte-p (- n lowsize) (bvchop highsize highval)))
                         t)
                     nil)))
   :hints (("Goal" :in-theory (enable BVCHOP-WHEN-I-IS-NOT-AN-INTEGER
                                      BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER)
            :cases ((integerp lowval))))))

(defthm unsigned-byte-p-of-bvcat-gen2
  (implies (and (>= n (+ lowsize highsize))
                (natp n)
                (natp lowsize)
                (natp highsize))
           (unsigned-byte-p n (bvcat highsize highval lowsize lowval)))
  :hints
  (("Goal" :use (:instance unsigned-byte-p-of-bvcat
                           (n (+ lowsize highsize)))
    :in-theory (disable unsigned-byte-p-of-bvcat))))

(defthmd bvcat-numeric-bound2
  (implies (and (syntaxp (quotep k))
                (syntaxp (quotep lowsize))
                (syntaxp (quotep highsize))
                (<= (expt 2 (+ lowsize highsize)) k)
                (natp lowsize)
                (natp highsize))
           (equal (< (bvcat highsize highval lowsize lowval) k)
                  t))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvcat
                                  (n (+ lowsize highsize)))
           :in-theory (e/d (unsigned-byte-p) (unsigned-byte-p-of-bvcat2
                                              unsigned-byte-p-of-bvcat-all-cases
                                              unsigned-byte-p-of-bvcat
                                              unsigned-byte-p-of-bvcat-gen
                                              unsigned-byte-p-of-bvcat-gen2
                                              ;logapp-recollect-from-shift
                                              )))))
(defthm bvcat-upper-bound-linear
  (implies (and (natp lowsize)
                (natp highsize))
           (< (bvcat highsize highval lowsize lowval) (expt 2 (+ highsize lowsize))))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :use (:instance bvcat-numeric-bound2
                                  (k (expt 2 (+ highsize lowsize)))))))

;was disabled (why?)
(defthm bvcat-of-0
  (equal (bvcat highsize 0 lowsize lowval)
         (bvchop lowsize lowval))
  :hints (("Goal" :in-theory (e/d (bvcat LOGAPP-0) (bvcat-recombine)))))

(defthm bvcat-of-0-and-0
  (equal (bvcat highsize 0 lowsize 0)
         0)
  :hints (("Goal" :in-theory (e/d (bvcat) (bvcat-recombine)))))

(defthm bvcat-when-highsize-is-0
  (implies (natp lowsize)
           (equal (bvcat 0 highval lowsize lowval)
                  (bvchop lowsize lowval)))
  :hints (("Goal" :cases ((integerp lowval))
           :in-theory (e/d (bvcat LOGAPP-0 BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
                           (bvcat-recombine)))))

(defthm bvcat-when-lowsize-is-not-posp
  (implies (not (posp lowsize))
           (equal (bvcat highsize highval lowsize lowval)
                  (bvchop highsize highval)))
  :hints (("Goal" :cases ((integerp lowval))
           :in-theory (e/d (bvcat) (bvcat-recombine)))))

(defthm bvcat-when-highsize-is-not-posp
  (implies (not (posp highsize))
           (equal (bvcat highsize highval lowsize lowval)
                  (bvchop lowsize lowval)))
  :hints (("Goal" :cases ((equal 0 highsize))
           :in-theory (e/d (bvcat BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
                           (bvcat-recombine)))))

(defthm bvcat-of-slice-and-slice-adjacent
  (implies (and (equal low1 (+ 1 high2))
                (equal size1 (+ 1 high1 (- low1)))
                (equal size2 (+ 1 high2 (- low2)))
                (<= low1 high1)
                (<= low2 high2)
                (natp low1)
                (natp low2)
                (natp high1)
                (natp high2))
           (equal (bvcat size1 (slice high1 low1 x) size2 (slice high2 low2 x))
                  (slice high1 low2 x)))
  :hints (("Goal" :in-theory (enable natp))))

(defthm bvcat-of-getbit-and-slice-adjacent
  (implies (and (equal n (+ 1 high2))
                (equal size2 (+ 1 high2 (- low2)))
                (<= low2 high2)
                (natp n)
                (natp low2)
                (natp high2))
           (equal (bvcat 1 (getbit n x) size2 (slice high2 low2 x))
                  (slice n low2 x)))
  :hints (("Goal" :use (:instance bvcat-of-slice-and-slice-adjacent (low1 n) (high1 n) (size1 1)))))

(defthm bvcat-of-slice-and-getbit-adjacent
  (implies (and (equal low (+ 1 n))
                (equal size (+ 1 high (- low)))
                (<= low high)
                (natp low)
                (natp n)
                (natp high))
           (equal (bvcat size (slice high low x) 1 (getbit n x))
                  (slice high n x)))
  :hints (("Goal" :use (:instance bvcat-of-slice-and-slice-adjacent (low2 n) (high2 n) (size2 1))
           :in-theory (disable <-of-+-of---and-0-arg1
                               <-of-+-of---and-0-arg2))))

(defthm bvcat-of-getbit-and-getbit-adjacent
  (implies (and (equal n (+ 1 m))
                (natp m))
           (equal (bvcat 1 (getbit n x) 1 (getbit m x))
                  (slice n m x))))

(defthm bvcat-of-slice-and-x-adjacent
  (implies (and (equal size1 (+ 1 high1 (- low1)))
                (<= low1 high1)
                (natp low1)
                (natp high1))
           (equal (bvcat size1 (slice high1 low1 x) low1 x)
                  (bvchop (+ 1 high1) x)))
  :hints (("Goal" :in-theory (enable natp))))


(defthm bvcat-of-getbit-and-x-adjacent
  (implies (natp n)
           (equal (bvcat 1 (getbit n x) n x)
                  (bvchop (+ 1 n) x))))

(defthmd getbit-of-bvcat-low
  (implies (and (< k lowsize)
                (integerp k)
                (<= 0 k)
                (integerp lowsize)
                (integerp lowval)
                (integerp highsize)
                (integerp highval)
                )
           (equal (getbit k (bvcat highsize highval lowsize lowval))
                  (getbit k lowval)))
  :hints
  (("Goal" :in-theory (e/d (bvcat getbit slice logtail-logapp)
                           (
                            BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                            SLICE-BECOMES-GETBIT
                            bvchop-1-becomes-getbit
                            bvcat-RECOMBINE)))))

(defthm getbit-of-bvcat-low-better
  (implies (and (< k lowsize)
                (natp k)
                (integerp lowsize)
                (integerp highsize))
           (equal (getbit k (bvcat highsize highval lowsize lowval))
                  (getbit k lowval)))
  :hints
  (("Goal" ;:use (:instance getbit-of-bvcat-low)
    :cases ((and (integerp lowval) (integerp highval))
            (and (integerp lowval) (not (integerp highval)))
            (and (not (integerp lowval)) (integerp highval)))
    :in-theory (enable getbit-of-bvcat-low))))

(defthm getbit-of-bvcat-too-high
  (implies (and (<= (+ highsize lowsize) n)
                (natp n)
                (natp highsize)
                (natp lowsize))
           (equal (getbit n (bvcat highsize highval lowsize lowval))
                  0))
  :hints (("Goal" :cases ((integerp lowval))
           :in-theory (enable getbit-too-high))))

(defthm getbit-of-bvcat-high
  (implies (and (<= lowsize k)
                (< (- k lowsize) highsize)
                (<= 0 lowsize)
                (integerp k)
                (integerp lowsize)
                (integerp highsize))
           (equal (getbit k (bvcat highsize highval lowsize lowval))
                  (getbit (- k lowsize) highval)))
  :hints (("Goal" :cases ((and (integerp lowval) (integerp highval))
                          (and (integerp lowval) (not (integerp highval)))
                          (and (not (integerp lowval)) (integerp highval)))
           :do-not '(preprocess)
           :in-theory (e/d (bvcat getbit slice logtail-of-bvchop logtail-logapp)
                           (bvchop-of-logtail slice-becomes-getbit
                                               bvchop-1-becomes-getbit bvcat-recombine bvchop-of-logtail
                                               bvchop-of-logtail-becomes-slice
                                               logtail-of-bvchop-becomes-slice)))))

;keeping this disabled, since it causes case splits
(defthmd getbit-of-bvcat-low-better-all-cases
  (implies (and (integerp k)
                (<= 0 k)
                (natp lowsize)
                (natp highsize))
           (equal (getbit k (bvcat highsize highval lowsize lowval))
                  (if (< k lowsize)
                      (getbit k lowval)
                    (if (< (- k lowsize) highsize)
                        (getbit (- k lowsize) highval)
                      0)))))

(defthm getbit-of-bvcat-high-better
   (implies (and (<= lowsize k)
;                 (< (- k lowsize) highsize)
                 (<= 0 lowsize)
                 (integerp k)
                 (<= 0 k)
                 (integerp lowsize)
                 (natp highsize)
                 )
            (equal (getbit k (bvcat highsize highval lowsize lowval))
                   (getbit (- k lowsize) (bvchop highsize highval))))
   :hints (("Goal" :in-theory (enable getbit-of-bvcat-low-better-all-cases GETBIT-TOO-HIGH))))

(defthm getbit-of-bvcat-all
  (equal (getbit k (bvcat highsize highval lowsize lowval))
         (if (natp highsize)
             (if (< (nfix k) (nfix lowsize))
                 (getbit k lowval)
               (if (< (- (nfix k) (nfix lowsize)) highsize)
                   (getbit (- (nfix k) (nfix lowsize)) highval)
                 0))
           (getbit k (bvchop lowsize lowval)))))

;associaed wrong?
(defthm bvcat-getbit-getbit-same
  (implies (and (equal highindex (+ 1 lowindex))
                (equal size2 (+ 1 highsize))
                (natp lowindex)
                (integerp highval)
                (natp highsize)
                (< 0 highsize)
                (integerp b))
           (equal (bvcat size2 (bvcat highsize highval 1 (getbit highindex b)) 1 (getbit lowindex b))
                  (bvcat highsize highval 2 (slice highindex lowindex b)))))

;drop?
(defthm logtail-of-bvcat-same
  (implies (and (integerp lowval)
                (< 0 size)
                (natp size))
           (equal (logtail size (bvcat highsize highval size lowval))
                  (bvchop highsize highval)))
  :hints (("Goal" :in-theory (e/d (bvcat) (bvcat-recombine)))))

(defthm bvchop-of-logapp-bigger
   (implies (and (< n2 n)
                 (natp n2))
            (equal (bvchop n (logapp n2 y x))
                   (if (natp n)
                       (logapp n2 y (bvchop (- n n2) x))
                     0)))
   :hints (("Goal" :in-theory (e/d (logapp
                                    slice
                                    ;;bvchop
                                    logtail
                                    )
                                   (bvchop-of-logtail-becomes-slice
                                    bvchop-of-logtail)))))

(defthm bvchop-of-logapp-both
  (implies (natp n2)
           (equal (bvchop n (logapp n2 y x))
                  (if (not (natp n))
                      0
                    (if (< n2 n)
                        (if (natp n)
                            (logapp n2 y (bvchop (- n n2) x))
                          0)
                      (bvchop n y)))))
  :hints (("Goal" :cases ((< n2 n)))))

;rename the params?
;drop in favor of the one below?
(defthmd bvcat-associative-helper
  (implies (and (equal lowsize1 (+ lowsize2 highsize2))
                (natp lowsize2)
                (natp highsize2)
                (natp highsize1))
           (equal (bvcat highsize1 z lowsize1 (bvcat highsize2 y lowsize2 x))
                  (bvcat (+ highsize1 highsize2) (bvcat highsize1 z highsize2 y) lowsize2 x)))
  :hints (("Goal" :use ((:instance bvchop-of-logapp
                                   (j y) (i (ifix x)) (size lowsize2) (size2  lowsize2)
                                   )
                        (:instance bvchop-of-logapp-bigger
                                   (n (+ highsize2 lowsize2))
                                   (n2 lowsize2)
                                   (y (ifix x))
                                   (x y)
                                   ))
           :cases ((integerp x))
           :in-theory (e/d (bvcat slice logapp-0 ;bvchop-of-logtail
                                  )
                           (                     ;associativity-of-logapp
                            slice-becomes-bvchop ;bvchop-logapp
                            bvchop-of-logtail-becomes-slice
                            bvchop-of-logapp-bigger
                            bvcat-recombine)))))

(defthm bvcat-associative
  (implies (and (equal highsize1 (+ lowsize2 highsize2))
                (natp lowsize2)
                (natp lowsize1)
                (natp highsize2)
                (natp highsize1))
           (equal (bvcat highsize1 (bvcat highsize2 highval2 lowsize2 lowval2) lowsize1 lowval1)
                  (bvcat highsize2 highval2 (+ lowsize2 lowsize1) (bvcat lowsize2 lowval2 lowsize1 lowval1))))
  :hints (("Goal" :in-theory (enable bvcat-associative-helper))))

(defthm bvcat-of-bvchop-high-tighten
  (implies (and (< n highsize) ;this may loop if we allow <=
                (integerp highsize)
                (integerp n))
           (equal (bvcat highsize (bvchop n x) lowsize lowval)
                  (bvcat n (bvchop n x) lowsize lowval)))
  :hints (("Goal" :in-theory (e/d (bvcat) (bvcat-recombine
                                           logtail-logapp)))))

(defthm bvcat-of-bvchop-tighten
  (implies (and (< highsize size)
                (natp size)
                (natp highsize)
                (integerp x)
                (integerp y))
           (equal (bvcat highsize (bvchop size y) lowsize x)
                  (bvcat highsize (bvchop highsize y) lowsize x)))
  :hints (("Goal" :in-theory (e/d (bvcat) (bvcat-recombine)))))

(defthm bvcat-equal-rewrite-no-first-components-same
  (implies (and (integerp x)
                (integerp y)
                (integerp y2)
                (natp size)
                (natp size2)
                (< 0 size2))
           (equal (equal (bvcat size2 y size x) (bvcat size2 y2 size x))
                  (equal (bvchop size2 y)
                         (bvchop size2 y2)))))

(defthm slice-of-logapp-hack
  (implies (and (natp size)
                (natp bound)
                (<= size bound))
           (equal (slice bound size (logapp size x -1))
                  (slice (- bound size) 0 -1)))
  :hints (("Goal" :in-theory (e/d (logapp slice logtail-of-bvchop ;repeatbit
                                          logtail
                                          )
                                  (slice-of-bvchop-low-gen
                                   bvchop-of-logtail-becomes-slice
                                   bvchop-of-logtail)))))

(defthm slice-of-bvcat-low
  (implies (and (<= lowbit highbit)
                (< highbit lowsize) (natp highbit)
                (natp lowbit)
                (natp highsize)
                (natp lowsize)
;                (integerp lowval)
;               (integerp highval)
                )
           (equal (slice highbit lowbit (bvcat highsize highval lowsize lowval))
                  (slice highbit lowbit lowval)))
  :hints (("Goal" :cases ((integerp lowval))
           :in-theory (e/d (bvcat slice bvchop-of-logapp-bigger
                                  bvchop-of-logtail
                                  ;;bvchop-logapp
                                  )
                           (logtail-shift-gen2-alt
                            logtail-of-bvchop-becomes-slice ;todo
                            bvchop-of-logtail-becomes-slice
                            slice-becomes-bvchop bvcat-recombine)))))

;todo analogues for other functions
;we now have a more general rules?
(defthm slice-of-bvcat-too-high
  (implies (and (<= (+ lowsize highsize) low)
                (<= low high) ;todo
                (natp low)
                (natp high)
                (natp lowsize)
                (natp highsize)
                (integerp lowval)
                (integerp highval))
           (equal (slice high low (bvcat highsize highval lowsize lowval))
                  0))
  :hints (("Goal" :cases ((integerp lowval))
           :in-theory (enable slice-too-high-is-0))))

;use trim?
;associated wrong
(defthm bvcat-of-bvcat-trim-high-arg
  (implies (and (< size1 (+ highsize lowsize))
                (natp size1)
                (< 0 size1)
                (natp size2)
                (natp lowsize)
                (natp highsize))
           (equal (bvcat size1 (bvcat highsize highval lowsize lowval) size2 x)
                  (if (<= size1 lowsize)
                      (bvcat size1 (bvchop size1 lowval) size2 x)
                      (bvcat size1
                             (bvcat (+ size1 (- lowsize))
                                    (bvchop (min size1 highsize) highval)
                                    lowsize lowval)
                             size2
                             x))))
  :hints (("Goal" :in-theory (disable bvcat-recombine bvcat-associative))))

(defthm slice-of-bvcat-hack
  (implies (and (< lowbit lowsize)
                (< highbit (+ lowsize highsize))
                (<= lowsize highbit)
                (natp lowsize)
                (natp highsize)
                (natp lowbit)
                (natp highbit))
           (equal (slice highbit lowbit (bvcat highsize x lowsize y))
                  (bvcat (+ highbit (- lowsize) 1)
                           (slice (- highbit lowsize) 0 x)
                           (- lowsize lowbit)
                           (slice (+ -1 lowsize) lowbit y))))
  :hints (("Goal" :use (:instance logapp-of-bvchop
                                  (size (+ (- lowbit) lowsize))
                                  (size2 (+ (- lowbit) lowsize))
                                  (i (logtail lowbit y))
                                  (j (bvchop (+ 1 highbit (- lowsize)) x)))

           :cases ((and (integerp x) (integerp y))
                   (and (integerp x) (not (integerp y)))
                   (and (not (integerp x)) (integerp y)))
           :in-theory (e/d (bvcat slice ;bvchop-logapp
                                  bvchop-of-logapp-bigger
                                  bvchop-of-logtail)
                           (slice-becomes-bvchop
                            bvchop-of-logtail-becomes-slice
                            logapp-of-bvchop
                            bvcat-recombine)))))

(defthmd slice-tighten-top-2
  (implies (and (<= n high)
                (force (unsigned-byte-p n x))
                (natp low)
                (natp n)
                (natp high)
                )
           (equal (slice high low x)
                  (slice (+ -1 n) low x)))
  :otf-flg t
  :hints (("Goal" :cases ((equal 0 low)
                          (<= low n))
           :in-theory (e/d (slice) (bvchop-of-logtail-becomes-slice)))))

(defthm slice-of-bvcat-hack-2
  (implies (and (< lowbit lowsize)
;(>= highbit (+ lowsize highsize))
                (<= lowsize highbit)
;                (<= lowbit highbit)
                (natp lowsize)
                (natp highsize)
                (natp lowbit)
                (natp highbit))
           (equal (slice highbit lowbit (bvcat highsize x lowsize y))
                  (bvcat
                   (min highsize (+ highbit (- lowsize) 1))
                   (slice (min (- highbit lowsize) (+ -1 highsize)) 0 x) (- lowsize lowbit)
                   (slice (+ -1 lowsize) lowbit y))))
  :hints (("Goal" :use (:instance slice-tighten-top-2
                                  (x (bvcat highsize x lowsize y))
                                  (low lowbit)
                                  (high highbit)
                                  (n (+ lowsize highsize))))))

(defthm slice-of-bvcat-low-better
  (implies (and ; (<= lowbit highbit)
            (< highbit lowsize)
            (natp highbit)
            (natp lowbit)
            (natp highsize)
            (natp lowsize))
           (equal (slice highbit lowbit
                         (bvcat highsize highval lowsize lowval))
                  (slice highbit lowbit lowval)))
  :hints (("Goal" :cases ((<= lowbit highbit)))))

(defthm slice-of-bvcat-hack-gen-better
  (implies (and (natp lowsize)
                ;(integerp highsize) ;
                (natp highsize)
                (natp lowbit)
                (natp highbit))
           (equal (slice highbit lowbit (bvcat highsize x lowsize y))
                  (if (<= lowsize highbit)
                      (if (< lowbit lowsize)
                          (bvcat (min highsize (+ highbit (- lowsize) 1))
                                 (slice (min (- highbit lowsize)
                                             (+ -1 highsize))
                                        0 x)
                                 (- lowsize lowbit)
                                 (slice (+ -1 lowsize) lowbit y))
                          (slice (- highbit lowsize)
                                 (- lowbit lowsize)
                                 (bvchop highsize x)))
                    (slice highbit lowbit y)))))

(defthm slice-of-bvcat-hack-gen-better-case-1
  (implies (and (> lowsize highbit)
                (natp lowsize)
                (natp highsize)
                (natp lowbit)
                (natp highbit))
           (equal (slice highbit lowbit (bvcat highsize x lowsize y))
                  (slice highbit lowbit y))))


(defthm slice-of-bvcat-hack-gen-better-case-2
  (implies (and (<= lowsize highbit)
                (< lowbit lowsize)
                (natp lowsize)
                (natp highsize)
                (natp lowbit)
                (natp highbit))
           (equal (slice highbit lowbit (bvcat highsize x lowsize y))
                  (bvcat (min highsize (+ highbit (- lowsize) 1))
                         (slice (min (- highbit lowsize)
                                     (+ -1 highsize))
                                0 x)
                         (- lowsize lowbit)
                         (slice (+ -1 lowsize) lowbit y)))))

(defthm slice-of-bvcat-hack-gen-better-case-3
  (implies (and (<= lowsize highbit)
                (<= lowsize lowbit)
                (natp lowsize)
                (natp highsize)
                (natp lowbit)
                (natp highbit))
           (equal (slice highbit lowbit (bvcat highsize x lowsize y))
                  (slice (- highbit lowsize)
                         (- lowbit lowsize)
                         (bvchop highsize x)))))

(defthm slice-of-bvcat-gen
  (implies (and (natp lowsize)
                (natp highsize) ;(integerp highsize)
                (natp lowbit)
                (integerp highbit))
           (equal (slice highbit lowbit (bvcat highsize x lowsize y))
                  (if (< highbit lowsize)
                      (slice highbit lowbit y)
                    (if (< lowbit lowsize)
                        (bvcat
                         ;;should we lift the min?
                         (min highsize (+ highbit (- lowsize) 1))
                         x ;used to have a slice around this
                         (- lowsize lowbit)
                         (slice (+ -1 lowsize) lowbit y))
                      (slice (- highbit lowsize)
                             (- lowbit lowsize)
                             (bvchop highsize x))))))
  :hints (("Goal" :in-theory (enable natp)
           :cases ((natp highbit)))))

(defthmd bvcat-numeric-bound2-core
  (implies (and (<= (expt 2 (+ lowsize highsize)) k)
                (natp lowsize)
                (natp highsize))
           (equal (< (bvcat highsize highval lowsize lowval) k)
                  t))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvcat
                                  (n (+ lowsize highsize)))
           :in-theory (e/d (unsigned-byte-p) (unsigned-byte-p-of-bvcat2
                                              unsigned-byte-p-of-bvcat-all-cases
                                              unsigned-byte-p-of-bvcat
                                              unsigned-byte-p-of-bvcat-gen
                                              unsigned-byte-p-of-bvcat-gen2)))))

;kill the 64 version
(defthm bvcat-numeric-bound
  (implies (and (syntaxp (quotep k))
                (<= (expt 2 (+ lowsize highsize)) k)
                (natp lowsize)
                (natp highsize))
           (< (bvcat highsize highval lowsize lowval) k))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvcat
                                  (n (+ lowsize highsize)))
           :in-theory (e/d (unsigned-byte-p) (unsigned-byte-p-of-bvcat2
                                              unsigned-byte-p-of-bvcat
                                              unsigned-byte-p-of-bvcat-all-cases
                                              unsigned-byte-p-of-bvcat-gen
                                              unsigned-byte-p-of-bvcat-gen2)))))

;this one requires bvcats (with the same sizes) on both sides and so is less aggressive
(defthm bvcat-equal-bvcat
  (equal (equal (bvcat highsize highval1 lowsize lowval1)
                (bvcat highsize highval2 lowsize lowval2))
         (and (equal (bvchop highsize highval1)
                     (bvchop highsize highval2))
              (equal (bvchop lowsize lowval1)
                     (bvchop lowsize lowval2))))
  :hints (("Goal" :cases ((and (posp lowsize) (posp highsize))
                          (and (not (posp lowsize)) (posp highsize))
                          (and (posp lowsize) (not (posp highsize)))))))

(defthm bvcat-numeric-bound-nil
  (implies (and (syntaxp (quotep k))
                (<= (+ -1 (expt 2 (+ lowsize highsize))) k)
                (natp lowsize)
                (natp highsize))
           (equal (< k (bvcat highsize highval lowsize lowval))
                  nil))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvcat
                                  (n (+ lowsize highsize))
                                  )
           :in-theory (e/d (unsigned-byte-p) (unsigned-byte-p-of-bvcat2
                                              unsigned-byte-p-of-bvcat
                                              unsigned-byte-p-of-bvcat-all-cases
                                              unsigned-byte-p-of-bvcat-gen
                                              unsigned-byte-p-of-bvcat-gen2)))))

;fixme gen the 1
(defthm bvcat-equal-0-rewrite2
   (implies (natp size)
            (equal (equal 0 (bvcat 1 x size 0))
                   (equal (getbit 0 x) 0)))
   :hints (("Goal" :in-theory (e/d (;getbit bvcat slice
                                    )
                                   (slice-becomes-getbit)))))

;compare to others
(defthm bvcat-combine-constants-old
  (implies (and (syntaxp (and (quotep lowval)
                              (quotep lowval2)))
                (equal totalsize (+ lowsize2 highsize))
                (natp lowsize)
                (natp lowsize2)
                (natp highsize))
           (equal (bvcat totalsize (bvcat highsize highval lowsize2 lowval2) lowsize lowval)
                  (bvcat highsize highval (+ lowsize lowsize2) (bvcat lowsize2 lowval2 lowsize lowval)))))

;finally the full lemma!
(defthm slice-of-bvcat-hack-gen
  (implies (and (<= lowsize highbit)
                (natp lowsize)
                (natp highsize)
                (natp lowbit)
                (natp highbit)
                )
           (equal (slice highbit lowbit (bvcat highsize x lowsize y))
                  (if (< lowbit lowsize)
                      (bvcat (min highsize (+ highbit (- lowsize) 1))
                             (slice (min (- highbit lowsize) (+ -1 highsize)) 0 x) (- lowsize lowbit)
                             (slice (+ -1 lowsize) lowbit y))
                    (slice (- highbit lowsize) (- lowbit lowsize) (bvchop highsize x))))))

(defthm bvcat-combine-constants
  (implies (and (syntaxp (and (quotep highval)
                              (quotep highval2)
                              (quotep highsize2)
                              (quotep highsize)))
                (equal lowsize2 (+ highsize lowsize))
                (< 0 highsize2)
                (natp highsize)
                (natp lowsize)
                (natp highsize2))
           (equal (bvcat highsize2 highval2 lowsize2 (bvcat highsize highval lowsize lowval))
                  (bvcat (+ highsize2 highsize) (bvcat highsize2 highval2 highsize highval) lowsize lowval))))

;more like this?
(defthm bvcat-subst-1
  (implies (and (equal (getbit 0 x) free)
                (syntaxp (and (quotep free)
                              (not (quotep x)))))
           (equal (bvcat 1 x n y)
                  (bvcat 1 free n y))))

;gen the 1
(defthm equal-bvcat-0-right
  (implies (natp n)
           (equal (equal 0 (bvcat n x 1 0))
                  (equal 0 (bvchop n x)))))

;gen the 1
(defthm equal-bvcat-0-left
  (implies (natp n)
           (equal (equal (bvcat n x 1 0) 0)
                  (equal (bvchop n x) 0))))

;replace the other one?
(defthm bvcat-associative-gen
  (implies
   (and (>= highsize1 (+ lowsize2 highsize2))
;        (posp highsize) ;drop?
        (natp lowsize2)
        (natp lowsize1)
        (natp highsize2)
        (natp highsize1))
   (equal (bvcat highsize1
                 (bvcat highsize2 highval2 lowsize2 lowval2)
                 lowsize1 lowval1)
          (bvcat highsize2 highval2 (+ lowsize2 lowsize1)
                 (bvcat lowsize2 lowval2 lowsize1 lowval1))))
  :hints (("Goal" :in-theory (enable posp))))

(defthm logtail-of-bvcat-low
  (implies (and (< n lowsize)
                (natp lowsize)
                (natp n))
           (equal (logtail n (bvcat highsize x lowsize y))
                  (bvcat highsize x (- lowsize n) (slice (+ -1 lowsize) n y))))
  :hints (("Goal" :in-theory (e/d (slice bvchop-of-logtail) (bvchop-of-logtail-becomes-slice))
           :cases ((natp highsize)))))

(defthmd *-of-expt-and-/-of-expt-collect
  (implies (and (integerp i)
                (integerp j))
           (equal (* (expt 2 i) (/ (expt 2 j)) x)
                  (* (expt 2 (- i j)) x)))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm ifix-when-integerp
  (implies (integerp x)
           (equal (ifix x)
                  x)))

;can loop
(defthmd *-of-half-and-expt-of-one-more
  (implies (integerp n)
           (equal (* 1/2 (* m (expt 2 (+ 1 n))))
                  (* m (expt 2 n))))
  :hints (("Goal" :in-theory (e/d (expt) (expt-hack)))))

(defthm /-of-expt-of-diff
  (implies (and (natp i)
                (natp j))
           (equal (/ (expt 2 (+ (- i) j)))
                  (expt 2 (- i j))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm logtail-logapp-better
  (implies (and (integerp size1)
                (integerp size)
                (>= size 0))
           (equal (logtail size (logapp size1 i j))
                  (if (<= 0 size1)
                      (if (< size size1)
                          (logapp (- size1 size)
                                  (logtail size i)
                                  j)
                          (logtail (- size size1) j))
                    (logtail size j))))
  :otf-flg t
  :hints (("Goal" :use (:instance logtail-logapp (i (ifix i)))
           :in-theory (e/d (slice bvchop-of-logtail ;enable this?
                                  )
                           (logtail-logapp
                            bvchop-of-logtail-becomes-slice)))))

;todo handle other cases
(defthm logtail-of-bvcat-when-extends-into-upper
  (implies (and (<= lowsize n)
                (natp n)
                (natp lowsize))
           (equal (logtail n (bvcat highsize x lowsize y))
                  (logtail (- n lowsize) (bvchop highsize x))))
  :otf-flg t
  :hints (("Goal"
           :cases ((< (+ highsize lowsize) n)
                   (equal n lowsize)
                   )
           :in-theory (e/d ( ;logtail
                            bvcat
                            ;;logapp
                            zip floor-normalize-denominator
                            *-of-expt-and-/-of-expt-collect)
                           (floor-of-*-of-/-and-1
                            bvcat-recombine
                            ;;myexpt-minus ;dup
                            )))))

(defthm logtail-of-bvcat
  (implies (and (natp n)
                (natp lowsize)
                )
           (equal (logtail n (bvcat highsize x lowsize y))
                  (if (<= lowsize n)
                      (logtail (- n lowsize) (bvchop highsize x))
                    (bvcat highsize x (- lowsize n) (slice (+ -1 lowsize) n y))))))

(defthm bvcat-of-slice-and-slice-adjacent-2
  (implies (and (equal low1 (+ 1 high2))
                (equal size3 (+ high2 1 (- low2)))
                (equal size4 (+ high1 1 (- low1)))
                (equal size2 (+ size3 size))
                (<= low2 high2)
                (<= low1 high1)
                (natp size)
                (natp low2)
                (natp high2)
                (natp low1)
                (natp high1))
           (equal (bvcat size4 (slice high1 low1 x) size2 (bvcat size3 (slice high2 low2 x) size y))
                  (bvcat (+ 1 high1 (- low2)) (slice high1 low2 x) size y)))
  :hints (("Goal" :in-theory (enable natp))))

(defthm bvcat-of-slice-and-getbit-adjacent-2
  (implies (and (equal low1 (+ 1 index))
                (equal size4 (+ high1 1 (- low1)))
                (equal size2 (+ 1 size))
                (<= low1 high1)
                (natp size)
                (natp index)
                (natp low1)
                (natp high1))
           (equal (bvcat size4 (slice high1 low1 x) size2 (bvcat 1 (getbit index x) size y))
                  (bvcat (+ 1 high1 (- index)) (slice high1 index x) size y)))
  :hints (("Goal" :in-theory (enable natp))))

(defthm bvcat-of-getbit-and-slice-adjacent-2
  (implies (and (equal index (+ 1 high2))
                (equal size3 (+ high2 1 (- low2)))
                (equal size2 (+ size3 size))
                (<= low2 high2)
                (natp size)
                (natp low2)
                (natp high2)
                (natp index))
           (equal (bvcat 1 (getbit index x) size2 (bvcat size3 (slice high2 low2 x) size y))
                  (bvcat (+ 1 index (- low2)) (slice index low2 x) size y)))
  :hints (("Goal" :in-theory (enable natp))))

;fixme do i have the complete set of these?
(defthm bvcat-of-getbit-and-getbit-adjacent-2
  (implies (and (equal n (+ 1 m))
                (equal j (+ 1 size))
                (natp size)
                (natp m))
           (equal (bvcat 1 (getbit n x) j (bvcat 1 (getbit m x) size y))
                  (bvcat 2 (slice n m x) size y))))

(defthm bvcat-of-slice-and-x-adjacent-2
  (implies (and (equal size2 (+ low size))
                (equal size3 (+ high 1 (- low)))
                (<= low high)
                (natp size)
                (natp low)
                (natp high))
           (equal (bvcat size3 (slice high low x) size2 (bvcat low x size y))
                  (bvcat (+ 1 high) (slice high 0 x) size y)))
  :hints (("Goal" :in-theory (enable natp))))

(defthm bvcat-of-getbit-and-x-adjacent-2
  (implies (and (natp size)
                (natp n)
                (equal size2 (+ n size)))
           (equal (bvcat 1 (getbit n x) size2 (bvcat n x size y))
                  (bvcat (+ 1 n) (slice n 0 x) size y)))
  :hints (("Goal" :in-theory (enable natp))))

;;rules to tighten bvcat... (drop these since we have the gen one?)

(defthm bvcat-of-getbit-high-tighten
  (implies (and (< 1 highsize) ;this may loop if we allow highsize=1
                (integerp highsize)
                (natp lowsize)
                (natp n)
                )
           (equal (bvcat highsize (getbit n x) lowsize lowval)
                  (bvcat 1 (getbit n x) lowsize lowval))))

(defthm bvcat-of-bvcat-high-tighten
  (implies (and (< (+ highsize2 lowsize2) highsize) ;this may loop if we allow <=
                (natp highsize)
                (natp lowsize)
                (natp lowsize2)
                (< 0 lowsize2) ;todo?
                (natp highsize2)
                )
           (equal (bvcat highsize (bvcat highsize2 highval2 lowsize2 lowval2) lowsize lowval)
                  (bvcat (+ highsize2 lowsize2) (bvcat highsize2 highval2 lowsize2 lowval2) lowsize lowval))))

(defthmd bvcat-when-lowsize-is-not-positive
  (implies (<= lowsize 0)
           (equal (bvcat highsize highval lowsize lowval)
                  (bvchop highsize highval)))
  :hints (("Goal" :cases ((integerp lowval))
           :in-theory (e/d (bvcat) (bvcat-recombine)))))

(defthm bvcat-fix-constant-arg2
  (implies (and (syntaxp (and (quotep highval)
                              (quotep highsize)))
                (not (unsigned-byte-p highsize highval))
                (natp highsize) ;prevents loops
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize (bvchop highsize highval) lowsize lowval))))

(defthm bvcat-when-arg2-is-not-an-integer
  (implies (and (syntaxp (quotep highval))
                (not (integerp highval)))
           (equal (bvcat highsize highval lowsize lowval)
                  (bvchop lowsize lowval)))
  :hints (("Goal" :in-theory (e/d (bvcat) (BVCAT-RECOMBINE)))))

(defthm bvcat-fix-constant-arg4
  (implies (and (syntaxp (and (quotep lowval)
                              (quotep lowsize)))
                (not (unsigned-byte-p lowsize lowval))
                (natp lowsize) ;prevents loops
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize highval lowsize (bvchop lowsize lowval)))))

(defthm split-bv
  (implies (and (unsigned-byte-p n y)
                (natp m)
                (< 0 m)
                (natp n)
                (<= m n))
           (equal y
                  (bvcat (+ n (- m)) (slice (+ -1 n) m y)
                         m (bvchop m y))))
  :rule-classes nil)

(defthm unsigned-byte-p-of-mod-of-expt
  (implies (and (natp n)
                (integerp x))
           (unsigned-byte-p n (mod x (expt 2 n))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthmd equal-of-bvchop-and-bvchop-when-unsigned-byte-p-of-bvchop
  (implies (and (unsigned-byte-p size2 (bvchop size1 x))
                (<= size2 size1)
                (natp size1)
                ;(natp size2)
                )
           (equal (equal (bvchop size1 x)
                         (bvchop size2 x))
                  t))
  :hints (("Goal" :use (:instance bvchop-of-bvchop (size1 size2) (size size1) (i x))
           :in-theory (disable bvchop-of-bvchop))))

;this should fire after equal-same?
(defthm equal-of-bvchop-and-bvchop-same
  (implies (and (natp size1)
                (natp size2))
           (equal (equal (bvchop size1 x) (bvchop size2 x))
                  (equal 0 (slice (+ -1 (max size1 size2)) (min size1 size2) x))))
  :hints (("Goal" :in-theory (e/d (slice bvchop-of-logtail equal-of-bvchop-and-bvchop-when-unsigned-byte-p-of-bvchop)
                                  (bvchop-of-logtail-becomes-slice
                                   equal-of-bvchop-and-bvchop-when-unsigned-byte-p-of-bvchop))
           :use ((:instance equal-of-bvchop-and-bvchop-when-unsigned-byte-p-of-bvchop)
                 (:instance equal-of-bvchop-and-bvchop-when-unsigned-byte-p-of-bvchop (size1 size2) (size2 size1))))))

(local (include-book "../../ihs/math-lemmas"))

;loops with LOGTAIL-EQUAL-0
(defthmd unsigned-byte-p-of-bvchop-tighter
  (implies (and (< size n) ;not putting <= here even though i perhaps could
                (posp size) ;gen?
                (natp n))
           (equal (unsigned-byte-p size (bvchop n x))
                  (equal 0 (slice (+ -1 n) size x))))
  :hints (("Goal"
           :use (:instance split-bv (y (bvchop n x))
                           (m size)
                           (n n))
           :in-theory (disable bvcat-of-bvchop-low bvcat-equal-rewrite-alt bvcat-equal-rewrite
                               bvcat-of-0))))
