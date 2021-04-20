; Mixed theorems about bit-vector operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rules") ;drop?
(include-book "getbit")
(include-book "repeatbit")
(local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system))
(local (include-book "arith"))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
;(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;todo

;(local (in-theory (enable boolor booland)))

; if x has a zero in it, and is negative, it can't be too big
(defthm getbit-of-0-bound-when-negative
  (implies (and (< x 0)
                (equal 0 (getbit n x))
                (integerp x)
                (natp n))
           (< x (- (expt 2 n))))
  :rule-classes (:rewrite ;:linear
                 )
  :hints (("Goal" :in-theory (e/d (getbit slice logtail)
                                  (SLICE-BECOMES-GETBIT
                                   BVCHOP-1-BECOMES-GETBIT
                                   BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

(defthmd high-slice-when-negative
  (implies (and (< x 0)
                (<= (- (expt 2 n)) x)
                (<= n low)
                (<= low high)
                (natp low)
                (integerp x)
                (natp n)
                (integerp high))
           (equal (slice high low x)
                  (repeatbit (+ 1 high (- low)) 1)))
  :hints (("Goal" :in-theory (e/d (getbit slice logtail)
                                  (slice-becomes-getbit
                                   bvchop-1-becomes-getbit
                                   bvchop-of-logtail-becomes-slice)))))

;may need GETBIT-EQUAL-1-POLARITY -- move it!
;; any bit above the sign bit is the same as the sign bit
(defthm getbit-when-signed-byte-p-high-helper
  (implies (and (signed-byte-p size x)
                (< (+ -1 size) n) ;this is only in the helper
                (posp size)
                (natp n))
           (equal (getbit n x)
                  (getbit (+ -1 size) x)))
  :rule-classes nil
  :hints (("Goal" :cases ((equal 1 (getbit (+ -1 size) x)))
           :use (:instance getbit-of-0-bound-when-negative)
           :in-theory (e/d (signed-byte-p getbit-too-high posp)
                           (getbit-of-0-bound-when-negative)))))

;todo: generalize this to the result of getting an upper slice?
(defthm getbit-when-signed-byte-p-high
  (implies (and (signed-byte-p size x)
                (<= size n) ;true for n=size-1 as well, but that could loop
                (posp size)
                (natp n))
           (equal (getbit n x)
                  (getbit (+ -1 size) x)))
  :hints (("Goal" :use (:instance getbit-when-signed-byte-p-high-helper))))

(defthm slice-when-signed-byte-p-high
  (implies (and (signed-byte-p size x)
                (<= (+ -1 size) low)
                (<= low high)
                (natp low)
                (natp high)
                (posp size)
                (natp n))
           (equal (slice high low x)
                  (repeatbit (+ 1 high (- low))
                             (getbit (+ -1 size) x))))
  :hints (("Goal" :cases ((and (< x 0) (equal 0 (GETBIT (+ -1 SIZE) X)))
                          (and (< x 0) (equal 1 (GETBIT (+ -1 SIZE) X)))
                          )
           :in-theory (enable SIGNED-BYTE-P
                              GETBIT-TOO-HIGH
                              SLICE-TOO-HIGH-HELPER
                              high-slice-when-negative))))

(DEFTHM BVCHOP-PLUS-TIMES-EXPT-LOGTAIL
  (IMPLIES (AND (INTEGERP X) (<= 0 SIZE))
           (EQUAL (+ (BVCHOP SIZE X)
                     (* (EXPT 2 SIZE) (LOGTAIL SIZE X)))
                  X))
  :HINTS
  (("Goal"
    :IN-THEORY
    (E/D (BVCHOP LOGTAIL MOD)
         (;MOD-RECOLLAPSE-LEMMA MOD-RECOLLAPSE-LEMMA2
          MOD-OF-EXPT-OF-2)))))

(defthm <-of-times-expt-logtail-cancel
  (implies (and (integerp x)
                (natp size))
           (equal (< (+ y (* (EXPT 2 size) (LOGTAIL size X))) X)
                  (< y (bvchop size x))))
  :hints (("Goal" :use (:instance bvchop-plus-times-expt-logtail)
           :in-theory (disable bvchop-plus-times-expt-logtail))))

(defthm <-of-times-expt-logtail-cancel2
  (implies (and (integerp x)
                (natp size))
           (equal (< X (+ y (* (EXPT 2 size) (LOGTAIL size X))))
                  (< (bvchop size x) y)))
  :hints (("Goal" :use (:instance bvchop-plus-times-expt-logtail)
           :in-theory (disable bvchop-plus-times-expt-logtail))))

(defthm distributivity-alt
  (equal (* (+ y z) x)
         (+ (* y x) (* z x))))

(defthm low-bits-dont-matter
  (implies (and (< x y)
                (< z (expt 2 n))
                (integerp x)
                (integerp z)
                (integerp y)
                )
           (< (+ z (* (expt 2 n) x))
              (* (expt 2 n) y)))
  :hints (("Goal" :in-theory (disable ;ineq-hack2 ineq-hack
                              *-preserves->=-for-nonnegatives <-*-right-cancel *-preserves->-for-nonnegatives-1)
           :use (:instance multiply-both-sides-hack (x y) (y (+ 1 x)) (z (expt 2 n))))))

(defthm logtail-times-expt-bound
  (implies (and (integerp x)
                (Natp size))
           (<= (* (EXPT 2 size) (LOGTAIL size X)) x))
  :hints (("Goal" :use (:instance bvchop-plus-times-expt-logtail)
           :in-theory (disable bvchop-plus-times-expt-logtail))))

(defthm plus-of-times-expt-bound
  (implies (and (< hv (logtail lowsize x))
                (integerp hv)
                (natp lowsize)
                (unsigned-byte-p lowsize lv)
                (integerp x)
                )
           (< (+ lv (* hv (expt 2 lowsize)))
              x))
  :hints (("Goal" :use ((:instance logtail-times-expt-bound (size lowsize))
                        (:instance low-bits-dont-matter (z lv) (n lowsize) (x hv) (y (LOGTAIL LOWSIZE X))))
           :in-theory (disable bvchop-plus-times-expt-logtail low-bits-dont-matter LOGTAIL-TIMES-EXPT-BOUND))))

;not tight?
(defthm plus-of-times-expt-bound2
  (implies (and (< (logtail lowsize x) hv)
                (integerp hv)
                (natp lowsize)
                (integerp x)
                (natp pos)
                )
           (not (< (+ pos (* hv (expt 2 lowsize))) x)))
  :hints (("Goal" :use ((:instance logtail-times-expt-bound (size lowsize))
                        (:instance low-bits-dont-matter (z lv) (n lowsize) (x hv) (y (LOGTAIL LOWSIZE X))))
           :in-theory (disable bvchop-plus-times-expt-logtail low-bits-dont-matter LOGTAIL-TIMES-EXPT-BOUND))))

(defthm logapp-less-than
  (implies (and (natp lowsize)
                (natp highsize)
                (integerp x)
                (integerp highval)
                )
           (equal (< (logapp lowsize lowval highval) x)
                  (or (< highval (logtail lowsize x))
                      (and (equal highval (logtail lowsize x))
                           (< (bvchop lowsize lowval) (bvchop lowsize x))))))
  :hints (("Goal"
           :use (;(:instance plus-of-times-expt-bound2 (hv highval))
                 ;(:instance plus-of-times-expt-bound (lv (BVCHOP LOWSIZE LOWVAL)) (hv highval))
                 )
           :in-theory (e/d (logapp slice) (;plus-of-times-expt-bound2
                                           ;PLUS-OF-TIMES-EXPT-BOUND
                                           anti-slice)))))

(defthm <-of-bvcat
  (implies (and (natp lowsize)
                (natp highsize)
                (natp x) ;gen
;(unsigned-byte-p (+ highsize lowsize) x)
                )
           (equal (< (bvcat highsize highval lowsize lowval) x)
                  (if (< x 0)
                      nil
                    (if (<= (expt 2 (+ lowsize highsize)) x)
                        t
                      (or (< (bvchop highsize highval)
                             (slice (+ -1 highsize lowsize)
                                    lowsize
                                    x))
                          (and (equal (bvchop highsize highval)
                                      (slice (+ -1 highsize lowsize)
                                             lowsize
                                             x))
                               (< (bvchop lowsize lowval)
                                  (bvchop lowsize x))))))))
  :hints (("Goal" :in-theory (e/d (bvcat slice
                                         ) (anti-slice)))))

(defthm bvlt-of-bvcat-arg2
  (implies (and (equal size (+ lowsize highsize))
                (natp lowsize)
                (natp highsize))
           (equal (bvlt size (bvcat highsize x lowsize y) k)
                  ;;redid conc
                  (boolor (bvlt highsize x (slice (+ -1 size) lowsize k))
                          (booland (equal (bvchop highsize x) (slice (+ -1 size) lowsize k))
                                   (bvlt lowsize y k)))))
  :hints (("Goal" :in-theory (e/d (bvlt)
                                  (<-becomes-bvlt <-becomes-bvlt-alt
;                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthmd logapp-less-than-alt-helper-1
  (IMPLIES (AND (NATP LOWSIZE)
                (NATP HIGHSIZE)
                (INTEGERP X)
                (INTEGERP HIGHVAL)
                (< (LOGTAIL LOWSIZE X) HIGHVAL))
           (< X
              (+ (BVCHOP LOWSIZE LOWVAL)
                 (* HIGHVAL (EXPT 2 LOWSIZE)))))
  :hints (("Goal" :use (:instance multiply-both-sides-hack (x (LOGTAIL LOWSIZE X)) (y (+ 1 HIGHVAL)) (z (expt 2 lowsize)))
           :in-theory (disable multiply-both-sides-hack))))

;; (< HIGHVAL (LOGTAIL LOWSIZE X))
;; (<= (+ 1 HIGHVAL) (LOGTAIL LOWSIZE X))
(defthm logapp-less-than-alt-helper-2
  (IMPLIES (AND (NATP LOWSIZE)
                (NATP HIGHSIZE)
                (INTEGERP X)
                (INTEGERP HIGHVAL)
                (<= HIGHVAL (LOGTAIL LOWSIZE X))
                (NOT (EQUAL HIGHVAL (LOGTAIL LOWSIZE X))))
           (<= (+ (BVCHOP LOWSIZE LOWVAL)
                  (* HIGHVAL (EXPT 2 LOWSIZE)))
               X))
  :hints (("Goal" :use ((:instance bvchop-plus-times-expt-logtail (size lowsize))
                        (:instance multiply-both-sides-hack (x (LOGTAIL LOWSIZE X)) (y (+ 1 HIGHVAL)) (z (expt 2 lowsize))))
           :in-theory (disable LOGTAIL-LESSP bvchop-plus-times-expt-logtail)
           )))

(defthm logapp-less-than-alt
  (implies (and (natp lowsize)
                (natp highsize)
                (integerp x)
                (integerp highval)
                )
           (equal (< x (logapp lowsize lowval highval))
                  (or (< (logtail lowsize x) highval)
                      (and (equal highval (logtail lowsize x))
                           (< (bvchop lowsize x)
                              (bvchop lowsize lowval))))))
  :hints (("Goal"
           :use ( ;(:instance multiply-both-sides-hack (x (LOGTAIL LOWSIZE X)) (y (+ 1 HIGHVAL)) (z (expt 2 lowsize)))
                 )
           :in-theory (e/d (logapp slice  logapp-less-than-alt-helper-1)
                           ( ;;plus-of-times-expt-bound2
                            PLUS-OF-TIMES-EXPT-BOUND
                            anti-slice
                            logtail-lessp
                            multiply-both-sides-hack
                            )))))

(defthm <-of-bvcat-alt-helper
  (implies (and (natp lowsize)
                (natp highsize)
                (natp x)
                (unsigned-byte-p (+ highsize lowsize) x)
                )
           (equal (< x (bvcat highsize highval lowsize lowval))
                  (if (< x 0)
                      t
                    (if (<= (expt 2 (+ lowsize highsize)) x)
                        nil
                      (or (< (slice (+ -1 highsize lowsize) lowsize x)
                             (bvchop highsize highval))
                          (and (equal (bvchop highsize highval)
                                      (slice (+ -1 highsize lowsize)
                                             lowsize
                                             x))
                               (< (bvchop lowsize x)
                                  (bvchop lowsize lowval))))))))
  :hints (("Goal" :in-theory (e/d (bvcat slice) (anti-slice)))))

(defthm <-of-bvcat-alt
  (implies (and (natp lowsize)
                (natp highsize)
                (natp x))
           (equal (< x (bvcat highsize highval lowsize lowval))
                  (if (< x 0)
                      t
                    (if (<= (expt 2 (+ lowsize highsize)) x)
                        nil
                      (or (< (slice (+ -1 highsize lowsize) lowsize x)
                             (bvchop highsize highval))
                          (and (equal (bvchop highsize highval)
                                      (slice (+ -1 highsize lowsize)
                                             lowsize
                                             x))
                               (< (bvchop lowsize x)
                                  (bvchop lowsize lowval))))))))
  :hints (("Goal" :use ((:instance BVCAT-NUMERIC-BOUND (k (EXPT 2 (+ LOWSIZE HIGHSIZE))))
                        (:instance <-of-bvcat-alt-helper))
           :in-theory (e/d (UNSIGNED-BYTE-P)(<-OF-BVCAT <-of-bvcat-alt-helper)))))

(defthm bvlt-of-bvcat-arg3
  (implies (and (equal size (+ lowsize highsize))
                (natp lowsize)
                (natp highsize))
           (equal (bvlt size k (bvcat highsize x lowsize y))
                  ;redid conc
                  (boolor (bvlt highsize (slice (+ -1 size) lowsize k) x)
                          (booland (equal (bvchop highsize x) (slice (+ -1 size) lowsize k))
                                   (bvlt lowsize k y)))))
  :hints (("Goal" :in-theory (e/d (bvlt)
                                  (<-becomes-bvlt <-becomes-bvlt-alt
;                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

;dangerous since we have a rule to take out the bvchop
(defthmd bvlt-of-bvcat-trim-gen
  (implies (< size (+ lowsize highsize))
           (equal (bvlt size (bvcat highsize x lowsize y) k)
                  (bvlt size (trim size (bvcat highsize x lowsize y)) k)))
  :hints (("Goal" :in-theory (enable trim))))

;these is a worse version of this in MUSE somewhere
(defthm sbvlt-of-bvsx-arg2
  (implies (and (signed-byte-p size2 y)
;                (natp size)
 ;               (natp size2)
                (posp size) ;gen
                (posp size2) ;gen
                (<= size2 size))
           (equal (sbvlt size (bvsx size size2 x) y)
                  (sbvlt size2 x y)))
  :hints (("Goal" :cases ((equal size size2))
           :in-theory (e/d (bvsx bvlt-of-bvcat-trim-gen boolor bvlt trim sbvlt-rewrite)
                                  (EXPONENTS-ADD
                                   ;BVCAT-OF-+-HIGH ;looped
                                   BVLT-OF-BVCHOP-ARG3-SAME
                                   BVLT-OF-BVCHOP-ARG2
                                   EXPONENTS-ADD-FOR-NONNEG-EXPONENTS
                                   )))))
