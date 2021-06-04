; Mixed theorems about slice
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "slice")
(include-book "bvplus")
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))

;move
;gen the bvchops
(defthm usigned-byte-p-of-+-of-bvchop-and-bvchop-one-more
  (implies (and (integerp size) (<= 0 size))
           (unsigned-byte-p (+ 1 size)
                            (+ (bvchop size x) (bvchop size y))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p EXPT-OF-+))))

(defthm logtail-of-plus-helper
  (implies (and (integerp x)
                (natp size)
                (integerp y))
           (equal (logtail size (+ x y))
                  (if (>= (+ (bvchop size x) (bvchop size y))
                          (expt 2 size))
                      (+ 1 (logtail size x) (logtail size y))
                    (+ (logtail size x) (logtail size y)))))
  :hints (("Goal" :in-theory (e/d (logtail floor-of-sum bvchop ;bvplus
                                           ;;mod-cancel
                                           )
                                  (mod-of-expt-of-2)))))

(defthm logtail-of-plus
  (implies (and (integerp x)
                (natp size)
                (integerp y))
           (equal (logtail size (+ x y))
                  (if (>= (bvplus (+ 1 size) (bvchop size x) (bvchop size y))
                          (expt 2 size))
                      (+ 1 (logtail size x) (logtail size y))
                    (+ (logtail size x) (logtail size y)))))
  :hints (("Goal" :use (:instance logtail-of-plus-helper)
           :in-theory (e/d (bvplus expt-of-+) ( logtail-of-plus-helper
                                      ;anti-bvplus
                                      )))))

(defthmd slice-of-sum-cases
  (implies (and (natp low)
                (natp high)
                (integerp x)
                (integerp y))
           (equal (slice high low (+ x y))
                  (if (< high low)
                      0
                    (if (<= (expt 2 low)
                            (+ (bvchop low x)
                               (bvchop low y)))
                        ;;if carry
                        (bvchop (+ 1 high (- low))
                                (+ 1
                                   (slice high low x)
                                   (slice high low y)))
                      ;;no carry:
                      (bvchop (+ 1 high (- low))
                              (+ (slice high low x)
                                 (slice high low y)))))))
  :hints (("Goal" :in-theory (e/d (slice bvchop-of-sum-cases bvplus logtail-of-bvchop expt-of-+)
                                  ( ;bvlt-of-plus-arg2 bvlt-of-plus-arg1
                                   ;anti-slice
                                   bvchop-of-logtail
                                   ;;logtail-of-sum
                                   )))))

(defthm logtail-of-minus
  (implies (and (integerp x)
                (natp size))
           (equal (logtail size (- x))
                  (if (equal 0 (bvchop size x))
                      (- (logtail size x))
                    (+ -1 (- (logtail size x))))))
  :hints (("Goal" :in-theory (e/d (logtail bvchop FLOOR-MINUS-ARG1
                                           EQUAL-OF-0-AND-MOD)
                                  (MOD-OF-EXPT-OF-2)))))

(defthm slice-of-minus
  (implies (and (integerp x)
                (<= low high)
                (natp low)
                (integerp high)
                )
           (equal (slice high low (- x))
                  (if (equal (bvchop low x) 0)
                      (bvchop (+ 1 high (- low)) (- (slice high low x)))
                    (bvchop (+ 1 high (- low)) (+ -1 (expt 2 (+ 1 high (- low))) (- (slice high low x)))))))
  :hints (("Goal" :in-theory (e/d (slice bvplus bvchop-of-sum-cases)
                                  (;anti-slice ;anti-bvplus
;bvlt-of-plus-arg1 bvlt-of-plus-arg2
                                   )))))
