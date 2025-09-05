; More theorems about repeatbit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "repeatbit")
(include-book "bvchop")
(include-book "logtail")
(include-book "slice-def")
(include-book "bvif") ; todo: factor out the def
(local (include-book "slice"))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

(defthm bvchop-of-repeatbit
  (implies (and (integerp n)
                (integerp size))
           (equal (bvchop n (repeatbit size bit))
                  (repeatbit (min n size) bit)))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm logtail-of-repeatbit
  (implies (and (<= n size)
                (natp n)
                (integerp size))
           (equal (logtail n (repeatbit size bit))
                  (repeatbit (- size n) bit)))
  :hints (("Goal" :in-theory (enable repeatbit logtail
                                     expt-of-+))))

(defthm slice-of-repeatbit
   (implies (and (natp low)
                 (natp high)
                 (integerp size))
            (equal (slice high low (repeatbit size bit))
                   (repeatbit (+ (min size (+ 1 high))
                                 (- low)) bit)))
   :hints (("Goal" :do-not '(preprocess)
            :use (:instance BVCHOP-OF-MASK-OTHER
                            (size2 (+ 1 HIGH (- LOW)))
                            (size1 (- size low))
                            )
            :in-theory (e/d (repeatbit slice
                             ;bvplus bvchop logtail
                                       )
                            (;anti-slice
                             bvchop-of-mask-other)))))

;; Gets rid of repeatbit (e.g., for STP)
(defthmd repeatbit-becomes-bvif
  (implies (syntaxp (quotep n))
           (equal (repeatbit n x)
                  (let ((bit (bvchop 1 x)))
                    (bvif n
                          (equal bit 1)
                          (+ -1 (expt 2 n)) ; should get evaluated
                          0))))
  :hints (("Goal" :in-theory (enable repeatbit))))
