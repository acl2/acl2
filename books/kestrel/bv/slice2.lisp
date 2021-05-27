; More rules about slice
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/polarity" :dir :system)
(include-book "slice")
(include-book "unsigned-byte-p-forced")
(include-book "bvcat")
(include-book "bv-syntax")
(local (include-book "unsigned-byte-p"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system))

(defthm <-tighten-when-slice-is-0
  (implies (and (syntaxp (want-to-strengthen (< x k)))
                (equal (slice high low x) 0) ;gen the 0?
                (syntaxp (quotep high))
                (syntaxp (quotep low))
                (natp high)
                (natp low)
                (<= low high)
                (<= k (expt 2 (+ 1 high)))
                (< (expt 2 low) k) ;prevents loops
                (natp k)
                (natp x)
                )
           (equal (< x k)
                  (< x (expt 2 low))))
  :hints (("Goal"
           :cases ((unsigned-byte-p (+ 1 high) x))
           :in-theory (e/d (slice) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

;consider enabling or improving
(defthmd usb-slice-helper
  (IMPLIES (AND (UNSIGNED-BYTE-P N X)
                (< M N)
                (EQUAL (SLICE (+ -1 N) M X) 0)
                (NATP M)
                (NATP N)
                )
           (UNSIGNED-BYTE-P M X))
  :hints (("Goal" :use (:instance BVCAT-SLICE-SAME ;(x x)
                                  (n m)
                                  (k (+ -1 n))
                                  (m (- n m)))
           :in-theory (e/d (BVCAT-OF-0) ( BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE
                                                             ;DAGIFY-INSIDE-HIDE-META-RULE
                                                           )))))

;ex: (UNSIGNED-BYTE-P 8 (BVXOR 9 X$0 X$1))
;not sure where this should go
(defthm rewrite-unsigned-byte-p-when-term-size-is-larger
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'x-size x) (x-size))
                (< n x-size)
                (natp n)
                (force (natp x-size))
                (force (unsigned-byte-p-forced x-size x)))
           (equal (unsigned-byte-p n x)
                  (equal (slice (+ -1 x-size) n  x)
                         0)))
  :hints (("Goal" :in-theory (enable SLICE-TOO-HIGH-IS-0 usb-slice-helper usb-slice-helper unsigned-byte-p-forced))))
