; Mixed theorems about bit-vector operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "sbvlt")
(include-book "bvlt")
(include-book "kestrel/utilities/myif-def" :dir :system)
(include-book "kestrel/booleans/boolor" :dir :system)
(local (include-book "logext"))
(local (include-book "logapp"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;;Splits into cases based on the signs of x and y
(defthmd sbvlt-rewrite
  (implies (posp size)
           (equal (sbvlt size x y)
                  (if (equal 0 (getbit (+ -1 size) x))
                      (if (equal 0 (getbit (+ -1 size) y))
                          ;; both non-negative:
                          (bvlt (+ -1 size) x y)
                        ;; x non-negative, y negative:
                        nil)
                    (if (equal 0 (getbit (+ -1 size) y))
                        ;; x negative, y non-negative:
                        t
                      ;; both negative:
                      (bvlt (+ -1 size) x y)))))
  :hints (("Goal" :in-theory (enable sbvlt bvlt ;LOGEXT-BECOMES-BVCHOP-WHEN-POSITIVE
                                         logext-when-negative logext-when-negative-2))))

;; To convert an sbvlt into a bvlt, we could use unsigned-byte-p claims, claims
;; equating the top bits of values with constants (with non-zero upper bit), or
;; sbvlt claims.  Of course, one val may just be a small constant...

(defthm sbvlt-becomes-bvlt-better
  (implies (and (unsigned-byte-p (+ -1 size) x)
                (unsigned-byte-p (+ -1 size) y)
                (posp size))
           (equal (sbvlt size x y)
                  (bvlt (+ -1 size) x y)))
  :hints (("Goal" :in-theory (enable sbvlt bvlt))))

;fixme weaken hyps to sbvle?  hmm. then it might loop when y is '0?!
;expensive..
(defthmd sbvlt-becomes-bvlt
  (implies (and (sbvlt size 0 x)
                (sbvlt size 0 y)
                (posp size))
           (equal (sbvlt size x y)
                  (bvlt (+ -1 size) x y)))
  :hints (("Goal" :use (:instance sbvlt-becomes-bvlt-better
                                  (x (bvchop size x))
                                  (y (bvchop size y))
                                  (size size))
           :in-theory (e/d (sbvlt <-of-0-and-logext-alt
                                  unsigned-byte-p-of-bvchop-one-more
                                  logext)
                           (sbvlt-becomes-bvlt-better)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;gen?
; but myif-of-nil-special seems to not fire
(defthm myif-of-sbvlt-of-0-and-equal-of-0
  (equal (myif (sbvlt size 0 x) nil (equal 0 x))
         (equal x 0))
  :hints (("Goal" :in-theory (enable myif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm boolor-of-sbvlt-of-constant-and-sbvlt-of-constant
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
           (equal (boolor (sbvlt size x k1)
                          (sbvlt size x k2))
                  (if (sbvle size k1 k2) ;gets computed
                      (sbvlt size x k2)
                    (sbvlt size x k1))))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-2
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
           (equal (boolor (sbvlt size k1 x)
                          (sbvlt size k2 x))
                  (if (sbvle size k2 k1) ;gets computed
                      (sbvlt size k2 x)
                    (sbvlt size k1 x))))
  :hints (("Goal" :in-theory (enable sbvlt))))
