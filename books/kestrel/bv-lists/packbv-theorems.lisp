; More rules about packbv
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "packbv")
(include-book "kestrel/lists-light/subrange" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "bvchop-list")
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))

;see also logtail-of-packbv-gen
;use take instead of firstn?
(defthm logtail-of-packbv
  (implies (and (<= count (len bvs))
                (<= n count)
                (natp count)
                (natp n))
           (equal (logtail n (packbv count 1 bvs))
                  (packbv (- count n) 1 (firstn (- count n) bvs))))
  :hints (("Subgoal *1/2" :cases ((equal n count)))
          ("Goal" ;:induct (induct-cdr-double-sub-1 bvs n count)
           :induct (packbv count 1 bvs)
           :do-not '(generalize eliminate-destructors fertilize)
           :expand ((all-unsigned-byte-p 1 bvs))
;           :expand (firstn (+ count (- n)) bvs)
           :in-theory (e/d (packbv) (;logtail-becomes-slice-bind-free
                                     bvcat-equal-rewrite-alt
                                     bvcat-equal-rewrite)))))

;; (local
;;  (defthm <-of-+-of-unary-
;;   (equal (< (+ (- x) y) 0)
;;          (< y x))))

(defthm unsigned-byte-p-of-car-when-all-unsigned-byte-p-cheap
  (implies (all-unsigned-byte-p size bvs)
           (equal (unsigned-byte-p size (car bvs))
                  (consp bvs)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p))))

(local (include-book "arithmetic/inequalities" :dir :system))

(local
 (defthm cancel-helper
   (implies (and (< 0 size)
                 (rationalp size)
                 (rationalp x)
                 (rationalp y))
            (equal (< 0 (+ size (* x size) (- (* size y))))
                   (< 0 (+ 1 x (- y)))))
   :hints (("Goal" :use (:instance 0-<-* (x size)
                                   (y (+ 1 x (- y))))
            :in-theory (disable 0-<-*)))))

(local
 (defthm cancel-helper2
   (implies (and (< 0 size)
                 (rationalp size)
                 (rationalp x)
                 (rationalp y))
            (equal (< (* x size) (+ (- size) (* size y)))
                   (< x (+ -1 y))))
   :hints (("Goal" :use (:instance <-*-left-cancel (z size)
                                   (x x)
                                   (y (+ -1 y)))))))

(local
 (defthm cancel-helper3
   (implies (and (< 0 size)
                 (rationalp size)
                 (rationalp x)
                 (rationalp z)
                 (rationalp y))
            (equal (< (* x size) (+ (- (* z size)) (* size y)))
                   (< x (+ (- z) y))))
   :hints (("Goal" :use (:instance <-*-left-cancel (z size)
                                   (x x)
                                   (y (+ (- z) y)))))))

(local
 (defthm cancel-helper4
   (implies (and (< 0 size)
                 (rationalp size)
                 (rationalp x)
                 (rationalp z)
                 (rationalp y))
            (equal (< (* x size) (* size y))
                   (< x y)))
   :hints (("Goal" :use (:instance <-*-left-cancel (z size)
                                   (x x)
                                   (y y))))))

(local
 (defthm cancel-helper5
   (implies (and (< 0 size)
                 (rationalp size)
                 (rationalp x)
                 (rationalp z)
                 (rationalp y))
            (equal (< (* x size) (+ (- size) (* y size)))
                   (< x (+ (- 1) y))))
   :hints (("Goal" :use (:instance <-*-left-cancel (z size)
                                   (x x)
                                   (y (+ (- 1) y)))))))

;does not match very nicely because of the * in the LHS
(defthm logtail-of-packbv-gen
  (implies (and (<= count (len bvs))
                (<= n count)
                (natp count)
                (natp n)
                (posp size))
           (equal (logtail (* n size) (packbv count size bvs))
                  (packbv (- count n) size (firstn (- count n) bvs))))
  :hints (("subgoal *1/2" :cases ((equal n count)))
          ("Goal"
           :induct (packbv count size bvs)
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (PACKBV bvchop-of-logtail-becomes-slice)
                           (BVCAT-EQUAL-REWRITE-ALT
                            BVCAT-EQUAL-REWRITE
                            ;;zp-open ;causes problems?
                            )))))

;drop?
(defthm slice-of-packbv-1
  (implies (and (< high count)
                (<= low high)
                (natp count)
                (natp low)
                (natp high)
                (all-unsigned-byte-p 1 bvs)
                (equal (len bvs) count))
           (equal (slice high low (packbv count 1 bvs))
                  (packbv (+ 1 (- high low)) 1 (subrange (+ -1 (- high) (len bvs))
                                                         (+ -1 (- low) (len bvs)) bvs))))
  :hints (("Goal" :in-theory (e/d (slice take-of-nthcdr-becomes-subrange)
                                  (bvchop-of-logtail-becomes-slice)))))

(local (include-book "arithmetic/top-with-meta" :dir :system)) ;for cancellation

;does not match very well, due to the * in the LHS
(defthm bvchop-of-packbv-new
  (implies (and (<= n count)
                (posp size)
                (natp n)
                (natp count))
           (equal (bvchop (* n size) (packbv count size bvs))
                  (packbv n
                          size
                          (nthcdr (- count n) bvs))))
  :hints (("Goal" :in-theory (e/d (packbv) (floor-upper-bound-linear)))))

;does not match very well, indexing using slice is awkward
(defthm slice-of-packbv
  (implies (and (< high count)
                (<= low high)
                (natp count)
                (natp low)
                (natp high)
                (posp size)
;                (all-unsigned-byte-p size bvs)
                (equal (len bvs) count))
           (equal (slice (+ -1 (* size (+ 1 high)))
                         (* size low)
                         (packbv count size bvs))
                  (packbv (+ 1 (- high low)) size (subrange (+ -1 (- high) (len bvs))
                                                            (+ -1 (- low) (len bvs))
                                                            bvs))))
  :hints (("Goal" :in-theory (e/d (slice take-of-nthcdr-becomes-subrange)
                                  (bvchop-of-logtail-becomes-slice
                                   bvchop-of-packbv-new))
           :use (:instance bvchop-of-packbv-new
                            (n (+ 1 high (- low)))
                            (count (+ (- low) (len bvs)))
                            (bvs (take (+ (- low) (len bvs)) bvs))))))

(defthm slice-of-packbv-alt
  (implies (and (< high count)
                (<= low high)
                (natp count)
                (natp low)
                (natp high)
                (posp size)
                (equal (len bvs) count))
           (equal (slice (+ -1 (* (+ 1 high) size))
                         (* low size)
                         (packbv count size bvs))
                  (packbv (+ 1 (- high low)) size (subrange (+ -1 (- high) (len bvs))
                                                            (+ -1 (- low) (len bvs))
                                                            bvs))))
  :hints (("Goal" :use (:instance slice-of-packbv)
           :in-theory (disable slice-of-packbv))))

;special case of low=1
(defthm slice-of-packbv-special
  (implies (and (< high count)
                (<= 1 high)
                (natp count)
                (natp high)
                (posp size)
                (equal (len bvs) count))
           (equal (slice (+ -1 (* (+ 1 high) size))
                         size
                         (packbv count size bvs))
                  (packbv high
                          size
                          (subrange (+ -1 (- high) (len bvs))
                                    (+ -2 (len bvs))
                                    bvs))))
  :hints (("Goal" :use (:instance slice-of-packbv (low 1))
           :in-theory (disable slice-of-packbv))))

(defthm packbv-of-if
  (equal (packbv num 1 (if test x y))
         (if test (packbv num 1 x)
           (packbv num 1 y))))

(defthm slice-of-packbv-8-special-case
  (implies (and (natp n)
                (< 0 n)
                (equal (len bvs) n) ;gen?
                )
           (equal (slice (+ -1 (* 8 n)) 8 (packbv n 8 bvs))
                  (packbv (+ -1 n)
                                8
                                ;;could use butlast or firstn here:
                                (subrange 0 ;(+ (- n) (len bvs))
                                                (+ -2 (len bvs))
                                                bvs))))
  :hints (("Goal" :use (:instance slice-of-packbv
                                  (size 8)
                                  (low 1)
                                  (high (- n 1))
                                  (count n)
                                  (bvs bvs)
                                  )
           :in-theory (disable slice-of-packbv))))


;; (defthm lemma
;;   (implies (and (rationalp itemsize)
;;                 (not (equal 0 ITEMSIZE))
;;                 (rationalp x))
;;            (equal (BINARY-* ITEMSIZE (BINARY-* (UNARY-/ ITEMSIZE) x))
;;                   x)))

(defthm packbv-of-append
  (implies (and (equal itemcount (+ (len l1) (len l2)))
                (posp itemsize))
           (equal (packbv itemcount itemsize (append l1 l2))
                  (bvcat (* (len l1) itemsize)
                         (packbv (len l1) itemsize l1)
                         (* (len l2) itemsize)
                         (packbv (len l2) itemsize l2))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :cases ((equal 0 (len l1)))
           :use (:instance slice-of-packbv
                           (high (+ -1 (len l1) (len l2)))
                           (low (len l2))
                           (size itemsize)
                           (count (+ (LEN L1) (LEN L2)))
                           (bvs (append l1 l2))
                           )
           :expand (packbv (+ (len l1) (len l2))
                           1 (cons (car l1) (append (cdr l1) l2)))
           :in-theory (e/d (;mod-=-0
                            equal-of-0-and-mod
                            )
                           (bvcat-equal-rewrite
                            slice-of-packbv)))))

(defthmd packbv-of-cdr
  (implies (and (equal n (+ -1 (len bvs)))
                (posp itemsize))
           (equal (packbv n itemsize (cdr bvs))
                  (bvchop (* n itemsize) (packbv (+ 1 n) itemsize bvs))))
  :hints (("Goal" :in-theory (enable ;mod-=-0
                              ))))

;consider packbv of lastn

(defthm equal-of-packbv-and-packbv
  (implies (posp size)
           (equal (equal (packbv n size x)
                         (packbv n size y))
                  (equal (bvchop-list size (take n x))
                         (bvchop-list size (take n y)))))
  :hints (("Goal" :induct t
           :in-theory (e/d (packbv take floor-minus-eric-better)
                           (bvchop-upper-bound)))))
