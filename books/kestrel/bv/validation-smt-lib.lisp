; Theorems to validate the SMT-LIB translation of the BV operators
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvuminus")
(include-book "bvminus")
(include-book "bvnot")
(include-book "bvand")
(include-book "bvor")
(include-book "bvxor")
(include-book "sbvdiv")
(include-book "bvdiv")
(local (include-book "sbvdiv-rules"))
(local (include-book "sbvlt-rules"))
(local (include-book "bvcat"))
(local (include-book "logand-b"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;; Validation theorems for a future SMT-LIB translation.
;; See https://smtlib.cs.uiowa.edu/logics-all.shtml

;; TODO: Push back some of the helper rules here to libraries

(local
 (defthm helper
   (implies (natp size)
            (equal (logand (bvchop size x)
                           (lognot (bvchop size y)))
                   (logand (bvchop size x)
                           (bvchop size (lognot y)))))
   :hints (("Goal" :use ((:instance logand-of-bvchop
                                    (x (bvchop size x))
                                    (y (lognot (bvchop size y)))
                                    (m size)))))))

;; (bvxor s t) abbreviates (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
(thm
 (implies (natp size)
          (equal (bvxor size x y)
                 (bvor size
                       (bvand size x (bvnot size y))
                       (bvand size (bvnot size x) y))))
 :hints (("Goal" :in-theory (enable bvxor bvand bvnot bvor))))

;; (bvsub s t) abbreviates (bvadd s (bvneg t))
(thm
 (implies (natp size)
          (equal (bvminus size x y)
                 (bvplus size x (bvuminus size y))))
 :hints (("Goal" :in-theory (enable bvminus bvuminus bvplus))))

(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;move, gen
(defthm bvdiv-of-+-of-expt-same-arg2
  (implies (and (natp size)
                (integerp x))
           (equal (bvdiv size (+ (expt 2 size) x) y)
                  (bvdiv size x y)))
  :hints (("Goal" :in-theory (enable bvdiv))))

(defthm bvdiv-of-+-of-expt-same-arg3
  (implies (and (natp size)
                (integerp y))
           (equal (bvdiv size x (+ (expt 2 size) y))
                  (bvdiv size x y)))
  :hints (("Goal" :in-theory (enable bvdiv))))

(defthm bvdiv-of---of-bvchop-arg2
  (implies (and (natp size)
                (integerp x))
           (equal (bvdiv size (- (bvchop size x)) y)
                  (bvdiv size (- x) y)))
  :hints (("Goal" :in-theory (enable bvdiv))))

(defthm bvdiv-of---of-bvchop-arg3
  (implies (and (natp size)
                (integerp y))
           (equal (bvdiv size x (- (bvchop size y)))
                  (bvdiv size x (- y))))
  :hints (("Goal" :use ((:instance bvdiv-of-bvchop-arg3-same (y (- y)))
                        (:instance bvdiv-of-bvchop-arg3-same (y (- (bvchop size y)))))
           :in-theory (disable bvdiv-of-bvchop-arg2-same
                               bvdiv-of-bvchop-arg3-same
                               bvdiv-of-bvchop-arg3
                               ;bvchop-of-minus-of-bvchop
                               ;bvdiv-of---of-bvchop-arg2
                               ))))

(defthmd narrow-bvchop-when-top-bit-0
  (implies (and (equal 0 (getbit (+ -1 size) x))
                (integerp x)
                (posp size))
           (equal (bvchop size x)
                  (bvchop (+ -1 size) x))))

(defthmd bvdiv-when-top-bits-are-0-narrow
  (implies (and (equal 0 (getbit (+ -1 size) x))
                (equal 0 (getbit (+ -1 size) y))
                (posp size)
                (integerp x)
                (integerp y)
                )
           (equal (bvdiv (+ -1 size) x y)
                  (bvdiv size x y)))
  :hints (("Goal" :in-theory (enable bvdiv narrow-bvchop-when-top-bit-0))))

;; (bvsdiv s t) abbreviates
;; (let ((?msb_s ((_ extract |m-1| |m-1|) s))
;;       (?msb_t ((_ extract |m-1| |m-1|) t)))
;;   (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
;;        (bvudiv s t)
;;        (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
;;             (bvneg (bvudiv (bvneg s) t))
;;             (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
;;                  (bvneg (bvudiv s (bvneg t)))
;;                  (bvudiv (bvneg s) (bvneg t))))))
(thm
 (implies (and (posp size)
               (integerp x)
               (integerp y))
          (equal (sbvdiv size x y)
                 (let ((msb-x (getbit (+ -1 size) x))
                       (msb-y (getbit (+ -1 size) y)))
                   (if (and (equal msb-x 0) (equal msb-y 0))
                       (bvdiv size x y)
                     (if (and (equal msb-x 1) (equal msb-y 0))
                         (bvuminus size (bvdiv size (bvuminus size x) y))
                       (if (and (equal msb-x 0) (equal msb-y 1))
                           (bvuminus size (bvdiv size x (bvuminus size y)))
                         (bvdiv size (bvuminus size x) (bvuminus size y))))))))
 :hints (("Goal" :in-theory (enable sbvdiv-rewrite sbvlt-rewrite
                                    bvdiv-when-top-bits-are-0-narrow))))

;; TODO: Consider how to translate sbvrem for SMTLIB and add validation theorem here.

;; (bvslt s t) abbreviates:
;; (or (and (= ((_ extract |m-1| |m-1|) s) #b1)
;;          (= ((_ extract |m-1| |m-1|) t) #b0))
;;     (and (= ((_ extract |m-1| |m-1|) s) ((_ extract |m-1| |m-1|) t))
;;          (bvult s t)))
(thm
 (implies (and (posp size)
               (integerp x)
               (integerp y))
          (equal (sbvlt size x y)
                 (or (and (equal (getbit (+ -1 size) x) 1)
                          (equal (getbit (+ -1 size) y) 0))
                     (and (equal (getbit (+ -1 size) x) (getbit (+ -1 size) y))
                          (bvlt size x y)))))
 :hints (("Goal" :in-theory (enable sbvlt-rewrite bvlt)
          :use ((:instance split-bv-top-add (x (bvchop size x)))
                (:instance split-bv-top-add (x (bvchop size y)))))))

;; TODO: Add more validation theorems
