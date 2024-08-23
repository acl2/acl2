; Supporting rules about bit-vectors
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: Push these back into libraries.

(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/bv/bvand" :dir :system)
(include-book "kestrel/bv/bvshr" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "kestrel/utilities/polarity" :dir :system) ; for want-to-strengthen
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/logand-b" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ; for slice-too-high-is-0-new (todo: move it)
(local (include-book "kestrel/bv/rules10" :dir :system)) ; todo, for logand-of-bvchop-becomes-bvand etc
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-and-expt" :dir :system))
;(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(defthm fix-of-ifix
  (equal (fix (ifix x))
         (ifix x)))

(defthm fix-when-integerp
  (implies (integerp x)
           (equal (fix x)
                  x)))

;; ;replace the other one!
;; (encapsulate ()
;;   (local (include-book "kestrel/arithmetic-light/expt" :dir :system))
;;   (defthm slice-of-times-of-expt-gen
;;     (implies (and            ;(<= j n) ;drop?
;;               (integerp x)   ;drop?
;;               (natp n)
;;               (natp j)
;;               (natp m))
;;              (equal (slice m n (* (expt 2 j) x))
;;                     (slice (- m j) (- n j) x)))
;;     :hints (("Goal" :in-theory (e/d (slice logtail nfix) ())))))

;move
;; ;avoids having to give a highsize
;; (defthm slice-of-logapp
;;   (implies (and (natp lowsize)
;;                 (natp low)
;;                 (natp high)
;;                 (integerp highval))
;;            (equal (slice high low (logapp lowsize lowval highval))
;;                   (slice high low (bvcat (+ 1 high (- lowsize)) highval lowsize lowval))))
;;   :otf-flg t
;;   :hints (("Goal" :use (:instance BVCAT-RECOMBINE
;;                                   (lowsize lowsize)
;;                                   (lowval lowval)
;;                                   (highval highval)
;;                                   (highsize (+ 1 high (- lowsize)))))))


;;   :hints (("Goal" :in-theory (e/d (;bvcat logapp
;;                                          ;slice-of-sum-cases
;;                                          )
;;                                   ()))))

;move
(defthm slice-of-logapp-case-1
  (implies (and (natp high)
                (natp low)
                ;; (natp lowsize)
                (<= lowsize low) ; this case
                (unsigned-byte-p lowsize lowval)
                (integerp highval))
           (equal (slice high low (logapp lowsize lowval highval))
                  (slice (+ (- lowsize) high) (+ (- lowsize) low) highval)))
  :hints (("Goal" :in-theory (e/d (slice logapp) (logtail-of-plus
                                                  unsigned-byte-p-of-logapp-large-case))
           :use (:instance unsigned-byte-p-of-logapp-large-case
                           (size1 low)
                           (size lowsize)
                           (i lowval)
                           (j (BVCHOP (+ LOW (- LOWSIZE)) HIGHVAL))))))


(defthm plus-of-minus1-and-bvcat-of-0
  (implies (and (posp lowsize)
                (integerp highval)
                (natp HIGHSIZE))
           (equal (+ -1 (bvcat highsize highval lowsize 0))
                  (if (equal (bvchop highsize highval) 0)
                      -1
                    (bvcat highsize (+ -1 highval) lowsize (+ -1 (expt 2 lowsize))))))
  :hints (("Goal" :in-theory (e/d (bvcat bvplus bvchop-of-sum-cases)
                                  (
                                   ;equal-of-+-when-negative-constant
                                   )))))

;drop?
(defthmd +-of-minus1-and-bvcat-of-0
  (implies (natp size)
           (equal (+ -1 (BVCAT 1 1 size 0))
                  (+ -1 (expt 2 size))))
  :hints (("Goal" :in-theory (enable bvcat))))

(defthm bvshr-of-logand-becomes-bvshr-of-bvand
  (implies (and (natp amt)
                (< amt 32))
           (equal (bvshr 32 (logand x y) amt)
                  (bvshr 32 (bvand (+ 32 amt) x y) amt)))
  :hints (("Goal" :in-theory (e/d (bvshr bvand slice logtail-of-bvchop)
                                  (slice-of-logand
                                   ;logand-of-bvchop-becomes-bvand-alt
                                   ;logand-of-bvchop-becomes-bvand
                                   bvchop-of-logtail-becomes-slice
                                   anti-slice
                                   BVAND-LOGTAIL-ARG2 ;looped
                                   BVAND-LOGTAIL-ARG1 ;looped
                                   )))))

(defthm bvchop-of-+-of-*-of-256
  (implies (and (integerp x)
                (integerp y))
           (equal (bvchop 8 (+ x (* 256 y)))
                  (bvchop 8 x))))

(defthmd mod-becomes-bvchop-8
  (implies (integerp x)
           (equal (mod x 256)
                  (bvchop 8 x)))
  :hints (("Goal" :in-theory (enable bvchop ifix))))

;move
(defthm bvchop-upper-bound-strong
  (implies (natp n)
           (<= (bvchop n x) (+ -1 (expt 2 n))))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvplus-of-*-of-256
  (implies (and (natp size)
                (<= 8 size)
                (unsigned-byte-p 8 byte)
                (integerp val))
           (equal (bvplus size byte (* 256 val))
                  (bvcat (- size 8) val 8 byte)))
  :hints (("Goal"
           :use (:instance bvchop-upper-bound-strong (n (+ -8 SIZE))
                           (x val))
           :in-theory (e/d (bvcat bvplus
                                        bvchop-of-sum-cases
                                        logtail
                                        EXPT-OF-+)
                           (bvchop-upper-bound
                            bvchop-upper-bound-strong
                            BVCHOP-BOUND-2)))))

(defthm open-ash-positive-constants
  (implies (and (syntaxp (and (quotep i)
                              (quotep c)))
                (natp c)
                (integerp i))
           (equal (ash i c)
                  (* i (expt 2 c))))
  :hints (("Goal" :in-theory (enable ash))))

;gen
(defthm strengthen-upper-bound-when-top-bit-0
  (implies (and (syntaxp (want-to-strengthen (< x 9223372036854775808)))
                (equal (getbit 63 x) 1)
                (integerp x))
           (equal (< x 9223372036854775808)
                  (<= x 0)))
  :hints (("Goal" :in-theory (e/d (getbit slice logtail)
                                  (slice-becomes-getbit
                                   bvchop-1-becomes-getbit
                                   bvchop-of-logtail-becomes-slice)))))

;; Since 0 and 1 are the only BVs less than 2
(defthmd <-of-bvchop-and-2
  (equal (< (BVCHOP size x) 2)
         (or (equal (BVCHOP size x) 0)
             (equal (BVCHOP size x) 1))))

;;gen
(defthm bvplus-subst-smaller-term
  (implies (and (equal (bvchop 32 x) (bvchop 32 x2))
                (syntaxp (smaller-termp x2 x)))
           (equal (bvplus 32 x y)
                  (bvplus 32 x2 y))))

(defthm equal-of-bvchop-and-bvplus-same
  (implies (natp size)
           (equal (equal (bvchop size x) (bvplus size y x))
                  (equal (bvchop size y) 0)))
  :hints (("Goal"
           :in-theory (e/d (bvplus bvchop-of-sum-cases bvuminus bvminus)
                           (bvminus-becomes-bvplus-of-bvuminus
                            ;; bvcat-of-+-high
                            ;; NTH-OF-CDR
                            )))))
