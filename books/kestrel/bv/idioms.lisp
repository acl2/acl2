; Idioms for expressing BV ops in terms of more common ones
;
; Copyright (C) 2017-2023 Kestrel Institute
; Copyright (C) 2017-2018 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvshl")
(include-book "bvshr")
(include-book "bvand")
(include-book "rules") ;for BVAND-OF-EXPT, todo reduce
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))

;;
;; library material
;;

;; Shows how to express bit extraction as masking followed by shifting.
(defthmd getbit-becomes-shift-of-mask
  (implies (and (unsigned-byte-p 8 x)
                (< n 8)
                (natp n))
           (equal (getbit n x)
                  (bvshr 8
                       (bvand 8
                              (expt 2 n)
                              x)
                       n)))
  :hints (("Goal" :in-theory (enable bvshr))))

;; Shows how to express bit slicing as masking followed by shifting.
;todo: use a better mask?
(defthmd slice-becomes-shift-of-mask
  (implies (and (unsigned-byte-p 8 x)
                (< high 8)
                (<= low high)
                (natp low)
                (natp high))
           (equal (slice high low x)
                  (bvshr 8
                       (bvand 8
                              (* (expt 2 low)
                                 (+ -1 (expt 2 (+ 1 (- high low)))))
                              x)
                       low)))
  :hints (("Goal" :in-theory (e/d (bvshr)
                                  (;slice-of-bvand
                                   DISTRIBUTIVITY
                                   )))))

;; Shows how to express bvcat in terms of shifting and ORing
(defthmd bvcat-becomes-bvor-of-bvshl
  (implies (and (natp highsize)
                (natp lowsize))
           (equal (bvcat highsize highval lowsize lowval)
                  (bvor (+ highsize lowsize)
                        (bvshl (+ highsize lowsize)
                               (bvchop highsize highval)
                               lowsize)
                        (bvchop lowsize lowval))))
  :hints (("Goal" :cases ((equal 0 (+ highsize lowsize)))
           :in-theory (enable bvshl))))

(defthmd bvchop-becomes-bvand32-with-mask
  (implies (and (natp n)
                (<= n 32))
           (equal (bvchop n x)
                  (bvand 32 x (+ -1 (expt 2 n)))))
  :hints (("Goal" :use (:instance bvand-with-mask-arg2-gen
                                  (size 32))
           :in-theory (disable bvand-with-mask-arg2-gen))))

(defthmd bvshr-extend-to-32bits
  (implies (natp amt)
           (equal (bvshr 8 x amt)
                  (bvshr 32 (bvchop 8 x) amt)))
  :hints (("Goal" :in-theory (enable bvshr))))

(defthmd bvand-extend-to-32bits
  (implies (and (natp size)
                (< size 32))
           (equal (bvand size x y)
                  (bvand 32 (bvchop size x) (bvchop size y))))
  :hints (("Goal" :in-theory (enable bvshr bvand))))

(defthmd bvor-extend-to-32bits
  (implies (and (natp size)
                (< size 32))
           (equal (bvor size x y)
                  (bvor 32 (bvchop size x) (bvchop size y))))
  :hints (("Goal" :in-theory (enable bvshr bvor))))

(defthm usb-when-usb8
  (implies (and (unsigned-byte-p 8 x) ;; e.g., since it's in a usb list
                (<= 8 n)
                (integerp n))
           (unsigned-byte-p n x)))

(defthmd bvshl-extend-to-32bits
  (implies (and (natp size)
                (< size 32)
                (unsigned-byte-p (- size amt) x)
                (natp amt)
                (<= amt size))
           (equal (bvshl size x amt)
                  (bvshl 32 x amt)))
  :hints (("Goal" :in-theory (enable bvshl))))

;these undo the shifting/masking changes
(in-theory (disable bvand-of-expt
                    bvand-128-hack
                    bvand-64-hack
                    bvand-32-hack
                    bvand-16-hack
                    bvand-8-hack
                    bvand-4-hack
                    bvand-2-hack
                    bvand-with-mask-better-eric
                    bvand-with-mask-better
                    bvand-with-mask
                    ;bvand-of-constant-tighten
                    ;bvshl-rewrite-for-constant-shift-amount
                    ;bvshl-rewrite-with-bvchop-for-constant-shift-amount
                    ;bvshl-rewrite-with-bvchop
                    bvand-with-mask-better-eric-alt))
