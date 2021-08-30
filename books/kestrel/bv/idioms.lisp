; Idioms for expressing BV ops in terms of more common ones
;
; Copyright (C) 2017-2020 Kestrel Institute
; Copyright (C) 2017-2018 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/bvshl" :dir :system)
(include-book "kestrel/bv/bvshr" :dir :system)
(include-book "kestrel/bv/bvand" :dir :system)
(include-book "kestrel/bv/rules" :dir :system) ;for BVAND-OF-EXPT, todo reduce
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))

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

(defthmd bvand-with-mask-of-ones
  (implies (and (natp size)
                (natp n)
                (<= n size)
                )
           (equal (bvand size (+ -1 (expt 2 n)) x)
                  (bvchop n x)))
  :hints (("Goal" :in-theory (e/d (bvand) (;logand-with-mask
                                           )))))

(defthmd bvand-with-mask-of-ones-alt
  (implies (and (natp size)
                (natp n)
                (<= n size)
                )
           (equal (bvand size x (+ -1 (expt 2 n)))
                  (bvchop n x)))
  :hints (("Goal" :in-theory (e/d (bvand) (;logand-with-mask
                                           )))))

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
  :hints (("Goal" :in-theory (e/d (bvshr bvand-with-mask-of-ones-alt)
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
  :hints (("Goal" :use (:instance bvand-with-mask-of-ones-alt
                                  (size 32))
           :in-theory (disable bvand-with-mask-of-ones-alt))))

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

;move to library
;also conside n > size (easy)
(defthm unsigned-byte-p-of-bvshl-gen
  (implies (and ;(< n size)
                (<= amt size)
                (natp amt)
                (unsigned-byte-p (- n amt) x)
                (natp n)
                (natp size))
           (unsigned-byte-p n (bvshl size x amt)))
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

(defthm bvand-with-mask-drop
  (implies (and (syntaxp (quotep mask))
                (logmaskp mask)
                (<= (integer-length mask) size)
                (natp size)
                (unsigned-byte-p (integer-length mask) y)
                )
           (equal (bvand size mask y)
                  y))
  :hints (("Goal" :use (:instance bvand-with-mask-better-eric (size2 size) (i y)))))
