; Axe support for replacing bitops functions
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/bitops" :dir :system) ; needed for part-install-width-low-becomes-bvcat-axe
(include-book "axe-syntax")
(include-book "axe-syntax-functions-bv")
(include-book "kestrel/bv/unsigned-byte-p-forced" :dir :system)
(local (include-book "kestrel/bv/intro" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/ash" :dir :system)) ; for ash-negative-becomes-slice
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/ash" :dir :system))

(local (in-theory (disable ash)))

;; We can only do this when we know the size of X
(defthmd part-install-width-low-becomes-bvcat-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize)) ;todo better message if we forget the package on dag-array (or make it a keyword?)
                (unsigned-byte-p-forced xsize x)
                (natp low)
                (natp width))
           (equal (bitops::part-install-width-low val x width low)
                  (bvcat (- xsize (+ width low))
                         (slice (+ -1 xsize) (+ low width) x)
                         (+ width low)
                         (bvcat width val low x)))))

;; Is ASH really a bitops function?
;; We can only do this when we know the size of X
(defthmd ash-negative-becomes-slice-axe
  (implies (and (< n 0) ; could allow 0, could restrict to constant n
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x)
                (integerp n))
           (equal (ash x n)
                  (slice (+ -1 xsize) (- n) x)))
  :hints (("Goal" :in-theory (disable ash-negative-becomes-slice)
           :use ash-negative-becomes-slice)))

; Only needed for Axe.
(defthmd integerp-of-part-install-width-low
  (integerp (bitops::part-install-width-low val x width low)))
