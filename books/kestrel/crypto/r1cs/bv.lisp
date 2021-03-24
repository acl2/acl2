; BV rules
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS") ;todo: change to ACL2

;; TODO: Move these to the BV library

(include-book "kestrel/bv/rules" :dir :system) ; for ACL2::BITNOT-BECOMES-BITXOR-WITH-1 ?
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/leftrotate" :dir :system)
(include-book "kestrel/bv/rightrotate" :dir :system)
(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/bv/bitnot" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv/rotate" :dir :system)
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))

(defthm bvplus-of-expt-2
  (equal (bvplus size x (expt 2 size))
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm getbit-of-bvplus-tighten-to-32
  (implies (and (< 32 size) ; prevent loops
                (< n 32)
                (natp n)
                (natp size))
           (equal (getbit n (bvplus size x y))
                  (getbit n (bvplus 32 x y))))
  :hints (("Goal" :in-theory (e/d (bvplus)
                                  (;ACL2::GETBIT-TRIM
                                   )))))

;gen
(defthmd slice-of-bvplus-tighten-to-32
  (implies (and (< 32 n)
                (< high 32)
                (<= low high) ;drop?
                (natp low)
                (natp high)
                (natp n))
           (equal (slice high low (bvplus n x y))
                  (slice high low (bvplus 32 x y))))
  :hints (("Goal" :in-theory (e/d (bvplus)
                                  (;ACL2::GETBIT-TRIM
                                   )))))

(defthmd bvchop-of-bvplus-tighten-to-32
  (implies (and (< 32 n)
                (natp n))
           (equal (bvchop 32 (bvplus n x y))
                  (bvchop 32 (bvplus 32 x y))))
  :hints (("Goal" :in-theory (e/d (bvplus)
                                  (;ACL2::GETBIT-TRIM
                                   )))))

(defthm bvplus-of-bvplus-trim-to-32-arg1
  (implies (and (< 32 n)
                (natp n))
           (equal (bvplus 32 (bvplus n x y) z)
                  (bvplus 32 (bvplus 32 x y) z)))
  :hints (("Goal" :in-theory (enable acl2::bvplus))))

(defthm bvplus-of-bvplus-trim-to-32-arg2
  (implies (and (< 32 n)
                (natp n))
           (equal (bvplus 32 z (bvplus n x y))
                  (bvplus 32 (bvplus 32 x y) z)))
  :hints (("Goal" :in-theory (enable acl2::bvplus))))

(defthm bvcat-of-slice-tighten
  (implies (and (<= highsize (- high low))
                (<= low high)
                (natp highsize)
                (natp low)
                (natp high))
           (equal (bvcat highsize (slice high low x) lowsize lowval)
                  (bvcat highsize (slice (+ -1 low highsize) low x) lowsize lowval))))

(defthm bvcat-of-bitnot-low
  (implies (natp highsize)
           (equal (bvcat highsize highval 1 (bitnot lowbit))
                  (bvxor (+ highsize 1)
                         1
                         (bvcat highsize highval 1 lowbit)))))

(defthm bvcat-of-bitnot-high
  (implies (natp lowsize)
           (equal (bvcat 1 (bitnot highval) lowsize lowval)
                  (bvxor (+ 1 lowsize)
                               (bvcat 1 1 lowsize 0) ;todo: simplify?
                               (bvcat 1 highval lowsize lowval)))))

(defthm bvcat-of-bvnot-low
  (implies (and (natp highsize)
                (posp lowsize) ;gen
                )
           (equal (bvcat highsize highval lowsize (bvnot lowsize lowbit))
                  (bvxor (+ highsize lowsize)
                               (bvchop lowsize -1) ;todo: improve?
                               (bvcat highsize highval lowsize lowbit))))
  :hints (("Goal" :in-theory (enable ACL2::BVXOR-ALL-ONES-HELPER-ALT))))

(defthm bvcat-of-bvxor-low-when-quotep
  (implies (and (syntaxp (quotep k))
                (natp highsize)
                (natp lowsize))
           (equal (bvcat highsize highval lowsize (bvxor lowsize k lowval))
                  (bvxor (+ highsize lowsize)
                               (bvchop lowsize k)
                               (bvcat highsize highval lowsize lowval))))
  :hints (("Goal" :cases ((equal 0 highsize)))))

(defthm bvcat-of-bvxor-high-when-quotep
  (implies (and (syntaxp (quotep k))
                (natp highsize)
                (natp lowsize))
           (equal (bvcat highsize (bvxor highsize k highval) lowsize lowval)
                  (bvxor (+ highsize lowsize)
                               (bvcat highsize k lowsize 0) ;should get computed
                               (bvcat highsize highval lowsize lowval))))
  :hints (("Goal" :cases ((equal 0 highsize)))))

(defthm bvcat-of-bitxor-low-when-quotep
  (implies (and (syntaxp (quotep k))
                (natp highsize))
           (equal (bvcat highsize highval 1 (bitxor k lowval))
                  (bvxor (+ highsize 1)
                               (bvchop 1 k)
                               (bvcat highsize highval 1 lowval))))
  :hints (("Goal" :cases ((equal 0 highsize)))))

(defthm bvcat-of-bitxor-high-when-quotep
  (implies (and (syntaxp (quotep k))
                (natp lowsize))
           (equal (bvcat 1 (bitxor k highval) lowsize lowval)
                  (bvxor (+ 1 lowsize)
                               (bvcat 1 k lowsize 0) ;should get computed
                               (bvcat 1 highval lowsize lowval))))
  :hints (("Goal" :cases ((equal 0 highsize)))))

(defthm bvcat-of-bvnot-high
  (implies (and (natp lowsize)
                (natp highsize))
           (equal (bvcat highsize (bvnot highsize highval) lowsize lowval)
                  (bvxor (+ highsize lowsize)
                               (bvcat highsize (bvchop highsize -1) lowsize 0) ;todo: simplify?
                               (bvcat highsize highval lowsize lowval))))
  :hints (("Goal" :cases ((equal 0 highsize))
           :in-theory (enable ACL2::BVXOR-ALL-ONES-HELPER-ALT))))

(defthm bvcat-of-slice-same-becomes-rightrotate
  (implies (and (equal upper-bit 31) ;gen!
                (equal upper-bit (+ -1 highsize lowsize))
                (natp highsize)
                (natp lowsize)
                (< lowsize upper-bit)
                (< highsize upper-bit)
                (posp highsize) ;gen
                )
           (equal (BVCAT highsize x lowsize (SLICE upper-bit highsize x))
                  (acl2::rightrotate (+ 1 upper-bit) highsize x)))
  :hints (("Goal" :in-theory (enable ;ACL2::RIGHTROTATE
                              ))))

(defthmd bvcat-of-bitxor-and-bitxor-adjacent-bits
  (implies (and (natp low1)
                (equal high1 (+ 1 low1))
                (natp low2)
                (equal high2 (+ 1 low2)))
           (equal (bvcat 1 (bitxor (getbit high1 x) (getbit high2 y))
                         1 (bitxor (getbit low1 x) (getbit low2 y)))
                  (bvxor 2 (slice high1 low1 x) (slice high2 low2 y)))))

;; has the first bitxor commuted
(defthmd bvcat-of-bitxor-and-bitxor-adjacent-bits-alt
  (implies (and (natp low1)
                (equal high1 (+ 1 low1))
                (natp low2)
                (equal high2 (+ 1 low2)))
           (equal (bvcat 1 (bitxor (getbit high2 y) (getbit high1 x))
                         1 (bitxor (getbit low1 x) (getbit low2 y)))
                  (bvxor 2 (slice high1 low1 x) (slice high2 low2 y)))))

(defthm bvxor-of-slice-trim
  (implies (and (< n (+ 1 (- high low)))
                (natp n)
                (< low high)
                (natp high)
                (natp low))
           (equal (bvxor n (slice high low x) y)
                  (bvxor n (slice (+ -1 (+ n low)) low x) y))))

(defthmd bvcat-of-bitxor-and-bvxor-adjacent-bits
  (implies (and (equal high1minus1 (+ -1 high1))
                (equal high2minus1 (+ -1 high2))
                (equal n (+ 1 (- high1minus1 low1)))
                (equal n (+ 1 (- high2minus1 low2)))
                (<= low1 high1minus1)
;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (bvcat 1 (bitxor (getbit high1 x) (getbit high2 y))
                         n (bvxor n (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvxor (+ 1 n)
                         (slice high1 low1 x) (slice high2 low2 y))))
  :hints (("Goal" :in-theory (enable acl2::getbit-leibniz))))

;; This version commutes the args to the first bitxor
(defthmd bvcat-of-bitxor-and-bvxor-adjacent-bits-alt
  (implies (and (equal high1minus1 (+ -1 high1))
                (equal high2minus1 (+ -1 high2))
                (equal n (+ 1 (- high1minus1 low1)))
                (equal n (+ 1 (- high2minus1 low2)))
                (<= low1 high1minus1)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (bvcat 1 (bitxor (getbit high2 y) (getbit high1 x))
                               n (bvxor n (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvxor (+ 1 n)
                               (slice high1 low1 x) (slice high2 low2 y))))
  :hints (("Goal" :use (:instance bvcat-of-bitxor-and-bvxor-adjacent-bits)
           :in-theory (disable bvcat-of-bitxor-and-bvxor-adjacent-bits))))

(defthmd bvcat-of-bvxor-and-bvxor-adjacent-bits
  (implies (and (equal high1minus1 (+ -1 mid1))
                (equal high2minus1 (+ -1 mid2))
                (equal n2 (+ 1 (- high1minus1 low1)))
                (equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (< low1 high1minus1)
                (< low2 high2minus1)
                (<= mid1 high1)
                (<= mid1 high2)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (bvcat n1 (bvxor n1 (slice high1 mid1 x) (slice high2 mid2 y))
                               n2 (bvxor n2 (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvxor (+ n1 n2)
                               (slice high1 low1 x) (slice high2 low2 y))))
  :hints (("Goal" :in-theory (enable acl2::slice-leibniz))))

;; This version commutes the args to the first bvxor
(defthmd bvcat-of-bvxor-and-bvxor-adjacent-bits-alt
  (implies (and (equal high1minus1 (+ -1 mid1))
                (equal high2minus1 (+ -1 mid2))
                (equal n2 (+ 1 (- high1minus1 low1)))
                (equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (< low1 high1minus1)
                (< low2 high2minus1)
                (<= mid1 high1)
                ;(<= mid2 high2)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (bvcat n1 (bvxor n1 (slice high2 mid2 y) (slice high1 mid1 x))
                               n2 (bvxor n2 (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvxor (+ n1 n2)
                               (slice high1 low1 x) (slice high2 low2 y))))
  :hints (("Goal" :in-theory (enable acl2::slice-leibniz))))

(defthmd bvcat-of-bvxor-and-bitxor-adjacent-bits
  (implies (and (equal mid1minus1 (+ -1 mid1))
                (equal mid2minus1 (+ -1 mid2))
                ;;(equal n2 (+ 1 (- high1minus1 low1)))
                ;;(equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                ;;(< low1 high1minus1)
                ;;(< low2 high2minus1)
                (<= mid1 high1)
                ;(<= mid2 high2)
                ;;(<= low2 high2minus1)
                ;;(natp low1)
                ;;(natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp mid1) ;why?
                (posp mid2) ;why?
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (bvcat n1 (bvxor n1 (slice high1 mid1 x) (slice high2 mid2 y))
                               1 (bitxor (getbit mid1minus1 x) (getbit mid2minus1 y)))
                  (bvxor (+ 1 n1)
                               (slice high1 mid1minus1 x)
                               (slice high2 mid2minus1 y))))
  :hints (("Goal" :in-theory (enable))))

;;this one commutes the args of the first bvxor
(defthmd bvcat-of-bvxor-and-bitxor-adjacent-bits-alt
  (implies (and (equal mid1minus1 (+ -1 mid1))
                (equal mid2minus1 (+ -1 mid2))
                ;;(equal n2 (+ 1 (- high1minus1 low1)))
                ;;(equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                ;;(< low1 high1minus1)
                ;;(< low2 high2minus1)
                (<= mid1 high1)
                (<= mid2 high2)
                ;;(<= low2 high2minus1)
                ;;(natp low1)
                ;;(natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp mid1) ;why?
                (posp mid2) ;why?
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (bvcat n1 (bvxor n1 (slice high2 mid2 y) (slice high1 mid1 x))
                               1 (bitxor (getbit mid1minus1 x) (getbit mid2minus1 y)))
                  (bvxor (+ 1 n1)
                               (slice high1 mid1minus1 x)
                               (slice high2 mid2minus1 y))))
  :hints (("Goal" :in-theory (enable))))

;only needed for axe
(defthmd acl2::bvcat-equal-rewrite-constant-alt
  (implies (and (syntaxp (quotep acl2::x))
                (syntaxp (quotep acl2::highsize))
                (syntaxp (quotep acl2::lowsize))
                (natp acl2::lowsize)
                (natp acl2::highsize))
           (equal (equal (bvcat acl2::highsize acl2::highval
                                acl2::lowsize acl2::lowval)
                         acl2::x)
                  (and
                   (unsigned-byte-p (+ acl2::lowsize acl2::highsize)
                                    acl2::x)
                   (equal (bvchop acl2::lowsize acl2::x)
                          (bvchop acl2::lowsize acl2::lowval))
                   (equal (slice (+ -1 acl2::lowsize acl2::highsize)
                                 acl2::lowsize acl2::x)
                          (bvchop acl2::highsize acl2::highval))))))

(defthmd bvcat-of-bvxor-and-bvxor-adjacent-bits-extra-left-assoc
  (implies (and (equal high1minus1 (+ -1 mid1))
                (equal high2minus1 (+ -1 mid2))
                (equal n2 (+ 1 (- high1minus1 low1)))
                (equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (equal n1+zsize (+ n1 zsize))
                (< low1 high1minus1)
                (< low2 high2minus1)
                (<= mid1 high1)
                (<= mid1 high2)
                ;;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                (natp zsize)
                )
           (equal (bvcat n1+zsize (bvcat zsize z n1 (bvxor n1 (slice high1 mid1 x) (slice high2 mid2 y)))
                         n2 (bvxor n2 (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvcat zsize z
                         (+ n1 n2)
                         (bvxor (+ n1 n2)
                                (slice high1 low1 x) (slice high2 low2 y)))))
  :hints (("Goal" :in-theory (enable ACL2::SLICE-LEIBNIZ))))

;commutes the first bvxor
(defthmd bvcat-of-bvxor-and-bvxor-adjacent-bits-extra-left-assoc-alt
  (implies (and (equal high1minus1 (+ -1 mid1))
                (equal high2minus1 (+ -1 mid2))
                (equal n2 (+ 1 (- high1minus1 low1)))
                (equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (equal n1+zsize (+ n1 zsize))
                (< low1 high1minus1)
                (< low2 high2minus1)
                (<= mid1 high1)
                (<= mid1 high2)
                ;;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                (natp zsize)
                )
           (equal (bvcat n1+zsize (bvcat zsize z n1 (bvxor n1 (slice high2 mid2 y) (slice high1 mid1 x)))
                               n2 (bvxor n2 (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvcat zsize z
                               (+ n1 n2)
                               (bvxor (+ n1 n2)
                                      (slice high1 low1 x) (slice high2 low2 y)))))
  :hints (("Goal" :use (:instance bvcat-of-bvxor-and-bvxor-adjacent-bits-extra-left-assoc)
           :in-theory (disable bvcat-of-bvxor-and-bvxor-adjacent-bits-extra-left-assoc))))

(defthmd bvcat-of-bitxor-and-bitxor-adjacent-bits-extra-left-assoc
  (implies (and (equal zsize+1 (+ 1 zsize))
                (equal high1 (+ 1 low1))
                (equal high2 (+ 1 low2))
                (natp zsize)
                (natp low1)
                (natp low2))
           (equal (bvcat zsize+1
                               (bvcat zsize z 1 (bitxor (getbit high1 x) (getbit high2 y)))
                               1
                               (bitxor (getbit low1 x) (getbit low2 y)))
                  (bvcat zsize
                               z
                               2
                               (bvxor 2 (slice high1 low1 x) (slice high2 low2 y))))))

;commutes the first xor
(defthmd bvcat-of-bitxor-and-bitxor-adjacent-bits-extra-left-assoc-alt
  (implies (and (equal zsize+1 (+ 1 zsize))
                (equal high1 (+ 1 low1))
                (equal high2 (+ 1 low2))
                (natp zsize)
                (natp low1)
                (natp low2))
           (equal (bvcat zsize+1
                               (bvcat zsize z 1 (bitxor (getbit high2 y) (getbit high1 x)))
                               1
                               (bitxor (getbit low1 x) (getbit low2 y)))
                  (bvcat zsize
                               z
                               2
                               (bvxor 2 (slice high1 low1 x) (slice high2 low2 y))))))

(defthmd bvcat-of-bitxor-and-bvxor-adjacent-bits-extra-left-assoc
  (implies (and (equal high1minus1 (+ -1 high1))
                (equal high2minus1 (+ -1 high2))
                (equal zsize+1 (+ 1 zsize))
                (equal n (+ 1 (- high1minus1 low1)))
                (equal n (+ 1 (- high2minus1 low2)))
                (<= low1 high1minus1)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                (natp zsize)
                )
           (equal (bvcat zsize+1
                               (bvcat zsize z 1 (bitxor (getbit high1 x) (getbit high2 y)))
                               n
                               (bvxor n (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvcat zsize
                               z
                               (+ 1 n)
                               (bvxor (+ 1 n)
                                            (slice high1 low1 x) (slice high2 low2 y)))))
  :hints (("Goal" :in-theory (enable acl2::getbit-leibniz))))

;commutes the first xor
(defthmd bvcat-of-bitxor-and-bvxor-adjacent-bits-extra-left-assoc-alt
  (implies (and (equal high1minus1 (+ -1 high1))
                (equal high2minus1 (+ -1 high2))
                (equal zsize+1 (+ 1 zsize))
                (equal n (+ 1 (- high1minus1 low1)))
                (equal n (+ 1 (- high2minus1 low2)))
                (<= low1 high1minus1)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                (natp zsize)
                )
           (equal (bvcat zsize+1
                               (bvcat zsize z 1 (bitxor (getbit high2 y) (getbit high1 x)))
                               n
                               (bvxor n (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvcat zsize
                               z
                               (+ 1 n)
                               (bvxor (+ 1 n)
                                            (slice high1 low1 x) (slice high2 low2 y)))))
  :hints (("Goal" :use bvcat-of-bitxor-and-bvxor-adjacent-bits-extra-left-assoc
           :in-theory (disable bvcat-of-bitxor-and-bvxor-adjacent-bits-extra-left-assoc))))

(defthmd bvcat-of-bvxor-and-bitxor-adjacent-bits-extra-left-assoc
  (implies (and (equal mid1minus1 (+ -1 mid1))
                (equal mid2minus1 (+ -1 mid2))
                ;;(equal n2 (+ 1 (- high1minus1 low1)))
                ;;(equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (equal zsize+n1 (+ n1 zsize))
                ;;(< low1 high1minus1)
                ;;(< low2 high2minus1)
                (<= mid1 high1)
                ;;(<= mid2 high2)
                ;;(<= low2 high2minus1)
                ;;(natp low1)
                ;;(natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp mid1)  ;why?
                (posp mid2)  ;why?
                (posp high1) ;why?
                (posp high2) ;why?
                (natp zsize)
                )
           (equal (bvcat zsize+n1
                               (bvcat zsize z n1 (bvxor n1 (slice high1 mid1 x) (slice high2 mid2 y)))
                               1 (bitxor (getbit mid1minus1 x) (getbit mid2minus1 y)))
                  (bvcat zsize z
                               (+ 1 n1)
                               (bvxor (+ 1 n1)
                                            (slice high1 mid1minus1 x)
                                            (slice high2 mid2minus1 y)))))
  :hints (("Goal" :in-theory (enable))))

;has the first xor commuted
(defthmd bvcat-of-bvxor-and-bitxor-adjacent-bits-extra-left-assoc-alt
  (implies (and (equal mid1minus1 (+ -1 mid1))
                (equal mid2minus1 (+ -1 mid2))
                ;;(equal n2 (+ 1 (- high1minus1 low1)))
                ;;(equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (equal zsize+n1 (+ n1 zsize))
                ;;(< low1 high1minus1)
                ;;(< low2 high2minus1)
                (<= mid1 high1)
                ;;(<= mid2 high2)
                ;;(<= low2 high2minus1)
                ;;(natp low1)
                ;;(natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp mid1)  ;why?
                (posp mid2)  ;why?
                (posp high1) ;why?
                (posp high2) ;why?
                (natp zsize)
                )
           (equal (bvcat zsize+n1
                               (bvcat zsize z n1 (bvxor n1 (slice high2 mid2 y) (slice high1 mid1 x)))
                               1 (bitxor (getbit mid1minus1 x) (getbit mid2minus1 y)))
                  (bvcat zsize z
                               (+ 1 n1)
                               (bvxor (+ 1 n1)
                                            (slice high1 mid1minus1 x)
                                            (slice high2 mid2minus1 y)))))
  :hints (("Goal" :in-theory (enable))))

;; this is for when we are associating to the left (unusual)
(defthmd acl2::bvcat-of-getbit-and-getbit-adjacent-2-left-assoc
  (implies (and (equal n (+ 1 m))
                (equal j (+ 1 size))
                (natp size)
                (natp m))
           (equal (bvcat j (bvcat size y 1 (getbit n x))
                         1 (getbit m x))
                  (bvcat size y 2 (slice n m x)))))

(defthmd acl2::bvcat-of-getbit-and-slice-adjacent-2-left-assoc
  (implies (and (equal n (+ 1 high))
                (equal j (+ 1 size))
                (equal k (+ 1 (- high low)))
                (<= low high)
                (natp size)
                (natp high)
                (natp low))
           (equal (bvcat j (bvcat size y 1 (getbit n x))
                               k (slice high low x))
                  (bvcat size
                               y
                               (+ 1 (- n low))
                               (slice n low x)))))

(defthmd acl2::bvcat-of-slice-and-slice-adjacent-2-left-assoc
  (implies (and (equal low1 (+ 1 high2))
                (equal size1 (+ size size2))
                (equal size2 (+ 1 (- high1 low1)))
                (equal size3 (+ 1 (- high2 low2)))
                (<= low1 high1)
                (<= low2 high2)
                (natp size)
                (natp high1)
                (natp low1)
                (natp high2)
                (natp low2))
           (equal (bvcat size1 (bvcat size y size2 (slice high1 low1 x))
                               size3 (slice high2 low2 x))
                  (bvcat size
                               y
                               (+ 1 (- high1 low2))
                               (slice high1 low2 x)))))

(defthmd acl2::bvcat-of-slice-and-getbit-adjacent-2-left-assoc
  (implies (and (equal low1 (+ 1 n))
                (equal size1 (+ size size2))
                (equal size2 (+ 1 (- high1 low1)))
                (<= low1 high1)
                (natp size)
                (natp high1)
                (natp low1)
                (natp n))
           (equal (bvcat size1 (bvcat size y size2 (slice high1 low1 x))
                               1 (getbit n x))
                  (bvcat size
                               y
                               (+ 2 high1 (- low1))
                               (slice high1 n x)))))



;; CAUTION: This will be unhelpful if the xors are not commuted right. Consider using a syntaxp hyp?
(defthmd bvcat-of-bitxor-and-bitxor
  (equal (bvcat 1 (bitxor a1 b1) 1 (bitxor a2 b2))
         (bvxor 2 (bvcat 1 a1 1 a2) (bvcat 1 b1 1 b2))))

;; CAUTION: This will be unhelpful if the xors are not commuted right. Consider using a syntaxp hyp?
(defthmd bvcat-of-bitxor-and-bvxor
  (implies (natp size)
           (equal (bvcat 1 (bitxor a1 b1) size (bvxor size a2 b2))
                  (bvxor (+ 1 size) (bvcat 1 a1 size a2) (bvcat 1 b1 size b2)))))

;; CAUTION: This will be unhelpful if the xors are not commuted right. Consider using a syntaxp hyp?
(defthmd bvcat-of-bvxor-and-bitxor
  (implies (natp size)
           (equal (bvcat size (bvxor size a1 b1) 1 (bitxor a2 b2))
                  (bvxor (+ 1 size) (bvcat size a1 1 a2) (bvcat size b1 1 b2)))))

;; CAUTION: This will be unhelpful if the xors are not commuted right. Consider using a syntaxp hyp?
(defthmd bvcat-of-bvxor-and-bvxor
  (implies (and (natp size1)
                (< 0 size1) ;why?
                (natp size2))
           (equal (bvcat size1 (bvxor size1 a1 b1) size2 (bvxor size2 a2 b2))
                  (bvxor (+ size1 size2) (bvcat size1 a1 size2 a2) (bvcat size1 b1 size2 b2)))))

;todo: gen the 32
(defthmd bvcat-becomes-rightrotate
  (implies (and (equal mid+1 (+ 1 mid))
                (equal highsize (+ 1 mid))
                (equal lowsize (- 31 mid))
                (< mid 31)
                (natp mid))
           (equal (bvcat highsize
                         (slice mid 0 x)
                         lowsize
                         (slice 31 mid+1 x))
                  (acl2::rightrotate 32 (+ 1 mid) x)))
  :hints (("Goal" :in-theory (enable ACL2::RIGHTROTATE))))

;usual case (slice down to 0 has become bvchop)
(defthmd bvcat-becomes-rightrotate-2
  (implies (and (equal highsize size)
                (equal lowsize (- 32 size))
                (< size 31)
                (natp size))
           (equal (bvcat highsize
                         (bvchop size x)
                         lowsize
                         (slice 31 size x))
                  (acl2::rightrotate 32 size x)))
  :hints (("Goal" :in-theory (e/d (ACL2::RIGHTROTATE) (ACL2::RIGHTROTATE-BECOMES-LEFTROTATE)))))

(defthmd bvcat-31-of-getbit-31-becomes-rightrotate
  (equal (bvcat 31 x 1 (getbit 31 x))
         (acl2::rightrotate 32 31 x)))

;; (defthmd bvcat-1-of-getbit-0-becomes-rightrotate
;;   (equal (bvcat 1 (getbit 0 x) 31 x)
;;          (acl2::rightrotate 32 1 x)))

;; Introduce BVPLUS
(defthmd mod-of-+-of-4294967296
  (implies (and (integerp x)
                (integerp y))
           (equal (mod (+ x y) 4294967296)
                  (bvplus 32 x y)))
  :hints (("Goal" :in-theory (enable acl2::bvplus acl2::bvchop))))

(defthm getbit-of-+-of-constant-irrel
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (equal 0 (acl2::bvchop (+ 1 n) k))
                (natp n)
                (integerp x)
                (integerp k))
           (equal (acl2::getbit n (+ k x))
                  (acl2::getbit n x)))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-plus))))

(defthm getbit-of-+-of-expt-same-arg1
  (implies (and (natp n)
                (integerp x))
           (equal (acl2::getbit n (+ (expt 2 n) x))
                  (acl2::bitnot (acl2::getbit n x))))
  :hints (("Goal" :in-theory (e/d (acl2::getbit acl2::slice acl2::bitnot)
                                  (acl2::slice-becomes-getbit
                                   acl2::bvchop-1-becomes-getbit
                                   acl2::bvchop-of-logtail-becomes-slice)))))

(defthm getbit-of-+-of-expt-same-arg2
  (implies (and (natp n)
                (integerp x))
           (equal (acl2::getbit n (+ x (expt 2 n)))
                  (acl2::bitnot (acl2::getbit n x))))
  :hints (("Goal" :in-theory (e/d (acl2::getbit acl2::slice acl2::bitnot)
                                  (acl2::slice-becomes-getbit
                                   acl2::bvchop-1-becomes-getbit
                                   acl2::bvchop-of-logtail-becomes-slice)))))

(defthm getbit-of-+-of-expt-same-when-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (equal k (expt 2 n))
                (natp n)
                (integerp x)
                (integerp k))
           (equal (acl2::getbit n (+ k x))
                  (acl2::bitnot (acl2::getbit n x))))
  :hints (("Goal" :use (getbit-of-+-of-expt-same-arg1)
           :in-theory (disable getbit-of-+-of-expt-same-arg1))))

(defthm bvxor-of-+-of-expt-of-one-less-arg2
  (implies (and (integerp x)
                (posp n))
           (equal (bvxor n extra (+ (expt 2 (+ -1 n)) x))
                  (bvcat 1
                         (acl2::bitnot (acl2::bitxor (acl2::getbit (- n 1) extra)
                                                     (acl2::getbit (- n 1) x)))
                         (- n 1)
                         (bvxor (- n 1) extra x))))
  :hints (("Goal" :in-theory (disable acl2::bvcat-of-getbit-and-x-adjacent

                                      bvcat-of-bitnot-high
                                      ))))

(defthm bvxor-of-+-of-expt-of-one-less-arg1
  (implies (and (integerp x)
                (posp n))
           (equal (bvxor n (+ (expt 2 (+ -1 n)) x) extra)
                  (bvcat 1
                         (acl2::bitnot (acl2::bitxor (acl2::getbit (- n 1) extra)
                                                     (acl2::getbit (- n 1) x)))
                         (- n 1)
                         (bvxor (- n 1) extra x))))
  :hints (("Goal" :in-theory (disable acl2::bvcat-of-getbit-and-x-adjacent

                                      bvcat-of-bitnot-high
                                      ))))

(defthm bvxor-of-+-of-expt-of-one-less-arg2-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (+ -1 n)))
                (integerp x)
                (posp n))
           (equal (bvxor n extra (+ k x))
                  (bvcat 1
                         (acl2::bitnot (acl2::bitxor (acl2::getbit (- n 1) extra)
                                                     (acl2::getbit (- n 1) x)))
                         (- n 1)
                         (bvxor (- n 1) extra x))))
  :hints (("Goal" :in-theory (disable acl2::bvcat-of-getbit-and-x-adjacent

                                      bvcat-of-bitnot-high
                                      ))))

(defthm bvxor-of-+-of-expt-of-one-less-arg1-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (+ -1 n)))
                (integerp x)
                (posp n))
           (equal (bvxor n (+ k x) extra)
                  (bvcat 1
                         (acl2::bitnot (acl2::bitxor (acl2::getbit (- n 1) extra)
                                                     (acl2::getbit (- n 1) x)))
                         (- n 1)
                         (bvxor (- n 1) extra x))))
  :hints (("Goal" :in-theory (disable acl2::bvcat-of-getbit-and-x-adjacent
                                      bvcat-of-bitnot-high))))

(defthm getbit-of-+-of-*-of-expt-when-bitp-arg2-arg1
  (implies (and (bitp bit)
                (integerp x)
                (natp n))
           (equal (acl2::getbit n (+ x (* (expt 2 n) bit)))
                  (acl2::bitxor bit (acl2::getbit n x))))
  :hints (("Goal" :cases ((equal bit 0))
           :in-theory (e/d (acl2::getbit acl2::slice acl2::bitnot ACL2::BVCHOP-OF-SUM-CASES)
                           (acl2::slice-becomes-getbit
                            acl2::bvchop-1-becomes-getbit
                            acl2::bvchop-of-logtail-becomes-slice)))))

(defthm getbit-of-+-of-*-of-expt-when-bitp-arg2-arg2
  (implies (and (bitp bit)
                (integerp x)
                (natp n))
           (equal (acl2::getbit n (+ x (* bit (expt 2 n))))
                  (acl2::bitxor bit (acl2::getbit n x))))
  :hints (("Goal" :use (getbit-of-+-of-*-of-expt-when-bitp-arg2-arg1)
           :in-theory (disable getbit-of-+-of-*-of-expt-when-bitp-arg2-arg1))))

(defthm getbit-of-+-of-*-of-expt-when-bitp-arg2-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 n))
                (bitp bit)
                (integerp x)
                (natp n))
           (equal (acl2::getbit n (+ x (* k bit)))
                  (acl2::bitxor bit (acl2::getbit n x))))
  :hints (("Goal" :in-theory (e/d (acl2::getbit acl2::slice acl2::bitnot)
                                  (acl2::slice-becomes-getbit
                                   acl2::bvchop-1-becomes-getbit
                                   acl2::bvchop-of-logtail-becomes-slice)))))
