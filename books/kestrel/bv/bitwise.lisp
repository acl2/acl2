; Rules about bitwise operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvand")
(include-book "bvxor")
(include-book "bvnot")
(include-book "bvor")
(include-book "bitxor")
(include-book "bitand")
(include-book "bitnot")
(include-book "bitor")
(include-book "bvcat")
(local (include-book "single-bit"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-mod-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
(local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
(local (include-book "kestrel/arithmetic-light/evenp" :dir :system))

;; (thm
;;  (implies (integerp x)
;;           (equal (INTEGERP (+ 1/2 (* 1/2 x)))
;;                  (not (evenp x))))
;;  :hints (("Goal" :in-theory (enable evenp))))

;see also one in thms.lisp

;; De Morgan
(defthmd bvnot-of-bvand
  (implies (natp n)
           (equal (bvnot n (bvand n x y))
                  (bvor n (bvnot n x) (bvnot n y))))
  :hints (("Goal" :in-theory (enable bvnot bvand bvor lognot-of-logand))))

;; De Morgan
(defthmd bvnot-of-bvor
  (implies (natp n)
           (equal (bvnot n (bvor n x y))
                  (bvand n (bvnot n x) (bvnot n y))))
  :hints (("Goal" :in-theory (enable bvnot bvand bvor lognot-of-logand))))

(local
 (defun floor2-floor2-sub1-induct (x y n)
  (if (zp n)
      (list x y n)
    (floor2-floor2-sub1-induct (floor x 2) (floor y 2) (+ -1 n)))))

(local
 (defthm evenp-when-equal-of-mod-of-expt-and-0
  (implies (and (equal (mod x (expt 2 n)) 0) ;n is a free var
                (posp n)
                (integerp x))
           (evenp x))
  :hints (("Goal" :in-theory (enable evenp-becomes-equal-of-0-and-mod)))))

(local
 (defthm evenp-when-equal-of-mod-of-2-and-0-cheap
  (implies (and (equal (mod x 2) 0)
                (integerp x))
           (evenp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable evenp-becomes-equal-of-0-and-mod)))))

(local
 (defthm mod-of-2-and-expt-of-2
  (implies (natp n)
           (equal (mod 2 (expt 2 n))
                  (if (< n 2)
                      0
                    2)))))

(local
 (defthm mod-of-1-and-expt-of-2
  (implies (natp n) ;gen?
           (equal (mod 1 (expt 2 n))
                  (if (< n 1)
                      0
                    1)))
  :hints (("Goal" :cases ((< n 0))))))

(local
 (defthm mod-of-floor-of-2-and-expt2-of-one-less
  (implies (and (equal (mod x (expt 2 n)) 0)
                (integerp x)
                (posp n))
           (equal (mod (floor x 2) (expt 2 (+ -1 n)))
                  0))
  :hints (("Goal" :in-theory (enable mod-expt-split)))))

(local
 (defthmd bvxor-of-bvand-same-arg2-helper
   (implies (and (unsigned-byte-p n x)
                 (natp n))
            (equal (bvxor n y (bvand n x y))
                   (bvand n y (bvnot n x))))
   :hints (("Goal" :in-theory (enable bvxor bvand bvnot logxor lognot-of-logand
                                      logand-of-bvchop)))))

;; Removes a mention of y
(defthm bvxor-of-bvand-same-arg2
  (equal (bvxor n y (bvand n x y))
         (bvand n y (bvnot n x)))
  :hints (("Goal" :cases ((natp n))
           :use (:instance bvxor-of-bvand-same-arg2-helper (x (bvchop n x))))))

(defthmd bvxor-of-+-of-1-split
  (implies (natp n)
           (equal (bvxor (+ 1 n) x y)
                  (bvcat 1 (acl2::bitxor (acl2::getbit n x) (acl2::getbit n y))
                         n (bvxor n x y)))))

;we currently prefer bvnot for mutli-bit opens and bitxor with 1 for single bit ops <- a bit weird
;not sure that's a good choice..  bvnot can interfere with the bvxor cancel rules..
(defthmd bvxor-all-ones-helper
  (equal (bvxor size (+ -1 (expt 2 size)) x)
         (bvnot size x))
  :hints (("Goal" :in-theory (e/d (bvnot ;mine for lemmas!
                                   bvxor
                                   LOGEQV
                                   logorc1
                                   ;;bvxor-blast
                                   logxor
                                   lognot-of-logand
                                   )
                                  (;BITNOT-BECOMES-BITXOR-WITH-1
                                   ;;BITXOR-OF-1-BECOMES-BITNOT-ARG1 ;looped
                                   )))))

(defthmd bvxor-all-ones-helper-alt
  (equal (bvxor size x (+ -1 (expt 2 size)))
         (bvnot size x))
  :hints (("Goal" :use (:instance bvxor-all-ones-helper)
           :in-theory (disable bvxor-all-ones-helper))))

;we currently prefer bvnot for mutli-bit opens and bitxor with 1 for single bit ops <- a bit weird
;not sure that's a good choice..  bvnot can interfere with the bvxor cancel rules..
(defthmd bvxor-all-ones
  (implies (and (syntaxp (and (quotep mask)
                              (quotep size)))
                (equal mask (+ -1 (expt 2 size))) ;fixme allow the sizes to differ?
                )
           (equal (bvxor size mask x)
                  (bvnot size x)))
  :hints (("Goal" :use (:instance bvxor-all-ones-helper)
           :in-theory (disable bvxor-all-ones-helper))))

(defthmd bvnot-becomes-bvxor
  (implies (and (syntaxp (quotep size)) ;drop?
;                (integerp x)
                (natp size))
           (equal (bvnot size x)
                  (bvxor size (+ -1 (expt 2 size)) x)))
  :hints (("Goal" :use (:instance bvxor-all-ones (mask (+ -1 (expt 2 size))))
           :in-theory (disable bvxor-all-ones))))

(theory-invariant (incompatible (:rewrite bvnot-becomes-bvxor) (:rewrite bvxor-all-ones)))

;use trim?
(defthm bitxor-of-slice-arg1
  (implies (and (<= low high)
                (natp low)
                (natp high))
           (equal (bitxor (slice high low x) y)
                  (bitxor (getbit low x) y)))
  :hints (("Goal" :in-theory (e/d (bitxor) (BVXOR-1-BECOMES-BITXOR)))))

;use trim?
;bozo analogue for bvand?
(defthm bitxor-of-slice-arg2
  (implies (and (<= low high)
                (natp low)
                (natp high))
           (equal (bitxor y (slice high low x))
                  (bitxor y (getbit low x))))
  :hints (("Goal" :in-theory (e/d (bitxor) (BVXOR-1-BECOMES-BITXOR)))))

(defthm equal-of-bvxor-ones-and-bvnot
  (implies (and (syntaxp (and (quotep mask) (quotep size)))
                (equal mask (+ -1 (expt 2 size))))
           (equal (equal (bvxor size mask x) (bvnot size x))
                  t))
  :hints (("Goal" :in-theory (enable bvxor-all-ones-helper))))

(defthm equal-of-bvnot-and-bvxor-ones
  (implies (and (syntaxp (and (quotep mask) (quotep size)))
                (equal mask (+ -1 (expt 2 size))))
           (equal (equal (bvnot size x) (bvxor size mask x))
                  t))
  :hints (("Goal" :use (:instance equal-of-bvxor-ones-and-bvnot)
           :in-theory (disable equal-of-bvxor-ones-and-bvnot))))

(defthmd bvand-of-bvnot-same-helper
  (implies (unsigned-byte-p size x)
           (equal (bvand size x (bvnot size x))
                  0))
  :hints (("Goal" :cases ((Natp size))
           :in-theory (e/d (bvand bvnot logand-of-bvchop)
                           (bvand-commutative)))))

(defthm bvand-of-bvnot-same
  (equal (bvand size x (bvnot size x))
         0)
  :hints (("Goal" :cases ((natp size))
           :use (:instance bvand-of-bvnot-same-helper (x (bvchop size x))))))

(defthm bvand-of-bvnot-same-alt
  (equal (bvand size (bvnot size x) x)
         0)
  :hints (("Goal" :use (:instance bvand-of-bvnot-same))))

;;(add-invisible-fns bvand bvnot)  ;;todo: it would be nice for this to work

(defthm bvand-of-bvand-of-bvnot-same
  (equal (bvand size x (bvand size (bvnot size x) y))
         0)
  :hints (("Goal" :use (:instance bvand-associative
                                  (y (bvnot size x))
                                  (z y)))))

(defthm bvand-of-bvand-of-bvnot-same-alt
  (equal (bvand size (bvnot size x) (bvand size x y))
         0)
  :hints (("Goal" :use (:instance bvand-of-bvand-of-bvnot-same)
           :in-theory (disable bvand-of-bvand-of-bvnot-same))))

;since it can be expensive to do this in general??...
(defthm getbit-of-bvxor-when-other-bit-is-0-arg1
  (implies (and (equal (getbit n x) 0)
                (< n size)
                (natp n)
                (natp size))
           (equal (getbit n (bvxor size x y))
                  (getbit n y)))
  :hints (("Goal" :in-theory (enable getbit-of-bvxor-core))))

;ffixme think these over
(defthm getbit-of-bvxor-when-other-bit-is-0-arg2
  (implies (and (equal (getbit n x) 0)
                (< n size)
                (natp n)
                (natp size))
           (equal (getbit n (bvxor size y x))
                  (getbit n y)))
  :hints (("Goal" :in-theory (enable getbit-of-bvxor-core))))

;bozo more like this, or a general rule with a syntaxp hyp?
(defthm getbit-of-bvand-too-high
  (implies (and (<= size n)
                (natp n)
                (natp size))
           (equal (getbit n (bvand size x y))
                  0))
  :hints (("Goal" :in-theory (enable getbit-too-high))))

;; this is x AND NOT(x) = 0 when we represent the NOT as an XOR with ones
(defthm bvand-of-bvxor-of-ones-same
  (implies (and (syntaxp (and (quotep k)            ;new
                              (quotep size)))
                (equal k (+ -1 (expt 2 size))))
           (equal (bvand size x (bvxor size k x))
                  0))
  :hints (("Goal" :in-theory (enable ;BVXOR-ALL-ONES-GEN
                              bvxor-all-ones-helper-alt))))

;; this is NOT(x) AND x = 0 when we represent the NOT as an XOR with ones
(defthm bvand-of-bvxor-of-ones-same-alt
  (implies (and (syntaxp (and (quotep k) ;new
                              (quotep size)))
                (equal k (+ -1 (expt 2 size))))
           (equal (bvand size (bvxor size k x) x)
                  0))
  :hints (("Goal" :in-theory (enable ;BVXOR-ALL-ONES-GEN
                              bvxor-all-ones-helper-alt))))

(defthm bvand-of-bvand-of-bvxor-of-ones-same
  (implies (equal k (+ -1 (expt 2 size)))
           (equal (bvand size x (bvand size (bvxor size k x) y))
                  0))
  :hints (("Goal" :use (:instance bvand-of-bvand-of-bvnot-same)
           :in-theory (e/d (BVXOR-ALL-ONES-HELPER-ALT) ( bvand-of-bvand-of-bvnot-same)))))

(defthm bvand-of-bvand-of-bvxor-of-ones-same-alt
  (implies (equal k (+ -1 (expt 2 size)))
           (equal (bvand size (bvxor size k x) (bvand size x y))
                  0))
  :hints (("Goal" :use (:instance bvand-of-bvand-of-bvnot-same)
           :in-theory (e/d (bvxor-all-ones-helper-alt) ( bvand-of-bvand-of-bvnot-same)))))

;may help when size is not a constant
(defthm bvand-of-bvxor-of-ones-same-another-alt
  (equal (bvand size x (bvxor size x (+ -1 (expt 2 size))))
         0)
  :hints
  (("Goal" :in-theory (enable bvxor-all-ones-helper-alt))))

;rename
(defthm bvand-of-bvand-of-bvnot-same-xor-version
  (implies (AND (SYNTAXP (AND (QUOTEP MASK) (QUOTEP SIZE)))
                (EQUAL MASK (+ -1 (EXPT 2 SIZE))))
           (equal (bvand size x (bvand size (bvxor size mask x) y))
                  0))
  :hints (("Goal" :in-theory (disable BVAND-OF-BVAND-OF-BVNOT-SAME)
           :use (BVXOR-ALL-ONES
                 (:instance bvand-of-bvand-of-bvnot-same)))))

;rename
(defthm bvand-of-bvand-of-bvnot-same-alt-xor-version
  (implies (AND (SYNTAXP (AND (QUOTEP MASK) (QUOTEP SIZE)))
                (EQUAL MASK (+ -1 (EXPT 2 SIZE))))
           (equal (bvand size (bvxor size mask x) (bvand size x y))
                  0))
  :hints (("Goal" :in-theory (disable BVAND-OF-BVAND-OF-BVNOT-SAME-alt)
           :use (BVXOR-ALL-ONES
                 (:instance bvand-of-bvand-of-bvnot-same-alt)))))

(defthm bitand-of-bitxor-of-1-same
  (equal (bitand x (bitxor 1 x))
         0)
  :hints (("Goal" :in-theory (e/d (bitand bitxor bitnot) (BVXOR-1-BECOMES-BITXOR)))))

(defthm bitand-of-bitxor-of-1-same-alt
  (equal (bitand x (bitand (bitxor 1 x) w)) ;yuck: replacing w with y fails due to alpha order
         0)
  :hints (("Goal" :in-theory (e/d (bitand bitxor bitnot) (BVXOR-1-BECOMES-BITXOR)))))

(defthm bvxor-of-bvand-tighten-alt
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvxor size1 z (bvand size2 x y))
                  (bvxor size1 z (bvand size1 x y))))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvand-of-bvxor-tighten
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvand size1 (bvxor size2 x y) z)
                  (bvand size1 (bvxor size1 x y) z)))
  :hints (("Goal" :in-theory (enable bvxor bvand))))

(defthm bvand-of-bvxor-tighten-alt
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvand size1 z (bvxor size2 x y))
                  (bvand size1 z (bvxor size1 x y))))
  :hints (("Goal" :in-theory (enable bvxor bvand))))

;gen the 1
;drop, since bvxor should go to bitxor first?
(defthmd bvxor-1
  (equal (bvxor 1 1 x)
         (bvnot 1 x))
  :hints (("Goal"
           :cases ((equal 0 (getbit 0 x)))
           :use ((:instance BVCHOP-LOGNOT-BVCHOP (n 1)))
           :in-theory (e/d (bvxor bvnot bitxor ;LOGXOR*
    ;                                          bvchop
    ;lognot getbit
                                  )
                           (SLICE-BECOMES-GETBIT
                            GETBIT-WHEN-NOT-0
                            BVCHOP-LOGNOT-BVCHOP
    ;BVCHOP-1-BECOMES-GETBIT
                            BVXOR-1-BECOMES-BITXOR)))))

;we should either prefer xors to nots, or vice versa (weird 4 rule loop if we are not careful)
(theory-invariant (incompatible (:rewrite bvxor-1) (:rewrite bitnot-becomes-bitxor-with-1)))

;bozo how can we decide which branch to move the lognot into?
(defthmd bvnot-of-bvxor-1
  (equal (bvnot 1 (bvxor 1 x y))
         (bvxor 1 (bvnot 1 x) y))
  :hints (("Goal" :in-theory (enable bitxor-split))))

(defthm bvnot-of-bvxor-1-back
   (equal (bvxor 1 (bvnot 1 x) y)
          (bvnot 1 (bvxor 1 x y)))
   :hints (("Goal" :use (:instance bvnot-of-bvxor-1))))

(defthm bvnot-of-bvxor-1-back-alt
  (equal (bvxor 1 y (bvnot 1 x))
         (bvnot 1 (bvxor 1 y x)))
  :hints (("Goal" :use (:instance bvnot-of-bvxor-1-back)
           :in-theory (e/d (BITXOR-COMMUTATIVE BITXOR-COMMUTATIVE-2) ( bvnot-of-bvxor-1-back)))))

;(local (in-theory (enable BITXOR-COMMUTATIVE BITXOR-COMMUTATIVE-2))) ;hope these don't loop

;gen the size!  or use bitnot
(defthm bvxor-of-x-and-bvnot-x
  (equal (bvxor 1 (bvnot 1 x) x)
         1))

(defthm bvxor-of-x-and-bvnot-x-alt
  (equal (bvxor 1 x (bvnot 1 x))
         1)
  :hints (("Goal" :in-theory (e/d (bitxor-commutative-2)
                                  (equal-of-0-and-bitxor)))))

(defthm bvxor-of-x-and-bvnot-x-alt-3terms
  (equal (bvxor 1 x (bvxor 1 (bvnot 1 x) y))
         (bvnot 1 y))
  :hints (("Goal" :in-theory (enable bitxor-commutative-2))))

(defthm bvxor-of-x-and-bvnot-x-3terms
  (equal (bvxor 1 (bvnot 1 x) (bvxor 1 x y))
         (bvnot 1 y)))

(defthm bvxor-of-bvnot-1
  (equal (bvxor 1 (bvnot 1 x) y)
         (bvnot 1 (bvxor 1 x y))))

(defthm bvxor-of-bvnot-2
  (equal (bvxor 1 y (bvnot 1 x))
         (bvnot 1 (bvxor 1 y x)))
  :hints (("Goal" :in-theory (enable bitxor-commutative-2))))

(defthm bvxor-of-bvxor-tighten
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvxor size1 (bvxor size2 x y) z)
                  (bvxor size1 (bvxor size1 x y) z)))
  :hints (("Goal" :in-theory (enable bvxor bvand))))

(defthm bvxor-of-bvxor-tighten-alt
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvxor size1 z (bvxor size2 x y))
                  (bvxor size1 z (bvxor size1 x y))))
  :hints (("Goal" :in-theory (enable bvxor bvand))))

;use trim
(defthm bvor-of-bvxor-tighten
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvor size1 (bvxor size2 x y) z)
                  (bvor size1 (bvxor size1 x y) z)))
  :hints (("Goal" :in-theory (enable bvor bvxor bvand))))

;use trim
(defthm bvor-of-bvxor-tighten-alt
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvor size1 z (bvxor size2 x y))
                  (bvor size1 z (bvxor size1 x y))))
  :hints (("Goal" :in-theory (enable bvor bvxor bvand))))

;rewrite to have bitnot in lhs?
(defthm bitor-x-not-x
  (equal (bitor x (bvnot 1 x))
         1)
  :hints (("Goal" :cases ((equal (bvchop 1 x) 1)
                          (equal (bvchop 1 x) 0))
           :in-theory (e/d (bitor bvor
                                  getbit
                                  bitxor
                                  bvxor
                                  bitnot
                                  )
                           (bvchop-1-becomes-getbit
                            slice-becomes-getbit
                            bvxor-1-becomes-bitxor)))))

;rewrite to have bitnot in lhs?
(defthm bitor-x-not-x-alt
  (equal (bitor (bvnot 1 x) x)
         1)
  :hints (("Goal" :use (:instance bitor-x-not-x)
           :in-theory (disable bitor-x-not-x))))

;or go to bitnot
(defthm bitxor-x-not-x
   (equal (bitxor x (bvnot 1 x))
          1)
   :hints (("Goal" :in-theory (e/d (bitnot) (equal-of-0-and-bitxor)))))

(defthm bitxor-x-not-x-alt
   (equal (bitxor (bvnot 1 x) x)
          1)
   :hints (("Goal" :in-theory (enable bitnot))))

;bozo gen the 1 and eventually the bvnot
(defthm getbit-of-bvnot-too-high
  (equal (getbit 1 (bvnot 1 x))
         0)
  :hints (("Goal" :in-theory (enable bitnot))))

(defthm slice-of-bitand-too-high
  (implies (and (<= 1 low)
                (natp low))
           (equal (slice high low (bitand x y))
                  0))
  :hints (("Goal" :in-theory (enable bitand slice-too-high-is-0))))

(defthm getbit-of-bvor-when-other-bit-is-0-arg1
  (implies (and (equal (getbit n x) 0)
                (< n size)
                (natp n)
                (natp size))
           (equal (getbit n (bvor size x y))
                  (getbit n y))))

(defthm getbit-of-bvor-when-other-bit-is-0-arg2
  (implies (and (equal (getbit n x) 0)
                (< n size)
                (natp n)
                (natp size))
           (equal (getbit n (bvor size y x))
                  (getbit n y))))

(defthm bvxor-of-slice-tighten
  (implies (and (<= size (- high low))
                (natp size)
                (< 0 size)
                (natp low)
                (natp high)
                )
           (equal (bvxor size x (slice high low y))
                  (bvxor size x (slice (+ low size -1) low y))))
  :hints (("Goal" :in-theory (e/d (bvxor) ()))))

(defthm bvxor-of-slice-tighten-alt
  (implies (and (<= size (- high low))
                (natp size)
                (< 0 size)
                (natp low)
                (natp high)
;                (integerp x)
 ;               (integerp y)
                )
           (equal (bvxor size (slice high low y) x)
                  (bvxor size (slice (+ low size -1) low y) x)))
  :hints (("Goal" :in-theory (e/d (bvxor) ()))))

(defthm bvand-of-slice-tighten-2
  (implies (and (< size (+ 1 high (- low)))
                (< 0 size)
                (natp size)
                (natp low)
                (natp high)
                (integerp x)
                (integerp y)
                )
           (equal (BVAND size y (SLICE high low x))
                  (BVAND size y (SLICE (+ low size -1) low x))))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-slice-tighten-1
  (implies (and (< size (+ 1 high (- low)))
                (< 0 size)
                (natp size)
                (natp low)
                (natp high)
                (integerp x)
                (integerp y)
                )
           (equal (BVAND size (SLICE high low x) y)
                  (BVAND size (SLICE (+ low size -1) low x) y)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvxor-of-slice-tighten-2
  (implies (and (< size (+ 1 high (- low)))
                (< 0 size)
                (natp size)
                (natp low)
                (natp high)
                (integerp x)
                (integerp y)
                )
           (equal (BVXOR size y (SLICE high low x))
                  (BVXOR size y (SLICE (+ low size -1) low x))))
  :hints (("Goal" :in-theory (e/d (bvxor) ()))))

(defthm bvxor-of-slice-tighten-1
  (implies (and (< size (+ 1 high (- low)))
                (< 0 size)
                (natp size)
                (natp low)
                (natp high)
                (integerp x)
                (integerp y)
                )
           (equal (BVXOR size (SLICE high low x) y)
                  (BVXOR size (SLICE (+ low size -1) low x) y)))
  :hints (("Goal" :in-theory (e/d (bvxor) ()))))

;use trim?
(defthm bvxor-of-bvor-tighten
  (implies (and (< size size2)
                (natp size)
                (natp size2))
           (equal (bvxor size (bvor size2 x y) z)
                  (bvxor size (bvor size x y) z)))
 :hints (("Goal" :in-theory (e/d (bvxor) ( BVCHOP-1-BECOMES-GETBIT)))))

;bozo more like this (all combinations!)
;how about a macro to prove all combinations of a given theorem.  you put in a placeholder a bunch of substitutions
;and it does the product...
;use trim?
(defthm bvxor-of-bvor-tighten-2
  (implies (and (< size size2)
                (natp size)
                (natp size2))
           (equal (bvxor size z (bvor size2 x y))
                  (bvxor size z (bvor size x y))))
 :hints (("Goal" :in-theory (e/d (bvxor) ( BVCHOP-1-BECOMES-GETBIT)))))

;here we tighten the call to size...
(defthm slice-of-bvxor-tighten2
  (implies (and (<= n high)
                (<= low n)
                (natp high)
                (natp low)
                (natp n))
           (equal (slice high low (bvxor n x y))
                  (slice (+ -1 n) low (bvxor n x y))))
  :hints (("Goal" :in-theory (e/d (slice) (slice-becomes-bvchop

                                           logtail-of-bvchop-becomes-slice
                                           bvchop-of-logtail-becomes-slice)))))

;gen the bvand to any op?
(defthm slice-of-bvand-tighten-high-index
  (implies (and (<= size high)
                (<= low size) ;bozo
                (< 0 size)
                (natp high)
                (natp size)
                (natp low))
           (equal (slice high low (bvand size x y))
                  (slice (+ -1 size) low (bvand size x y))))
  :hints (("Goal" :in-theory (enable bvand))))

(defthmd getbit-of-bvand-core
  (implies (and (< n size) (posp size))
           (equal (getbit n (bvand size x y))
                  (bvand 1 (getbit n x) (getbit n y))))
  :hints
  (("Goal"
    :in-theory
    (e/d
     (getbit bvand bvchop-of-logtail slice)
     (slice-becomes-getbit bvchop-1-becomes-getbit
                           bvchop-of-logtail-becomes-slice
                           LOGTAIL-OF-BVCHOP-BECOMES-SLICE)))))
