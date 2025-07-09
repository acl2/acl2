; Axe rules to convert non-BV functions to BV functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2021 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "axe-syntax")
(include-book "axe-syntax-functions-bv")
(include-book "kestrel/bv/defs" :dir :system)
(include-book "kestrel/bv/sbvlt-def" :dir :system)
(include-book "kestrel/bv/bvequal" :dir :system)
;(local (include-book "kestrel/bv/rules" :dir :system));drop?
(local (include-book "kestrel/bv/bvsx" :dir :system))
(local (include-book "kestrel/bv/bvand" :dir :system))
(local (include-book "kestrel/bv/bvor" :dir :system))
(local (include-book "kestrel/bv/bvxor" :dir :system))
(local (include-book "kestrel/bv/bvplus" :dir :system))
(local (include-book "kestrel/bv/bvminus" :dir :system))
(local (include-book "kestrel/bv/bvmult" :dir :system))
(local (include-book "kestrel/bv/bvshl" :dir :system))
(local (include-book "kestrel/bv/bvshr" :dir :system))
(local (include-book "kestrel/bv/bvashr" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/bv/bvnot" :dir :system))
(local (include-book "kestrel/bv/bitnot" :dir :system))
(local (include-book "kestrel/bv/bitand" :dir :system))
(local (include-book "kestrel/bv/bitor" :dir :system))
(local (include-book "kestrel/bv/bitxor" :dir :system))
(local (include-book "kestrel/bv/logext" :dir :system))
(local (include-book "kestrel/bv/bvif" :dir :system))
(local (include-book "kestrel/bv/bvlt" :dir :system))
(local (include-book "kestrel/bv/sbvlt" :dir :system))

;; These rules work together with TRIM rules such as trim-of-logand-becomes-bvand.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: what if X is a call of +, but we can't show that the arguments are integers?
(defthmd bvchop-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvchop size x)
                  (bvchop size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd getbit-convert-arg2-to-bv-axe
  (implies (and (< 0 n) ;if n=0 it's already being trimmed by the getbit (BOZO make sure we can simplify such cases..)
                (axe-syntaxp (term-should-be-converted-to-bvp x 'nil dag-array))
                (integerp n))
           (equal (getbit n x)
                  (getbit n (trim (+ 1 n) x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd slice-convert-arg3-to-bv-axe
  (implies (and (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
                (syntaxp (and (quotep high)
                              (quotep low)))
                (natp high)
                (natp low))
           (equal (slice high low x)
                  (slice high low (trim (+ 1 high) x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvcat-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp high nil dag-array))
           (equal (bvcat highsize high lowsize low)
                  (bvcat highsize (trim highsize high) lowsize low)))
  :hints (("Goal" :in-theory (enable trim bvcat))))

(defthmd bvcat-convert-arg4-to-bv-axe
  (implies (and (axe-syntaxp (term-should-be-converted-to-bvp low nil dag-array))
                (integerp lowsize))
           (equal (bvcat highsize high lowsize low)
                  (bvcat highsize high lowsize (trim lowsize low))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvnot-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvnot size x)
                  (bvnot size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvand-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvand size x y)
                  (bvand size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvand-convert-arg3-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
           (equal (bvand size x y)
                  (bvand size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvor-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvor size x y)
                  (bvor size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvor-convert-arg3-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
           (equal (bvor size x y)
                  (bvor size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvxor-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvxor size x y)
                  (bvxor size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvxor-convert-arg3-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
           (equal (bvxor size x y)
                  (bvxor size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bitnot-convert-arg1-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bitnot x)
                  (bitnot (trim 1 x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bitand-convert-arg1-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bitand x y)
                  (bitand (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitand-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
           (equal (bitand x y)
                  (bitand x (trim 1 y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bitor-convert-arg1-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bitor x y)
                  (bitor (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitor-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
           (equal (bitor x y)
                  (bitor x (trim 1 y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bitxor-convert-arg1-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bitxor x y)
                  (bitxor (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitxor-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
           (equal (bitxor x y)
                  (bitxor x (trim 1 y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Doesn't apply when x is a + since we turn bvplus back into + for x86 stack pointer calculations.
(defthmd bvplus-convert-arg2-to-bv-axe-restricted
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x '(binary-+) dag-array))
           (equal (bvplus size x y)
                  (bvplus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

;; Doesn't apply when y is a + since we turn bvplus back into + for x86 stack pointer calculations.
(defthmd bvplus-convert-arg3-to-bv-axe-restricted
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y '(binary-+) dag-array))
           (equal (bvplus size x y)
                  (bvplus size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvplus-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvplus size x y)
                  (bvplus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvplus-convert-arg3-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
           (equal (bvplus size x y)
                  (bvplus size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In case we keep bvminus instead of going to bvplus of bvuminus
(defthmd bvminus-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvminus size x y)
                  (bvminus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

;; In case we keep bvminus instead of going to bvplus of bvuminus
(defthmd bvminus-convert-arg3-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
           (equal (bvminus size x y)
                  (bvminus size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvuminus-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x '(binary-+) dag-array))
           (equal (bvuminus size x)
                  (bvuminus size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvmult-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvmult size x y)
                  (bvmult size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvmult-convert-arg3-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
           (equal (bvmult size x y)
                  (bvmult size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvequal-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvequal size x y)
                  (bvequal size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvequal-convert-arg3-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
           (equal (bvequal size x y)
                  (bvequal size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;other arg too?
(defthmd bvshl-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvshl size x shift-amount)
                  (bvshl size (trim size x) shift-amount)))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;other arg too?
(defthmd bvshr-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvshr size x shift-amount)
                  (bvshr size (trim size x) shift-amount)))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;other arg too?
(defthmd bvashr-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvashr size x shift-amount)
                  (bvashr size (trim size x) shift-amount)))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvsx-convert-arg3-to-bv-axe
  (implies (and (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
                (natp new-size) ; todo
                )
           (equal (bvsx new-size old-size x)
                  (bvsx new-size old-size (trim old-size x))))
  :hints (("Goal" :cases ((natp old-size))
           :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd logext-convert-arg2-to-bv-axe
  (implies (and (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
                (posp size))
           (equal (logext size x)
                  (logext size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvif-convert-arg3-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp then nil dag-array))
           (equal (bvif size test then else)
                  (bvif size test (trim size then) else)))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable trim))))

(defthmd bvif-convert-arg4-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp else nil dag-array))
           (equal (bvif size test then else)
                  (bvif size test then (trim size else))))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvlt-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvlt size x y)
                  (bvlt size (trim size x) y)))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable trim))))

(defthmd bvlt-convert-arg3-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
           (equal (bvlt size x y)
                  (bvlt size x (trim size y))))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd sbvlt-convert-arg2-to-bv-axe
  (implies (and (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
                (posp size))
           (equal (sbvlt size x y)
                  (sbvlt size (trim size x) y)))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable trim))))

(defthmd sbvlt-convert-arg3-to-bv-axe
  (implies (and (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
                (posp size))
           (equal (sbvlt size x y)
                  (sbvlt size x (trim size y))))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvdiv-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvdiv size x y)
                  (bvdiv size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvdiv-convert-arg3-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
           (equal (bvdiv size x y)
                  (bvdiv size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvmod-convert-arg2-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp x nil dag-array))
           (equal (bvmod size x y)
                  (bvmod size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim bvmod))))

(defthmd bvmod-convert-arg3-to-bv-axe
  (implies (axe-syntaxp (term-should-be-converted-to-bvp y nil dag-array))
           (equal (bvmod size x y)
                  (bvmod size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim bvmod))))
