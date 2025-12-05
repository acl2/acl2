; Trim-based rules to convert functions to BV functions
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-syntax") ; for convertible-to-bvp
(include-book "trim")
(include-book "bvand")
(include-book "bvor")
(include-book "bvxor")
(include-book "bvplus")
(include-book "bvminus")
(include-book "bvnot")
(include-book "bvshr-def")
(include-book "bvmult-def")
(include-book "bvcat-def")
(include-book "bvsx-def")
(include-book "logext-def")
(include-book "bvlt-def")
(include-book "bvdiv")
(include-book "bitnot")
(include-book "bitand")
(include-book "bitor")
(include-book "bitxor")
(include-book "trim-elim-rules-non-bv") ; to get rid of the TRIMs introduced by these rules
(local (include-book "bvcat"))
(local (include-book "slice"))
(local (include-book "bvshr"))
(local (include-book "bvsx"))
(local (include-book "bvlt"))

;; The rules in this book convert certain arguments of BV functions to be calls
;; of BV operators.  The approach has 2 steps:

;; Step 1: The rules in this book begin the conversion by inserting calls of
;; TRIM.

;; Step 2 The rules in trim-elim-rules-non-bv.lisp use the inserted calls of
;; TRIM to convert their arguments to bvops.

;; Note: Axe has its own version of such rules, since they use complex
;; syntaxp hyps.  See ../axe/convert-to-bv-rules-axe.lisp.

;; TODO: Add more of these, based on axe/convert-to-bv-rules-axe.lisp.

(defthmd bvplus-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bvplus size x y)
                  (bvplus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvplus-convert-arg3-to-bv
  (implies (syntaxp (convertible-to-bvp y))
           (equal (bvplus size x y)
                  (bvplus size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvminus-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bvminus size x y)
                  (bvminus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvminus-convert-arg3-to-bv
  (implies (syntaxp (convertible-to-bvp y))
           (equal (bvminus size x y)
                  (bvminus size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvuminus-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bvuminus size x)
                  (bvuminus size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvmult-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bvmult size x y)
                  (bvmult size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvmult-convert-arg3-to-bv
  (implies (syntaxp (convertible-to-bvp y))
           (equal (bvmult size x y)
                  (bvmult size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvdiv-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bvdiv size x y)
                  (bvdiv size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvdiv-convert-arg3-to-bv
  (implies (syntaxp (convertible-to-bvp y))
           (equal (bvdiv size x y)
                  (bvdiv size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvshr-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bvshr size x shift-amount)
                  (bvshr size (trim size x) shift-amount)))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvcat-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp high))
           (equal (bvcat highsize high lowsize low)
                  (bvcat highsize (trim highsize high) lowsize low)))
  :hints (("Goal" :in-theory (enable trim bvcat))))

(defthmd bvcat-convert-arg4-to-bv
  (implies (and (syntaxp (convertible-to-bvp low))
                (integerp lowsize))
           (equal (bvcat highsize high lowsize low)
                  (bvcat highsize high lowsize (trim lowsize low))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd slice-convert-arg3-to-bv
  (implies (and (syntaxp (and (convertible-to-bvp x)
                              (quotep high)
                              (quotep low)))
                (natp high)
                (natp low))
           (equal (slice high low x)
                  (slice high low (trim (+ 1 high) x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvlt-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bvlt size x y)
                  (bvlt size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvlt-convert-arg3-to-bv
  (implies (syntaxp (convertible-to-bvp y))
           (equal (bvlt size x y)
                  (bvlt size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvnot-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bvnot size x)
                  (bvnot size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvand-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bvand size x y)
                  (bvand size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvand-convert-arg3-to-bv
  (implies (syntaxp (convertible-to-bvp y))
           (equal (bvand size x y)
                  (bvand size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvor-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bvor size x y)
                  (bvor size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvor-convert-arg3-to-bv
  (implies (syntaxp (convertible-to-bvp y))
           (equal (bvor size x y)
                  (bvor size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvxor-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bvxor size x y)
                  (bvxor size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvxor-convert-arg3-to-bv
  (implies (syntaxp (convertible-to-bvp y))
           (equal (bvxor size x y)
                  (bvxor size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bitnot-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bitnot x)
                  (bitnot (trim 1 x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bitand-convert-arg1-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bitand x y)
                  (bitand (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitand-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp y))
           (equal (bitand x y)
                  (bitand x (trim 1 y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bitor-convert-arg1-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bitor x y)
                  (bitor (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitor-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp y))
           (equal (bitor x y)
                  (bitor x (trim 1 y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bitxor-convert-arg1-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bitxor x y)
                  (bitxor (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitxor-convert-arg2-to-bv
  (implies (syntaxp (convertible-to-bvp y))
           (equal (bitxor x y)
                  (bitxor x (trim 1 y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvsx-convert-arg3-to-bv
  (implies (syntaxp (convertible-to-bvp x))
           (equal (bvsx new-size old-size x)
                  (bvsx new-size old-size (trim old-size x))))
  :hints (("Goal" :in-theory (enable trim))))
