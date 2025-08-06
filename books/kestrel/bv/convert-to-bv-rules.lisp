; Trim-based rules to convert functions to BV functions
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-syntax")
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
(local (include-book "bvcat"))
(local (include-book "slice"))
(local (include-book "bvshr"))
(local (include-book "bvsx"))
(local (include-book "logxor-b"))
(local (include-book "logior-b"))
(local (include-book "logand-b"))
(local (include-book "logext"))

;; Step 1: These rules begin the conversion by inserting calls of trim.  (Axe has
;; its own version of such rules, since they use complex syntaxp hyps.  See
;; books/kestrel/axe/bv-rules-axe.lisp.)

(defthmd bvplus-convert-arg2-to-bv
  (implies (syntaxp (and (consp x)
                         (member-eq (ffn-symb x) *functions-convertible-to-bv*)))
           (equal (bvplus size x y)
                  (bvplus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvplus-convert-arg3-to-bv
  (implies (syntaxp (and (consp y)
                         (member-eq (ffn-symb y) *functions-convertible-to-bv*)))
           (equal (bvplus size x y)
                  (bvplus size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvshr-convert-arg2-to-bv
  (implies (syntaxp (and (consp x)
                         (member-eq (ffn-symb x) *functions-convertible-to-bv*)))
           (equal (bvshr size x shift-amount)
                  (bvshr size (trim size x) shift-amount)))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvcat-convert-arg2-to-bv
  (implies (syntaxp (and (consp high)
                         (member-eq (ffn-symb high) *functions-convertible-to-bv*)))
           (equal (bvcat highsize high lowsize low)
                  (bvcat highsize (trim highsize high) lowsize low)))
  :hints (("Goal" :in-theory (enable trim bvcat))))

(defthmd bvcat-convert-arg4-to-bv
  (implies (and (syntaxp (and (consp low)
                              (member-eq (ffn-symb low) *functions-convertible-to-bv*)))
                (integerp lowsize))
           (equal (bvcat highsize high lowsize low)
                  (bvcat highsize high lowsize (trim lowsize low))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd slice-convert-arg3-to-bv
  (implies (and (syntaxp (and (consp x)
                              (member-eq (ffn-symb x) *functions-convertible-to-bv*)
                              (quotep high)
                              (quotep low)))
                (natp high)
                (natp low))
           (equal (slice high low x)
                  (slice high low (trim (+ 1 high) x))))
  :hints (("Goal" :in-theory (enable trim))))

;; TODO: Add more of these, baseed on axe/bv-rules-axe.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Step 2: These rules finish the conversion after other rules introduce trim.

;; WARNING: Keep these in sync with *functions-convertible-to-bv*.

(defthmd trim-of-logand-becomes-bvand
  (equal (trim size (logand x y))
         (bvand size x y))
  :hints (("Goal" :in-theory (enable trim bvand))))

(defthmd trim-of-logior-becomes-bvor
  (equal (trim size (logior x y))
         (bvor size x y))
  :hints (("Goal" :in-theory (enable trim bvor))))

(defthmd trim-of-logxor-becomes-bvxor
  (equal (trim size (logxor x y))
         (bvxor size x y))
  :hints (("Goal" :in-theory (enable trim bvxor))))

(defthmd trim-of-lognot-becomes-bvnot
  (equal (trim size (lognot x))
         (bvnot size x))
  :hints (("Goal" :in-theory (enable trim bvnot))))

;; TODO: Consider what happens if a TRIM gets introduced but these rules can't
;; get rid of it due to their hyps:

(defthmd trim-of-+-becomes-bvplus
  (implies (and (integerp x)
                (integerp y))
           (equal (trim size (+ x y))
                  (bvplus size x y)))
  :hints (("Goal" :in-theory (enable trim bvplus))))

(defthmd trim-of-unary---becomes-bvuminus
  (implies (integerp x)
           (equal (trim size (- x))
                  (bvuminus size x)))
  :hints (("Goal" :in-theory (enable trim bvuminus))))

(defthmd trim-of-*-becomes-bvmult
  (implies (and (integerp x)
                (integerp y))
           (equal (trim size (* x y))
                  (bvmult size x y)))
  :hints (("Goal" :in-theory (enable trim bvmult))))

;; not needed because (- x y) translates to a call of +
;; (defthmd trim-of---becomes-bvminus
;;   (implies (and (integerp x)
;;                 (integerp y))
;;            (equal (trim size (- x y))
;;                   (bvminus size x y)))
;;   :hints (("Goal" :in-theory (enable trim bvminus))))

(defthm trim-of-logext-becomes-bvsx
  (implies (and ;(natp size)
                (posp size2))
           (equal (trim size (logext size2 x))
                  (if (< size2 size)
                      (bvsx size size2 x)
                    ;; no sign extension needed in this case:
                    (bvchop size x))))
  :hints (("Goal" :cases ((natp size))
                  :in-theory (e/d (trim) (logext)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
