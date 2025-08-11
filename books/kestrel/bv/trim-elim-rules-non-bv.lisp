; Trim-based rules to convert non-BV functions to BV functions
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The file includes rules about TRIM applied to non-BV functions.  These rules
;; finish the conversion after other rules (from convert-to-bv-rules.lisp or
;; ../axe/convert-to-bv-rules-axe.lisp) introduce trim.  See also
;; trim-elim-rules-bv.lisp, which covers trim applied to BV functions.

(include-book "trim")
(include-book "bvnot")
(include-book "bvplus")
(include-book "bvmult")
(include-book "bvuminus")
(include-book "bvand")
(include-book "bvor")
(include-book "bvxor")
(include-book "bvsx")
(local (include-book "logxor-b"))
(local (include-book "logior-b"))
(local (include-book "logand-b"))
(local (include-book "logext"))

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
