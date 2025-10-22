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
(include-book "bvlt-def")
(include-book "trim-elim-rules-non-bv") ; to get rid of the TRIMs introduced by these rules
(local (include-book "bvcat"))
(local (include-book "slice"))
(local (include-book "bvshr"))
(local (include-book "bvsx"))
(local (include-book "bvlt"))

;; Step 1: These rules begin the conversion by inserting calls of trim.  (Axe has
;; its own version of such rules, since they use complex syntaxp hyps.  See
;; ../axe/bv-rules-axe.lisp.)

;; Step 2 is done by the rules in trim-elim-rules-non-bv.lisp

;; See also ../axe/convert-to-bv-rules-axe.lisp

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

(defthmd bvlt-convert-arg2-to-bv
  (implies (syntaxp (and (consp x)
                         (member-eq (ffn-symb x) *functions-convertible-to-bv*)))
           (equal (bvlt size x y)
                  (bvlt size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvlt-convert-arg3-to-bv
  (implies (syntaxp (and (consp y)
                         (member-eq (ffn-symb y) *functions-convertible-to-bv*)))
           (equal (bvlt size x y)
                  (bvlt size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))
