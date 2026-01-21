; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "std/util/defredundant" :dir :system))

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/basic/arith-equivs" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Defines predicates, fixers, and equivalence relations for the basic
;; arithmetic types and their "maybe" variants.
;; Reuses the existing definitions when available.
;; Introduces basic fixer/equivalence rules, and relates the equivalences with
;; refinement rules.
;; Disables equivalence functions by default.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (;; Fixers
          bfix
          pos-fix
          lposfix
          lnfix
          lifix

          ;; Equivalences
          bit-equiv
          pos-equiv
          nat-equiv
          int-equiv
          rational-equiv
          number-equiv
          ))

;;;;;;;;;;;;;;;;;;;;

(add-macro-fn bfix bfix$inline)
(add-macro-fn lposfix lposfix$inline)
(add-macro-fn lnfix lnfix$inline)
(add-macro-fn lifix lifix$inline)

(add-macro-fn bit-equiv bit-equiv$inline)
(add-macro-fn pos-equiv pos-equiv$inline)
(add-macro-fn nat-equiv nat-equiv$inline)
(add-macro-fn int-equiv int-equiv$inline)
(add-macro-fn rational-equiv rational-equiv$inline)
(add-macro-fn number-equiv number-equiv$inline)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable bit-equiv
                    pos-equiv
                    nat-equiv
                    nat-equiv
                    int-equiv
                    rational-equiv
                    number-equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-inline bit-fix (b)
  (declare (xargs :guard (bitp b)))
  (mbe :logic (bfix b)
       :exec b))

(defun-inline rational-fix (x)
  (declare (xargs :guard (rationalp x)
                  :guard-hints (("Goal" :in-theory (enable rfix)))))
  (mbe :logic (rfix x)
       :exec x))

(defun-inline number-fix (x)
  (declare (xargs :guard (acl2-numberp x)
                  :guard-hints (("Goal" :in-theory (enable fix)))))
  (mbe :logic (fix x)
       :exec x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bfix-when-bitp
  (implies (bitp x)
           (equal (bfix x)
                  x)))

;; Avoid name clash with std
(defthmd bfix-when-not-bitp-unlimited
  (implies (not (bitp x))
           (equal (bfix x)
                  0)))

(defthm bfix-when-not-bitp-cheap
  (implies (not (bitp x))
           (equal (bfix x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by bfix-when-not-bitp-unlimited)))

;;;;;;;;;;;;;;;;;;;;

(defthm pos-fix-when-posp
  (implies (posp x)
           (equal (pos-fix x)
                  x)))

(defthmd pos-fix-when-not-posp
  (implies (not (posp x))
           (equal (pos-fix x)
                  1))
  :hints (("Goal" :in-theory (enable pos-fix))))

(defthm pos-fix-when-not-posp-cheap
  (implies (not (posp x))
           (equal (pos-fix x)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by pos-fix-when-not-posp)))

;;;;;;;;;;;;;;;;;;;;

(defthm nfix-when-natp
  (implies (natp x)
           (equal (nfix x)
                  x)))

;; Avoid name clash with std
(defthmd nfix-when-not-natp-unlimited
  (implies (not (natp x))
           (equal (nfix x)
                  0))
  :hints (("Goal" :in-theory (enable nfix))))

(defthm nfix-when-not-natp-cheap
  (implies (not (natp x))
           (equal (nfix x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by nfix-when-not-natp-unlimited)))

;;;;;;;;;;;;;;;;;;;;

(defthm rfix-when-rationalp
  (implies (rationalp x)
           (equal (rfix x)
                  x))
  :hints (("Goal" :in-theory (enable rfix))))

(defthmd rfix-when-not-rationalp
  (implies (not (rationalp x))
           (equal (rfix x)
                  0))
  :hints (("Goal" :in-theory (enable rfix))))

(defthm rfix-when-not-rationalp-cheap
  (implies (not (rationalp x))
           (equal (rfix x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by rfix-when-not-rationalp)))

;;;;;;;;;;;;;;;;;;;;

(defthm fix-when-acl2-numberp
  (implies (acl2-numberp x)
           (equal (fix x)
                  x))
  :hints (("Goal" :in-theory (enable fix))))

(defthmd fix-when-not-acl2-numberp
  (implies (not (acl2-numberp x))
           (equal (fix x)
                  0))
  :hints (("Goal" :in-theory (enable fix))))

(defthm fix-when-not-acl2-numberp-cheap
  (implies (not (acl2-numberp x))
           (equal (fix x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by fix-when-not-acl2-numberp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defequiv bit-equiv)
(defequiv pos-equiv)
(defequiv nat-equiv)
(defequiv int-equiv)
(defequiv rational-equiv)
(defequiv number-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-inline fast-bit-equiv (x y)
  (declare (xargs :guard (and (bitp x) (bitp y))
                  :guard-hints (("Goal" :in-theory (enable bit-equiv)))))
  (mbe :logic (bit-equiv x y)
       :exec (= (the bit x)
                (the bit y))))

(defun-inline fast-pos-equiv (x y)
  (declare (xargs :guard (and (posp x) (posp y))
                  :guard-hints (("Goal" :in-theory (enable pos-equiv)))))
  (mbe :logic (pos-equiv x y)
       :exec (= (the (integer 1 *) x)
                (the (integer 1 *) y))))

(defun-inline fast-nat-equiv (x y)
  (declare (xargs :guard (and (natp x) (natp y))
                  :guard-hints (("Goal" :in-theory (enable nat-equiv)))))
  (mbe :logic (nat-equiv x y)
       :exec (= (the unsigned-byte x)
                (the unsigned-byte y))))

(defun-inline fast-int-equiv (x y)
  (declare (xargs :guard (and (integerp x) (integerp y))
                  :guard-hints (("Goal" :in-theory (enable int-equiv)))))
  (mbe :logic (int-equiv x y)
       :exec (= (the integer x)
                (the integer y))))

(defun-inline fast-rational-equiv (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))
                  :guard-hints (("Goal" :in-theory (enable rational-equiv)))))
  (mbe :logic (rational-equiv x y)
       :exec (= (the rational x)
                (the rational y))))

(defun-inline fast-number-equiv (x y)
  (declare (xargs :guard (and (acl2-numberp x) (acl2-numberp y))
                  :guard-hints (("Goal" :in-theory (enable number-equiv)))))
  (mbe :logic (number-equiv x y)
       :exec (= (the number x)
                (the number y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm equal-bfix-foward-to-bit-equiv-both
  (implies (equal (bfix x) (bfix y))
           (bit-equiv x y))
  :rule-classes :forward-chaining)

(in-theory (enable equal-bfix-foward-to-bit-equiv-both))

(defthm equal-pos-fix-foward-to-pos-equiv-both
  (implies (equal (pos-fix x) (pos-fix y))
           (pos-equiv x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pos-equiv))))

(defthm equal-nfix-foward-to-nat-equiv-both
  (implies (equal (nfix x) (nfix y))
           (nat-equiv x y))
  :rule-classes :forward-chaining)

(in-theory (enable equal-nfix-foward-to-nat-equiv-both))

(defthm equal-ifix-foward-to-int-equiv-both
  (implies (equal (ifix x) (ifix y))
           (int-equiv x y))
  :rule-classes :forward-chaining)

(in-theory (enable equal-ifix-foward-to-int-equiv-both))

(defthm equal-rfix-foward-to-rational-equiv-both
  (implies (equal (rfix x) (rfix y))
           (rational-equiv x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rational-equiv))))

(defthm equal-fix-foward-to-number-equiv-both
  (implies (equal (fix x) (fix y))
           (number-equiv x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable number-equiv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrefinement number-equiv rational-equiv
  :hints (("Goal" :in-theory (enable number-equiv
                                     rational-equiv
                                     fix
                                     rfix))))

(defrefinement rational-equiv int-equiv
  :hints (("Goal" :in-theory (enable rational-equiv
                                     int-equiv
                                     rfix
                                     ifix))))

(defrefinement int-equiv nat-equiv)

(defrefinement nat-equiv pos-equiv
  :hints (("Goal" :in-theory (enable nat-equiv
                                     pos-equiv
                                     nfix
                                     pos-fix))))

(defrefinement nat-equiv bit-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defcong bit-equiv equal (bfix x) 1)
(defcong pos-equiv equal (pos-fix x) 1)
(defcong nat-equiv equal (nfix x) 1)
(defcong int-equiv equal (ifix x) 1)
(defcong rational-equiv equal (rfix x) 1)
(defcong number-equiv equal (fix x) 1)

;;;;;;;;;;;;;;;;;;;;

(defthm bfix-under-bit-equiv
  (bit-equiv (bfix x)
             x)
  :rule-classes (:rewrite :rewrite-quoted-constant))

(defthm pos-fix-under-pos-equiv
  (pos-equiv (pos-fix x)
             x)
  :rule-classes (:rewrite :rewrite-quoted-constant))

(defthm nfix-under-nat-equiv
  (nat-equiv (nfix x)
             x)
  :rule-classes (:rewrite :rewrite-quoted-constant))

(defthm ifix-under-int-equiv
  (int-equiv (ifix x)
             x)
  :rule-classes (:rewrite :rewrite-quoted-constant))

(defthm fix-under-number-equiv
  (number-equiv (fix x)
                x)
  :rule-classes (:rewrite :rewrite-quoted-constant))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Maybe variants

(std::defredundant
  :names (;; Predicates
          maybe-bitp
          maybe-posp
          maybe-natp
          maybe-integerp

          ;; Fixers
          maybe-bit-fix
          maybe-posp-fix
          maybe-natp-fix
          maybe-integerp-fix

          ;; Equivalences
          maybe-bit-equiv
          maybe-pos-equiv
          maybe-nat-equiv
          maybe-integer-equiv
          ))

;;;;;;;;;;;;;;;;;;;;

(add-macro-fn maybe-bitp maybe-bitp$inline)
(add-macro-fn maybe-posp maybe-posp$inline)
(add-macro-fn maybe-natp maybe-natp$inline)
(add-macro-fn maybe-integerp maybe-integerp$inline)

(add-macro-fn maybe-bit-fix maybe-bit-fix$inline)
(add-macro-fn maybe-posp-fix maybe-posp-fix$inline)
(add-macro-fn maybe-natp-fix maybe-natp-fix$inline)
(add-macro-fn maybe-integerp-fix maybe-integerp-fix$inline)

(add-macro-fn maybe-bit-equiv maybe-bit-equiv$inline)
(add-macro-fn maybe-pos-equiv maybe-pos-equiv$inline)
(add-macro-fn maybe-nat-equiv maybe-nat-equiv$inline)
(add-macro-fn maybe-integer-equiv maybe-integer-equiv$inline)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable maybe-bit-equiv
                    maybe-pos-equiv
                    maybe-nat-equiv
                    maybe-integer-equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline maybe-rationalp (x)
  (declare (xargs :guard t))
  (or (not x)
      (rationalp x)))

(defund-inline maybe-numberp (x)
  (declare (xargs :guard t))
  (or (not x)
      (acl2-numberp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: strengthen maybe-bitp-compound-recognizer in std/basic/defs
(defthm maybe-bitp-compound-recognizer-strong
  (equal (maybe-bitp x)
         (or (not x)
             (bitp x)))
  :rule-classes :compound-recognizer
  :hints (("Goal" :in-theory (enable maybe-bitp))))

(defthm maybe-posp-compound-recognizer
  (equal (maybe-posp x)
         (or (and (integerp x)
                  (< 0 x))
             (not x)))
  :rule-classes :compound-recognizer)

(defthm maybe-natp-compound-recognizer
  (equal (maybe-natp x)
         (or (not x)
             (and (integerp x)
                  (<= 0 x))))
  :rule-classes :compound-recognizer)

(defthm maybe-integerp-compound-recognizer
  (equal (maybe-integerp x)
         (or (integerp x)
             (not x)))
  :rule-classes :compound-recognizer)

(defthm maybe-rationalp-compound-recognizer
  (equal (maybe-rationalp x)
         (or (not x)
             (rationalp x)))
  :rule-classes :compound-recognizer
  :hints (("Goal" :in-theory (enable maybe-rationalp))))

(defthm maybe-numberp-compound-recognizer
  (equal (maybe-numberp x)
         (or (not x)
             (acl2-numberp x)))
  :rule-classes :compound-recognizer
  :hints (("Goal" :in-theory (enable maybe-numberp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline maybe-rational-fix (x)
  (declare (xargs :guard (maybe-rationalp x)))
  (mbe :logic (if x (rfix x) nil)
       :exec x))

(defund-inline maybe-number-fix (x)
  (declare (xargs :guard (maybe-numberp x)))
  (mbe :logic (if x (fix x) nil)
       :exec x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm maybe-bit-fix-when-maybe-bitp
  (implies (maybe-bitp x)
           (equal (maybe-bit-fix x)
                  x)))

(defthmd maybe-bit-fix-when-not-maybe-bitp
  (implies (not (maybe-bitp x))
           (equal (maybe-bit-fix x)
                  0))
  :hints (("Goal" :in-theory (enable maybe-bit-fix))))

(defthm maybe-bit-fix-when-not-maybe-bitp-cheap
  (implies (not (maybe-bitp x))
           (equal (maybe-bit-fix x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by maybe-bit-fix-when-not-maybe-bitp)))

;;;;;;;;;;;;;;;;;;;;

(defthm maybe-posp-fix-when-maybe-posp
  (implies (maybe-posp x)
           (equal (maybe-posp-fix x)
                  x)))

(defthmd maybe-posp-fix-when-not-maybe-posp
  (implies (not (maybe-posp x))
           (equal (maybe-posp-fix x)
                  1))
  :hints (("Goal" :in-theory (enable maybe-posp-fix))))

(defthm maybe-posp-fix-when-not-maybe-posp-cheap
  (implies (not (maybe-posp x))
           (equal (maybe-posp-fix x)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by maybe-posp-fix-when-not-maybe-posp)))

;;;;;;;;;;;;;;;;;;;;

(defthm maybe-natp-fix-when-maybe-natp
  (implies (maybe-natp x)
           (equal (maybe-natp-fix x)
                  x)))

(defthmd maybe-natp-fix-when-not-maybe-natp
  (implies (not (maybe-natp x))
           (equal (maybe-natp-fix x)
                  0))
  :hints (("Goal" :in-theory (enable maybe-natp-fix))))

(defthm maybe-natp-fix-when-not-maybe-natp-cheap
  (implies (not (maybe-natp x))
           (equal (maybe-natp-fix x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by maybe-natp-fix-when-not-maybe-natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm maybe-integerp-fix-when-maybe-integerp
  (implies (maybe-integerp x)
           (equal (maybe-integerp-fix x)
                  x)))

(defthmd maybe-integerp-fix-when-not-maybe-integerp
  (implies (not (maybe-integerp x))
           (equal (maybe-integerp-fix x)
                  0))
  :hints (("Goal" :in-theory (enable maybe-integerp-fix))))

(defthm maybe-integerp-fix-when-not-maybe-integerp-cheap
  (implies (not (maybe-integerp x))
           (equal (maybe-integerp-fix x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by maybe-integerp-fix-when-not-maybe-integerp)))

;;;;;;;;;;;;;;;;;;;;

(defthm maybe-rational-fix-when-maybe-rationalp
  (implies (maybe-rationalp x)
           (equal (maybe-rational-fix x)
                  x))
  :hints (("Goal" :in-theory (enable maybe-rational-fix))))

(defthmd maybe-rational-fix-when-not-maybe-rationalp
  (implies (not (maybe-rationalp x))
           (equal (maybe-rational-fix x)
                  0))
  :hints (("Goal" :in-theory (enable maybe-rational-fix))))

(defthm maybe-rational-fix-when-not-maybe-rationalp-cheap
  (implies (not (maybe-rationalp x))
           (equal (maybe-rational-fix x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by maybe-rational-fix-when-not-maybe-rationalp)))

;;;;;;;;;;;;;;;;;;;;

(defthm maybe-number-fix-when-maybe-numberp
  (implies (maybe-numberp x)
           (equal (maybe-number-fix x)
                  x))
  :hints (("Goal" :in-theory (enable maybe-number-fix))))

(defthmd maybe-number-fix-when-not-maybe-numberp
  (implies (not (maybe-numberp x))
           (equal (maybe-number-fix x)
                  0))
  :hints (("Goal" :in-theory (enable maybe-number-fix))))

(defthm maybe-number-fix-when-not-maybe-numberp-cheap
  (implies (not (maybe-numberp x))
           (equal (maybe-number-fix x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by maybe-number-fix-when-not-maybe-numberp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline maybe-rational-equiv (x y)
  (declare (xargs :guard (and (maybe-rationalp x) (maybe-rationalp y))))
  (equal (maybe-rational-fix x)
         (maybe-rational-fix y)))

(defund-inline maybe-number-equiv (x y)
  (declare (xargs :guard (and (maybe-numberp x) (maybe-numberp y))))
  (equal (maybe-number-fix x)
         (maybe-number-fix y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defequiv maybe-bit-equiv)
(defequiv maybe-pos-equiv)
(defequiv maybe-nat-equiv)
(defequiv maybe-integer-equiv)

(defequiv maybe-rational-equiv
  :hints (("Goal" :in-theory (enable maybe-rational-equiv))))

(defequiv maybe-number-equiv
  :hints (("Goal" :in-theory (enable maybe-number-equiv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm equal-maybe-bit-fix-foward-to-maybe-bit-equiv-both
  (implies (equal (maybe-bit-fix x) (maybe-bit-fix y))
           (maybe-bit-equiv x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable maybe-bit-equiv))))

(defthm equal-maybe-posp-fix-foward-to-maybe-pos-equiv-both
  (implies (equal (maybe-posp-fix x) (maybe-posp-fix y))
           (maybe-pos-equiv x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable maybe-pos-equiv))))

(defthm equal-maybe-nat-fix-foward-to-maybe-nat-equiv-both
  (implies (equal (maybe-natp-fix x) (maybe-natp-fix y))
           (maybe-nat-equiv x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable maybe-nat-equiv))))

(defthm equal-maybe-integerp-fix-foward-to-integer-equiv-both
  (implies (equal (maybe-integerp-fix x) (maybe-integerp-fix y))
           (maybe-integer-equiv x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable maybe-integer-equiv))))

(defthm equal-maybe-rational-fix-foward-to-maybe-rational-equiv-both
  (implies (equal (maybe-rational-fix x) (maybe-rational-fix y))
           (maybe-rational-equiv x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable maybe-rational-equiv))))

(defthm equal-maybe-number-fix-foward-to-maybe-number-equiv-both
  (implies (equal (maybe-number-fix x) (maybe-number-fix y))
           (maybe-number-equiv x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable maybe-number-equiv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrefinement maybe-number-equiv number-equiv
  :hints (("Goal" :in-theory (enable maybe-number-equiv
                                     number-equiv
                                     maybe-number-fix))))

(defrefinement maybe-rational-equiv rational-equiv
  :hints (("Goal" :in-theory (enable maybe-rational-equiv
                                     rational-equiv
                                     maybe-rational-fix))))

(defrefinement maybe-integer-equiv int-equiv
  :hints (("Goal" :in-theory (enable maybe-integer-equiv
                                     int-equiv
                                     maybe-integerp-fix))))

(defrefinement maybe-nat-equiv nat-equiv
  :hints (("Goal" :in-theory (enable maybe-nat-equiv
                                     nat-equiv
                                     maybe-natp-fix))))

(defrefinement maybe-pos-equiv pos-equiv
  :hints (("Goal" :in-theory (enable maybe-pos-equiv
                                     pos-equiv
                                     maybe-posp-fix))))

(defrefinement maybe-bit-equiv bit-equiv
  :hints (("Goal" :in-theory (enable maybe-bit-equiv
                                     bit-equiv
                                     maybe-bit-fix))))

;;;;;;;;;;;;;;;;;;;;

(defrefinement maybe-number-equiv maybe-rational-equiv
  :hints (("Goal" :in-theory (enable maybe-number-equiv
                                     maybe-rational-equiv
                                     maybe-number-fix
                                     maybe-rational-fix))))

(defrefinement maybe-rational-equiv maybe-integer-equiv
  :hints (("Goal" :in-theory (enable maybe-rational-equiv
                                     maybe-integer-equiv
                                     maybe-rational-fix
                                     maybe-integerp-fix))))

(defrefinement maybe-integer-equiv maybe-nat-equiv
  :hints (("Goal" :in-theory (enable maybe-integer-equiv
                                     maybe-nat-equiv
                                     maybe-integerp-fix
                                     maybe-natp-fix))))

(defrefinement maybe-nat-equiv maybe-pos-equiv
  :hints (("Goal" :in-theory (enable maybe-nat-equiv
                                     maybe-pos-equiv
                                     maybe-natp-fix
                                     maybe-posp-fix))))

(defrefinement maybe-nat-equiv maybe-bit-equiv
  :hints (("Goal" :in-theory (enable maybe-nat-equiv
                                     maybe-bit-equiv
                                     maybe-natp-fix
                                     maybe-bit-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defcong maybe-bit-equiv equal (maybe-bit-fix x) 1)
(defcong maybe-pos-equiv equal (maybe-posp-fix x) 1)
(defcong maybe-nat-equiv equal (maybe-natp-fix x) 1)
(defcong maybe-integer-equiv equal (maybe-integerp-fix x) 1)

(defcong maybe-rational-equiv equal (maybe-rational-fix x) 1
  :hints (("Goal" :in-theory (enable maybe-rational-equiv))))

(defcong maybe-number-equiv equal (maybe-number-fix x) 1
  :hints (("Goal" :in-theory (enable maybe-number-equiv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm maybe-bit-fix-under-maybe-bit-equiv
  (maybe-bit-equiv (maybe-bit-fix x)
                   x)
  :rule-classes (:rewrite :rewrite-quoted-constant))

(defthm maybe-posp-fix-under-maybe-pos-equiv
  (maybe-pos-equiv (maybe-posp-fix x)
                   x)
  :rule-classes (:rewrite :rewrite-quoted-constant))

(defthm maybe-integerp-fix-under-maybe-integer-equiv
  (maybe-integer-equiv (maybe-integerp-fix x)
                       x)
  :rule-classes (:rewrite :rewrite-quoted-constant))

(defthm maybe-rational-fix-under-maybe-rational-equiv
  (maybe-rational-equiv (maybe-rational-fix x)
                        x)
  :rule-classes (:rewrite :rewrite-quoted-constant)
  :hints (("Goal" :in-theory (enable maybe-rational-equiv))))

(defthm maybe-number-fix-under-maybe-number-equiv
  (maybe-number-equiv (maybe-number-fix x)
                      x)
  :rule-classes (:rewrite :rewrite-quoted-constant)
  :hints (("Goal" :in-theory (enable maybe-number-equiv))))
