; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "arith-fix-and-equiv"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Definitions from arith-fix-and-equiv. Including this book allows one to
;; include arith-fix-and-equiv locally.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (;; Fixers
          bfix
          bit-fix
          pos-fix
          lposfix
          lnfix
          lifix
          rational-fix
          number-fix

          ;; Equivalences
          bit-equiv
          fast-bit-equiv
          pos-equiv
          fast-pos-equiv
          nat-equiv
          fast-nat-equiv
          int-equiv
          fast-int-equiv
          rational-equiv
          fast-rational-equiv
          number-equiv
          fast-number-equiv
          ))

;;;;;;;;;;;;;;;;;;;;

(add-macro-fn bfix bfix$inline)
(add-macro-fn bit-fix bit-fix$inline)
(add-macro-fn lposfix lposfix$inline)
(add-macro-fn lnfix lnfix$inline)
(add-macro-fn lifix lifix$inline)
(add-macro-fn rational-fix rational-fix$inline)
(add-macro-fn number-fix number-fix$inline)

(add-macro-fn bit-equiv bit-equiv$inline)
(add-macro-fn fast-bit-equiv fast-bit-equiv$inline)
(add-macro-fn pos-equiv pos-equiv$inline)
(add-macro-fn fast-pos-equiv fast-pos-equiv$inline)
(add-macro-fn nat-equiv nat-equiv$inline)
(add-macro-fn fast-nat-equiv fast-nat-equiv$inline)
(add-macro-fn int-equiv int-equiv$inline)
(add-macro-fn fast-int-equiv fast-int-equiv$inline)
(add-macro-fn rational-equiv rational-equiv$inline)
(add-macro-fn fast-rational-equiv fast-rational-equiv$inline)
(add-macro-fn number-equiv number-equiv$inline)
(add-macro-fn fast-number-equiv fast-number-equiv$inline)

;;;;;;;;;;;;;;;;;;;;

(defequiv bit-equiv)
(defequiv pos-equiv)
(defequiv nat-equiv)
(defequiv int-equiv)
(defequiv rational-equiv)
(defequiv number-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (;; Predicates
          maybe-bitp
          maybe-posp
          maybe-natp
          maybe-integerp
          maybe-rationalp
          maybe-numberp

          ;; Fixers
          maybe-bit-fix
          maybe-posp-fix
          maybe-natp-fix
          maybe-integerp-fix
          maybe-rational-fix
          maybe-number-fix

          ;; Equivalences
          maybe-bit-equiv
          maybe-pos-equiv
          maybe-nat-equiv
          maybe-integer-equiv
          maybe-rational-equiv
          maybe-number-equiv
          ))

;;;;;;;;;;;;;;;;;;;;

(add-macro-fn maybe-bitp maybe-bitp$inline)
(add-macro-fn maybe-posp maybe-posp$inline)
(add-macro-fn maybe-natp maybe-natp$inline)
(add-macro-fn maybe-integerp maybe-integerp$inline)
(add-macro-fn maybe-rationalp maybe-rationalp$inline)
(add-macro-fn maybe-numberp maybe-numberp$inline)

(add-macro-fn maybe-bit-fix maybe-bit-fix$inline)
(add-macro-fn maybe-posp-fix maybe-posp-fix$inline)
(add-macro-fn maybe-natp-fix maybe-natp-fix$inline)
(add-macro-fn maybe-integerp-fix maybe-integerp-fix$inline)
(add-macro-fn maybe-rational-fix maybe-rational-fix$inline)
(add-macro-fn maybe-number-fix maybe-number-fix$inline)

(add-macro-fn maybe-bit-equiv maybe-bit-equiv$inline)
(add-macro-fn maybe-pos-equiv maybe-pos-equiv$inline)
(add-macro-fn maybe-nat-equiv maybe-nat-equiv$inline)
(add-macro-fn maybe-integer-equiv maybe-integer-equiv$inline)
(add-macro-fn maybe-rational-equiv maybe-rational-equiv$inline)
(add-macro-fn maybe-number-equiv maybe-number-equiv$inline)

;;;;;;;;;;;;;;;;;;;;

(defequiv maybe-bit-equiv)
(defequiv maybe-pos-equiv)
(defequiv maybe-nat-equiv)
(defequiv maybe-integer-equiv)
(defequiv maybe-rational-equiv)
(defequiv maybe-number-equiv)
