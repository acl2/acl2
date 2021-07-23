; Axe variants of the prime field + BV rules
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "bv-rules")
(include-book "kestrel/axe/axe-syntax-functions" :dir :system)

;; restricts it the variables
(defthm add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-negated-start-axe
  (implies (and (syntaxp (and (quotep k1)
                              (quotep p)))
                (acl2::axe-syntaxp (and (acl2::syntactic-variablep bit1 acl2::dag-array)
                                        (acl2::syntactic-variablep bit2 acl2::dag-array)))
                (equal k1 (neg 2 p)) ;k1 = -2
                (primep p)
                (< 2 p)
                (bitp bit1)
                (bitp bit2))
           (equal (add (mul k1 bit1 p) (neg bit2 p) p)
                  (mul (neg 1 p) (acl2::bvcat 1 bit1 1 bit2) p)))
  :hints (("Goal" :use add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-negated-start
           :in-theory (disable add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-negated-start))))

;; restricts it the variables
(defthm add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-negated-start-alt-axe
  (implies (and (syntaxp (and (quotep k1)
                              (quotep p)))
                (acl2::axe-syntaxp (and (acl2::syntactic-variablep bit1 acl2::dag-array)
                                        (acl2::syntactic-variablep bit2 acl2::dag-array)))
                (equal k1 (neg 2 p)) ;k1 = -2
                (primep p)
                (< 2 p)
                (bitp bit1)
                (bitp bit2))
           (equal (add (neg bit2 p) (mul k1 bit1 p) p)
                  (mul (neg 1 p) (acl2::bvcat 1 bit1 1 bit2) p)))
  :hints (("Goal" :use add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-negated-start-alt
           :in-theory (disable add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-negated-start-alt))))

;; restricts it the variables
;;has an extra addend
(defthm add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-negated-start-extra-axe
  (implies (and (syntaxp (and (quotep k1)
                              (quotep p)))
                (acl2::axe-syntaxp (and (acl2::syntactic-variablep bit1 acl2::dag-array)
                                        (acl2::syntactic-variablep bit2 acl2::dag-array)))
                (equal k1 (neg 2 p)) ;k1 = -2
                (primep p)
                (< 2 p)
                (bitp bit1)
                (bitp bit2))
           (equal (add (mul k1 bit1 p) (add (neg bit2 p) extra p) p)
                  (add (mul (neg 1 p) (acl2::bvcat 1 bit1 1 bit2) p) extra p)))
  :hints (("Goal" :use (add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-negated-start)
           :in-theory (disable add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-negated-start))))

;; restricts it the variables
;;has an extra addend
(defthm add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-negated-start-extra-alt-axe
  (implies (and (syntaxp (and (quotep k1)
                              (quotep p)))
                (acl2::axe-syntaxp (and (acl2::syntactic-variablep bit1 acl2::dag-array)
                                        (acl2::syntactic-variablep bit2 acl2::dag-array)))
                (equal k1 (neg 2 p)) ;k1 = -2
                (primep p)
                (< 2 p)
                (bitp bit1)
                (bitp bit2))
           (equal (add (neg bit2 p) (add (mul k1 bit1 p) extra p) p)
                  (add (mul (neg 1 p) (acl2::bvcat 1 bit1 1 bit2) p)
                       extra p)))
  :hints (("Goal" :use (add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-negated-start-alt)
           :in-theory (disable add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-negated-start-alt))))
