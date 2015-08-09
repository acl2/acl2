#|
  Book:      TEA-fibs
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Lee Pike, Galois Connections, Inc. <leepike@galois.com>
|#

(in-package "ACL2")

; Edited by Matt K.:
; (include-book "make-theorems" :dir :books)
(include-book "../books/make-theorems")

;; --------------------------------------------------------
;; COMPILER OUTPUT
(include-book "TEA-source-shallow-canon")
(include-book "TEA-source-shallow-flatten")
;; --------------------------------------------------------

(make-thm :name |type-0-0-thm|
          :thm-type type
          :itr-term (|$itr_0_typep| x)
          :ind-term (|$ind_0_typep| x)
          :enables (|$itr_0_typep| |$ind_0_typep|))

(make-thm :name |inv-encode-thm|
          :thm-type invariant
          :arg-list (|z| |y| |k3| |k2| |k1| |k0|)
          :arg-types ((|$itr_0_typep| |k0|)
                      (|$itr_0_typep| |k1|)
                      (|$itr_0_typep| |k2|)
                      (|$itr_0_typep| |k3|)
                      (|$itr_0_typep| |y|)
                      (|$itr_0_typep| |z|))
          :ind-name |sums_4_ys_4_zs_4|
          :itr-name |iter_sums_ys_zs_6|
          :init-hist ((0) (0) (0))
          :hist-widths (0 0 0)
          :branches (|sums_4| |ys_4| |zs_4|))

(make-thm :name |type-1-2-1-thm|
          :thm-type type
          :itr-term (and (|$itr_1_typep| x)
                         (|$itr_2_typep| y))
          :ind-term (|$ind_1_typep| (list x y))
          :enables (|$itr_1_typep| |$itr_2_typep| |$ind_1_typep|))

(make-thm :name |inv-decode-thm|
          :thm-type invariant
          :arg-list (|z| |y| |k3| |k2| |k1| |k0|)
          :arg-types ((|$itr_0_typep| |k0|)
                      (|$itr_0_typep| |k1|)
                      (|$itr_0_typep| |k2|)
                      (|$itr_0_typep| |k3|)
                      (|$itr_0_typep| |y|)
                      (|$itr_0_typep| |z|))
          :ind-name |sums_3_ys_3_zs_3|
          :init-hist ((0) (0) (0))
          :itr-name |iter_sums_ys_zs_5|
          :hist-widths (0 0 0)
          :branches (|sums_3| |zs_3| |ys_3|))
