#|
  Book:      RC6-fibs
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Lee Pike, Galois Connections, Inc. <leepike@galois.com>
|#

(in-package "ACL2")

; Edited by Matt K.:
; (include-book "make-theorems" :dir :books)
(include-book "../books/make-theorems")

;; --------------------------------------------------------
;; COMPILER OUTPUT
(include-book "RC6-source-shallow-canon")
(include-book "RC6-source-shallow-flatten")
;; --------------------------------------------------------

; Matt K. mod April 2016 for the addition of a type-set bit for the set {1}.
(local (in-theory (disable (:t b-not))))

(make-thm :name |inv-consts|
          :thm-type invariant
          :itr-name |iter_consts_3|
          :ind-name |consts_2|
          :branches (|consts_2|)
          :init-hist (0)
          :hist-widths (0))

(make-thm :name |comp_1|
          :thm-type comp
          :itr-term (|$itr_comp_1| x)
          :ind-term (|$ind_takes_1| x))

(make-thm :name |inst_2|
          :thm-type fn
          :itr-term (|itr_inits_2|)
          :ind-term (|ind_inits_2|))

(make-thm :name |type0|
          :thm-type type
          :itr-term (|$itr_0_typep| x)
          :ind-term (|$ind_0_typep| x)
          :enables (|$itr_0_typep| |$ind_0_typep|))

(make-thm :name |inv-s-l|
          :thm-type invariant
          :arg-list (|init|)
          :arg-types ((|$itr_0_typep| |init|))
          :itr-name |iter_s_l_3|
          :ind-name |s_2_l_2|
          :branches (|s_2| |l_2|)
          :init-hist ((0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                      (0 0))
          :hist-widths (6 1))

(make-thm :name |type1|
          :thm-type type
          :itr-term (|$itr_1_typep| x)
          :ind-term (|$ind_1_typep| x)
          :enables (|$itr_1_typep| |$ind_1_typep|))
