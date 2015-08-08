#|
  Book:      proof-fac
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Lee Pike, Galois Connections, Inc. <leepike@galois.com>
|#

(in-package "ACL2")

; Edited by Matt K.:
; (include-book "make-theorems" :dir :books)
(include-book "../books/make-theorems")

;; --------------------------------------------------------
;; COMPILER OUTPUT
(include-book "fac-source-shallow-canon")
(include-book "fac-source-shallow-flatten")
;; --------------------------------------------------------

(make-thm :name |inv-facs-thm|
          :thm-type invariant
          :ind-name |idx_2_facs_2|
          :itr-name |iter_idx_facs_3|
          :init-hist ((0) (0))
          :hist-widths (0 0)
          :branches (|idx_2| |facs_2|))

(make-thm :name |fac-thm|
          :thm-type fn
          :itr-term (|itr_fac| i)
          :ind-term (|ind_fac| i))
