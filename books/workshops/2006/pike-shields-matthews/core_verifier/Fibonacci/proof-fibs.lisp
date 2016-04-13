#|
  Book:      proof-fibs
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Lee Pike, Galois Connections, Inc. <leepike@galois.com>
|#

(in-package "ACL2")

; Edited by Matt K.:
; (include-book "make-theorems" :dir :books)
(include-book "../books/make-theorems")

;; --------------------------------------------------------
;; COMPILER OUTPUT
(include-book "fibs-source-shallow-canon")
(include-book "fibs-source-shallow-flatten")
;; --------------------------------------------------------

; Matt K. mod April 2016 for the addition of a type-set bit for the set {1}.
(local (in-theory (disable (:t b-not))))

(make-thm :name |inv-fibs-thm|
          :thm-type invariant
          :ind-name |fibs_2|
          :itr-name |iter_fibs_3|
          :init-hist (0 0)
          :hist-widths (1)
          :branches (|fibs_2|))

(make-thm :name |fibs-thm|
          :thm-type fn
          :itr-term (|itr_fib| i)
          :ind-term (|ind_fib| i))
