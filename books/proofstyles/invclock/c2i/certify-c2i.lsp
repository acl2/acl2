#|

  certify-c2i.lsp
  ~~~~~~~~~~~~~~~~

This script is for certification of all the books that convert clock function
proofs to inductive invariant proofs.

|#

(set-inhibit-output-lst '(proof-tree prove))
(ubt! 1)

;; This book shows how to do the generic transformation for total correctness
;; proofs.
(certify-book "c2i-total")
(u)

;; This script does the same for partial correctness.
(certify-book "c2i-partial")
(u)

;; This book defines a macro called clock-to-inv that automatically
;; functionally instantiates the proofs above for concrete programs.
(certify-book "clock-to-inv")
(u)

(set-inhibit-output-lst '(proof-tree))

