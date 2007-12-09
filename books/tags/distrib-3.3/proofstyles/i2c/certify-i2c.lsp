#|

  certify-i2c.lsp
  ~~~~~~~~~~~~~~~~

This script is for certification of all the books that convert inductive
invariant proofs to clock function proofs.

|#

(set-inhibit-output-lst '(proof-tree prove))
(ubt! 1)

;; This book shows how to do the generic transformation for total correctness
;; proofs.
(certify-book "i2c-total")
(u)

;; This script does the same for partial correctness.
(certify-book "i2c-partial")
(u)

;; This book defines a macro called inv-to-clock that automatically
;; functionally instantiates the proofs above for concrete programs.
(certify-book "inv-to-clock")
(u)

(set-inhibit-output-lst '(proof-tree))