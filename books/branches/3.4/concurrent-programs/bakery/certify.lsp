#|

  certify.lsp
  ~~~~~~~~~~~

This file is meant for running the proof of the simplified bakery
implementation. We decompose our proof into a number of books. Each of the
books should certify in ACL2 V2.6. The result is a proof of the bakery
implementation being refinement upto finite stuttering to a simplified model.
The model is simple enough for it to be obvious that it has all the properties
we need.  The proof is now a guarantee that the implementation guarantees the
desired properties.

Note: We designate all the final theorems and the functions they involve with a
capital DEFTHM and DEFUN respectively, so that they are easy to identify.

The theorems we prove are summarized in final-theorems.lisp. This book should
be a proof that the implementation is a stuttering bisimulation of the
original.

Where applicable, (in fact in all the theorems other than >>-stutter2,) we
prove the corresponding version of the theorem without fairness assumptions. It
turns out that the fairness is required only in the theorem >>-stutter2, and I
hope this fact becomes evident in the proof.

|#

(set-inhibit-output-lst '(proof-tree prove))

(ubt! 1)

(certify-book "total-order")
(u)

(certify-book "apply-total-order")
(u)

(certify-book "records")
(u)

(certify-book "variables")
(u)

(certify-book "measures")
(u)

(certify-book "fairenv")
(u)

(certify-book "lexicographic")
(u)

(certify-book "programs")
(u)

(certify-book "properties-of-sets")
(u)

(certify-book "properties")
(u)

(certify-book "initial-state")
(u)

(certify-book "labels")
(u)

(certify-book "stutter1-match")
(u)

(certify-book "pos=1+temp")
(u)

(certify-book "lexicographic-pos")
(u)

(certify-book "stutter2")
(u)

(certify-book "inv-sufficient")
(u)

(certify-book "inv-persists")
 (u)

(certify-book "final-theorems")
(u)

(set-inhibit-output-lst '(proof-tree))



