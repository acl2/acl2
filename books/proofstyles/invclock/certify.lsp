#|

 certify.lsp
 ~~~~~~~~~~~

This script file certifies all the books for proving the equivalence between
clock functions and inductive invariants in ACL2. 

The set of books here is (hopefully) well documented. For further details about
the books the reader is encouraged to look at the following paper on the
subject.

1. S. Ray and J S. Moore. Proof Styles in Operational Semantics. In A. J. Hu
   and A. K. Martin, editors, Proceedings of the 5th International Conference
   on Formal Methods in Computer-Aided Design (FMCAD 2004), volume 3312 of LNCS,
   Nov 2004, pages 67-81. Springer-Verlag.

|#


(set-inhibit-output-lst '(proof-tree prove))

(ubt! 1)

;; The directory i2c contains the set of books that show how to transform
;; inductive invariant proofs to clock function proofs. 
(set-cbd "i2c")
(ld "certify-i2c.lsp")

(set-cbd "..")

;; The directory c2i contains the set of books that show how to transform clock
;; function proofs to inductive invariants.
(set-cbd "c2i")
(ld "certify-c2i.lsp")

(set-cbd "..")

;; Finally the directory compose contains the books for composition of proofs.
(set-cbd "compose")
(ld "certify-compose.lsp")

(set-cbd "..")

(set-inhibit-output-lst '(proof-tree prove))
