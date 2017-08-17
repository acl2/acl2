;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; To ensure both of these certify...
(local
 (encapsulate
   ()
   (local (include-book "non-marking-mode-top" :ttags :all))))

(local
 (encapsulate
   ()
   (local (include-book "marking-mode-top" :ttags :all))))
