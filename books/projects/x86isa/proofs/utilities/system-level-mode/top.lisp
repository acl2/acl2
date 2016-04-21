;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; This is the top-level book to include when reasoning about code in
;; the system-level mode.

(include-book "non-marking-mode-utils" :ttags :all)
(include-book "paging-lib/paging-top" :ttags :all)
