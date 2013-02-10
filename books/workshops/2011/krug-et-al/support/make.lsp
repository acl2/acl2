
;;; I am now using:
;;; /projects/hvg/parallel/acl2p/ccl-saved_acl2p

;;; (set-gag-mode :goals)

(set-waterfall-parallelism :full)

(set-waterfall-printing :limited)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(certify-book "Symbolic/vanilla-partial-correctness")

:u

(certify-book "Symbolic/extended-partial-correctness")

:u

(certify-book "Symbolic/defsimulate+")

:u

(certify-book "Utilities/bytes-and-words")

:u

(certify-book "Utilities/misc")

:u

(certify-book "Utilities/total-order")

:u

(certify-book "Utilities/records")

:u

(certify-book "Utilities/disjoint")

:u

(certify-book "Memory/memory-acl2")

:u

(certify-book "Memory/memory-low")

:u

(certify-book "Memory/paging")

:u

(certify-book "Memory/memory")

:u

(certify-book "Y86/y86")

:u

(certify-book "Y86/asm")

:u

(certify-book "MinVisor/setup-nested-page-tables")

:u

(certify-book "MinVisor/va-to-pa-thm")
