
; top.lisp                                  Vivek & Warren

; This is the top-level book that provides VWSIM, defined in
; "driver.lsp", with the certified books the simulator uses.

(in-package "ACL2")

; utilities to convert SPICE format to VWSIM HDL
(include-book "parse-spice/spice-to-vwsim")
(include-book "vw-flatten-top-sort")

; build a sparse matrix from VWSIM HDL description of circuit
(include-book "sra-vw-flat-sim-help")

; Since the matrix solver ("dz-unc") is not currently guard-verified,
; we must skip some proofs in this book since it uses the solver.
(set-inhibit-warnings "Skip-proofs")
; the top-level simulator function is defined here.
(include-book "sra-vw-flat-sim" :skip-proofs-okp t)
(set-inhibit-warnings)

;; help with post-simulation processing of simulation values directly
;; from the REC STOBJ.
(include-book "print-records-rec")

;; help with writing simulation output to a csv file
(include-book "write-csv")

;; help with plotting simulation output from a csv file
(include-book "gnuplot" :ttags :all)
