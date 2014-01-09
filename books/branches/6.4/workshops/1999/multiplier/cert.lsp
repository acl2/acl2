;;;***************************************************************
;;;Proof of Correctness of a Floating Point Multiplier

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1999
;;;***************************************************************

(in-package "ACL2")

;;Certify the RTL definitions and the compiler:

(certify-book "rtl")

:u

(certify-book "compiler")

;;Compile the multiplier, generating the files "fmul.lisp"
;;and "fmul*.lisp":

(compile-pipeline "fmul" z)

:u

;;Certify the compiled multiplier (this requires the RTL definitions):

(certify-book "fmul")

:u

;;Certify the book "spec", which contains the definitions required
;;for the correctness statement and introduces the constrained
;;inputs, which are required by the "fmul*" book:

(certify-book "spec")

:u

;;Certify the book "fmul-star":

(certify-book "fmul-star")

:u

;;Prove the theorem:

(certify-book "proof")
