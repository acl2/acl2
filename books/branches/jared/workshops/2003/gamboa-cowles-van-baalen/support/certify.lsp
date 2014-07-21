;;; Run this script to certify all the books.  But first, certify matalg in
;;; ../../cowles-gamboa-van-baalen_matrix/support/.

(certify-book "linalg" 0)

:u

(ld "defpkg.lisp")

(certify-book "kalman-defs" 1)

:u

(certify-book "kalman-proof" 1 t :skip-proofs-okp t :defaxioms-okp t)

:u

(certify-book "kalman-demo" 1 t :skip-proofs-okp t :defaxioms-okp t)
