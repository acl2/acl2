; rank245.lisp -- Appendix A of the paper: the rank-245 scheme for 7x7
; matrix multiplication over F_2.
;
; The masks in rank245-data.lisp were decoded from the Base32/zlib block
; in the paper by decode_scheme.py (bit 7*i+j of a mask is entry [i,j],
; which is exactly our index convention midx).  Here ACL2 checks, by
; evaluation, that the 245 rank-one terms are distinct, have nonzero
; factors, and sum to M^(7): i.e. that the data is a scheme in the sense
; of Definition 2.2.

(in-package "ACL2")

(include-book "scheme")
(include-book "rank245-data")

;; Little-endian bit vector of length L of a natural number.
(defun mask->bv (L m)
  (declare (xargs :guard (and (natp L) (natp m))))
  (if (zp L)
      nil
    (cons (logand m 1) (mask->bv (1- L) (ash m -1)))))

(defun masks->scheme (L lst)
  (declare (xargs :guard (and (natp L) (true-listp lst)) :verify-guards nil))
  (if (atom lst)
      nil
    (cons (list (mask->bv L (first (car lst)))
                (mask->bv L (second (car lst)))
                (mask->bv L (third (car lst))))
          (masks->scheme L (cdr lst)))))

(defconst *rank245-scheme* (masks->scheme 49 *rank245-masks*))

(defthm rank245-has-245-terms
  (equal (len *rank245-scheme*) 245))

(defthm rank245-terms-distinct
  (no-duplicatesp-equal *rank245-scheme*))

;; The scheme is a decomposition of the 7x7 matrix multiplication tensor
;; over F_2 with 245 nonzero rank-one terms (checked by evaluation).
(defthm rank245-is-a-scheme
  (schemep 7 *rank245-scheme*))

;; For comparison: the naive scheme has 7^3 = 343 terms.
(defthm naive-7-has-343-terms
  (equal (len (naive-scheme 7)) 343))

;; Hence, by Theorem 4.1 (connectivity.lisp), the rank-245 scheme is
;; reachable from the naive scheme by flip and plus moves alone; see
;; rank245-reachable in top.lisp.
