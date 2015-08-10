;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; b-ops-aux-def.lisp
; This file contains definitions of auxiliary definition of bit operations.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; [Jared] changed this book to just be an include of the identical book
(include-book "workshops/1999/pipeline/b-ops-aux-def" :dir :system)

;; (include-book "trivia")
;; (include-book "ihs")

;; (deflabel begin-b-ops-aux-def)

;; ;; Bs-and takes arbitrary number of bits. It returns 1 if all
;; ;; arguments are 1's, otherwise return 0.
;; (defmacro bs-and (x y &rest rst)
;;   (xxxjoin 'b-and (cons x (cons y rst))))

;; ;; Bs-and takes arbitrary number of bits. It returns 1 if any
;; ;; argument is 1, otherwise return 0.
;; (defmacro bs-ior (x y &rest rst)
;;   (xxxjoin 'b-ior (cons x (cons y rst))))

;; ;; b1p returns T if x is 1, nil if x is 0.
;; (defun b1p (x)
;;   (declare (xargs :guard (bitp x)))
;;   (not (zbp x)))

;; ;; Bit if operation.
;; (defmacro b-if (test a1 ax)
;;   `(if (b1p ,test) ,a1 ,ax))

;; ;; N-bit bit vector comparator.  If the least significant n-bit of
;; ;; vectors x and y are equal, bv-eqv returns 1.
;; (defun bv-eqv (n x y)
;;   (declare (xargs :guard (and (integerp x) (integerp y)
;; 			      (integerp n) (<= 0 n))))
;;   (if (equal (loghead n x) (loghead n y)) 1 0))

;; (defthm bitp-bv-eqv
;;     (bitp (bv-eqv n x y)))

;; (defthm bit-p-unsigned-byte-p-1
;; 	     (implies (bitp x)
;; 		      (unsigned-byte-p 1 x))
;; 	   :hints (("Goal" :in-theory (enable unsigned-byte-p bitp))))

;; ;; Note on disabled and enabled functions
;; ;; All bit operations except for b-if are disabled.  We'd like to
;; ;; deal with bit operations without opening them.  However, enabling
;; ;; b-if allows the prover to examine cases automatically.

;; (in-theory (disable b1p))
;; (in-theory (disable bv-eqv))
