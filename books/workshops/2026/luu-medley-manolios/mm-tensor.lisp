; The matrix multiplication tensor and correct schemes.
;
; mm-tensor n is the tensor of the bilinear map (A,B) |-> AB on n x n
; matrices: the sum over all i,j,k < n of e_ij (x) e_jk (x) e_ik.  Validated
; computationally at n = 2: the entry of mm-tensor at position
; ((a,b),(c,d),(e,f)) is 1 exactly when b = c, a = e and d = f.
;
; correct-schemep: a scheme is correct when it is well formed and its
; scheme-sum is mm-tensor.

(in-package "ACL2")

(include-book "tensor")
(local (include-book "std/lists/append" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The matrix multiplication tensor
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bit-unit-list ((j natp) (n natp))
  :returns (l bit-list-p)
  (if (zp n)
      nil
    (if (zp j)
        (cons 1 (bit-listn0 (1- n)))
      (cons 0 (bit-unit-list (1- j) (1- n)))))
  ///

  (defrule bit-listnp-of-bit-unit-list
    (bit-listnp (bit-unit-list j n) n)
    :enable (bit-listnp)))

(define bit-mat-unit ((i natp) (j natp) (m natp) (n natp))
  :returns (a bit-list-listp)
  (if (zp m)
      nil
    (if (zp i)
        (cons (bit-unit-list j n) (bit-mat0 (1- m) n))
      (cons (bit-listn0 n) (bit-mat-unit (1- i) j (1- m) n))))
  ///

  (defrule bit-matp-of-bit-mat-unit
    (bit-matp (bit-mat-unit i j m n) m n)
    :enable (bit-matp))
  (defrule len-of-mat-flat-of-bit-mat-unit
    (implies (and (natp m) (natp n))
             (equal (len (mat-flat (bit-mat-unit i j m n)))
                    (* m n)))
    :use ((:instance len-of-mat-flat (a (bit-mat-unit i j m n))))
    :disable (len-of-mat-flat bit-mat-unit)))

;;; mm-tensor n = sum over i,j,k < n of e_ij (x) e_jk (x) e_ik.

(define mm-tensor-3 ((i natp) (j natp) (k natp) (n natp))
  :returns (tt bit-list-p)
  :verify-guards :after-returns
  (if (zp k)
      (bit-listn0 (* n n n n n n))
    (bit-list-add
     (tensor (bit-mat-unit i j n n)
             (bit-mat-unit j (1- k) n n)
             (bit-mat-unit i (1- k) n n))
     (mm-tensor-3 i j (1- k) n)))
  ///

  (defrule len-of-mm-tensor-3
    (implies (natp n)
             (equal (len (mm-tensor-3 i j k n))
                    (* n n n n n n)))
    :enable (bit-listn0))

  (defrule bit-listnp-of-mm-tensor-3
    (implies (natp n)
             (bit-listnp (mm-tensor-3 i j k n) (* n n n n n n)))
    :enable (bit-listnp-alt-def)
    :disable mm-tensor-3))

(define mm-tensor-2 ((i natp) (j natp) (n natp))
  :returns (tt bit-list-p)
  :verify-guards :after-returns
  (if (zp j)
      (bit-listn0 (* n n n n n n))
    (bit-list-add (mm-tensor-3 i (1- j) n n)
                  (mm-tensor-2 i (1- j) n)))
  ///

  (defrule len-of-mm-tensor-2
    (implies (natp n)
             (equal (len (mm-tensor-2 i j n))
                    (* n n n n n n)))
    :enable (bit-listn0))

  (defrule bit-listnp-of-mm-tensor-2
    (implies (natp n)
             (bit-listnp (mm-tensor-2 i j n) (* n n n n n n)))
    :enable (bit-listnp-alt-def)
    :disable mm-tensor-2))

(define mm-tensor-1 ((i natp) (n natp))
  :returns (tt bit-list-p)
  :verify-guards :after-returns
  (if (zp i)
      (bit-listn0 (* n n n n n n))
    (bit-list-add (mm-tensor-2 (1- i) n n)
                  (mm-tensor-1 (1- i) n)))
  ///

  (defrule len-of-mm-tensor-1
    (implies (natp n)
             (equal (len (mm-tensor-1 i n))
                    (* n n n n n n)))
    :enable (bit-listn0))

  (defrule bit-listnp-of-mm-tensor-1
    (implies (natp n)
             (bit-listnp (mm-tensor-1 i n) (* n n n n n n)))
    :enable (bit-listnp-alt-def)
    :disable mm-tensor-1))

(define mm-tensor ((n natp))
  :returns (tt bit-list-p)
  (mm-tensor-1 n n)
  ///

  (defrule len-of-mm-tensor
    (implies (natp n)
             (equal (len (mm-tensor n))
                    (* n n n n n n))))

  ;; The size-constrained return theorem.
  (defrule bit-listnp-of-mm-tensor
    (implies (natp n)
             (bit-listnp (mm-tensor n) (* n n n n n n)))
    :enable (bit-listnp-alt-def)
    :disable mm-tensor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Correct schemes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The theorems about correct-schemep under valid paths
;;; (correct-schemep-of-apply-moves, add-duplicate-correctness) live in
;;; add-duplicate.lisp, which has the sum-preservation and Lemma 4.5 machinery
;;; in scope.

(define correct-schemep (sch (n natp))
  :returns (yes/no booleanp)
  (and (schemep sch n)
       (equal (scheme-sum sch n) (mm-tensor n))))
