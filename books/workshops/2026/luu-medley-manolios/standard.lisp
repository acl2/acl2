; The standard matrix multiplication algorithm as a correct scheme.
;
; standard-scheme n is the obag of the n^3 unit summands
; (e_ij, e_jk, e_ik) for i,j,k < n, built by the same three nested
; downward recursions as mm-tensor (mm-tensor.lisp): the innermost level
; inserts one summand per k, and the outer two levels join the bags of the
; inner level with insert-list (zero-support.lisp).  Because the levels
; mirror mm-tensor-3/2/1 exactly, scheme-sum-of-insert and
; scheme-sum-of-insert-list turn the scheme-sum of each level into the
; corresponding mm-tensor level, which gives
;
;   (correct-schemep (standard-scheme n) n)   for every natural n
;
; (theorem correct-schemep-of-standard-scheme), so correct-schemep is
; satisfiable at every n.  The rank is n^3 (scheme-rank-of-standard-scheme).
; Validated by execution before the proofs: at n = 2 the construction is
; exactly *arb-std2* (arbitrary.lisp), and at n = 3 correct-schemep holds.

(in-package "ACL2")

(include-book "zero-support")
(local (include-book "arithmetic/top-with-meta" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Unit summands are summands
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The unit matrix e_ij is not the zero matrix: the entries at (i,j)
;;; differ (mat-entry-of-bit-mat-unit, mat-entry-of-bit-mat0 in mmt.lisp).

(defruled bit-mat-unit-not-bit-mat0
  (implies (and (natp i) (natp j) (natp n) (< i n) (< j n))
           (not (equal (bit-mat-unit i j n n) (bit-mat0 n n))))
  :use ((:instance mat-entry-of-bit-mat-unit (a i) (b j) (m n))
        (:instance mat-entry-of-bit-mat0 (m n)))
  :disable (mat-entry mat-entry-of-bit-mat-unit mat-entry-of-bit-mat0
            bit-mat-unit bit-mat0))

;;; Stated on the (list a b c) form, which is what summand (an enabled
;;; definition) rewrites to.

(defruled summandp-of-unit-summand
  (implies (and (natp n)
                (natp i1) (natp j1) (natp i2) (natp j2) (natp i3) (natp j3)
                (< i1 n) (< j1 n) (< i2 n) (< j2 n) (< i3 n) (< j3 n))
           (summandp (list (bit-mat-unit i1 j1 n n)
                           (bit-mat-unit i2 j2 n n)
                           (bit-mat-unit i3 j3 n n))
                     n))
  :enable (bit-mat-unit-not-bit-mat0)
  :disable (bit-mat-unit bit-mat0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The standard scheme
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; standard-scheme n = the bag of e_ij (x) e_jk (x) e_ik over i,j,k < n,
;;; in the three levels of mm-tensor.  Each level carries a summand-listp
;;; theorem under the same index bounds as nth-of-mm-tensor-3/2/1
;;; (mmt.lisp), and a mat-triple-listp theorem for the insert-list guards.

(define standard-scheme-3 ((i natp) (j natp) (k natp) (n natp))
  :returns (sch obag::bagp)
  :verify-guards :after-returns
  (if (zp k)
      nil
    (obag::insert (summand (bit-mat-unit i j n n)
                           (bit-mat-unit j (1- k) n n)
                           (bit-mat-unit i (1- k) n n))
                  (standard-scheme-3 i j (1- k) n)))
  ///
  (defrule summand-listp-of-standard-scheme-3
    (implies (and (natp n) (natp i) (natp j) (natp k)
                  (< i n) (< j n) (<= k n))
             (summand-listp (standard-scheme-3 i j k n) n))
    :induct (standard-scheme-3 i j k n)
    :enable (summandp-of-unit-summand)
    :disable (summandp bit-mat-unit))
  (defrule mat-triple-listp-of-standard-scheme-3
    (mat-triple-listp (standard-scheme-3 i j k n))
    :induct (standard-scheme-3 i j k n)
    :enable (mat-triple-listp-of-insert)
    :disable (bit-mat-unit)))

(define standard-scheme-2 ((i natp) (j natp) (n natp))
  :returns (sch obag::bagp)
  :verify-guards :after-returns
  (if (zp j)
      nil
    (insert-list (standard-scheme-3 i (1- j) n n)
                 (standard-scheme-2 i (1- j) n)))
  ///
  (defrule summand-listp-of-standard-scheme-2
    (implies (and (natp n) (natp i) (natp j)
                  (< i n) (<= j n))
             (summand-listp (standard-scheme-2 i j n) n))
    :induct (standard-scheme-2 i j n)
    :disable (summandp))
  (defrule mat-triple-listp-of-standard-scheme-2
    (mat-triple-listp (standard-scheme-2 i j n))
    :induct (standard-scheme-2 i j n)
    :enable (mat-triple-listp-of-insert-list)))

(define standard-scheme-1 ((i natp) (n natp))
  :returns (sch obag::bagp)
  :verify-guards :after-returns
  (if (zp i)
      nil
    (insert-list (standard-scheme-2 (1- i) n n)
                 (standard-scheme-1 (1- i) n)))
  ///
  (defrule summand-listp-of-standard-scheme-1
    (implies (and (natp n) (natp i) (<= i n))
             (summand-listp (standard-scheme-1 i n) n))
    :induct (standard-scheme-1 i n)
    :disable (summandp))
  (defrule mat-triple-listp-of-standard-scheme-1
    (mat-triple-listp (standard-scheme-1 i n))
    :induct (standard-scheme-1 i n)
    :enable (mat-triple-listp-of-insert-list)))

(define standard-scheme ((n natp))
  :returns (sch obag::bagp)
  (standard-scheme-1 n n)
  ///
  (defrule summand-listp-of-standard-scheme
    (implies (natp n)
             (summand-listp (standard-scheme n) n))
    :disable (summandp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Validation by execution
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; At n = 2 the construction is the rank-8 standard scheme of
;;; arbitrary.lisp (obags are canonical, so insertion order is immaterial);
;;; at n = 3 it is correct.

(assert-event (equal (standard-scheme 2) *arb-std2*))
(assert-event (correct-schemep (standard-scheme 3) 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Correctness
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule schemep-of-standard-scheme
  (implies (natp n)
           (schemep (standard-scheme n) n))
  :disable (summand-listp))

;;; scheme-sum level by level: the empty bag denotes the zero tensor (the
;;; base case of every level), inserting a summand adds its tensor
;;; (scheme-sum-of-insert, tensor.lisp), and joining a bag adds its sum
;;; (scheme-sum-of-insert-list, zero-support.lisp).

(defruled scheme-sum-of-nil
  (equal (scheme-sum nil n)
         (bit-listn0 (* n n n n n n)))
  :enable (scheme-sum))

(defruled scheme-sum-of-standard-scheme-3
  (implies (and (natp n) (natp i) (natp j) (natp k)
                (< i n) (< j n) (<= k n))
           (equal (scheme-sum (standard-scheme-3 i j k n) n)
                  (mm-tensor-3 i j k n)))
  :induct (standard-scheme-3 i j k n)
  :enable (standard-scheme-3 mm-tensor-3 scheme-sum-of-insert scheme-sum-of-nil
           summandp-of-unit-summand)
  :disable (tensor summandp summand-listp bit-mat-unit))

(defruled scheme-sum-of-standard-scheme-2
  (implies (and (natp n) (natp i) (natp j)
                (< i n) (<= j n))
           (equal (scheme-sum (standard-scheme-2 i j n) n)
                  (mm-tensor-2 i j n)))
  :induct (standard-scheme-2 i j n)
  :enable (standard-scheme-2 mm-tensor-2 scheme-sum-of-insert-list scheme-sum-of-nil
           scheme-sum-of-standard-scheme-3)
  :disable (summandp summand-listp))

(defruled scheme-sum-of-standard-scheme-1
  (implies (and (natp n) (natp i) (<= i n))
           (equal (scheme-sum (standard-scheme-1 i n) n)
                  (mm-tensor-1 i n)))
  :induct (standard-scheme-1 i n)
  :enable (standard-scheme-1 mm-tensor-1 scheme-sum-of-insert-list scheme-sum-of-nil
           scheme-sum-of-standard-scheme-2)
  :disable (summandp summand-listp))

(defrule scheme-sum-of-standard-scheme
  (implies (natp n)
           (equal (scheme-sum (standard-scheme n) n)
                  (mm-tensor n)))
  :enable (standard-scheme mm-tensor scheme-sum-of-standard-scheme-1))

(defrule correct-schemep-of-standard-scheme
  (implies (natp n)
           (correct-schemep (standard-scheme n) n))
  :enable (correct-schemep)
  :disable (schemep standard-scheme))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Rank
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; scheme-rank is len; inserting into a bag adds one element, joining
;;; a list adds its length, so the levels have k, j*n and i*n*n summands.

(defruled len-of-insert
  (implies (obag::bagp b)
           (equal (len (obag::insert x b))
                  (1+ (len b))))
  :induct (obag::insert x b)
  :enable (obag::insert obag::bagp obag::head obag::tail obag::emptyp obag::bfix))

(defruled len-of-insert-list
  (implies (obag::bagp b)
           (equal (len (insert-list l b))
                  (+ (len l) (len b))))
  :induct (insert-list l b)
  :enable (insert-list len-of-insert))

(defruled len-of-standard-scheme-3
  (equal (len (standard-scheme-3 i j k n))
         (nfix k))
  :induct (standard-scheme-3 i j k n)
  :enable (standard-scheme-3 len-of-insert)
  :disable (bit-mat-unit))

(defruled len-of-standard-scheme-2
  (equal (len (standard-scheme-2 i j n))
         (* (nfix j) (nfix n)))
  :induct (standard-scheme-2 i j n)
  :enable (standard-scheme-2 len-of-insert-list len-of-standard-scheme-3))

(defruled len-of-standard-scheme-1
  (equal (len (standard-scheme-1 i n))
         (* (nfix i) (nfix n) (nfix n)))
  :induct (standard-scheme-1 i n)
  :enable (standard-scheme-1 len-of-insert-list len-of-standard-scheme-2))

(defrule scheme-rank-of-standard-scheme
  (implies (natp n)
           (equal (scheme-rank (standard-scheme n))
                  (* n n n)))
  :enable (standard-scheme scheme-rank len-of-standard-scheme-1))
