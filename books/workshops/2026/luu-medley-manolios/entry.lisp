(in-package "ACL2")

(include-book "tensor")

(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Entry semantics for the flat-list tensor representation.
;;;
;;; The tensors of tensor.lisp are flat bit lists; this book recovers their
;;; entry-level reading.  The main results are nth-of-tensor, which shows
;;; that the flat index
;;;
;;;   jc + ic*n + jb*n^2 + ib*n^3 + ja*n^4 + ia*n^5
;;;
;;; of (tensor a b c) holds the product a[ia,ja] * b[ib,jb] * c[ic,jc], and
;;; nth-of-scheme-sum, which reads an entry of a scheme's denotation as the
;;; xor over the summands of the corresponding tensor entries.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Entries of bit lists are bits.  The structural version is the proof
;;; vehicle; the exported dimensioned version has the usual free-variable
;;; caveat (n occurs only in the hypotheses) and thus fires only when a
;;; bit-listnp assumption is syntactically present.

(defruled bitp-of-nth-when-bit-list-p
  (implies (and (bit-list-p x)
                (< (nfix i) (len x)))
           (bitp (nth i x)))
  :induct (cdr-dec-induct x i))

(defrule bitp-of-nth-when-bit-listnp
  (implies (and (bit-listnp x n)
                (< (nfix i) (nfix n)))
           (bitp (nth i x)))
  :use (bitp-of-nth-when-bit-list-p
        len-of-bit-listnp)
  :cases ((natp n)))

;;; nth through the pointwise operations.  bit-list-add consumes its two
;;; arguments in lockstep while the index decreases, so the induction merges
;;; cdr-dec-induct on each argument with the shared counter.

(defrule nth-of-bit-list-add
  (implies (and (< (nfix i) (len x))
                (< (nfix i) (len y)))
           (equal (nth i (bit-list-add x y))
                  (bitxor (nth i x) (nth i y))))
  :induct (list (cdr-dec-induct x i) (cdr-dec-induct y i))
  :enable bit-list-add)

(defrule nth-of-bit-list-scale
  (implies (< (nfix i) (len x))
           (equal (nth i (bit-list-scale b x))
                  (bitand b (nth i x))))
  :induct (cdr-dec-induct x i)
  :enable bit-list-scale)

(defrule nth-of-bit-listn0
  (implies (< (nfix i) (nfix k))
           (equal (nth i (bit-listn0 k))
                  0))
  :induct (dec-dec-induct i k)
  :enable (bit-listn0 repeat))

;;; Two arithmetic facts about block indices, proved once with nonlinear
;;; arithmetic and replayed linearly everywhere else: a block of size k
;;; starts no earlier than k when at least one whole block precedes it, and
;;; a row-major pair index i*n + j lies below n^2.

(local
 (defruled times-lower-bound
   (implies (and (integerp i)
                 (< 0 i)
                 (natp k))
            (<= k (* i k)))
   :rule-classes :linear
   :hints (("Goal" :nonlinearp t))))

(local
 (defruled pair-index-upper-bound
   (implies (and (natp i) (natp j) (natp n)
                 (< i n) (< j n))
            (< (+ j (* i n)) (* n n)))
   :rule-classes :linear
   :hints (("Goal" :nonlinearp t))))

;;; nth through the outer product: entry (i, j) of the outer product, at flat
;;; index j + i*|v|, is the product of the factors' entries.

(defrule nth-of-bit-list-outer
  (implies (and (natp i) (natp j)
                (< i (len u))
                (< j (len v)))
           (equal (nth (+ j (* i (len v))) (bit-list-outer u v))
                  (bitand (nth i u) (nth j v))))
  :induct (cdr-dec-induct u i)
  :enable (bit-list-outer times-lower-bound))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Matrix entry access, and nth through mat-flat: row-major flattening puts
;;; entry (i, j) at flat index j + i*n.  The core states the row count as
;;; (len a) so that its hypotheses are stable under cdr-dec induction, in
;;; the manner of mat-flat-of-bit-mat-add-core in bits.lisp.

(define mat-entry ((i natp) (j natp) (a bit-list-listp))
  :enabled t
  (nth j (nth i a)))

(local
 (defruled nth-of-mat-flat-core
   (implies (and (bit-matp a (len a) n)
                 (natp n) (natp i) (natp j)
                 (< i (len a)) (< j n))
            (equal (nth (+ j (* i n)) (mat-flat a))
                   (nth j (nth i a))))
   :induct (cdr-dec-induct a i)
   :enable (mat-flat bit-matp len-of-bit-listnp times-lower-bound)))

(defrule nth-of-mat-flat
  (implies (and (bit-matp a m n)
                (natp m) (natp n)
                (natp i) (natp j)
                (< i m) (< j n))
           (equal (nth (+ j (* i n)) (mat-flat a))
                  (mat-entry i j a)))
  :use (nth-of-mat-flat-core
        (:instance len-of-bit-matp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The main entry-semantics theorem: the flat tensor list, read at the
;;; row-major index of ((ia, ja), (ib, jb), (ic, jc)), is the product of the
;;; three matrix entries.  The proof composes nth-of-bit-list-outer twice --
;;; once to split off the a-block, once to split the b- and c-blocks --
;;; and then reads each factor through nth-of-mat-flat.

(defrule nth-of-tensor
  (implies (and (bit-matp a n n)
                (bit-matp b n n)
                (bit-matp c n n)
                (natp n)
                (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n))
           (equal (nth (+ jc (* ic n) (* jb n n) (* ib n n n)
                          (* ja n n n n) (* ia n n n n n))
                      (tensor a b c))
                  (bitand (mat-entry ia ja a)
                          (bitand (mat-entry ib jb b)
                                  (mat-entry ic jc c)))))
  :do-not-induct t
  :enable tensor
  :disable (nth-of-bit-list-outer nth-of-mat-flat)
  :use ((:instance nth-of-bit-list-outer
                   (u (mat-flat a))
                   (v (bit-list-outer (mat-flat b) (mat-flat c)))
                   (i (+ ja (* ia n)))
                   (j (+ jc (* ic n) (* jb n n) (* ib n n n))))
        (:instance nth-of-bit-list-outer
                   (u (mat-flat b))
                   (v (mat-flat c))
                   (i (+ jb (* ib n)))
                   (j (+ jc (* ic n))))
        (:instance nth-of-mat-flat (a a) (m n) (i ia) (j ja))
        (:instance nth-of-mat-flat (a b) (m n) (i ib) (j jb))
        (:instance nth-of-mat-flat (a c) (m n) (i ic) (j jc))
        (:instance pair-index-upper-bound (i ia) (j ja) (n n))
        (:instance pair-index-upper-bound (i ib) (j jb) (n n))
        (:instance pair-index-upper-bound (i ic) (j jc) (n n))
        (:instance pair-index-upper-bound
                   (i (+ jb (* ib n))) (j (+ jc (* ic n))) (n (* n n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Entry semantics of a whole scheme: entry idx of the denotation is the
;;; xor over the summands of entry idx of each summand's tensor.

;;; The ifix is a no-op on the value -- bitxor ifixes its arguments anyway
;;; (bitxor-of-ifix-arg1 in bits.lisp) -- and is what makes the guard
;;; provable: idx is not bounded by anything in scope, so nth can run off the
;;; end and return nil, which is not an integer.  Unlike a-witness-sum, this
;;; function has no dimension formal, so the bound cannot be stated.

(define scheme-sum-entry ((idx natp) (l mat-triple-listp))
  :returns (b bitp)
  (if (atom l)
      0
    (bitxor (ifix (nth idx (summand-tensor (car l))))
            (scheme-sum-entry idx (cdr l)))))

(defrule nth-of-scheme-sum
  (implies (and (summand-dim-listp l n)
                (natp n)
                (< (nfix idx) (* n n n n n n)))
           (equal (nth idx (scheme-sum l n))
                  (scheme-sum-entry idx l)))
  :induct (scheme-sum l n)
  :enable (scheme-sum scheme-sum-entry)
  :disable (tensor))
