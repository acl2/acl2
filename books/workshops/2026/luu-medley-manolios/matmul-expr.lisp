; An expression language for bilinear matrix multiplication algorithms over
; F2, its evaluator, and the translation of an algorithm into the list of
; matrix triples (summands) whose eval-scheme (adequacy.lisp) computes the
; same function.
;
; Bilinear algorithms.  The flip graph literature's notion of a matrix
; multiplication algorithm is the bilinear one: each of the R
; multiplications multiplies a linear form in the entries of the first
; matrix by a linear form in the entries of the second, and each output
; entry is a sum of some of the R products.  This is exactly what a rank-R
; decomposition of the matrix multiplication tensor expresses, so it is the
; class of algorithms for which "scheme" and "algorithm" are two views of
; one object.  Quadratic algorithms, whose multiplications may combine
; entries of both matrices in one factor, are excluded: they do not
; correspond to tensor rank, and the usual reduction of a quadratic
; algorithm to a bilinear one of at most twice the rank divides by 2, which
; is unavailable over F2.
;
; The language.  A linear form over one n x n matrix is (:var i j) with
; i, j < n, (:add e1 e2), or (:scale b e) with b a bit; lformp is the
; recognizer, eval-lform the evaluator (var reads the entry, add is xor,
; scale is and), and lform-mat the coefficient matrix (var is the unit
; matrix e_ij, add is bit-mat-add, scale is bit-mat-scale).  A product is
; (:mul d-form f-form).  An algorithm is a pair (prods . outs): prods is a
; list of R products and outs an n x n table (a list of n rows of n lists)
; whose entry (k, l) lists the indices of the products whose sum is output
; entry (k, l); repeats are allowed and cancel in pairs.  eval-algo builds
; the output matrix entry by entry.
;
; The translation.  Product r with forms (a, b) and output table outs becomes
; the triple (lform-mat a, lform-mat b, c-mat r outs), where c-mat has a 1 at
; (k, l) exactly when r occurs an odd number of times in outs[k][l]; algo-
; triples is the list of these and algo-scheme the bag of the nonzero ones.
;
; The theorems.  eval-lform-is-mat-dot: evaluating a form is the inner
; product of its coefficient matrix with the input.  eval-algo-is-eval-
; scheme: evaluating an algorithm is eval-scheme of its triples.  The proof
; is entrywise: entry (k, l) of eval-scheme of the triples is the xor over
; the products r of value_r * parity(r in outs[k][l]), which the parity
; lemma prods-xor-is-prods-parity-xor identifies with the xor of value_r
; over the index list outs[k][l]; mat-diff-pos (span.lisp) lifts the
; entrywise identity to the matrices.
;
; Validated by execution at n = 2 before proving: Strassen's seven-product
; algorithm (all signs vanish over F2) computes bit-mat-mul and agrees with
; eval-scheme of its triples on all 256 pairs of inputs, and its scheme is a
; correct scheme of rank 7; see the assert-event forms at the end.
;
; Composition with completeness.lisp (the theorem that a list of triples
; computing the product yields a correct scheme) gives algo-to-correct-scheme,
; proved in algo-completeness.lisp.

(in-package "ACL2")

(include-book "adequacy")

(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; bitxor-of-0-arg1 rewrites (bitxor 0 x) to (getbit 0 x); this puts it back
;; when x is known to be a bit (as in adequacy.lisp).
(local
 (defrule getbit-0-of-bit
   (implies (bitp x)
            (equal (getbit 0 x) x))))

;;; Linear forms

(define lformp (e (n natp))
  :returns (yes/no booleanp)
  (and (consp e)
       (true-listp e)
       (equal (len e) 3)
       (case (car e)
         (:var (and (natp (cadr e)) (natp (caddr e))
                    (< (cadr e) n) (< (caddr e) n)))
         (:add (and (lformp (cadr e) n) (lformp (caddr e) n)))
         (:scale (and (bitp (cadr e)) (lformp (caddr e) n)))
         (t nil))))

(define eval-lform (e (m bit-list-listp) (n natp))
  :guard (and (lformp e n) (bit-matp m n n))
  :guard-hints (("Goal" :in-theory (e/d (lformp integerp-of-mat-entry) (mat-entry))))
  :returns (b bitp :hyp :guard
              :hints (("Goal" :in-theory (e/d (lformp) (mat-entry bitp)))))
  :verify-guards :after-returns
  (case (car e)
    (:var (mat-entry (cadr e) (caddr e) m))
    (:add (bitxor (eval-lform (cadr e) m n) (eval-lform (caddr e) m n)))
    (:scale (bitand (cadr e) (eval-lform (caddr e) m n)))
    (t 0))
  ///
  ;; The guard prover states its obligations with integerp, on which the
  ;; bitp return theorem does not fire (cf. integerp-of-mat-entry).
  (defruled integerp-of-eval-lform
    (implies (and (lformp e n) (bit-matp m n n) (natp n))
             (integerp (eval-lform e m n)))
    :use bitp-of-eval-lform
    :disable bitp-of-eval-lform))

(define lform-mat (e (n natp))
  :guard (lformp e n)
  :guard-hints (("Goal" :in-theory (enable lformp)))
  :returns (a bit-list-listp)
  :verify-guards :after-returns
  (case (car e)
    (:var (bit-mat-unit (cadr e) (caddr e) n n))
    (:add (bit-mat-add (lform-mat (cadr e) n) (lform-mat (caddr e) n)))
    (:scale (bit-mat-scale (cadr e) (lform-mat (caddr e) n)))
    (t (bit-mat0 n n)))
  ///
  (defrule bit-matp-of-lform-mat
    (implies (lformp e n)
             (bit-matp (lform-mat e n) n n))
    :enable lformp))

;;; Products and algorithms

(define prodp (p (n natp))
  :returns (yes/no booleanp)
  (and (true-listp p)
       (equal (len p) 3)
       (eq (car p) :mul)
       (lformp (cadr p) n)
       (lformp (caddr p) n)))

(define prod-listp (l (n natp))
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (prodp (car l) n)
         (prod-listp (cdr l) n)))
  ///
  (defrule true-listp-when-prod-listp
    (implies (prod-listp l n)
             (true-listp l))
    :rule-classes (:rewrite :forward-chaining))
  (defrule prodp-of-nth-when-prod-listp
    (implies (and (prod-listp l n)
                  (< (nfix i) (len l)))
             (prodp (nth i l) n))
    :induct (cdr-dec-induct l i)))

(define index-listp (l (r natp))
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (natp (car l))
         (< (car l) r)
         (index-listp (cdr l) r)))
  ///
  (defrule nat-listp-when-index-listp
    (implies (index-listp l r)
             (nat-listp l))
    :rule-classes (:rewrite :forward-chaining)))

(define idx-rowp (x)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (nat-listp (car x))
         (idx-rowp (cdr x)))))

(define idx-tablep (x)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (idx-rowp (car x))
         (idx-tablep (cdr x)))))

(define outs-rowp (row (r natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp n)
      (null row)
    (and (consp row)
         (index-listp (car row) r)
         (outs-rowp (cdr row) r (1- n))))
  ///
  (defrule idx-rowp-when-outs-rowp
    (implies (outs-rowp row r n)
             (idx-rowp row))
    :rule-classes (:rewrite :forward-chaining))
  (defrule true-listp-when-outs-rowp
    (implies (outs-rowp row r n)
             (true-listp row))
    :rule-classes (:rewrite :forward-chaining))
  (defruled len-of-outs-rowp
    (implies (and (outs-rowp row r n)
                  (natp n))
             (equal (len row) n))))

(define outs-rowsp (outs (r natp) (m natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp m)
      (null outs)
    (and (consp outs)
         (outs-rowp (car outs) r n)
         (outs-rowsp (cdr outs) r (1- m) n)))
  ///
  (defrule idx-tablep-when-outs-rowsp
    (implies (outs-rowsp outs r m n)
             (idx-tablep outs))
    :rule-classes (:rewrite :forward-chaining))
  (defrule true-listp-when-outs-rowsp
    (implies (outs-rowsp outs r m n)
             (true-listp outs))
    :rule-classes (:rewrite :forward-chaining))
  (defruled len-of-outs-rowsp
    (implies (and (outs-rowsp outs r m n)
                  (natp m))
             (equal (len outs) m))))

(define algop (alg (n natp))
  :returns (yes/no booleanp)
  (and (consp alg)
       (prod-listp (car alg) n)
       (outs-rowsp (cdr alg) (len (car alg)) n n)))

;;; Rows of the table

(local
 (defruled outs-rowp-of-nth-when-outs-rowsp-core
   (implies (and (outs-rowsp outs r (len outs) n)
                 (< (nfix k) (len outs)))
            (outs-rowp (nth k outs) r n))
   :induct (cdr-dec-induct outs k)
   :enable outs-rowsp))

(defrule outs-rowp-of-nth-when-outs-rowsp
  (implies (and (outs-rowsp outs r m n)
                (natp m)
                (< (nfix k) m))
           (outs-rowp (nth k outs) r n))
  :do-not-induct t
  :use (outs-rowp-of-nth-when-outs-rowsp-core
        len-of-outs-rowsp))

(local
 (defruled index-listp-of-nth-when-outs-rowp-core
   (implies (and (outs-rowp row r (len row))
                 (< (nfix l) (len row)))
            (index-listp (nth l row) r))
   :induct (cdr-dec-induct row l)
   :enable outs-rowp))

(defrule index-listp-of-nth-when-outs-rowp
  (implies (and (outs-rowp row r n)
                (natp n)
                (< (nfix l) n))
           (index-listp (nth l row) r))
  :do-not-induct t
  :use (index-listp-of-nth-when-outs-rowp-core
        len-of-outs-rowp))

;;; The two rules above do not chain (n is free in the second), so the entry
;;; of the table is read in one step; the free m and n are the ones the
;;; algop hypothesis supplies.
(defrule index-listp-of-nth-nth-when-outs-rowsp
  (implies (and (outs-rowsp outs r m n)
                (natp m) (natp n)
                (< (nfix k) m)
                (< (nfix l) n))
           (index-listp (nth l (nth k outs)) r))
  :do-not-induct t
  :use (outs-rowp-of-nth-when-outs-rowsp
        (:instance index-listp-of-nth-when-outs-rowp (row (nth k outs)))))

;;; The guard obligations of nth and of prods-xor, in the shapes the guard
;;; prover leaves them.
(defrule true-listp-of-nth-when-outs-rowsp
  (implies (and (outs-rowsp outs r m n)
                (natp m)
                (< (nfix k) m))
           (true-listp (nth k outs)))
  :do-not-induct t
  :use (outs-rowp-of-nth-when-outs-rowsp)
  :disable (outs-rowp-of-nth-when-outs-rowsp))

(defrule nat-listp-of-nth-nth-when-outs-rowsp
  (implies (and (outs-rowsp outs r m n)
                (natp m) (natp n)
                (< (nfix k) m)
                (< (nfix l) n))
           (nat-listp (nth l (nth k outs))))
  :do-not-induct t
  :use (index-listp-of-nth-nth-when-outs-rowsp)
  :disable (index-listp-of-nth-nth-when-outs-rowsp))

;;; Evaluating an algorithm

(define prod-value (p (d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (prodp p n) (bit-matp d n n) (bit-matp f n n))
  :guard-hints (("Goal" :in-theory (enable prodp integerp-of-eval-lform)))
  :returns (b bitp)
  (bitand (eval-lform (cadr p) d n)
          (eval-lform (caddr p) f n)))

(define prods-xor ((idxs nat-listp) (prods true-listp)
                   (d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (index-listp idxs (len prods))
              (prod-listp prods n)
              (bit-matp d n n)
              (bit-matp f n n))
  :guard-hints (("Goal" :in-theory (enable index-listp)))
  :returns (b bitp)
  :verify-guards :after-returns
  (if (atom idxs)
      0
    (bitxor (prod-value (nth (car idxs) prods) d f n)
            (prods-xor (cdr idxs) prods d f n))))

(define algo-entry (alg (d bit-list-listp) (f bit-list-listp)
                    (k natp) (l natp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n)
              (< k n) (< l n))
  :guard-hints (("Goal" :in-theory (enable algop) :do-not-induct t))
  :returns (b bitp)
  (prods-xor (nth l (nth k (cdr alg))) (car alg) d f n))

(define eval-algo-row (alg (d bit-list-listp) (f bit-list-listp)
                       (k natp) (c natp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n)
              (< k n) (<= c n))
  :returns (row bit-list-p)
  (if (zp c)
      nil
    (cons (algo-entry alg d f k (- n c) n)
          (eval-algo-row alg d f k (1- c) n)))
  ///
  (defrule bit-listnp-of-eval-algo-row
    (bit-listnp (eval-algo-row alg d f k c n) c)
    :enable bit-listnp))

(define eval-algo-rows (alg (d bit-list-listp) (f bit-list-listp)
                        (c natp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n)
              (<= c n))
  :returns (a bit-list-listp)
  (if (zp c)
      nil
    (cons (eval-algo-row alg d f (- n c) n n)
          (eval-algo-rows alg d f (1- c) n)))
  ///
  (defrule bit-matp-of-eval-algo-rows
    (bit-matp (eval-algo-rows alg d f c n) c n)
    :enable bit-matp))

(define eval-algo (alg (d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n))
  :returns (a bit-list-listp)
  (eval-algo-rows alg d f n n)
  ///
  (defrule bit-matp-of-eval-algo
    (bit-matp (eval-algo alg d f n) n n)))

;;; Translation

(define occ-parity ((r natp) (idxs nat-listp))
  :returns (b bitp)
  (if (atom idxs)
      0
    (bitxor (if (equal (car idxs) r) 1 0)
            (occ-parity r (cdr idxs)))))

(define c-mat-row ((r natp) (row idx-rowp))
  :returns (x bit-list-p)
  (if (atom row)
      nil
    (cons (occ-parity r (car row))
          (c-mat-row r (cdr row))))
  ///
  (defrule bit-listnp-of-c-mat-row
    (implies (outs-rowp row rr n)
             (bit-listnp (c-mat-row r row) n))
    :induct (outs-rowp row rr n)
    :enable (outs-rowp bit-listnp)))

(define c-mat ((r natp) (outs idx-tablep))
  :returns (a bit-list-listp)
  (if (atom outs)
      nil
    (cons (c-mat-row r (car outs))
          (c-mat r (cdr outs))))
  ///
  (defrule bit-matp-of-c-mat
    (implies (outs-rowsp outs rr m n)
             (bit-matp (c-mat r outs) m n))
    :induct (outs-rowsp outs rr m n)
    :enable (outs-rowsp bit-matp)))

(define triples-from ((prods true-listp) (outs idx-tablep) (r natp) (n natp))
  :guard (prod-listp prods n)
  :guard-hints (("Goal" :in-theory (enable prod-listp prodp)))
  :returns (l mat-triple-listp)
  (if (atom prods)
      nil
    (cons (list (lform-mat (cadr (car prods)) n)
                (lform-mat (caddr (car prods)) n)
                (c-mat r outs))
          (triples-from (cdr prods) outs (1+ r) n)))
  ///
  (defrule len-of-triples-from
    (equal (len (triples-from prods outs r n))
           (len prods)))
  (defrule summand-dim-listp-of-triples-from
    (implies (and (prod-listp prods n)
                  (outs-rowsp outs rr n n))
             (summand-dim-listp (triples-from prods outs r n) n))
    :induct (triples-from prods outs r n)
    :enable (prod-listp prodp)))

(define algo-triples (alg (n natp))
  :guard (algop alg n)
  :guard-hints (("Goal" :in-theory (enable algop)))
  :returns (l mat-triple-listp)
  (triples-from (car alg) (cdr alg) 0 n)
  ///
  (defrule summand-dim-listp-of-algo-triples
    (implies (algop alg n)
             (summand-dim-listp (algo-triples alg n) n))
    :enable algop))

(define algo-scheme (alg (n natp))
  :guard (algop alg n)
  :returns (sch obag::bagp)
  (insert-all-nonzero (algo-triples alg n) nil n)
  ///
  (defrule schemep-of-algo-scheme
    (implies (algop alg n)
             (schemep (algo-scheme alg n) n))
    :disable (insert-all-nonzero)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 2: the coefficient-matrix lemma
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Evaluating a linear form is the inner product of its coefficient matrix
;;; with the input: mat-dot of a unit matrix is the entry (adequacy.lisp),
;;; and mat-dot is additive and homogeneous in its first argument, which
;;; comes down to bitand distributing over bitxor.

;; On bits; the general statement is also true (bitand and bitxor read
;; their arguments through bvchop) but the bit form is what the inductions
;; below need.  bitp is disabled in the proofs that use these so that the
;; hypotheses are not split into the four constant cases.
(defruled bitand-of-bitxor-arg1
  (implies (and (bitp a) (bitp b) (bitp c))
           (equal (bitand (bitxor a b) c)
                  (bitxor (bitand a c) (bitand b c)))))

(defruled bitand-of-bitxor-arg2
  (implies (and (bitp a) (bitp b) (bitp c))
           (equal (bitand c (bitxor a b))
                  (bitxor (bitand c a) (bitand c b)))))

;; The inner product is additive and homogeneous in its first argument.  The
;; merged induction cdrs x, y and z together (as in entry.lisp).
(defruled bit-list-dot-of-bit-list-add-arg1
  (implies (and (bit-list-p x) (bit-list-p y) (bit-list-p z)
                (equal (len x) (len y)))
           (equal (bit-list-dot (bit-list-add x y) z)
                  (bitxor (bit-list-dot x z) (bit-list-dot y z))))
  :induct (list (cdr-cdr-induct x y) (cdr-cdr-induct x z))
  :enable (bit-list-dot bit-list-add bitand-of-bitxor-arg1)
  :disable (bitp))

(defruled bit-list-dot-of-bit-list-scale-arg1
  (implies (and (bitp b) (bit-list-p x) (bit-list-p y))
           (equal (bit-list-dot (bit-list-scale b x) y)
                  (bitand b (bit-list-dot x y))))
  :induct (bit-list-dot x y)
  :enable (bit-list-dot bit-list-scale bitand-of-bitxor-arg2
           bitand-commutative-2)
  :disable (bitp bit-list-scale-of-0))

(defruled mat-dot-of-bit-mat-add-arg1
  (implies (and (bit-matp a m n) (bit-matp b m n) (bit-list-listp d)
                (natp m) (natp n))
           (equal (mat-dot (bit-mat-add a b) d)
                  (bitxor (mat-dot a d) (mat-dot b d))))
  :enable (mat-dot mat-flat-of-bit-mat-add bit-list-dot-of-bit-list-add-arg1))

(defruled mat-dot-of-bit-mat-scale-arg1
  (implies (and (bitp b) (bit-list-listp a) (bit-list-listp d))
           (equal (mat-dot (bit-mat-scale b a) d)
                  (bitand b (mat-dot a d))))
  :enable (mat-dot mat-flat-of-bit-mat-scale bit-list-dot-of-bit-list-scale-arg1)
  :disable (bitp bit-list-scale-of-0))

;; mat-dot-of-bit-mat-add-arg1 has its dimensions m, n free, so it cannot
;; fire inside the induction; this form binds n through lform-mat.
(defruled mat-dot-of-bit-mat-add-lform-mat
  (implies (and (lformp e1 n) (lformp e2 n) (bit-list-listp d) (natp n))
           (equal (mat-dot (bit-mat-add (lform-mat e1 n) (lform-mat e2 n)) d)
                  (bitxor (mat-dot (lform-mat e1 n) d)
                          (mat-dot (lform-mat e2 n) d))))
  :use ((:instance mat-dot-of-bit-mat-add-arg1
                   (a (lform-mat e1 n)) (b (lform-mat e2 n)) (m n))))

(defruled eval-lform-is-mat-dot
  (implies (and (lformp e n) (bit-matp m n n) (natp n))
           (equal (eval-lform e m n)
                  (mat-dot (lform-mat e n) m)))
  :induct (lform-mat e n)
  :enable (lformp eval-lform lform-mat mat-dot-of-bit-mat-unit
           mat-dot-of-bit-mat-add-lform-mat mat-dot-of-bit-mat-scale-arg1)
  :disable (mat-entry))

(defrule mat-dot-of-lform-mat
  (implies (and (lformp e n) (bit-matp m n n) (natp n))
           (equal (mat-dot (lform-mat e n) m)
                  (eval-lform e m n)))
  :enable eval-lform-is-mat-dot)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 3: entries of eval-algo, of c-mat, and of eval-scheme of the triples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The entry characterization of eval-algo: position j of the row for
;;; columns n-c .. n-1 is column n-c+j, likewise for rows (as for
;;; bit-mat-mul in adequacy.lisp).

(defruled nth-of-eval-algo-row
  (implies (and (natp j) (natp c) (< j c))
           (equal (nth j (eval-algo-row alg d f k c n))
                  (algo-entry alg d f k (+ j (- n c)) n)))
  :induct (dec-dec-induct j c)
  :enable eval-algo-row
  :expand ((eval-algo-row alg d f k c n)))

(defruled nth-of-eval-algo-rows
  (implies (and (natp i) (natp c) (< i c))
           (equal (nth i (eval-algo-rows alg d f c n))
                  (eval-algo-row alg d f (+ i (- n c)) n n)))
  :induct (dec-dec-induct i c)
  :enable eval-algo-rows
  :expand ((eval-algo-rows alg d f c n)))

(defruled mat-entry-of-eval-algo
  (implies (and (natp k) (natp l) (natp n)
                (< k n) (< l n))
           (equal (mat-entry k l (eval-algo alg d f n))
                  (algo-entry alg d f k l n)))
  :enable (eval-algo nth-of-eval-algo-rows nth-of-eval-algo-row))

;;; Entries of a scaled c-mat: the parity of r in the table entry, scaled.
;;; No dimension is needed here, only that the indices are in range.

(defruled len-of-c-mat-row
  (equal (len (c-mat-row r row)) (len row))
  :enable c-mat-row)

(defruled len-of-c-mat
  (equal (len (c-mat r outs)) (len outs))
  :enable c-mat)

(defruled nth-of-c-mat
  (equal (nth k (c-mat r outs))
         (c-mat-row r (nth k outs)))
  :induct (cdr-dec-induct outs k)
  :enable (c-mat c-mat-row))

(defruled nth-of-c-mat-row
  (implies (< (nfix l) (len row))
           (equal (nth l (c-mat-row r row))
                  (occ-parity r (nth l row))))
  :induct (cdr-dec-induct row l)
  :enable c-mat-row)

(defruled mat-entry-of-bit-mat-scale-c-mat
  (implies (and (natp k) (natp l)
                (< k (len outs))
                (< l (len (nth k outs))))
           (equal (mat-entry k l (bit-mat-scale s (c-mat r outs)))
                  (bitand s (occ-parity r (nth l (nth k outs))))))
  :enable (nth-row-of-bit-mat-scale nth-of-c-mat nth-of-c-mat-row
           len-of-c-mat len-of-c-mat-row))

;;; The in-range conditions above, from the table's shape (free r, m, n are
;;; supplied by the outs-rowsp hypothesis in scope).

(defruled len-of-nth-when-outs-rowsp
  (implies (and (outs-rowsp outs r m n)
                (natp m) (natp n)
                (< (nfix k) m))
           (equal (len (nth k outs)) n))
  :use (outs-rowp-of-nth-when-outs-rowsp
        (:instance len-of-outs-rowp (row (nth k outs)))))

;;; mat-entry-of-bit-mat-add (mmt.lisp) has m free; this form binds n
;;; through eval-scheme.

(defruled mat-entry-of-bit-mat-add-eval-scheme
  (implies (and (bit-matp x n n)
                (summand-dim-listp sch n)
                (natp n) (natp k) (natp l) (< k n) (< l n))
           (equal (mat-entry k l (bit-mat-add x (eval-scheme sch d f n)))
                  (bitxor (mat-entry k l x)
                          (mat-entry k l (eval-scheme sch d f n)))))
  :use ((:instance mat-entry-of-bit-mat-add
                   (x x) (y (eval-scheme sch d f n)) (m n) (i k) (j l))))

;;; The xor over the products, numbered from r on, of the product's value
;;; scaled by the parity of the product's index in idxs.  This is what entry
;;; (k, l) of eval-scheme of the triples computes, with idxs = outs[k][l].
(define prods-parity-xor ((prods true-listp) (idxs nat-listp) (r natp)
                          (d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (prod-listp prods n) (bit-matp d n n) (bit-matp f n n))
  :guard-hints (("Goal" :in-theory (enable prod-listp)))
  :returns (b bitp)
  :verify-guards :after-returns
  (if (atom prods)
      0
    (bitxor (bitand (prod-value (car prods) d f n)
                    (occ-parity r idxs))
            (prods-parity-xor (cdr prods) idxs (1+ r) d f n))))

;;; Entry (k, l) of eval-scheme of the triples from index r on.

(defruled mat-entry-of-eval-scheme-of-triples-from
  (implies (and (prod-listp prods n)
                (outs-rowsp outs rr n n)
                (bit-matp d n n) (bit-matp f n n)
                (natp n) (natp k) (natp l) (< k n) (< l n))
           (equal (mat-entry k l (eval-scheme (triples-from prods outs r n) d f n))
                  (prods-parity-xor prods (nth l (nth k outs)) r d f n)))
  :induct (triples-from prods outs r n)
  :enable (triples-from eval-scheme prods-parity-xor prod-value prod-listp prodp
           mat-entry-of-bit-mat-add-eval-scheme mat-entry-of-bit-mat-scale-c-mat
           len-of-outs-rowsp len-of-nth-when-outs-rowsp)
  :disable (mat-entry))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 4: the parity lemma and the main theorem
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The parity lemma: the xor of value_r over an index list equals the xor
;;; over all products r of value_r times the parity of r's occurrences in
;;; the list, because repeated indices cancel in pairs.  Proved by peeling
;;; one index off the list: the parity sum over (cons i idxs) is the parity
;;; sum over (list i), which is value_i alone, xor the parity sum over idxs.

(defruled prods-parity-xor-of-nil
  (equal (prods-parity-xor prods nil r d f n) 0)
  :induct (prods-parity-xor prods nil r d f n)
  :enable (prods-parity-xor occ-parity))

(defruled occ-parity-of-cons
  (equal (occ-parity r (cons i idxs))
         (bitxor (if (equal i r) 1 0) (occ-parity r idxs)))
  :enable occ-parity)

(defruled occ-parity-of-single
  (equal (occ-parity r (list i))
         (if (equal i r) 1 0))
  :enable occ-parity)

(defruled prods-parity-xor-of-cons
  (equal (prods-parity-xor prods (cons i idxs) r d f n)
         (bitxor (prods-parity-xor prods (list i) r d f n)
                 (prods-parity-xor prods idxs r d f n)))
  :induct (prods-parity-xor prods idxs r d f n)
  :enable (prods-parity-xor occ-parity-of-cons occ-parity-of-single
           bitand-of-bitxor-arg2))

(defruled prods-parity-xor-of-single
  (implies (and (natp r) (natp i))
           (equal (prods-parity-xor prods (list i) r d f n)
                  (if (and (<= r i) (< i (+ r (len prods))))
                      (prod-value (nth (- i r) prods) d f n)
                    0)))
  :induct (prods-parity-xor prods (list i) r d f n)
  :enable (prods-parity-xor occ-parity-of-single))

(defruled prods-xor-is-prods-parity-xor
  (implies (index-listp idxs (len prods))
           (equal (prods-xor idxs prods d f n)
                  (prods-parity-xor prods idxs 0 d f n)))
  :induct (prods-xor idxs prods d f n)
  :enable (prods-xor index-listp prods-parity-xor-of-nil
           prods-parity-xor-of-cons prods-parity-xor-of-single))

;;; The entrywise identity, and its lift to matrices by mat-diff-pos.

(defruled mat-entry-of-eval-algo-is-mat-entry-of-eval-scheme
  (implies (and (algop alg n) (natp n)
                (bit-matp d n n) (bit-matp f n n)
                (natp k) (natp l) (< k n) (< l n))
           (equal (mat-entry k l (eval-algo alg d f n))
                  (mat-entry k l (eval-scheme (algo-triples alg n) d f n))))
  :enable (algop algo-triples algo-entry mat-entry-of-eval-algo
           prods-xor-is-prods-parity-xor
           mat-entry-of-eval-scheme-of-triples-from)
  :disable (mat-entry))

(defrule eval-algo-is-eval-scheme
  (implies (and (algop alg n) (natp n)
                (bit-matp d n n) (bit-matp f n n))
           (equal (eval-algo alg d f n)
                  (eval-scheme (algo-triples alg n) d f n)))
  :do-not-induct t
  :disable (mat-entry eval-algo eval-scheme algo-triples)
  :use ((:instance mat-diff-pos-correct
                   (x (eval-algo alg d f n))
                   (y (eval-scheme (algo-triples alg n) d f n))
                   (m n))
        (:instance mat-entry-of-eval-algo-is-mat-entry-of-eval-scheme
                   (k (car (mat-diff-pos (eval-algo alg d f n)
                                         (eval-scheme (algo-triples alg n) d f n))))
                   (l (cdr (mat-diff-pos (eval-algo alg d f n)
                                         (eval-scheme (algo-triples alg n) d f n)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Example algorithms at n = 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Strassen's algorithm over F2 (all signs vanish).  The products, in
;;; order:
;;;   M1 = (a11 + a22)(b11 + b22)   M2 = (a21 + a22) b11
;;;   M3 = a11 (b12 + b22)          M4 = a22 (b21 + b11)
;;;   M5 = (a11 + a12) b22          M6 = (a21 + a11)(b11 + b12)
;;;   M7 = (a12 + a22)(b21 + b22)
;;; and the outputs C11 = M1 + M4 + M5 + M7, C12 = M3 + M5, C21 = M2 + M4,
;;; C22 = M1 + M2 + M3 + M6, as 0-based product indices.

(defconst *strassen2*
  (cons (list (list :mul '(:add (:var 0 0) (:var 1 1)) '(:add (:var 0 0) (:var 1 1)))
              (list :mul '(:add (:var 1 0) (:var 1 1)) '(:var 0 0))
              (list :mul '(:var 0 0) '(:add (:var 0 1) (:var 1 1)))
              (list :mul '(:var 1 1) '(:add (:var 1 0) (:var 0 0)))
              (list :mul '(:add (:var 0 0) (:var 0 1)) '(:var 1 1))
              (list :mul '(:add (:var 1 0) (:var 0 0)) '(:add (:var 0 0) (:var 0 1)))
              (list :mul '(:add (:var 0 1) (:var 1 1)) '(:add (:var 1 0) (:var 1 1))))
        '(((0 3 4 6) (2 4))
          ((1 3) (0 1 2 5)))))

(assert-event (algop *strassen2* 2))

;; Its scheme is a correct scheme of rank 7.
(assert-event (and (correct-schemep (algo-scheme *strassen2* 2) 2)
                   (equal (scheme-rank (algo-scheme *strassen2* 2)) 7)))

;;; All 256 pairs of 2 x 2 inputs: Strassen computes the product, and
;;; eval-algo agrees with eval-scheme of the triples.  mat2 decodes the 16
;;; matrices from 0..15; the decoders and loops are local, and so are the
;;; checks that mention them.

;;; Repeated indices cancel in pairs: C11 written with M3 twice more gives
;;; the same triples and the same outputs.

(defconst *strassen2-rep*
  (cons (car *strassen2*)
        '(((0 3 4 6 2 2) (2 4))
          ((1 3) (0 1 2 5)))))

(assert-event (and (algop *strassen2-rep* 2)
                   (equal (algo-triples *strassen2-rep* 2)
                          (algo-triples *strassen2* 2))))

;;; The naive eight-product algorithm translates to a correct scheme of
;;; rank 8.

(defconst *naive2*
  (cons (list (list :mul '(:var 0 0) '(:var 0 0))
              (list :mul '(:var 0 1) '(:var 1 0))
              (list :mul '(:var 0 0) '(:var 0 1))
              (list :mul '(:var 0 1) '(:var 1 1))
              (list :mul '(:var 1 0) '(:var 0 0))
              (list :mul '(:var 1 1) '(:var 1 0))
              (list :mul '(:var 1 0) '(:var 0 1))
              (list :mul '(:var 1 1) '(:var 1 1)))
        '(((0 1) (2 3))
          ((4 5) (6 7)))))

(assert-event (and (algop *naive2* 2)
                   (correct-schemep (algo-scheme *naive2* 2) 2)
                   (equal (scheme-rank (algo-scheme *naive2* 2)) 8)))

