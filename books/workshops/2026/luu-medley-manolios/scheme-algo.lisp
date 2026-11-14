; scheme-algo.lisp -- from schemes back to algorithms: schemes are canonical
; representatives of bilinear matrix multiplication algorithms over F2.
;
; matmul-expr.lisp translates an algorithm of the expression language to a
; list of matrix triples (algo-triples) and to a scheme (algo-scheme, the bag
; of the nonzero triples).  This book gives the other direction.  A matrix a
; becomes the linear form (mat-lform a n), the sum of the variables (:var i j)
; at the positions where a has a 1, row by row; its coefficient matrix is a
; (lform-mat-of-mat-lform).  A list l of triples (A_r, B_r, C_r) becomes the
; algorithm (scheme-algo l n) with one product (:mul (mat-lform A_r) (mat-lform
; B_r)) per triple and the output table (triples-outs l n) whose entry (k, l)
; lists, once each and in increasing order, the indices r with C_r[k,l] = 1;
; c-mat reads the C factors back off this table (c-mat-of-triples-outs).
;
; Theorems.  algo-triples-of-scheme-algo: translating the algorithm of a list
; of triples gives the list back, so the translation is onto and scheme-algo
; is its section.  algo-scheme-of-scheme-algo: a scheme converted to an
; algorithm and translated back is itself.  eval-scheme-algo: the algorithm
; of a list computes eval-scheme of the list.  scheme-algo-correct: the
; algorithm of a correct scheme is a correct algorithm (algo-correctp), the
; converse of algo-to-correct-scheme in algo-completeness.lisp.  Finally,
; eval-scheme is determined by scheme-sum (eval-scheme-when-scheme-sum-equal)
; and dropping zero summands does not change the sum (scheme-sum-of-algo-
; scheme); algo-class.lisp builds the equivalence of algorithms on these.
;
; The matrix identities are proved entrywise (mat-entry-of-bit-mat-add/unit/
; scale) and lifted by mat-diff-pos (span.lisp); the list identity of the
; round trip is proved elementwise (nth of both sides) and lifted by
; first-diff-index.

(in-package "ACL2")

(include-book "algo-completeness")

(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; bitxor-of-0-arg1 rewrites (bitxor 0 x) to (getbit 0 x); this puts it back
;; when x is known to be a bit (as in adequacy.lisp).
(local
 (defrule getbit-0-of-bit
   (implies (bitp x)
            (equal (getbit 0 x) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 1: the algorithm of a list of triples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Structural guard support: a row read off a bit-list-list is a true list
;;; (nil when out of range), so mat-entry's nth calls are guard-safe without
;;; dimensions.

(defrule true-listp-of-nth-when-bit-list-listp
  (implies (bit-list-listp x)
           (true-listp (nth i x)))
  :induct (cdr-dec-induct x i))

;;; The linear form of a matrix: for row i, the sum of (:var i j) over the
;;; columns j = n-c .. n-1 where a[i,j] = 1, ending in the empty sum
;;; (:scale 0 (:var 0 0)); then the sum of the rows n-c .. n-1.  Built by
;;; downward recursions like eval-algo-row, so the positions come out in
;;; row-major order.

(define mat-lform-row ((a bit-list-listp) (i natp) (c natp) (n natp))
  :guard (and (bit-matp a n n) (< i n) (<= c n))
  :returns (e (lformp e n) :hyp :guard
              :hints (("Goal" :in-theory (enable lformp))))
  (if (zp c)
      '(:scale 0 (:var 0 0))
    (if (equal (mat-entry i (- n c) a) 1)
        (list :add (list :var i (- n c)) (mat-lform-row a i (1- c) n))
      (mat-lform-row a i (1- c) n))))

(define mat-lform-rows ((a bit-list-listp) (c natp) (n natp))
  :guard (and (bit-matp a n n) (<= c n) (< 0 n))
  :returns (e (lformp e n) :hyp :guard
              :hints (("Goal" :in-theory (enable lformp))))
  (if (zp c)
      '(:scale 0 (:var 0 0))
    (list :add (mat-lform-row a (- n c) n n) (mat-lform-rows a (1- c) n))))

(define mat-lform ((a bit-list-listp) (n natp))
  :guard (and (bit-matp a n n) (< 0 n))
  :returns (e (lformp e n) :hyp :guard)
  (mat-lform-rows a n n))

;;; The output table.  (c-indices l k j r) lists, in increasing order, the
;;; indices r, r+1, ... of the triples of l whose C factor has a 1 at (k, j);
;;; the table has row k, column j equal to (c-indices l k j 0).

(define c-indices ((l mat-triple-listp) (k natp) (j natp) (r natp))
  :returns (idxs nat-listp :hyp (natp r))
  (if (atom l)
      nil
    (if (equal (mat-entry k j (caddr (car l))) 1)
        (cons r (c-indices (cdr l) k j (1+ r)))
      (c-indices (cdr l) k j (1+ r))))
  ///
  ;; Stated with the bound as a variable so that it matches (len l) at r = 0.
  (defrule index-listp-of-c-indices
    (implies (and (natp r)
                  (equal m (+ r (len l))))
             (index-listp (c-indices l k j r) m))
    :enable index-listp))

(define triples-outs-row ((l mat-triple-listp) (k natp) (c natp) (n natp))
  :guard (<= c n)
  :returns (row idx-rowp)
  (if (zp c)
      nil
    (cons (c-indices l k (- n c) 0)
          (triples-outs-row l k (1- c) n)))
  ///
  (defrule outs-rowp-of-triples-outs-row
    (outs-rowp (triples-outs-row l k c n) (len l) c)
    :enable outs-rowp))

(define triples-outs-rows ((l mat-triple-listp) (c natp) (n natp))
  :guard (<= c n)
  :returns (outs idx-tablep)
  (if (zp c)
      nil
    (cons (triples-outs-row l (- n c) n n)
          (triples-outs-rows l (1- c) n)))
  ///
  (defrule outs-rowsp-of-triples-outs-rows
    (outs-rowsp (triples-outs-rows l c n) (len l) c n)
    :enable outs-rowsp))

(define triples-outs ((l mat-triple-listp) (n natp))
  :returns (outs idx-tablep)
  (triples-outs-rows l n n)
  ///
  (defrule outs-rowsp-of-triples-outs
    (outs-rowsp (triples-outs l n) (len l) n n)))

;;; The products, one per triple, and the algorithm.

(define scheme-prods ((l mat-triple-listp) (n natp))
  :guard (and (summand-dim-listp l n) (< 0 n))
  :returns (prods true-listp)
  (if (atom l)
      nil
    (cons (list :mul (mat-lform (car (car l)) n) (mat-lform (cadr (car l)) n))
          (scheme-prods (cdr l) n)))
  ///
  (defrule len-of-scheme-prods
    (equal (len (scheme-prods l n)) (len l)))
  (defrule prod-listp-of-scheme-prods
    (implies (and (summand-dim-listp l n) (natp n) (< 0 n))
             (prod-listp (scheme-prods l n) n))
    :enable (prod-listp prodp)))

(define scheme-algo ((l mat-triple-listp) (n natp))
  :guard (and (summand-dim-listp l n) (< 0 n))
  :returns (alg consp)
  (cons (scheme-prods l n) (triples-outs l n))
  ///
  (defrule algop-of-scheme-algo
    (implies (and (summand-dim-listp l n) (natp n) (< 0 n))
             (algop (scheme-algo l n) n))
    :enable algop))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 2: the coefficient matrix of mat-lform is the matrix
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; An entry of a bit matrix that is not 1 is 0.  bitp-of-mat-entry states
;;; the bit type but does not case-split on its own, and mat-entry stays
;;; disabled in the inductions below.

(defruled mat-entry-is-0-when-not-1
  (implies (and (bit-matp x m n)
                (natp m) (natp n) (natp i) (natp j) (< i m) (< j n)
                (not (equal (mat-entry i j x) 1)))
           (equal (mat-entry i j x) 0))
  :use bitp-of-mat-entry
  :disable (mat-entry bitp-of-mat-entry))

;;; lform-mat of the empty form '(:scale 0 (:var 0 0)) opens to the scaled
;;; unit below; its entries are 0.

(defruled mat-entry-of-lform-mat-empty
  (implies (and (natp n) (natp k) (natp l) (< k n) (< l n))
           (equal (mat-entry k l (bit-mat-scale 0 (bit-mat-unit 0 0 n n)))
                  0))
  :disable (mat-entry)
  :use ((:instance mat-entry-of-bit-mat-scale
                   (b 0) (a (bit-mat-unit 0 0 n n)) (m n) (i k) (j l))))

;;; mat-entry-of-bit-mat-add (mmt.lisp) has m free; this form binds n through
;;; lform-mat.

(defruled mat-entry-of-bit-mat-add-lform-mat
  (implies (and (bit-matp x n n) (lformp e n)
                (natp n) (natp k) (natp l) (< k n) (< l n))
           (equal (mat-entry k l (bit-mat-add x (lform-mat e n)))
                  (bitxor (mat-entry k l x) (mat-entry k l (lform-mat e n)))))
  :use ((:instance mat-entry-of-bit-mat-add
                   (x x) (y (lform-mat e n)) (m n) (i k) (j l))))

;;; Entries of the row form: a[i,l] in row i at the columns l >= n-c covered
;;; so far, 0 elsewhere; then of the row sum: a[k,l] in the rows k >= n-c.

(defruled mat-entry-of-lform-mat-of-mat-lform-row
  (implies (and (bit-matp a n n)
                (natp n) (natp i) (natp c) (natp k) (natp l)
                (< i n) (<= c n) (< k n) (< l n))
           (equal (mat-entry k l (lform-mat (mat-lform-row a i c n) n))
                  (if (and (equal k i) (<= (- n c) l))
                      (mat-entry i l a)
                    0)))
  :induct (mat-lform-row a i c n)
  :enable (mat-lform-row lform-mat mat-entry-of-lform-mat-empty
           mat-entry-of-bit-mat-add-lform-mat mat-entry-is-0-when-not-1)
  :disable (mat-entry))

(defruled mat-entry-of-lform-mat-of-mat-lform-rows
  (implies (and (bit-matp a n n)
                (natp n) (< 0 n) (natp c) (natp k) (natp l)
                (<= c n) (< k n) (< l n))
           (equal (mat-entry k l (lform-mat (mat-lform-rows a c n) n))
                  (if (<= (- n c) k)
                      (mat-entry k l a)
                    0)))
  :induct (mat-lform-rows a c n)
  :enable (mat-lform-rows lform-mat mat-entry-of-lform-mat-empty
           mat-entry-of-bit-mat-add-lform-mat
           mat-entry-of-lform-mat-of-mat-lform-row)
  :disable (mat-entry))

;;; Both are n x n with the same entries, so they are equal (mat-diff-pos).

(defrule lform-mat-of-mat-lform
  (implies (and (bit-matp a n n) (natp n) (< 0 n))
           (equal (lform-mat (mat-lform a n) n) a))
  :do-not-induct t
  :enable (mat-lform)
  :disable (mat-entry)
  :use ((:instance mat-diff-pos-correct
                   (x (lform-mat (mat-lform a n) n)) (y a) (m n))
        (:instance mat-entry-of-lform-mat-of-mat-lform-rows
                   (c n)
                   (k (car (mat-diff-pos (lform-mat (mat-lform a n) n) a)))
                   (l (cdr (mat-diff-pos (lform-mat (mat-lform a n) n) a))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 3: c-mat reads the C factors back off the table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The parity of an index r0 in (c-indices l k j r): 0 below r, and the
;;; entry C_{r0-r}[k,j] of the triple it names otherwise.  Each index occurs
;;; at most once, so parity is membership.

(defruled occ-parity-of-c-indices-below
  (implies (and (natp r) (natp r0) (< r0 r))
           (equal (occ-parity r0 (c-indices l k j r)) 0))
  :induct (c-indices l k j r)
  :enable (c-indices occ-parity))

(defruled occ-parity-of-c-indices
  (implies (and (summand-dim-listp l n)
                (natp n) (natp k) (natp j) (< k n) (< j n)
                (natp r) (natp r0) (<= r r0) (< r0 (+ r (len l))))
           (equal (occ-parity r0 (c-indices l k j r))
                  (mat-entry k j (caddr (nth (- r0 r) l)))))
  :induct (c-indices l k j r)
  :enable (c-indices occ-parity occ-parity-of-c-indices-below
           mat-entry-is-0-when-not-1)
  :disable (mat-entry))

;;; The entry characterization of the table, as for eval-algo: position j of
;;; the row for columns n-c .. n-1 is column n-c+j, likewise for rows.

(defruled nth-of-triples-outs-row
  (implies (and (natp j) (natp c) (< j c))
           (equal (nth j (triples-outs-row l k c n))
                  (c-indices l k (+ j (- n c)) 0)))
  :induct (dec-dec-induct j c)
  :enable triples-outs-row
  :expand ((triples-outs-row l k c n)))

(defruled nth-of-triples-outs-rows
  (implies (and (natp i) (natp c) (< i c))
           (equal (nth i (triples-outs-rows l c n))
                  (triples-outs-row l (+ i (- n c)) n n)))
  :induct (dec-dec-induct i c)
  :enable triples-outs-rows
  :expand ((triples-outs-rows l c n)))

(defruled nth-nth-of-triples-outs
  (implies (and (natp n) (natp k) (natp j) (< k n) (< j n))
           (equal (nth j (nth k (triples-outs l n)))
                  (c-indices l k j 0)))
  :enable (triples-outs nth-of-triples-outs-rows nth-of-triples-outs-row))

;;; Entry (k, j) of c-mat r of the table is the parity of r in the table
;;; entry (nth-of-c-mat, nth-of-c-mat-row in matmul-expr.lisp), which is
;;; C_r[k,j].  The in-range condition of nth-of-c-mat-row comes from the
;;; table's shape.

(defruled mat-entry-of-c-mat-of-triples-outs
  (implies (and (summand-dim-listp l n)
                (natp n) (natp k) (natp j) (< k n) (< j n)
                (natp r) (< r (len l)))
           (equal (mat-entry k j (c-mat r (triples-outs l n)))
                  (mat-entry k j (caddr (nth r l)))))
  :do-not-induct t
  :enable (nth-of-c-mat nth-nth-of-triples-outs)
  :use ((:instance len-of-nth-when-outs-rowsp
                   (outs (triples-outs l n)) (r (len l)) (m n) (n n) (k k))
        (:instance nth-of-c-mat-row
                   (row (nth k (triples-outs l n))) (l j) (r r))
        (:instance occ-parity-of-c-indices (r 0) (r0 r))))

;;; The factors of the r-th triple of a dimensioned list are n x n.

(defrule factors-of-nth-when-summand-dim-listp
  (implies (and (summand-dim-listp l n)
                (< (nfix r) (len l)))
           (and (mat-triplep (nth r l))
                (bit-matp (car (nth r l)) n n)
                (bit-matp (cadr (nth r l)) n n)
                (bit-matp (caddr (nth r l)) n n)))
  :induct (cdr-dec-induct l r))

(defrule c-mat-of-triples-outs
  (implies (and (summand-dim-listp l n)
                (natp n) (natp r) (< r (len l)))
           (equal (c-mat r (triples-outs l n))
                  (caddr (nth r l))))
  :do-not-induct t
  :disable (mat-entry c-mat triples-outs)
  :use ((:instance bit-matp-of-c-mat
                   (outs (triples-outs l n)) (rr (len l)) (m n))
        (:instance mat-diff-pos-correct
                   (x (c-mat r (triples-outs l n))) (y (caddr (nth r l))) (m n))
        (:instance mat-entry-of-c-mat-of-triples-outs
                   (k (car (mat-diff-pos (c-mat r (triples-outs l n))
                                         (caddr (nth r l)))))
                   (j (cdr (mat-diff-pos (c-mat r (triples-outs l n))
                                         (caddr (nth r l))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 4: the round trip (theorem 1)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Element i of the translation of the algorithm of l is (A_i, B_i, C_i):
;;; the coefficient matrices of the i-th product's forms are A_i and B_i by
;;; lform-mat-of-mat-lform, and c-mat i of the table is C_i by
;;; c-mat-of-triples-outs.  Both sides are true lists of the same length, so
;;; first-diff-index (span.lisp) lifts the elementwise identity to the lists.

(defrule true-listp-when-summand-dim-listp
  (implies (and (summand-dim-listp l n)
                (natp n))
           (true-listp l))
  :rule-classes (:rewrite :forward-chaining))

(defrule list-of-factors-when-mat-triplep
  (implies (mat-triplep s)
           (equal (list (car s) (cadr s) (caddr s)) s))
  :expand ((len s) (len (cdr s)) (len (cddr s)) (len (cdddr s))
           (true-listp s) (true-listp (cdr s)) (true-listp (cddr s))
           (true-listp (cdddr s))))

(defruled nth-of-scheme-prods
  (implies (and (natp i) (< i (len l)))
           (equal (nth i (scheme-prods l n))
                  (list :mul (mat-lform (car (nth i l)) n)
                        (mat-lform (cadr (nth i l)) n))))
  :induct (cdr-dec-induct l i)
  :enable scheme-prods)

;; The merged induction cdrs prods while incrementing r (triples-from) and
;; decrementing i (cdr-dec-induct).
(defruled nth-of-triples-from
  (implies (and (natp i) (natp r) (< i (len prods)))
           (equal (nth i (triples-from prods outs r n))
                  (list (lform-mat (cadr (nth i prods)) n)
                        (lform-mat (caddr (nth i prods)) n)
                        (c-mat (+ r i) outs))))
  :induct (list (triples-from prods outs r n) (cdr-dec-induct prods i))
  :enable triples-from)

(defrule algo-triples-of-scheme-algo
  (implies (and (summand-dim-listp l n) (natp n) (< 0 n))
           (equal (algo-triples (scheme-algo l n) n) l))
  :do-not-induct t
  :enable (algo-triples scheme-algo true-listp-when-mat-triple-listp)
  :disable (mat-entry triples-from scheme-prods triples-outs c-mat lform-mat
            mat-lform)
  :use ((:instance first-diff-index-bound
                   (x (triples-from (scheme-prods l n) (triples-outs l n) 0 n))
                   (y l))
        (:instance nth-of-first-diff-index
                   (x (triples-from (scheme-prods l n) (triples-outs l n) 0 n))
                   (y l))
        (:instance nth-of-triples-from
                   (prods (scheme-prods l n)) (outs (triples-outs l n)) (r 0)
                   (i (first-diff-index
                       (triples-from (scheme-prods l n) (triples-outs l n) 0 n)
                       l)))
        (:instance nth-of-scheme-prods
                   (i (first-diff-index
                       (triples-from (scheme-prods l n) (triples-outs l n) 0 n)
                       l)))
        (:instance c-mat-of-triples-outs
                   (r (first-diff-index
                       (triples-from (scheme-prods l n) (triples-outs l n) 0 n)
                       l)))
        (:instance factors-of-nth-when-summand-dim-listp
                   (r (first-diff-index
                       (triples-from (scheme-prods l n) (triples-outs l n) 0 n)
                       l)))
        (:instance lform-mat-of-mat-lform
                   (a (car (nth (first-diff-index
                                 (triples-from (scheme-prods l n) (triples-outs l n) 0 n)
                                 l)
                                l))))
        (:instance lform-mat-of-mat-lform
                   (a (cadr (nth (first-diff-index
                                  (triples-from (scheme-prods l n) (triples-outs l n) 0 n)
                                  l)
                                 l))))
        (:instance list-of-factors-when-mat-triplep
                   (s (nth (first-diff-index
                            (triples-from (scheme-prods l n) (triples-outs l n) 0 n)
                            l)
                           l)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 5: schemes are fixed points; evaluation and correctness (theorems 2-4)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Inserting the elements of a scheme, in order, into the empty bag rebuilds
;;; the scheme: its summands are nonzero, so none is dropped, and inserting
;;; the head into the tail of a bag gives the bag (insert-of-car-into-cdr,
;;; bags.lisp).

(defruled insert-all-nonzero-of-scheme
  (implies (and (obag::bagp sch)
                (summand-listp sch n))
           (equal (insert-all-nonzero sch nil n) sch))
  :induct (insert-all-nonzero sch nil n)
  :enable (insert-all-nonzero))

;;; Theorem 2: a scheme converted to an algorithm and translated back is
;;; itself.

(defrule algo-scheme-of-scheme-algo
  (implies (and (schemep sch n) (natp n) (< 0 n))
           (equal (algo-scheme (scheme-algo sch n) n) sch))
  :enable (algo-scheme insert-all-nonzero-of-scheme)
  :disable (insert-all-nonzero scheme-algo algo-triples))

;;; Theorem 3: the algorithm of a list computes eval-scheme of the list
;;; (eval-algo-is-eval-scheme and the round trip).

(defrule eval-scheme-algo
  (implies (and (summand-dim-listp l n) (natp n) (< 0 n)
                (bit-matp d n n) (bit-matp f n n))
           (equal (eval-algo (scheme-algo l n) d f n)
                  (eval-scheme l d f n)))
  :disable (scheme-algo eval-algo eval-scheme algo-triples))

;;; Theorem 4: the algorithm of a correct scheme is correct, by adequacy
;;; (eval-scheme-computes-product) at the witness of algo-correctp.

(defrule scheme-algo-correct
  (implies (and (correct-schemep sch n) (natp n) (< 0 n))
           (algo-correctp (scheme-algo sch n) n))
  :expand ((algo-correctp (scheme-algo sch n) n))
  :use ((:instance eval-scheme-computes-product
                   (d (mv-nth 0 (algo-correctp-witness (scheme-algo sch n) n)))
                   (f (mv-nth 1 (algo-correctp-witness (scheme-algo sch n) n)))))
  :enable (correct-schemep)
  :disable (eval-algo eval-scheme bit-mat-mul scheme-algo
            eval-scheme-computes-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 6: eval-scheme depends only on scheme-sum
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; eval-scheme is determined by scheme-sum: the flat of eval-scheme is the
;;; contraction of scheme-sum with the inputs (tensor-contract-of-scheme-sum,
;;; adequacy.lisp), and mat-flat is injective.

(defruled eval-scheme-when-scheme-sum-equal
  (implies (and (summand-dim-listp l1 n)
                (summand-dim-listp l2 n)
                (natp n) (bit-matp d n n) (bit-matp f n n)
                (equal (scheme-sum l1 n) (scheme-sum l2 n)))
           (equal (eval-scheme l1 d f n) (eval-scheme l2 d f n)))
  :do-not-induct t
  :disable (eval-scheme scheme-sum tensor-contract)
  :use ((:instance mat-flat-injective
                   (a (eval-scheme l1 d f n)) (b (eval-scheme l2 d f n)) (m n))
        (:instance tensor-contract-of-scheme-sum (sch l1))
        (:instance tensor-contract-of-scheme-sum (sch l2))))

;;; Dropping the zero summands and moving to a bag keeps the sum
;;; (scheme-sum-of-list-to-scheme, completeness.lisp).

(defrule scheme-sum-of-algo-scheme
  (implies (and (algop alg n) (natp n))
           (equal (scheme-sum (algo-scheme alg n) n)
                  (scheme-sum (algo-triples alg n) n)))
  :enable (algo-scheme list-to-scheme)
  :disable (algo-triples scheme-sum insert-all-nonzero)
  :use ((:instance scheme-sum-of-list-to-scheme (l (algo-triples alg n)))))

;;; Equivalent algorithms compute the same function: eval-algo is eval-scheme
;;; of the triples, whose scheme-sum is that of the common scheme.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The round trip on Strassen's algorithm
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (let ((l (algo-triples *strassen2* 2)))
                (equal (algo-triples (scheme-algo l 2) 2) l)))
(assert-event (let ((s (algo-scheme *strassen2* 2)))
                (equal (algo-scheme (scheme-algo s 2) 2) s)))
