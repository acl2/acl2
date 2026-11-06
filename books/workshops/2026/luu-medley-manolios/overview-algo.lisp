; overview-algo.lisp -- schemes as equivalence classes of algorithms.
;
; Third tour of the development (after overview-prelims.lisp and
; overview-proof.lisp).  The main theorem is about schemes: multisets of
; summands (A,B,C) whose tensors sum to the matrix multiplication tensor.
; This file explains how schemes relate to algorithms, in the ordinary
; sense of a recipe for multiplying two matrices.  Read overview-
; prelims.lisp first for the objects and the notation of the commentary.
;
; The picture.  A bilinear algorithm over F2 is a list of R products of a
; linear form in the entries of the first matrix by a linear form in the
; entries of the second, and an n x n table saying which products are
; summed into each output entry.  Every algorithm TRANSLATES to a scheme,
; one summand per product: the coefficient matrices of the two forms and
; the matrix recording which output entries use the product.  Translation
; is many-to-one.  It forgets the order of the products, the way each
; form is written (a+b and b+a have the same coefficient matrix), and
; repeated indices in the table; it drops the products whose summand is
; zero; and it sorts, since a scheme is an ordered bag.  Two algorithms
; are EQUIVALENT when they translate to the same scheme (scheme-equiv).
; This is an equivalence relation in ACL2's own sense (defequiv), and its
; classes are exactly the schemes: every scheme is the class of some
; algorithm, because a scheme CONVERTS to an algorithm (scheme-algo)
; whose translation is the scheme itself.  Converting the scheme of an
; algorithm gives the canonical representative of its class (algo-canon):
; equivalent algorithms have equal representatives and conversely, the
; representative is equivalent to the algorithm, and it is its own
; representative.  Equivalent algorithms compute the same function.
;
; Correctness lives on the class.  A correct algorithm (one that returns
; the product on all inputs) translates to a correct scheme, whose rank is
; at most R (completeness); a correct scheme converts to a correct
; algorithm (soundness).  So the main theorem, a statement about schemes,
; is a statement about bilinear algorithms up to equivalence.
;
; Existence is also a statement about an algorithm: the textbook algorithm,
; one product D[i,j] F[j,k] per i, j, k with output entry (i,k) summing
; the products for its i and k, is written in the language and its
; translation is the standard scheme, the bag of the n^3 summands
; (E_ij, E_jk, E_ik), which is correct for every n.
;
; Every definition and theorem below is restated verbatim from the books
; this file includes (adequacy.lisp, completeness.lisp, matmul-expr.lisp,
; algo-completeness.lisp, scheme-algo.lisp, algo-class.lisp,
; standard.lisp, naive-algo.lisp), with proof hints and routine typing
; theorems left out; certification checks that the restatements match.

(in-package "ACL2")

(include-book "naive-algo")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Algorithms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Linear forms are (:var i j), the entry (i,j) of a matrix, (:add e1 e2)
; and (:scale b e).  Whether a form reads the first or the second matrix
; is decided by its position in a product (:mul d-form f-form).  An
; algorithm is (prods . outs): prods a list of R products, outs an n x n
; table whose entry (k,l) lists the indices of the products summed into
; output entry (k,l), repeats allowed.  Only bilinear algorithms are
; representable: a product of two forms in the same matrix has no place
; in the language, which is what makes rank the right measure.

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
         (prod-listp (cdr l) n))))

(define index-listp (l (r natp))
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (natp (car l))
         (< (car l) r)
         (index-listp (cdr l) r))))

(define outs-rowp (row (r natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp n)
      (null row)
    (and (consp row)
         (index-listp (car row) r)
         (outs-rowp (cdr row) r (1- n)))))

(define outs-rowsp (outs (r natp) (m natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp m)
      (null outs)
    (and (consp outs)
         (outs-rowp (car outs) r n)
         (outs-rowsp (cdr outs) r (1- m) n))))

(define algop (alg (n natp))
  :returns (yes/no booleanp)
  (and (consp alg)
       (prod-listp (car alg) n)
       (outs-rowsp (cdr alg) (len (car alg)) n n)))

; Running an algorithm on matrices d and f.  A form is evaluated on its
; matrix, the value of a product is the product of the values of its two
; forms, output entry (k,l) is the xor of the values of the products
; listed at (k,l), and the result is built row by row.

(define eval-lform (e (m bit-list-listp) (n natp))
  :guard (and (lformp e n) (bit-matp m n n))
  :returns (b bitp :hyp :guard)
  :verify-guards :after-returns
  (case (car e)
    (:var (mat-entry (cadr e) (caddr e) m))
    (:add (bitxor (eval-lform (cadr e) m n) (eval-lform (caddr e) m n)))
    (:scale (bitand (cadr e) (eval-lform (caddr e) m n)))
    (t 0)))

(define prod-value (p (d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (prodp p n) (bit-matp d n n) (bit-matp f n n))
  :returns (b bitp)
  (bitand (eval-lform (cadr p) d n)
          (eval-lform (caddr p) f n)))

(define prods-xor ((idxs nat-listp) (prods true-listp)
                   (d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (index-listp idxs (len prods))
              (prod-listp prods n)
              (bit-matp d n n)
              (bit-matp f n n))
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
          (eval-algo-row alg d f k (1- c) n))))

(define eval-algo-rows (alg (d bit-list-listp) (f bit-list-listp)
                        (c natp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n)
              (<= c n))
  :returns (a bit-list-listp)
  (if (zp c)
      nil
    (cons (eval-algo-row alg d f (- n c) n n)
          (eval-algo-rows alg d f (1- c) n))))

(define eval-algo (alg (d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n))
  :returns (a bit-list-listp)
  (eval-algo-rows alg d f n n))

; A correct algorithm returns the matrix product on every pair of inputs.

(defun-sk algo-correctp (alg n)
  (forall (d f)
          (implies (and (bit-matp d n n)
                        (bit-matp f n n))
                   (equal (eval-algo alg d f n)
                          (bit-mat-mul d f n)))))

; Three algorithms for 2 x 2 matrices.  The naive one has one product per
; term of the definition; entry (0,0) is d[0,0]f[0,0] + d[0,1]f[1,0], the
; xor of products 0 and 1.  Strassen's has seven products M1..M7 and
; outputs C11 = M1+M4+M5+M7, C12 = M3+M5, C21 = M2+M4, C22 = M1+M2+M3+M6,
; with 0-based product indices; over F2 all the signs vanish.  The third
; is Strassen's with product 2 listed twice more at entry (0,0), which
; cancels: it is a different algorithm that does the same thing.

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

(defconst *strassen2-rep*
  (cons (car *strassen2*)
        '(((0 3 4 6 2 2) (2 4))
          ((1 3) (0 1 2 5)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Running a list of summands
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of summands (A_r, B_r, C_r) is itself a recipe: multiply the
; inner product of A_r with D by the inner product of B_r with F, once per
; summand, and add C_r times the result into the output.  (mat-dot a d) is
; the F2 inner product of two matrices, the sum over g,h of A_gh D_gh;
; bit-mat-mul is the ordinary product of two n x n matrices, entry (k,l)
; being the sum over h of D_kh F_hl.  A correct scheme computes the product
; (eval-scheme-computes-product): contracting the tensor of the scheme
; with D and F gives eval-scheme, and contracting mm-tensor gives the
; product.

(define bit-list-dot ((x bit-list-p) (y bit-list-p))
  :returns (b bitp)
  (if (and (consp x) (consp y))
      (bitxor (bitand (car x) (car y))
              (bit-list-dot (cdr x) (cdr y)))
    0))

(define mat-dot ((a bit-list-listp) (d bit-list-listp))
  :returns (b bitp)
  (bit-list-dot (mat-flat a) (mat-flat d)))

(define bit-mat-scale ((b bitp) (a bit-list-listp))
  :returns (c bit-list-listp)
  (if (atom a)
      nil
    (cons (bit-list-scale b (car a))
          (bit-mat-scale b (cdr a)))))

(define mat-mul-entry ((d bit-list-listp) (f bit-list-listp)
                       (k natp) (l natp) (h natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (< k n) (< l n) (<= h n))
  :returns (b bitp)
  :verify-guards :after-returns
  (if (zp h)
      0
    (bitxor (bitand (mat-entry k (1- h) d) (mat-entry (1- h) l f))
            (mat-mul-entry d f k l (1- h) n))))

(define bit-mat-mul-row ((d bit-list-listp) (f bit-list-listp)
                         (k natp) (c natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (< k n) (<= c n))
  :returns (r bit-list-p)
  :verify-guards :after-returns
  (if (zp c)
      nil
    (cons (mat-mul-entry d f k (- n c) n n)
          (bit-mat-mul-row d f k (1- c) n))))

(define bit-mat-mul-rows ((d bit-list-listp) (f bit-list-listp)
                          (c natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (<= c n))
  :returns (a bit-list-listp)
  :verify-guards :after-returns
  (if (zp c)
      nil
    (cons (bit-mat-mul-row d f (- n c) n n)
          (bit-mat-mul-rows d f (1- c) n))))

(define bit-mat-mul ((d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n))
  :returns (a bit-list-listp)
  (bit-mat-mul-rows d f n n))

(define eval-scheme ((sch mat-triple-listp) (d bit-list-listp)
                     (f bit-list-listp) (n natp))
  :returns (c bit-list-listp)
  :verify-guards :after-returns
  (if (atom sch)
      (bit-mat0 n n)
    (bit-mat-add (bit-mat-scale (bitand (mat-dot (car (car sch)) d)
                                        (mat-dot (cadr (car sch)) f))
                                (caddr (car sch)))
                 (eval-scheme (cdr sch) d f n))))

(defrule eval-scheme-computes-product
  (implies (and (correct-schemep sch n)
                (natp n)
                (bit-matp d n n)
                (bit-matp f n n))
           (equal (eval-scheme sch d f n)
                  (bit-mat-mul d f n))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Translation: algorithm to scheme
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lform-mat is the coefficient matrix of a form.  Product r becomes the
; summand (A_r, B_r, C_r) with A_r and B_r the coefficient matrices of
; its two forms and C_r the matrix with a 1 at (k,l) iff r occurs an odd
; number of times in outs[k][l].  algo-triples is the list of summands in
; product order; algo-scheme drops the zero summands and builds the bag.
; Both steps forget something: lform-mat forgets how a form was written,
; c-mat forgets repeated indices, the bag forgets order and zero
; summands.

(define lform-mat (e (n natp))
  :guard (lformp e n)
  :returns (a bit-list-listp)
  :verify-guards :after-returns
  (case (car e)
    (:var (bit-mat-unit (cadr e) (caddr e) n n))
    (:add (bit-mat-add (lform-mat (cadr e) n) (lform-mat (caddr e) n)))
    (:scale (bit-mat-scale (cadr e) (lform-mat (caddr e) n)))
    (t (bit-mat0 n n))))

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
          (c-mat-row r (cdr row)))))

(define c-mat ((r natp) (outs idx-tablep))
  :returns (a bit-list-listp)
  (if (atom outs)
      nil
    (cons (c-mat-row r (car outs))
          (c-mat r (cdr outs)))))

(define triples-from ((prods true-listp) (outs idx-tablep) (r natp) (n natp))
  :guard (prod-listp prods n)
  :returns (l mat-triple-listp)
  (if (atom prods)
      nil
    (cons (list (lform-mat (cadr (car prods)) n)
                (lform-mat (caddr (car prods)) n)
                (c-mat r outs))
          (triples-from (cdr prods) outs (1+ r) n))))

(define algo-triples (alg (n natp))
  :guard (algop alg n)
  :returns (l mat-triple-listp)
  (triples-from (car alg) (cdr alg) 0 n))

(define algo-scheme (alg (n natp))
  :guard (algop alg n)
  :returns (sch obag::bagp)
  (insert-all-nonzero (algo-triples alg n) nil n))

; Translation preserves what is computed: running an algorithm is running
; its list of summands (eval-scheme, adequacy.lisp), because a repeated
; index cancels in pairs exactly as the parity in C_r says.

(defrule eval-algo-is-eval-scheme
  (implies (and (algop alg n) (natp n)
                (bit-matp d n n) (bit-matp f n n))
           (equal (eval-algo alg d f n)
                  (eval-scheme (algo-triples alg n) d f n))))

; Completeness for lists of summands first.  (agrees-on-unitsp l n) checks
; that the list returns the product on every pair of unit matrices; that
; is enough, because the product of two unit inputs reads off one entry
; of the tensor, so agreement on all n^4 pairs forces the scheme sum to
; equal mm-tensor entry by entry.  list-to-scheme drops the zero summands
; and builds the bag; computes-productp says the list returns the product
; on all inputs.

(define agrees-on-units-4 ((l mat-triple-listp) (g natp) (h natp) (i natp)
                           (j natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp j)
      t
    (and (equal (eval-scheme l (bit-mat-unit g h n n) (bit-mat-unit i (1- j) n n) n)
                (bit-mat-mul (bit-mat-unit g h n n) (bit-mat-unit i (1- j) n n) n))
         (agrees-on-units-4 l g h i (1- j) n))))

(define agrees-on-units-3 ((l mat-triple-listp) (g natp) (h natp) (i natp)
                           (n natp))
  :returns (yes/no booleanp)
  (if (zp i)
      t
    (and (agrees-on-units-4 l g h (1- i) n n)
         (agrees-on-units-3 l g h (1- i) n))))

(define agrees-on-units-2 ((l mat-triple-listp) (g natp) (h natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp h)
      t
    (and (agrees-on-units-3 l g (1- h) n n)
         (agrees-on-units-2 l g (1- h) n))))

(define agrees-on-units-1 ((l mat-triple-listp) (g natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp g)
      t
    (and (agrees-on-units-2 l (1- g) n n)
         (agrees-on-units-1 l (1- g) n))))

(define agrees-on-unitsp ((l mat-triple-listp) (n natp))
  :returns (yes/no booleanp)
  (agrees-on-units-1 l n n))

(define list-to-scheme ((l mat-triple-listp) (n natp))
  :returns (sch obag::bagp)
  (insert-all-nonzero l nil n))

(defun-sk computes-productp (l n)
  (forall (d f)
          (implies (and (bit-matp d n n)
                        (bit-matp f n n))
                   (equal (eval-scheme l d f n)
                          (bit-mat-mul d f n)))))

(defrule completeness
  (implies (and (summand-dim-listp l n)
                (natp n) (< 0 n)
                (computes-productp l n))
           (correct-schemep (list-to-scheme l n) n)))

; Completeness for algorithms: a correct algorithm translates to a correct
; scheme, of rank at most the number of products.

(defrule algo-to-correct-scheme
  (implies (and (algop alg n) (natp n) (< 0 n) (algo-correctp alg n))
           (correct-schemep (algo-scheme alg n) n)))

(defrule scheme-rank-of-algo-scheme
  (implies (algop alg n)
           (<= (scheme-rank (algo-scheme alg n)) (len (car alg)))))

(assert-event (and (correct-schemep (algo-scheme *strassen2* 2) 2)
                   (equal (scheme-rank (algo-scheme *strassen2* 2)) 7)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Existence: the textbook algorithm
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The textbook algorithm for n x n matrices has one product
; (:mul (:var i j) (:var j k)) for each i, j, k below n, and output entry
; (i,k) is the sum of the products whose first form reads row i and whose
; second form reads column k.  The products are listed in three levels,
; k innermost, each level counting down; the output table is read off the
; product list by prod-indices.

(define naive-prods-3 ((i natp) (j natp) (k natp) (n natp))
  :guard (and (< i n) (< j n) (<= k n))
  :returns (prods true-listp)
  (if (zp k)
      nil
    (cons (list :mul (list :var i j) (list :var j (1- k)))
          (naive-prods-3 i j (1- k) n))))

(define naive-prods-2 ((i natp) (j natp) (n natp))
  :guard (and (< i n) (<= j n))
  :returns (prods true-listp)
  (if (zp j)
      nil
    (append (naive-prods-3 i (1- j) n n)
            (naive-prods-2 i (1- j) n))))

(define naive-prods-1 ((i natp) (n natp))
  :guard (<= i n)
  :returns (prods true-listp)
  (if (zp i)
      nil
    (append (naive-prods-2 (1- i) n n)
            (naive-prods-1 (1- i) n))))

(define naive-prods ((n natp))
  :returns (prods true-listp)
  (naive-prods-1 n n))

(define prod-indices ((prods true-listp) (i natp) (k natp) (r natp) (n natp))
  :guard (prod-listp prods n)
  :returns (idxs nat-listp :hyp (natp r))
  (if (atom prods)
      nil
    (if (and (equal (cadr (cadr (car prods))) i)
             (equal (caddr (caddr (car prods))) k))
        (cons r (prod-indices (cdr prods) i k (1+ r) n))
      (prod-indices (cdr prods) i k (1+ r) n))))

(define naive-outs-row ((prods true-listp) (i natp) (c natp) (n natp))
  :guard (and (prod-listp prods n) (<= c n))
  :returns (row idx-rowp)
  (if (zp c)
      nil
    (cons (prod-indices prods i (- n c) 0 n)
          (naive-outs-row prods i (1- c) n))))

(define naive-outs-rows ((prods true-listp) (c natp) (n natp))
  :guard (and (prod-listp prods n) (<= c n))
  :returns (outs idx-tablep)
  (if (zp c)
      nil
    (cons (naive-outs-row prods (- n c) n n)
          (naive-outs-rows prods (1- c) n))))

(define naive-outs ((prods true-listp) (n natp))
  :guard (prod-listp prods n)
  :returns (outs idx-tablep)
  (naive-outs-rows prods n n))

(define naive-algo ((n natp))
  :returns (alg consp)
  (cons (naive-prods n) (naive-outs (naive-prods n) n)))

; The standard scheme is the bag of the n^3 summands (E_ij, E_jk, E_ik),
; built by the same three levels; its tensor is mm-tensor level by level
; (standard.lisp).

(define standard-scheme-3 ((i natp) (j natp) (k natp) (n natp))
  :returns (sch obag::bagp)
  :verify-guards :after-returns
  (if (zp k)
      nil
    (obag::insert (summand (bit-mat-unit i j n n)
                           (bit-mat-unit j (1- k) n n)
                           (bit-mat-unit i (1- k) n n))
                  (standard-scheme-3 i j (1- k) n))))

(define standard-scheme-2 ((i natp) (j natp) (n natp))
  :returns (sch obag::bagp)
  :verify-guards :after-returns
  (if (zp j)
      nil
    (insert-list (standard-scheme-3 i (1- j) n n)
                 (standard-scheme-2 i (1- j) n))))

(define standard-scheme-1 ((i natp) (n natp))
  :returns (sch obag::bagp)
  :verify-guards :after-returns
  (if (zp i)
      nil
    (insert-list (standard-scheme-2 (1- i) n n)
                 (standard-scheme-1 (1- i) n))))

(define standard-scheme ((n natp))
  :returns (sch obag::bagp)
  (standard-scheme-1 n n))

(defrule correct-schemep-of-standard-scheme
  (implies (natp n)
           (correct-schemep (standard-scheme n) n)))

; The translation of the textbook algorithm is the standard scheme, so it
; is a correct scheme for every n, and the algorithm returns the product.
; The proof matches product r with summand r: the coefficient matrices of
; the two forms are the A and B factors, and the unit matrix at (row of
; the first variable, column of the second) is the C factor, so the
; output table read off the products is the one conversion reads off the
; C factors, and the round trip of the previous section applies.

(defrule algop-of-naive-algo
  (implies (and (natp n) (< 0 n))
           (algop (naive-algo n) n)))

(defrule algo-scheme-of-naive-algo
  (implies (natp n)
           (equal (algo-scheme (naive-algo n) n)
                  (standard-scheme n))))

(defrule correct-schemep-of-naive-algo-scheme
  (implies (natp n)
           (correct-schemep (algo-scheme (naive-algo n) n) n)))

(defrule naive-algo-correct
  (implies (and (natp n) (< 0 n))
           (algo-correctp (naive-algo n) n)))

(assert-event (and (equal (algo-scheme (naive-algo 2) 2) (algo-scheme *naive2* 2))
                   (equal (algo-scheme (naive-algo 3) 3) (standard-scheme 3))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Conversion: scheme to algorithm
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; mat-lform builds a form whose coefficient matrix is a given matrix: the
; sum of (:var i j) over the 1-entries in row-major order, an empty sum
; being a form scaled by 0.  triples-outs builds the output table from
; the C factors, listing at (k,l), once each and in increasing order, the
; indices of the summands whose C has a 1 there.  scheme-algo puts the
; two together, one product per summand, in the order of the list.

(define mat-lform-row ((a bit-list-listp) (i natp) (c natp) (n natp))
  :guard (and (bit-matp a n n) (< i n) (<= c n))
  :returns (e (lformp e n) :hyp :guard)
  (if (zp c)
      '(:scale 0 (:var 0 0))
    (if (equal (mat-entry i (- n c) a) 1)
        (list :add (list :var i (- n c)) (mat-lform-row a i (1- c) n))
      (mat-lform-row a i (1- c) n))))

(define mat-lform-rows ((a bit-list-listp) (c natp) (n natp))
  :guard (and (bit-matp a n n) (<= c n) (< 0 n))
  :returns (e (lformp e n) :hyp :guard)
  (if (zp c)
      '(:scale 0 (:var 0 0))
    (list :add (mat-lform-row a (- n c) n n) (mat-lform-rows a (1- c) n))))

(define mat-lform ((a bit-list-listp) (n natp))
  :guard (and (bit-matp a n n) (< 0 n))
  :returns (e (lformp e n) :hyp :guard)
  (mat-lform-rows a n n))

(defrule lform-mat-of-mat-lform
  (implies (and (bit-matp a n n) (natp n) (< 0 n))
           (equal (lform-mat (mat-lform a n) n) a)))

(define c-indices ((l mat-triple-listp) (k natp) (j natp) (r natp))
  :returns (idxs nat-listp :hyp (natp r))
  (if (atom l)
      nil
    (if (equal (mat-entry k j (caddr (car l))) 1)
        (cons r (c-indices (cdr l) k j (1+ r)))
      (c-indices (cdr l) k j (1+ r)))))

(define triples-outs-row ((l mat-triple-listp) (k natp) (c natp) (n natp))
  :guard (<= c n)
  :returns (row idx-rowp)
  (if (zp c)
      nil
    (cons (c-indices l k (- n c) 0)
          (triples-outs-row l k (1- c) n))))

(define triples-outs-rows ((l mat-triple-listp) (c natp) (n natp))
  :guard (<= c n)
  :returns (outs idx-tablep)
  (if (zp c)
      nil
    (cons (triples-outs-row l (- n c) n n)
          (triples-outs-rows l (1- c) n))))

(define triples-outs ((l mat-triple-listp) (n natp))
  :returns (outs idx-tablep)
  (triples-outs-rows l n n))

(defrule c-mat-of-triples-outs
  (implies (and (summand-dim-listp l n)
                (natp n) (natp r) (< r (len l)))
           (equal (c-mat r (triples-outs l n))
                  (caddr (nth r l)))))

(define scheme-prods ((l mat-triple-listp) (n natp))
  :guard (and (summand-dim-listp l n) (< 0 n))
  :returns (prods true-listp)
  (if (atom l)
      nil
    (cons (list :mul (mat-lform (car (car l)) n) (mat-lform (cadr (car l)) n))
          (scheme-prods (cdr l) n))))

(define scheme-algo ((l mat-triple-listp) (n natp))
  :guard (and (summand-dim-listp l n) (< 0 n))
  :returns (alg consp)
  (cons (scheme-prods l n) (triples-outs l n)))

; Translating a converted list of summands gives the list back, and a
; scheme converted and translated is itself: conversion is a section of
; translation, so translation is onto schemes.

(defrule algo-triples-of-scheme-algo
  (implies (and (summand-dim-listp l n) (natp n) (< 0 n))
           (equal (algo-triples (scheme-algo l n) n) l)))

(defrule algo-scheme-of-scheme-algo
  (implies (and (schemep sch n) (natp n) (< 0 n))
           (equal (algo-scheme (scheme-algo sch n) n) sch)))

; Conversion preserves what is computed, and soundness follows: a correct
; scheme converts to a correct algorithm (eval-scheme-computes-product,
; adequacy.lisp, says a correct scheme computes the product).

(defrule eval-scheme-algo
  (implies (and (summand-dim-listp l n) (natp n) (< 0 n)
                (bit-matp d n n) (bit-matp f n n))
           (equal (eval-algo (scheme-algo l n) d f n)
                  (eval-scheme l d f n))))

(defrule scheme-algo-correct
  (implies (and (correct-schemep sch n) (natp n) (< 0 n))
           (algo-correctp (scheme-algo sch n) n)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Equivalence: schemes are the classes of algorithms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; An algorithm carries its dimension: the output table has one row per
; row of the result.

(define algo-dim ((alg consp))
  :returns (n natp)
  (len (cdr alg)))

(defrule algo-dim-when-algop
  (implies (and (algop alg n) (natp n))
           (equal (algo-dim alg) n)))

; Two algorithms are equivalent when they have the same dimension and
; translate to the same scheme.  defequiv proves that this is an
; equivalence relation (boolean, reflexive, symmetric, transitive) and
; registers it with ACL2 as one.

(define scheme-equiv (a1 a2)
  :guard (and (consp a1) (consp a2)
              (algop a1 (algo-dim a1)) (algop a2 (algo-dim a2)))
  :returns (yes/no booleanp)
  (and (equal (algo-dim a1) (algo-dim a2))
       (equal (algo-scheme a1 (algo-dim a1))
              (algo-scheme a2 (algo-dim a2)))))

(defequiv scheme-equiv)

; Equivalent algorithms compute the same function.  (Not conversely:
; Strassen's algorithm and the naive one compute the same function and
; are not equivalent.  The relation is "same bilinear scheme", which is
; finer than "same function".)

(defrule eval-algo-when-scheme-equiv
  (implies (and (algop a1 n) (algop a2 n)
                (scheme-equiv a1 a2)
                (natp n) (< 0 n)
                (bit-matp d n n) (bit-matp f n n))
           (equal (eval-algo a1 d f n) (eval-algo a2 d f n))))

; The canonical representative of an algorithm's class: the conversion
; of its scheme.  defcong registers that scheme-equiv arguments give
; equal representatives, so ACL2 may replace an algorithm by an
; equivalent one under algo-canon.

(define algo-canon (alg)
  :guard (and (consp alg) (algop alg (algo-dim alg)) (< 0 (algo-dim alg)))
  :returns (alg1 consp)
  (scheme-algo (algo-scheme alg (algo-dim alg)) (algo-dim alg)))

(defcong scheme-equiv equal (algo-canon alg) 1)

; The representative is an algorithm of the same dimension and the same
; scheme, hence equivalent to the original; it is its own representative;
; and two algorithms are equivalent exactly when their representatives
; are equal.  With algo-scheme-of-scheme-algo (every scheme is the scheme
; of its conversion) this is the whole picture: the classes of
; scheme-equiv are in bijection with schemes, and each class has the
; converted scheme as its distinguished member.

(defrule algop-of-algo-canon
  (implies (and (algop alg n) (natp n) (< 0 n))
           (algop (algo-canon alg) n)))

(defrule algo-dim-of-algo-canon
  (implies (and (algop alg n) (natp n) (< 0 n))
           (equal (algo-dim (algo-canon alg)) n)))

(defrule algo-scheme-of-algo-canon
  (implies (and (algop alg n) (natp n) (< 0 n))
           (equal (algo-scheme (algo-canon alg) n)
                  (algo-scheme alg n))))

(defrule scheme-equiv-of-algo-canon
  (implies (and (algop alg n) (natp n) (< 0 n))
           (scheme-equiv (algo-canon alg) alg)))

(defrule algo-canon-of-algo-canon
  (implies (and (algop alg n) (natp n) (< 0 n))
           (equal (algo-canon (algo-canon alg))
                  (algo-canon alg))))

(defrule scheme-equiv-iff-algo-canon-equal
  (implies (and (algop a1 n) (algop a2 n) (natp n) (< 0 n))
           (iff (scheme-equiv a1 a2)
                (equal (algo-canon a1) (algo-canon a2)))))

; The three example algorithms.  Strassen, Strassen with the repeated
; index, and the representative of their class are three different
; algorithms with one scheme; the naive algorithm is in another class.

(assert-event (and (scheme-equiv *strassen2* *strassen2-rep*)
                   (scheme-equiv *strassen2* (algo-canon *strassen2*))
                   (not (equal *strassen2* *strassen2-rep*))
                   (not (equal *strassen2* (algo-canon *strassen2*)))
                   (equal (algo-canon *strassen2*) (algo-canon *strassen2-rep*))))

(assert-event (and (not (scheme-equiv *strassen2* *naive2*))
                   (correct-schemep (algo-scheme *naive2* 2) 2)))
