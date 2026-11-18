; naive-algo.lisp -- the textbook matrix multiplication algorithm, written in
; the expression language, translates to the standard scheme.
;
; (naive-algo n) is the algorithm with one product (:mul (:var i j) (:var j k))
; for each i, j, k < n, whose output table lists at entry (i,k) the products
; whose first form reads row i and whose second form reads column k: entry
; (i,k) of the result is the sum over j of D[i,j] F[j,k].  Its translation
; (algo-scheme) is the standard scheme of standard.lisp
; (algo-scheme-of-naive-algo), hence a correct scheme for every n
; (correct-schemep-of-naive-algo-scheme), and the algorithm itself returns
; the product on all inputs (naive-algo-correct).
;
; Proof.  standard-list is the flat list of the n^3 unit summands
; (E_ij, E_jk, E_ik) in the order in which the products of naive-algo are
; listed, so that the two are matched element by element (unit-matchp):
; the coefficient matrices of the two forms are the A and B factors, and
; the C factor is the unit matrix at (row of the first variable, column of
; the second).  Under this matching, the output table read off the
; products is the table triples-outs reads off the C factors, and
; triples-from produces the same triples as for the products scheme-algo
; builds from the list; algo-triples-of-scheme-algo (scheme-algo.lisp)
; then returns the list.  Separately, the standard scheme is insert-list
; of standard-list, since its three levels mirror the list's, and
; insert-all-nonzero of a list of summands is insert-list.  The corollary
; on the algorithm uses eval-algo-is-eval-scheme and the fact that
; eval-scheme depends only on scheme-sum.

(in-package "ACL2")

(include-book "algo-class")
(include-book "standard")

(local (include-book "arithmetic/top-with-meta" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 1: the algorithm
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The products, in three levels: k innermost, each level counting down.

(define naive-prods-3 ((i natp) (j natp) (k natp) (n natp))
  :guard (and (< i n) (< j n) (<= k n))
  :returns (prods true-listp)
  (if (zp k)
      nil
    (cons (list :mul (list :var i j) (list :var j (1- k)))
          (naive-prods-3 i j (1- k) n)))
  ///
  (defrule prod-listp-of-naive-prods-3
    (implies (and (natp i) (natp j) (natp k) (natp n)
                  (< i n) (< j n) (<= k n))
             (prod-listp (naive-prods-3 i j k n) n))
    :induct (naive-prods-3 i j k n)
    :enable (prod-listp prodp lformp)))

(defrule prod-listp-of-append
  (implies (and (prod-listp a n) (prod-listp b n))
           (prod-listp (append a b) n))
  :induct (prod-listp a n)
  :enable (prod-listp))

(define naive-prods-2 ((i natp) (j natp) (n natp))
  :guard (and (< i n) (<= j n))
  :returns (prods true-listp)
  (if (zp j)
      nil
    (append (naive-prods-3 i (1- j) n n)
            (naive-prods-2 i (1- j) n)))
  ///
  (defrule prod-listp-of-naive-prods-2
    (implies (and (natp i) (natp j) (natp n) (< i n) (<= j n))
             (prod-listp (naive-prods-2 i j n) n))
    :induct (naive-prods-2 i j n)
    :enable (prod-listp)))

(define naive-prods-1 ((i natp) (n natp))
  :guard (<= i n)
  :returns (prods true-listp)
  (if (zp i)
      nil
    (append (naive-prods-2 (1- i) n n)
            (naive-prods-1 (1- i) n)))
  ///
  (defrule prod-listp-of-naive-prods-1
    (implies (and (natp i) (natp n) (<= i n))
             (prod-listp (naive-prods-1 i n) n))
    :induct (naive-prods-1 i n)
    :enable (prod-listp)))

(define naive-prods ((n natp))
  :returns (prods true-listp)
  (naive-prods-1 n n)
  ///
  (defrule prod-listp-of-naive-prods
    (implies (natp n)
             (prod-listp (naive-prods n) n))))

;;; The output table: entry (i,k) lists the indices of the products whose
;;; first form reads row i and whose second form reads column k.

(define prod-indices ((prods true-listp) (i natp) (k natp) (r natp) (n natp))
  :guard (prod-listp prods n)
  :guard-hints (("Goal" :in-theory (enable prod-listp prodp lformp)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 2: the standard scheme as a flat list
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; mat-triple-listp-of-append and summand-listp-of-append are in arbitrary.lisp.

(define standard-list-3 ((i natp) (j natp) (k natp) (n natp))
  :returns (l mat-triple-listp)
  :verify-guards :after-returns
  (if (zp k)
      nil
    (cons (summand (bit-mat-unit i j n n)
                   (bit-mat-unit j (1- k) n n)
                   (bit-mat-unit i (1- k) n n))
          (standard-list-3 i j (1- k) n)))
  ///
  (defrule summand-listp-of-standard-list-3
    (implies (and (natp n) (natp i) (natp j) (natp k)
                  (< i n) (< j n) (<= k n))
             (summand-listp (standard-list-3 i j k n) n))
    :induct (standard-list-3 i j k n)
    :enable (summandp-of-unit-summand)
    :disable (summandp bit-mat-unit)))

(define standard-list-2 ((i natp) (j natp) (n natp))
  :returns (l mat-triple-listp :hints (("Goal" :in-theory (enable mat-triple-listp-of-append))))
  (if (zp j)
      nil
    (append (standard-list-3 i (1- j) n n)
            (standard-list-2 i (1- j) n)))
  ///
  (defrule summand-listp-of-standard-list-2
    (implies (and (natp n) (natp i) (natp j)
                  (< i n) (<= j n))
             (summand-listp (standard-list-2 i j n) n))
    :induct (standard-list-2 i j n)
    :enable (summand-listp-of-append)
    :disable (summandp)))

(define standard-list-1 ((i natp) (n natp))
  :returns (l mat-triple-listp :hints (("Goal" :in-theory (enable mat-triple-listp-of-append))))
  (if (zp i)
      nil
    (append (standard-list-2 (1- i) n n)
            (standard-list-1 (1- i) n)))
  ///
  (defrule summand-listp-of-standard-list-1
    (implies (and (natp n) (natp i) (<= i n))
             (summand-listp (standard-list-1 i n) n))
    :induct (standard-list-1 i n)
    :enable (summand-listp-of-append)
    :disable (summandp)))

(define standard-list ((n natp))
  :returns (l mat-triple-listp)
  (standard-list-1 n n)
  ///
  (defrule summand-listp-of-standard-list
    (implies (natp n)
             (summand-listp (standard-list n) n))
    :disable (summandp)))

;;; The standard scheme is insert-list of the flat list.

(defruled insert-list-of-insert-bag
  (implies (obag::bagp b)
           (equal (insert-list (obag::insert x b) s)
                  (obag::insert x (insert-list b s))))
  :induct (cdr-induct b)
  :enable (insert-list obag::bagp obag::insert obag::emptyp
           obag::head obag::tail obag::bfix))

(defruled insert-list-of-insert-list
  (implies (and (obag::bagp b) (obag::bagp s))
           (equal (insert-list (insert-list a b) s)
                  (insert-list a (insert-list b s))))
  :induct (insert-list a b)
  :enable (insert-list insert-list-of-insert-bag))

(defrule insert-list-of-nil-list
  (equal (insert-list nil b) b)
  :enable (insert-list))

(defruled standard-scheme-3-is-insert-list
  (equal (standard-scheme-3 i j k n)
         (insert-list (standard-list-3 i j k n) nil))
  :induct (standard-scheme-3 i j k n)
  :enable (standard-scheme-3 standard-list-3 insert-list)
  :disable (bit-mat-unit))

(defruled standard-scheme-2-is-insert-list
  (equal (standard-scheme-2 i j n)
         (insert-list (standard-list-2 i j n) nil))
  :induct (standard-scheme-2 i j n)
  :enable (standard-scheme-2 standard-list-2 insert-list-of-append
           insert-list-of-insert-list standard-scheme-3-is-insert-list))

(defruled standard-scheme-1-is-insert-list
  (equal (standard-scheme-1 i n)
         (insert-list (standard-list-1 i n) nil))
  :induct (standard-scheme-1 i n)
  :enable (standard-scheme-1 standard-list-1 insert-list-of-append
           insert-list-of-insert-list standard-scheme-2-is-insert-list))

(defruled standard-scheme-is-insert-list
  (equal (standard-scheme n)
         (insert-list (standard-list n) nil))
  :enable (standard-scheme standard-list standard-scheme-1-is-insert-list))

;;; insert-all-nonzero of a list of (nonzero) summands is insert-list.

(defruled insert-all-nonzero-is-insert-list
  (implies (summand-listp l n)
           (equal (insert-all-nonzero l s n)
                  (insert-list l s)))
  :induct (insert-all-nonzero l s n)
  :enable (insert-all-nonzero insert-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 3: matching the products with the summands
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Product r and summand r correspond: the coefficient matrices of the two
;;; forms are the A and B factors, and the C factor is the unit matrix at
;;; (row of the first variable, column of the second variable).

(define unit-matchp (p l (n natp))
  :guard (and (prod-listp p n) (mat-triple-listp l))
  :guard-hints (("Goal" :in-theory (enable prod-listp prodp lformp)))
  :returns (yes/no booleanp)
  (if (atom p)
      (atom l)
    (and (consp l)
         (equal (car (car l)) (lform-mat (cadr (car p)) n))
         (equal (cadr (car l)) (lform-mat (caddr (car p)) n))
         (natp (cadr (cadr (car p))))
         (< (cadr (cadr (car p))) n)
         (natp (caddr (caddr (car p))))
         (< (caddr (caddr (car p))) n)
         (equal (caddr (car l))
                (bit-mat-unit (cadr (cadr (car p))) (caddr (caddr (car p))) n n))
         (unit-matchp (cdr p) (cdr l) n)))
  ///
  (defrule unit-matchp-of-nil
    (unit-matchp nil nil n))
  (defrule len-when-unit-matchp
    (implies (unit-matchp p l n)
             (equal (len p) (len l)))
    :induct (unit-matchp p l n))
  (defrule unit-matchp-of-append
    (implies (and (unit-matchp p1 l1 n) (unit-matchp p2 l2 n))
             (unit-matchp (append p1 p2) (append l1 l2) n))
    :induct (unit-matchp p1 l1 n)))

(defrule unit-matchp-of-naive-prods-3
  (implies (and (natp i) (natp j) (natp k) (natp n)
                (< i n) (< j n) (<= k n))
           (unit-matchp (naive-prods-3 i j k n) (standard-list-3 i j k n) n))
  :induct (naive-prods-3 i j k n)
  :enable (naive-prods-3 standard-list-3 unit-matchp lform-mat)
  :disable (bit-mat-unit))

(defrule unit-matchp-of-naive-prods-2
  (implies (and (natp i) (natp j) (natp n)
                (< i n) (<= j n))
           (unit-matchp (naive-prods-2 i j n) (standard-list-2 i j n) n))
  :induct (naive-prods-2 i j n)
  :enable (naive-prods-2 standard-list-2))

(defrule unit-matchp-of-naive-prods-1
  (implies (and (natp i) (natp n) (<= i n))
           (unit-matchp (naive-prods-1 i n) (standard-list-1 i n) n))
  :induct (naive-prods-1 i n)
  :enable (naive-prods-1 standard-list-1))

(defrule unit-matchp-of-naive-prods
  (implies (natp n)
           (unit-matchp (naive-prods n) (standard-list n) n))
  :enable (naive-prods standard-list))

;;; Under the matching, the output table read off the products is the one
;;; triples-outs reads off the C factors.

(defruled prod-indices-when-unit-matchp
  (implies (and (unit-matchp p l n)
                (natp n) (natp i) (natp k) (< i n) (< k n))
           (equal (prod-indices p i k r n)
                  (c-indices l i k r)))
  :induct (list (prod-indices p i k r n) (unit-matchp p l n))
  :enable (unit-matchp prod-indices c-indices)
  :disable (mat-entry bit-mat-unit lform-mat mat-entry-of-bit-mat-unit)
  :hints (("Subgoal *1/2"
           :use ((:instance mat-entry-of-bit-mat-unit
                            (a i) (b k)
                            (i (cadr (cadr (car p))))
                            (j (caddr (caddr (car p))))
                            (m n) (n n))))))

(defruled naive-outs-row-when-unit-matchp
  (implies (and (unit-matchp p l n)
                (natp n) (natp i) (< i n) (natp c) (<= c n))
           (equal (naive-outs-row p i c n)
                  (triples-outs-row l i c n)))
  :induct (naive-outs-row p i c n)
  :enable (naive-outs-row triples-outs-row prod-indices-when-unit-matchp))

(defruled naive-outs-rows-when-unit-matchp
  (implies (and (unit-matchp p l n)
                (natp n) (natp c) (<= c n))
           (equal (naive-outs-rows p c n)
                  (triples-outs-rows l c n)))
  :induct (naive-outs-rows p c n)
  :enable (naive-outs-rows triples-outs-rows naive-outs-row-when-unit-matchp))

(defruled naive-outs-when-unit-matchp
  (implies (and (unit-matchp p l n) (natp n))
           (equal (naive-outs p n)
                  (triples-outs l n)))
  :enable (naive-outs triples-outs naive-outs-rows-when-unit-matchp))

;;; Under the matching, triples-from gives the same triples as for the
;;; products scheme-algo builds from the list.

(defruled triples-from-when-unit-matchp
  (implies (and (unit-matchp p l n)
                (summand-dim-listp l n)
                (natp n) (< 0 n))
           (equal (triples-from p outs r n)
                  (triples-from (scheme-prods l n) outs r n)))
  :induct (list (triples-from p outs r n) (unit-matchp p l n))
  :enable (unit-matchp triples-from scheme-prods)
  :disable (lform-mat mat-lform bit-mat-unit c-mat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 4: the theorems
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule algo-triples-of-naive-algo
  (implies (and (natp n) (< 0 n))
           (equal (algo-triples (naive-algo n) n)
                  (standard-list n)))
  :do-not-induct t
  :enable (algo-triples naive-algo scheme-algo)
  :disable (naive-prods naive-outs standard-list triples-from scheme-prods
            triples-outs summand-dim-listp)
  :use ((:instance naive-outs-when-unit-matchp
                   (p (naive-prods n)) (l (standard-list n)))
        (:instance triples-from-when-unit-matchp
                   (p (naive-prods n)) (l (standard-list n))
                   (outs (triples-outs (standard-list n) n)) (r 0))
        (:instance algo-triples-of-scheme-algo (l (standard-list n)))
        (:instance summand-dim-listp-when-summand-listp
                   (l (standard-list n)))))

(defrule algo-scheme-of-naive-algo
  (implies (natp n)
           (equal (algo-scheme (naive-algo n) n)
                  (standard-scheme n)))
  :cases ((zp n))
  :enable (algo-scheme insert-all-nonzero-is-insert-list
           standard-scheme-is-insert-list)
  :disable (algo-triples naive-algo standard-list insert-all-nonzero
            insert-list standard-scheme))

(defrule correct-schemep-of-naive-algo-scheme
  (implies (natp n)
           (correct-schemep (algo-scheme (naive-algo n) n) n))
  :disable (algo-scheme naive-algo))

(defrule algop-of-naive-algo
  (implies (and (natp n) (< 0 n))
           (algop (naive-algo n) n))
  :do-not-induct t
  :enable (algop naive-algo scheme-algo)
  :disable (naive-outs naive-prods standard-list triples-outs scheme-prods
            summand-dim-listp)
  :use ((:instance naive-outs-when-unit-matchp
                   (p (naive-prods n)) (l (standard-list n)))
        (:instance algop-of-scheme-algo (l (standard-list n)))
        (:instance summand-dim-listp-when-summand-listp
                   (l (standard-list n)))
        (:instance len-when-unit-matchp
                   (p (naive-prods n)) (l (standard-list n)))))

(defrule naive-algo-correct
  (implies (and (natp n) (< 0 n))
           (algo-correctp (naive-algo n) n))
  :do-not-induct t
  :expand ((algo-correctp (naive-algo n) n))
  :disable (naive-algo eval-algo eval-scheme scheme-sum algo-triples
            algo-scheme standard-list standard-scheme bit-mat-mul
            summand-dim-listp)
  :use ((:instance eval-algo-is-eval-scheme
                   (alg (naive-algo n))
                   (d (mv-nth 0 (algo-correctp-witness (naive-algo n) n)))
                   (f (mv-nth 1 (algo-correctp-witness (naive-algo n) n))))
        (:instance scheme-sum-of-algo-scheme (alg (naive-algo n)))
        (:instance eval-scheme-when-scheme-sum-equal
                   (l1 (standard-list n)) (l2 (standard-scheme n))
                   (d (mv-nth 0 (algo-correctp-witness (naive-algo n) n)))
                   (f (mv-nth 1 (algo-correctp-witness (naive-algo n) n))))
        (:instance eval-scheme-computes-product
                   (sch (standard-scheme n))
                   (d (mv-nth 0 (algo-correctp-witness (naive-algo n) n)))
                   (f (mv-nth 1 (algo-correctp-witness (naive-algo n) n))))
        (:instance summand-dim-listp-when-summand-listp
                   (l (standard-list n)))
        (:instance summand-dim-listp-when-summand-listp
                   (l (standard-scheme n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Executable evidence at n = 2 and n = 3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The textbook algorithm at n = 2 is in the class of *naive2*
;;; (matmul-expr.lisp), the same eight products in another order.
(assert-event (and (algop (naive-algo 2) 2)
                   (scheme-equiv (naive-algo 2) *naive2*)
                   (equal (algo-scheme (naive-algo 2) 2) (standard-scheme 2))
                   (equal (algo-scheme (naive-algo 3) 3) (standard-scheme 3))
                   (not (scheme-equiv (naive-algo 2) *strassen2*))))
