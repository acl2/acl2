; algo-completeness.lisp -- completeness for the expression language: every
; correct bilinear matrix multiplication algorithm over F2, written in the
; language of matmul-expr.lisp, translates to a correct scheme.
;
; matmul-expr.lisp gives the language, its evaluator eval-algo, the
; translation algo-triples to a list of matrix triples, and the theorem
; that eval-algo equals eval-scheme of the triples.  completeness.lisp
; gives the theorem that a list of triples computing the product on all
; inputs is, once zero summands are dropped, a correct scheme.  This book
; composes the two.

(in-package "ACL2")

(include-book "matmul-expr")
(include-book "completeness")

;;; The algorithm is correct: it returns the product on all n x n inputs.

(defun-sk algo-correctp (alg n)
  (forall (d f)
          (implies (and (bit-matp d n n)
                        (bit-matp f n n))
                   (equal (eval-algo alg d f n)
                          (bit-mat-mul d f n)))))

;;; A correct algorithm translates to a list of triples that computes the
;;; product, by eval-algo-is-eval-scheme.

(defruled computes-productp-of-algo-triples
  (implies (and (algop alg n) (natp n) (algo-correctp alg n))
           (computes-productp (algo-triples alg n) n))
  :expand ((computes-productp (algo-triples alg n) n))
  :use ((:instance algo-correctp-necc
                   (d (mv-nth 0 (computes-productp-witness (algo-triples alg n) n)))
                   (f (mv-nth 1 (computes-productp-witness (algo-triples alg n) n)))))
  :disable (eval-algo eval-scheme algo-triples bit-mat-mul))

;;; Completeness for algorithms: (algo-scheme alg n) is the bag of the
;;; nonzero summands of the translation, and it is a correct scheme.

(defrule algo-to-correct-scheme
  (implies (and (algop alg n) (natp n) (< 0 n) (algo-correctp alg n))
           (correct-schemep (algo-scheme alg n) n))
  :enable (algo-scheme list-to-scheme computes-productp-of-algo-triples)
  :use ((:instance completeness (l (algo-triples alg n))))
  :disable (algo-triples))

;;; Its rank is at most the number of products of the algorithm.

(defrule scheme-rank-of-algo-scheme
  (implies (algop alg n)
           (<= (scheme-rank (algo-scheme alg n)) (len (car alg))))
  :enable (algo-scheme algo-triples list-to-scheme)
  :use ((:instance scheme-rank-of-list-to-scheme (l (algo-triples alg n)))))
