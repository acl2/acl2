; algo-class.lisp -- schemes as equivalence classes of algorithms.
;
; scheme-algo.lisp relates algorithms of the expression language (matmul-
; expr.lisp) to schemes in both directions: algo-scheme translates an
; algorithm to its scheme, scheme-algo converts a scheme to an algorithm, and
; translating a converted scheme gives the scheme back.  The translation is
; many-to-one: it sorts the summands, drops the zero ones, and forgets the
; order of the products, the syntax of the linear forms and the repeated
; output indices.  This book states the resulting picture in the vocabulary
; of equivalence relations, with ACL2's own defequiv and defcong.
;
; An algorithm carries its dimension: the output table has one row per row of
; the result, so (algo-dim alg) = (len (cdr alg)) is n whenever (algop alg n).
; Two algorithms are scheme-equiv when they have the same dimension and the
; same scheme.  This is an equivalence relation on all objects (defequiv), and
; its classes are the schemes: every scheme is the class of its converted algorithm
; (algo-scheme-of-scheme-algo).  The canonical representative of a class is
; (algo-canon alg), the algorithm of the scheme of alg; algo-canon respects
; scheme-equiv (defcong), is a fixed point of itself, is equivalent to its
; argument, and two algorithms are equivalent exactly when their canonical
; representatives are equal.  Equivalent algorithms compute the same function
; on every pair of inputs (eval-algo-when-scheme-equiv).
;
; Evidence at n = 2 at the end of the book: Strassen's algorithm, its variant
; with a repeated output index and its canonical representative are pairwise
; equivalent and have one canonical representative; the naive algorithm is
; not equivalent to them, although it is also correct.

(in-package "ACL2")

(include-book "scheme-algo")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 1: the dimension of an algorithm
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled len-when-outs-rowsp
  (implies (and (outs-rowsp outs r m n) (natp m))
           (equal (len outs) m))
  :induct (outs-rowsp outs r m n)
  :enable outs-rowsp)

(define algo-dim ((alg consp))
  :returns (n natp)
  (len (cdr alg))
  ///
  (defrule algo-dim-when-algop
    (implies (and (algop alg n) (natp n))
             (equal (algo-dim alg) n))
    :enable (algop len-when-outs-rowsp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 2: the equivalence relation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define scheme-equiv (a1 a2)
  :guard (and (consp a1) (consp a2)
              (algop a1 (algo-dim a1)) (algop a2 (algo-dim a2)))
  :returns (yes/no booleanp)
  (and (equal (algo-dim a1) (algo-dim a2))
       (equal (algo-scheme a1 (algo-dim a1))
              (algo-scheme a2 (algo-dim a2))))
  ///
  (defequiv scheme-equiv))

;;; Equivalent algorithms compute the same function.

(defrule eval-algo-when-scheme-equiv
  (implies (and (algop a1 n) (algop a2 n)
                (scheme-equiv a1 a2)
                (natp n) (< 0 n)
                (bit-matp d n n) (bit-matp f n n))
           (equal (eval-algo a1 d f n) (eval-algo a2 d f n)))
  :do-not-induct t
  :enable (scheme-equiv)
  :disable (eval-scheme scheme-sum algo-triples algo-scheme eval-algo
            scheme-sum-of-algo-scheme eval-algo-is-eval-scheme)
  :use ((:instance eval-algo-is-eval-scheme (alg a1))
        (:instance eval-algo-is-eval-scheme (alg a2))
        (:instance eval-scheme-when-scheme-sum-equal
                   (l1 (algo-triples a1 n)) (l2 (algo-triples a2 n)))
        (:instance scheme-sum-of-algo-scheme (alg a1))
        (:instance scheme-sum-of-algo-scheme (alg a2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 3: the canonical representative of a class
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule mat-triple-listp-when-summand-dim-listp
  (implies (summand-dim-listp l n)
           (mat-triple-listp l))
  :induct (summand-dim-listp l n))

(define algo-canon (alg)
  :guard (and (consp alg) (algop alg (algo-dim alg)) (< 0 (algo-dim alg)))
  :guard-hints (("Goal" :use ((:instance schemep-of-algo-scheme
                                         (n (algo-dim alg)))
                              (:instance mat-triple-listp-when-summand-dim-listp
                                         (l (algo-scheme alg (algo-dim alg)))
                                         (n (algo-dim alg))))))
  :returns (alg1 consp)
  (scheme-algo (algo-scheme alg (algo-dim alg)) (algo-dim alg))
  ///
  (defrule algop-of-algo-canon
    (implies (and (algop alg n) (natp n) (< 0 n))
             (algop (algo-canon alg) n))
    :disable (scheme-algo algo-scheme)
    :use (schemep-of-algo-scheme
          (:instance algop-of-scheme-algo (l (algo-scheme alg n)))))

  (defcong scheme-equiv equal (algo-canon alg) 1
    :hints (("Goal" :in-theory (enable scheme-equiv)))))

(defrule algo-dim-of-algo-canon
  (implies (and (algop alg n) (natp n) (< 0 n))
           (equal (algo-dim (algo-canon alg)) n))
  :disable (algo-canon)
  :use ((:instance algo-dim-when-algop (alg (algo-canon alg)))))

(defrule algo-scheme-of-algo-canon
  (implies (and (algop alg n) (natp n) (< 0 n))
           (equal (algo-scheme (algo-canon alg) n)
                  (algo-scheme alg n)))
  :enable algo-canon
  :disable (scheme-algo algo-scheme)
  :use schemep-of-algo-scheme)

(defrule scheme-equiv-of-algo-canon
  (implies (and (algop alg n) (natp n) (< 0 n))
           (scheme-equiv (algo-canon alg) alg))
  :enable scheme-equiv
  :disable (algo-canon algo-scheme))

(defrule algo-canon-of-algo-canon
  (implies (and (algop alg n) (natp n) (< 0 n))
           (equal (algo-canon (algo-canon alg))
                  (algo-canon alg)))
  :disable (algo-canon algo-scheme)
  :use ((:instance scheme-equiv-implies-equal-algo-canon-1
                   (alg (algo-canon alg)) (alg-equiv alg))))

(defruled scheme-equiv-when-algo-canon-equal
  (implies (and (algop a1 n) (algop a2 n) (natp n) (< 0 n)
                (equal (algo-canon a1) (algo-canon a2)))
           (scheme-equiv a1 a2))
  :enable scheme-equiv
  :disable (algo-canon algo-scheme algo-scheme-of-algo-canon)
  :use ((:instance algo-scheme-of-algo-canon (alg a1))
        (:instance algo-scheme-of-algo-canon (alg a2))))

(defrule scheme-equiv-iff-algo-canon-equal
  (implies (and (algop a1 n) (algop a2 n) (natp n) (< 0 n))
           (iff (scheme-equiv a1 a2)
                (equal (algo-canon a1) (algo-canon a2))))
  :disable (algo-canon algo-scheme)
  :use ((:instance scheme-equiv-implies-equal-algo-canon-1
                   (alg a1) (alg-equiv a2))
        scheme-equiv-when-algo-canon-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Executable evidence at n = 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Strassen, its variant with a repeated output index, and its canonical
;;; representative are three different algorithms in one class; the naive
;;; algorithm is in another class, although both classes are correct.
(assert-event (and (scheme-equiv *strassen2* *strassen2-rep*)
                   (scheme-equiv *strassen2* (algo-canon *strassen2*))
                   (not (equal *strassen2* *strassen2-rep*))
                   (not (equal *strassen2* (algo-canon *strassen2*)))
                   (equal (algo-canon *strassen2*) (algo-canon *strassen2-rep*))
                   (equal (algo-canon (algo-canon *strassen2*))
                          (algo-canon *strassen2*))))
(assert-event (and (not (scheme-equiv *strassen2* *naive2*))
                   (correct-schemep (algo-scheme *strassen2* 2) 2)
                   (correct-schemep (algo-scheme *naive2* 2) 2)))
