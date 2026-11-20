; rank245.lisp -- the rank-245 scheme for 7x7 matrix multiplication over F2
; given in Appendix A of the companion paper (Medley, Gokul, Luu and
; Manolios, ALENEX 2027) is a correct scheme, checked by evaluation, and is
; therefore reachable from the standard scheme by the main theorem.
;
; rank245-data.lisp holds the 245 summands as triples of 49-bit masks,
; decoded from the paper's Base32/zlib block by the script the paper gives;
; bit 7*i+j of a mask is entry [i,j] of the matrix.

(in-package "ACL2")

(include-book "main")
(include-book "standard")
(include-book "rank245-data")

;; A list of triples of masks.
(define mask-triple-listp (l)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (true-listp (car l))
         (equal (len (car l)) 3)
         (natp (first (car l)))
         (natp (second (car l)))
         (natp (third (car l)))
         (mask-triple-listp (cdr l)))))

;; Row i of the n x n matrix encoded by mask m: bit n*i + j is column j.
;; The row is built from column n-j down, so no shifting is needed.
(define mask-row ((m natp) (i natp) (j natp) (n natp))
  :guard (<= j n)
  :returns (r bit-list-p)
  (if (zp j)
      nil
    (cons (if (logbitp (+ (* n i) (- n j)) m) 1 0)
          (mask-row m i (1- j) n))))

(define mask-rows ((m natp) (i natp) (n natp))
  :guard (<= i n)
  :returns (a bit-list-listp)
  (if (zp i)
      nil
    (cons (mask-row m (- n i) n n)
          (mask-rows m (1- i) n))))

(define mask-mat ((m natp) (n natp))
  :returns (a bit-list-listp)
  (mask-rows m n n))

(define masks-scheme ((l mask-triple-listp) (n natp))
  :returns (sch obag::bagp)
  :verify-guards :after-returns
  (if (atom l)
      nil
    (obag::insert (summand (mask-mat (first (car l)) n)
                           (mask-mat (second (car l)) n)
                           (mask-mat (third (car l)) n))
                  (masks-scheme (cdr l) n))))

(defconst *rank245-scheme* (masks-scheme *rank245-masks* 7))

;; Checked by evaluation.
(defrule rank245-has-rank-245
  (equal (scheme-rank *rank245-scheme*) 245))

(defrule rank245-is-correct
  (correct-schemep *rank245-scheme* 7))

;; By the main theorem, the standard rank-343 scheme reaches it.  Pure
;; instantiation: the theory is kept minimal so that ACL2 does not try to
;; run main-path on the concrete schemes.
(defrule rank245-reachable-from-standard
  (b* ((path (main-path (standard-scheme 7) *rank245-scheme* 7))
       (res (apply-moves path (standard-scheme 7) 7)))
    (and (path-validp path (standard-scheme 7) 7)
         (equal res *rank245-scheme*)))
  :in-theory (union-theories (theory 'minimal-theory)
                             '((:executable-counterpart natp)
                               (:executable-counterpart <)
                               (:executable-counterpart not)))
  :use ((:instance flip-plus-connectivity (n 7) (sch (standard-scheme 7))
                   (sch2 *rank245-scheme*))
        (:instance correct-schemep-of-standard-scheme (n 7))
        rank245-is-correct))
