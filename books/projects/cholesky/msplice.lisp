;; Copyright (C) 2024 Carl Kwan
;;
;; Methods for "splicing" up matrices
;;
;; Summary:
;;      This file contains events for defining the matrix analogs for
;;      nthcdr and append. Presently, the only definitions included are
;;      - col-append, append two matrices column-wise
;;      - nth-col-cdr, get the nth final columns of a matrix
;;      - nth-row-cdr, get the nth final rows of a matrix
;;
;; Requires:
(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "workshops/2003/hendrix/support/mmult" :dir :system)

(set-induction-depth-limit 1)

(defthm col-count-col-cons
 (implies (col-cons-guard c m)
          (equal (col-count (col-cons c m))
                 (+ 1 (col-count m)))))

(defmacro col-append-guard (m n)
  `(and (matrixp ,m)
	(matrixp ,n)
	(or (m-emptyp ,m)
            (m-emptyp ,n)
	    (equal (row-count ,m) (row-count ,n)))))

(define col-append ((M matrixp) (N matrixp))
 :guard (col-append-guard m n)
 :returns mn
 :verify-guards nil
 (cond ((not (col-append-guard m n)) 
        (mzero (row-count n) (col-count n)))
       ((m-emptyp m) n)
       ((m-emptyp n) m)
       (t (col-cons (col-car m) 
                     (col-append (col-cdr M) N))))
 ///
 (more-returns
  (mn (implies (col-append-guard m n)
               (equal (row-count mn)
                      (if (m-emptyp m) (row-count n) (row-count m))))
      :name row-count-col-append)
  (mn (matrixp mn))
  (mn (implies (col-append-guard m n)
               (equal (col-count mn)
                      (+ (col-count m) (col-count n))))
      :name col-count-col-append))

 (verify-guards col-append)

 (defthm col-append-m-emptyp
  (implies (col-append-guard m n)
           (equal (m-emptyp (col-append m n)) 
                  (and (m-emptyp m) (m-emptyp n)))))

 (defthm col-append-def
  (implies (col-append-guard m n)
           (equal (col-append m n)
                  (if (m-emptyp m)
                      n
                      (col-cons (col-car m) (col-append (col-cdr m) n)))))
  :rule-classes ((:definition)))

 (encapsulate
  ()
  (local
   (defthm lemma-1
    (implies (and (matrixp m) (consp (row-car m)))
             (equal (append (row-car m) nil)
                    (row-car m)))))

  (local 
   (defthm lemma-2
    (implies (matrixp m)
             (equal (append (row i m) nil) (row i m)))))
            
  ;; Induction hint not necessary for ACL2 version 8.5. However, the ACL2
  ;; development version as of 2024-06-28 (and possibly earlier) requires 
  ;; this hint.
  (defthm row-of-col-append
   (implies (col-append-guard m n)
            (equal (row i (col-append m n))
                   (append (row i m) (row i n))))
   :hints (("Goal" :induct (col-append m n)))))

 (defthm sm*-col-append
  (implies (col-append-guard M N)
           (equal (sm* a (col-append M N))
                  (col-append (sm* a M) (sm* a N)))))

 (defthm col*-col-append
  (implies (and (col-append-guard M N) (col*-guard v M) (col*-guard v N))
           (equal (col* v (col-append M N))
                  (append (col* v M) (col* v N)))))

 (defthm mvectorp-of-col*-col-append
  (implies (and (col-append-guard M N) (col*-guard v M) (col*-guard v N))
           (mvectorp (col* v (col-append m n))))
  :rule-classes :type-prescription)

 (defthm len-of-col*-col-append
  (implies (and (col-append-guard M N) (col*-guard v M) (col*-guard v N))
           (equal (len (col* v (col-append m n))) (+ (col-count m) (col-count n)))))

 (defthm m*-col-append
  (implies (and (m*-guard A B) (col-append-guard B C) (m*-guard A C))
           (equal (m* A (col-append B C))
                  (col-append (m* A B) (m* A C))))
  :hints (("Goal" :in-theory (e/d (m*-by-col-def) (m*))))))
        ;; end of define col-append

;; Get final columns of a matrix
(define nth-col-cdr ((i natp) (m matrixp))
 :guard (< i (col-count m))
 :returns (rest matrixp)
 (if (not (matrixp m)) 
     (m-empty) 
     (if (zp i) 
         m 
         (nth-col-cdr (1- i) (col-cdr m))))
 ///
 (more-returns 
  (rest (implies (matrixp m)
                 (equal (col i m)
                        (col-car rest)))
        :name col-car-of-nth-col-cdr)
  (rest (implies (and (matrixp m) (< i 0)) (equal rest m))
        :name nth-col-cdr-<-0)
  (rest (implies (m-emptyp m) (m-emptyp rest))
        :name nth-col-cdr-when-emptyp)
  (rest (implies (not (integerp i)) (equal rest (if (matrixp m) m (m-empty))))
        :name nth-col-cdr-when-not-integer))

 (defthm nth-col-cdr-of-zero
  (equal (nth-col-cdr 0 m) (if (matrixp m) m (m-empty))))

 (defthm nth-col-cdr-of-col-cons
  (implies (col-cons-guard c m) 
           (equal (nth-col-cdr i (col-cons c m))
                  (if (zp i) (col-cons c m) (nth-col-cdr (1- i) m)))))

 (local (set-induction-depth-limit 2))

 ;; Induction hint not necessary for ACL2 version 8.5. However, the ACL2
 ;; development version as of 2024-06-28 (and possibly earlier) requires 
 ;; this hint.
 (defthm row-of-nth-col-cdr
  (implies (matrixp m)
           (equal (row j (nth-col-cdr i m))
                  (nthcdr i (row j m))))
  :hints (("Goal" :induct (nth-col-cdr i m)))))
;; end define

(in-theory (disable col-car-of-nth-col-cdr nth-col-cdr-<-0 nth-col-cdr-when-emptyp))

;; Get final rows of a matrix
(define nth-row-cdr ((i natp) (m matrixp))
 :guard (< i (row-count m))
 :returns (rest matrixp)
 :enabled t
 (if (not (matrixp m))
     (m-empty)
     (if (zp i)
         m
         (nth-row-cdr (1- i) (row-cdr m))))
 ///
 (more-returns 
  (rest (implies (matrixp m)
                 (equal (row i m)
                        (row-car rest)))
        :name row-car-of-nth-row-cdr)
  (rest (implies (and (matrixp m) (< i 0)) (equal rest m))
        :name nth-row-cdr-<-0)
  (rest (implies (m-emptyp m) (m-emptyp rest))
        :name nth-row-cdr-when-emptyp)
  (rest (implies (matrixp m)
                 (equal (col-count rest) (if (< (nfix i) (row-count m)) (col-count m) 0)))
        :name col-count-of-nth-row-cdr)
  (rest (implies (matrixp m) 
                 (equal (row-count rest) (if (< (nfix i) (row-count m)) (- (row-count m) (nfix i)) 0)))
        :name row-count-of-nth-row-cdr)
  (rest (implies (not (integerp i)) (equal rest (if (matrixp m) m (m-empty))))
        :name nth-row-cdr-when-not-integer))

 (defthm nth-row-cdr-of-zero
  (equal (nth-row-cdr 0 m) (if (matrixp m) m (m-empty))))


 (defthmd row-car-nth-row-cdr
  (implies (matrixp m)
           (equal (row-car (nth-row-cdr i m))
                  (row i m)))
  :hints (("Goal" :in-theory (enable nth-row-cdr row)))))
