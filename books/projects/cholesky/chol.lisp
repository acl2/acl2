;; Copyright (C) 2024 Carl Kwan
;;
;; Summary:
;;      Defining Cholesky decomposition and proving its correctness.
;;
;;      Main definitions:
;;      - get-L, get the lower triangular part of a matrix
;;      - chol, logical Cholesky decomposition of a matrix
;;      - positive-definite-p, recognize a positive definite matrix
;;      - chol-fact-exists, posits the existance of a Cholesky decomposition
;;      - chol-exec, executable Cholesky decomposition using iterative square root
;;
;;      Main theorems:
;;      - chol-correctness, correctness of chol
;;      - cholesky-factorization-theorem, Cholesky Factorization Theorem
;;
;; Requires:
; cert_param: (uses-acl2r)
(in-package "ACL2")
(include-book "mlayers")
(include-book "msym")
(include-book "msplice")
(include-book "nonstd/nsa/sqrt" :dir :system)

(verify-guards acl2-sqrt)

;; Get lower triangular part of a matrix
;; Do not put 1s on the diagonal
;;  [ * * * * * ]     [ *         ]
;;  [ * * * * * ]     [ * *       ]
;;  [ * * * * * ] --> [ * * *     ]
;;      ...               ...
;;  [ * ... * * ]     [ * ... * * ]
(define get-L ((A matrixp))
 :measure (and (col-count A) (row-count A))
 :returns L
 :verify-guards nil
 (b* (((unless (matrixp A)) (m-empty))
      ((if (m-emptyp A)) A)
      ((if (m-emptyp (col-cdr A))) A)
      ((if (m-emptyp (row-cdr A)))
           (col-cons (col-car A) (mzero (row-count A)
                                        (1- (col-count A))))))
     (row-cons (cons (car (row-car A)) (vzero (1- (col-count A))))
               (col-cons (col-car (row-cdr A))
                         (get-L (row-cdr (col-cdr A))))))
 ///
 (more-returns
  ;; "Type" theorems
  (L (implies (matrixp A) (equal (row-count L) (row-count A)))
     :name row-count-get-L)
  (L (implies (matrixp A) (equal (col-count L) (col-count A)))
     :name col-count-get-L)
  (L (matrixp L))

  (L (equal (m-emptyp L) (or (m-emptyp A) (not (matrixp A))))
     :name m-emptyp-get-L)
  (L (implies (and (matrixp A) (not (m-emptyp (col-cdr A))))
              (not (m-emptyp (col-cdr L))))
     :name m-emptyp-col-cdr-get-L))

 ;; Necessary for verifying guards
 (defthm get-l-col-cons-def
  (implies (and (matrixp A)
                (not (m-emptyp (col-cdr A)))
                (not (m-emptyp (row-cdr A))))
           (equal (get-L A)
                  (col-cons (col-car A)
                            (row-cons (vzero (1- (col-count A)))
                                      (get-L (row-cdr (col-cdr A)))))))
  :hints (("Goal"
           :use ((:instance row-cons-col-cons
                            (m (get-L (row-cdr (col-cdr A))))
                            (l (cons (car (row-car A)) (vzero (1- (col-count A)))))
                            (k (col-car (row-cdr A))))))))
 (verify-guards get-L)

 ;; "Unwrapping" theorems
 (defthm col-car-get-L
  (implies (and (matrixp A))
           (equal (col-car (get-L A))
                  (col-car A))))

 (defthm row-car-get-L
  (implies (and (matrixp A) (not (m-emptyp A)))
           (equal (row-car (get-L A))
                  (cons (car (row-car A))
                        (vzero (1- (col-count A)))))))

 (defthm col-car-row-cdr-get-L
  (implies (and (matrixp A) (not (m-emptyp A)))
           (equal (col-car (row-cdr (get-L A)))
                  (col-car (row-cdr A)))))

;; Move "unwrapping" to inside get-L
(defthm col-cdr-row-cdr-get-L
 (implies (matrixp A)
          (equal (col-cdr (row-cdr (get-L A)))
                 (get-L (row-cdr (col-cdr A))))))

;; Move "unwrapping" to inside get-L
(defthm row-cdr-col-cdr-get-L
 (implies (matrixp A)
          (equal (row-cdr (col-cdr (get-L A)))
                 (get-L (row-cdr (col-cdr A)))))))
;; end define

;; Logical definition of Cholesky decomposition
;; Use of mbe here is for demonstrative purposes
(define chol ((A matrixp))
 :guard (and (equal (col-count A) (row-count A))
             (equal (mtrans A) A))
 :measure (and (col-count A) (row-count A))
 :verify-guards nil
 (mbe
 :logic
  (b* (;; BASE CASES
       ((unless (mbt (matrixp A))) (m-empty))    ;; If A not a matrix, return empty  
       ((if (m-emptyp A)) A)                     ;; If A empty, return A
       (alph (car (col-car A)))                  ;; alph := "top left" scalar in A
       ((unless (realp alph))                    ;; If alph not real, return a zero 
                (mzero (row-count A)             ;;   matrix of the same dimensions
                       (col-count A)))           ;;   as A
       ((if (<= alph 0))                         ;; If alph not positive, return a 
        (mzero (row-count A)                     ;;   zero matrix of the same 
               (col-count A)))                   ;;   dimensions as A
 
       ;; PARTITION
       (a21 (col-car (row-cdr A)))               ;; [ alph | a12 ] := A
       (a12 (row-car (col-cdr A)))               ;; [ ---------- ]
       (A22 (col-cdr (row-cdr A)))               ;; [ a21  | A22 ]
       (alph (acl2-sqrt alph))                   ;; alph := sqrt(alph)
 
       ;; BASE CASES
       ((if (m-emptyp (col-cdr A)))              ;; If A is a column, return
        (row-cons (list alph)                    ;;   [   1   ] [ a1 ] = [ a1 ] = A
                  (sm* (/ alph)                  ;;   [ a2/a1 ]          [ a2 ]   
                       (row-cdr A))))            ;;   [  ...  ]          [ ...]   
       ((if (m-emptyp (row-cdr A)))              ;; If A is a row, return 
        (row-cons (cons alph a12)                ;;   [ alph a12 ]
                  (m-empty)))
 
       ;; UPDATE
       (a21 (sv* (/ alph) a21))                  ;; a21 := a21 / alph
       (A22 (m+ A22 (sm* -1 (out-* a21 a21)))))  ;; A22 := A22 - a21 * a21T
 
      ;; RECURSE                                 ;;  [ alph | a12       ]
      (row-cons (cons alph a12)                  ;;  [ ---------------- ]
                (col-cons a21 (chol A22))))      ;;  [ a21  | CHOL(A22) ]  
 :exec
   (b* (((if (m-emptyp A)) A)
        (alph (car (col-car A)))
        ((unless (realp alph)) (mzero (row-count A) (col-count A)))
        ((if (<= alph 0))
         (mzero (row-count A)
                (col-count A)))
  
        (a21 (col-car (row-cdr A)))
        (a12 (row-car (col-cdr A)))
        (A22 (col-cdr (row-cdr A)))
        (alph (acl2-sqrt alph))
  
        ;; Base case:
        ;; m = [ a1 a2 ... ] = [ 1 ] [ a1 a2 ... ]
        ((if (or (m-emptyp (row-cdr A)) (m-emptyp (col-cdr A))))
         (row-cons (cons alph nil) (m-empty)))
        ;; Want to set:
        ;;  a21 = a21 / alpha
        ;;  A22 = A22 - out-*(a21, a12)
        (a21 (sv* (/ alph) a21))
        (A22 (m+ A22 (sm* -1 (out-* a21 a21)))))
       (row-cons (cons alph a12)
                 (col-cons a21 (chol A22)))))

 ///
 (defthm row-count-chol
  (implies (matrixp A)
           (equal (row-count (chol A)) (row-count A))))

 (defthm col-count-chol
  (implies (matrixp A)
           (equal (col-count (chol A)) (col-count A))))

 (defthm matrixp-of-chol (matrixp (chol A))
  :rule-classes :type-prescription)

 (verify-guards chol)

 (defthm m-emptyp-chol
  (equal (m-emptyp (chol A))
         (or (m-emptyp A) (not (matrixp A)))))

 ;; theorems about emptiness
 (defthm m-emptyp-row-cdr-/-col-cdr-chol
  (implies (and (matrixp A)
                (equal (col-count A) (row-count A))
                (or (not (m-emptyp (row-cdr A)))
                    (not (m-emptyp (col-cdr A)))))
           (and (not (m-emptyp (row-cdr (chol A))))
                (not (m-emptyp (col-cdr (chol A)))))))

 (defthm col-car-of-chol
  (b* ((a21 (col-car (row-cdr A)))
       (alph (car (row-car A))))
      (implies (and (realp alph) (< 0 alph) (matrixp A))
               (equal (col-car (chol A))
                      (cons (acl2-sqrt alph)
                            (sv* (/ (acl2-sqrt alph)) a21))))))

 (defthm col-car-row-cdr-chol
  (b* ((a21 (col-car (row-cdr A)))
       (alph (car (row-car A))))
      (implies (and (realp alph) (< 0 alph) (matrixp A))
               (equal (col-car (row-cdr (chol A)) )
                      (sv* (/ (acl2-sqrt alph)) a21))))))
;; end define

(local
 (defthm acl2-numberp-of-acl2-sqrt
  (implies (realp a)
           (acl2-numberp (acl2-sqrt a)))))

;; Formal derivation of 'right-looking' Cholesky algorithm
;; View A = LU as
;;
;; [ alph |   * ]   [ lam | 0 ] [ lam | l^T ]
;; [ ---------- ] = [ ------- ] [ --------- ]
;; [ a21  | A22 ]   [   l | L ] [   0 | L^T ]
;;
;; Our assumption was that A22 would be handled by the algorithm recursively:
;;      lam := sqrt(alph)
;;
(encapsulate
 nil

 (local (in-theory (enable chol)))

 (local
  (defthm car-row-car-col-car
   (equal (car (row-car A)) (car (col-car A)))))

 (local
  (defthm type-lemma
   (implies (and (matrixp A)
                 (not (m-emptyp (row-cdr A)))
                 (equal (col-count A) (row-count A)))
            (and (equal (row-count (row-cdr (chol A)))
                        (row-count (row-cdr A)))))))

 (local
  (defthm lemma-1
   (implies (and (matrixp A)
                 (not (m-emptyp (row-cdr A)) )
                 (equal (mtrans A) A)
                 (equal (col-count a) (row-count a)))
            (equal (row-cdr (col-cons (cons (acl2-sqrt (car (col-car a)))
                                            (sv* (/ (acl2-sqrt (car (col-car a))))
                                                 (col-car (row-cdr a))))
                                      (row-cons (vzero (col-count (col-cdr a)))
                                                (get-l (col-cdr (row-cdr (chol a)))))))
                   (col-cons (sv* (/ (acl2-sqrt (car (col-car a))))
                                  (col-car (row-cdr a)))
                             (get-l (col-cdr (row-cdr (chol a)))))))
   :hints (("goal" :use ((:instance col-cons-row-cons
                                    (l (cons (acl2-sqrt (car (col-car a)))
                                             (sv* (/ (acl2-sqrt (car (col-car a))))
                                                  (col-car (row-cdr a)))))
                                    (k (vzero (col-count (col-cdr a))))
                                    (m (get-l (col-cdr (row-cdr (chol a)))))))))))

 (local
  (defthmd lemma-2
   (b* ((alph    (car (row-car A)))
        (L       (get-L (chol A)))
        (Lt      (mtrans L)))
       (implies (and (< 0 alph)
                     (realp alph)
                     (matrixp A)
                     (not (m-emptyp (row-cdr A)) )
                     (equal (mtrans A) A)
                     (equal (col-count A) (row-count A)))
                (equal (row* (col-car Lt) (row-cdr L))
                       (col-car (row-cdr A)))))))

 (defthm chol-expand-layer
  (b* ((alph    (car (row-car A)))
       (L       (get-L (chol A)))
       (Lt      (mtrans L)))
      (implies (and (< 0 alph)
                    (realp alph)
                    (matrixp A)
                    (not (m-emptyp (col-cdr (row-cdr A))))
                    (not (m-emptyp (row-cdr (col-cdr A))))
                    (equal (mtrans A) A)
                    (equal (col-count A) (row-count A)))
               (equal (m* L Lt)
                      (row-cons
                       (row-car A)
                       (col-cons (col-car (row-cdr A))
                                 (m+ (out-* (col-car (row-cdr L))
                                            (row-car (col-cdr Lt)))
                                     (m* (col-cdr (row-cdr L))
                                         (row-cdr (col-cdr Lt)))))))))
  :hints (("Goal" :use ((:instance lemma-2))
                  :in-theory (disable mtrans get-l-col-cons-def)))))
;;; end encapsulate

(define positive-definite-p ((A matrixp))
 :guard (equal (col-count A) (row-count A))
 :measure (and (row-count A) (col-count A))
 :returns (pd booleanp)
 (b* (;; BASE CASES
      ((unless (matrixp A)) nil)                   ;; If A not a matrix, return empty  
      ((if (m-emptyp A)) t)                        ;; If A empty, return A

      ;; CHECK IF DETERMINANT SO FAR IS POSITIVE
      (alph (car (col-car A)))                     ;; alph := "top left" scalar in A
      ((unless (realp alph)) nil)                  ;; If alph not real, return nil
      ((unless (< 0 alph))   nil)                  ;; If alph not positive, return nil
                                                      
      ;; BASE CASES
      ((if (m-emptyp (row-cdr A))) t)              ;; If A is a row, return t                                                                 
      ((if (m-emptyp (col-cdr A))) t)              ;; If A is a column, return t
                                                   
      ;; PARTITION
      (a12     (row-car (col-cdr A)))              ;; [ alph | a12 ] := A                                   
      (a21     (col-car (row-cdr A)))              ;; [ ---------- ]                                        
      (A22     (col-cdr (row-cdr A)))              ;; [ a21  | A22 ] 

      ;; COMPUTE THE SCHUR COMPLEMENT
      (alph    (acl2-sqrt alph))                      
      (a12     (sv* (/ alph) a12))                 
      (a21     (sv* (/ alph) a21))                 
      (A22     (m+ A22 (sm* -1 (out-* a12 a21))))) ;; A22 := A22 - a12 * a21T / alph
     
     ;; RECURSE
     (positive-definite-p A22))                    ;; Check if A22 is positive definite 
 ///

 ;; N + M - N = M
 (local
  (defthm lemma-1
   (implies (and (matrixp m) (matrixp n) (m+-guard m n))
            (equal (m+ n (m+ m (sm* -1 n))) m))))

 (local
  (defthm mtrans-implies-a21-=-a12
   (implies (and (matrixp A)
                 (equal (row-count A) (col-count A))
                 (equal (mtrans A) A))
            (b* ((a21 (col-car (row-cdr A)))
                 (a12 (row-car (col-cdr A))))
                (equal a12 a21)))
   :hints (("Goal" :expand (mtrans A)))))

 (local (in-theory (enable chol rewrap-matrix)))

 (defthm chol-correctness
   (b* ((L       (get-L (chol A)))
        (Lt      (mtrans L)))
       (implies (and (positive-definite-p A)
                     (equal (mtrans A) A)
                     (equal (col-count A) (row-count A)))
                (equal (m* L Lt) A)))
   :hints (("Subgoal *1/5" :use ((:instance rewrap-matrix (m A)))))))

(define lower-tri-p ((A matrixp))
 :measure (and (col-count A) (row-count A))
 :returns (L? booleanp)
 (b* (((unless (matrixp A)) nil)
      ((if (m-emptyp A)) t)
      ((if (m-emptyp (col-cdr A))) t)
      ((if (m-emptyp (row-cdr A)))
           (equal (col-cdr A)
                  (mzero (row-count A) (1- (col-count A))))))
     (and (equal (row-car A)
                 (cons (car (row-car A))
                       (vzero (1- (col-count A)))))
          (lower-tri-p (row-cdr (col-cdr A)))))
 ///

 (defthm lower-tri-p-implies-matrixp
  (implies (lower-tri-p A) (matrixp A)))

 (defthm lower-tri-p-of-get-L
  (lower-tri-p (get-l A))
  :hints (("Goal" :in-theory (enable get-l)))))

(defun-sk chol-fact-exists (A)
  (exists (L) (and (lower-tri-p L)
                   (equal (m* L (mtrans L)) A))))

(defthm cholesky-factorization-theorem
 (implies (and (equal (mtrans A) A)
               (positive-definite-p A)
               (equal (col-count A) (row-count A)))
          (chol-fact-exists A))
 :hints (("Goal"
          :use ((:instance chol-fact-exists-suff (L (get-l (chol A))))))))

(in-theory (disable chol-expand-layer))


(verify-guards guess-num-iters-aux)
;(verify-guards iterate-sqrt-range :hints (("Goal" :cases ((realp high) (realp low)))))
;(verify-guards sqrt-iter)

;; To enable execution, we use sqrt-iter instead of acl2-sqrt. Here eps should
;; be "small" in order for sqrt-iter to be accurate.  Verify guards is set to
;; "nil" because iterate-sqrt-range seemingly cannot be guard verified, and
;; therefore neither can sqrt-iter.  Possible solutions: 
;; 	(1) define a guard-verified version of iterate-sqrt-range for use in an
;;          alternate sqrt function that is otherwise identical to sqrt-iter / 
;; 	    acl2-sqrt; 
;; 	(2) define another sqrt function using a different algorithm and prove
;; 	    it converges to acl2-sqrt. 
;; We perform (2) but keep sqrt-iter here as a placeholder for now (see ACL2
;; proof of Heron's method when available).
(define chol-exec ((A matrixp) (eps realp))
 :guard (and (equal (col-count A) (row-count A))
             (equal (mtrans A) A))
 :measure (and (col-count A) (row-count A))
 :verify-guards nil
 (mbe
  :logic
  (b* (;; BASE CASES
       ((unless (mbt (matrixp A))) (m-empty))         ;; If A not a matrix, return empty 
       ((if (m-emptyp A)) A)                          ;; If A empty, return A
       (alph (car (col-car A)))                       ;; alph := "top left" scalar in A
       ((unless (realp alph))                         ;; If alph not real, return a zero 
                (mzero (row-count A)                  ;;   matrix of the same dimensions
                       (col-count A)))                ;;   as A
       ((if (<= alph 0))                              ;; If alph not positive, return a 
        (mzero (row-count A)                          ;;   zero matrix of the same 
               (col-count A)))                        ;;   dimensions as A
 
       ;; PARTITION
       (a21 (col-car (row-cdr A)))                    ;; [ alph | a12 ] := A
       (a12 (row-car (col-cdr A)))                    ;; [ ---------- ]
       (A22 (col-cdr (row-cdr A)))                    ;; [ a21  | A22 ]
       (alph (sqrt-iter alph eps))                    ;; alph := sqrt(alph)
 
       ;; BASE CASES
       ((if (m-emptyp (col-cdr A)))                   ;; If A is a column, return
        (row-cons (list alph)                         ;;   [   1   ] [ a1 ] = [ a1 ] = A
                  (sm* (/ alph)                       ;;   [ a2/a1 ]          [ a2 ]   
                       (row-cdr A))))                 ;;   [  ...  ]          [ ...]   
       ((if (m-emptyp (row-cdr A)))                   ;; If A is a row, return 
        (row-cons (cons alph a12)                     ;;   [ alph a12 ]
                  (m-empty)))
 
       ;; UPDATE
       (a21 (sv* (/ alph) a21))                       ;; a21 := a21 / alph
       (A22 (m+ A22 (sm* -1 (out-* a21 a21)))))       ;; A22 := A22 - a21 * a21T
 
      ;; RECURSE                                      ;;  [ alph | a12       ]
      (row-cons (cons alph a12)                       ;;  [ ---------------- ]
                (col-cons a21 (chol-exec A22 eps))))  ;;  [ a21  | CHOL(A22) ]  
  :exec
   (b* (((if (m-emptyp A)) A)
        (alph (car (col-car A)))
        ((if (<= alph 0))
         (mzero (row-count A)
                (col-count A)))
  
        (a21 (col-car (row-cdr A)))
        (a12 (row-car (col-cdr A)))
        (A22 (col-cdr (row-cdr A)))
        (alph (sqrt-iter alph eps))
  
        ;; Base case:
        ;; m = [ a1 a2 ... ] = [ 1 ] [ a1 a2 ... ]
        ((if (or (m-emptyp (row-cdr A)) (m-emptyp (col-cdr A))))
         (row-cons (cons alph nil) (m-empty)))
        ;; Want to set:
        ;;  a21 = a21 / alpha
        ;;  A22 = A22 - out-*(a21, a12)
        (a21 (sv* (/ alph) a21))
        (A22 (m+ A22 (sm* -1 (out-* a21 a21)))))
       (row-cons (cons alph a12)
                 (col-cons a21 (chol-exec A22 eps))))))

