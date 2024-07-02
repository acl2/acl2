;; LU decomposition in ACL2
;; Summary:
;;      The main definitions in this file are 
;;      - get-U, which accesses the upper triangular part of a matrix
;;      - get-L, which accesses the lower unit trigular part of a matrix
;;      - lu, which computes the LU factorization of a matrix
;;      - nonsingular-leading-principal-submatrices-p, which recognizes
;;        matrices with nonsingular leading principal submatrices
;;
;;      The main theorems in this file is
;;      - lu-correctness-induction-step, which states
;;              (equal (m* L U) m)
;;        provided that m is an n x n matrix with n > 1 and the principle
;;        submatrix has an LU factorization
;;      - lu-correctness, which states 
;;              (equal (m* L U) m)
;;        provided that m is an n x n matrix with nonsingular leading principal
;;        submatrices
;; Requires:
(in-package "ACL2")
(include-book "mout")
(include-book "std/util/bstar" :dir :system)

(set-induction-depth-limit 2)

(defthmd rewrap-matrix
 (implies (and (matrixp m) (not (m-emptyp (row-cdr m))))
          (equal (row-cons (row-car m)
                           (col-cons (col-car (row-cdr m))
                                     (col-cdr (row-cdr m))))
                 m))
 :hints (("Goal" :use ((:instance col-cons-elim (m (row-cdr m)))
                       (:instance row-cons-elim)))))

;; Get upper triangular part of a matrix
;; for taking U in LU
;;  [ * * * * * ]     [ * * * * * ]
;;  [ * * * * * ]     [   * * * * ]
;;  [ * * * * * ] --> [     * * * ]
;;      ...               ...
;;  [ * ... * * ]     [         * ] 
(define get-U ((m matrixp))
 :measure (and (col-count m) (row-count m))
 :returns U
 :verify-guards nil
 (b* (((unless (matrixp m)) (m-empty))
      ((if (m-emptyp m)) m)
      ((if (m-emptyp (row-cdr m))) m)
      ((if (m-emptyp (col-cdr m))) (row-cons (row-car m) (mzero (1- (row-count m)) (col-count m)))))
     (row-cons (row-car m)
               (col-cons (vzero (1- (row-count m)))
                         (get-U (row-cdr (col-cdr m))))))
 ///
 (more-returns
  ;; "Type" theorems
  (U (implies (matrixp m) (equal (row-count U) (row-count m)))
     :name row-count-get-U)
  (U (implies (matrixp m) (equal (col-count U) (col-count m)))
     :name col-count-get-U)
  (U (matrixp U))

  (U (implies (and (matrixp m) (not (m-emptyp (col-cdr m))))
              (not (m-emptyp (col-cdr U))))
     :name m-emptyp-col-cdr-get-U)

  ;; "Unwrapping" theorems
  (U (implies (matrixp m) (equal (row-car U) (row-car m)))
     :name row-car-get-U)
  (U (equal (m-emptyp U) (or (m-emptyp m) (not (matrixp m))))
     :name m-emptyp-get-U)
  (U (implies (and (matrixp m) (not (m-emptyp m)))
              (equal (col-car U) (cons (car (row-car m))
                                       (vzero (1- (row-count m))))))
     :name col-car-get-U)
  (U (implies (and (matrixp m) (not (m-emptyp m)) (matrixp n))
              (equal (row* (col-car U) n)
                     (sv* (car (row-car m)) (col-car n))))
     :name row*-col-car-get-U)
  (U (implies (and (matrixp m))
              (equal (row-car (col-cdr U))
                     (row-car (col-cdr m))))
     :name row-car-col-cdr-get-U))

 ;; Move "unwrapping" to inside get-U
 (defthm row-cdr-col-cdr-get-U
  (implies (matrixp m)
           (equal (row-cdr (col-cdr (get-U m))) (get-U (row-cdr (col-cdr m))))))
 
 (defthm m-emptyp-row-cdr-col-cdr-get-u-when-square
  (implies (and (matrixp m) 
                (equal (col-count m) (row-count m))
                (or (not (m-emptyp (row-cdr m)))
                    (not (m-emptyp (col-cdr m)))))
           (and (not (m-emptyp (row-cdr (get-U m))))
                (not (m-emptyp (col-cdr (get-u m)))))))

 (verify-guards get-u))

;; Get lower triangular part of a matrix
;; for taking L in LU
;; Replace with 1s on the diagonal 
;;  [ * * * * * ]     [ 1         ]
;;  [ * * * * * ]     [ * 1       ]
;;  [ * * * * * ] --> [ * * 1     ]
;;      ...               ...
;;  [ * ... * * ]     [ * ... * 1 ] 
(define get-L ((m matrixp))
 :measure (and (col-count m) (row-count m))
 :returns L
 :verify-guards nil
 (b* (((unless (matrixp m)) (m-empty))
      ((if (m-emptyp m)) m)
      ((if (m-emptyp (row-cdr m))) (row-cons (cons 1 (vzero (1- (col-count m)))) (m-empty)))
      ((if (m-emptyp (col-cdr m))) (row-cons (cons 1 nil) (row-cdr m))))
     (row-cons (cons 1 (vzero (1- (col-count m))))
               (col-cons (col-car (row-cdr m))
                         (get-L (row-cdr (col-cdr m))))))
 ///
 (more-returns
  ;; "Type" theorems
  (L (implies (matrixp m) (equal (row-count L) (row-count m)))
     :name row-count-get-L)
  (L (implies (matrixp m) (equal (col-count L) (col-count m)))
     :name col-count-get-L)
  (L (matrixp L))

  (L (equal (m-emptyp L) (or (m-emptyp m) (not (matrixp m))))
     :name m-emptyp-L)
  (L (implies (and (matrixp m) (not (m-emptyp (col-cdr m))))
              (not (m-emptyp (col-cdr L))))
     :name m-emptyp-col-cdr-get-L)

  ;; "Unwrapping" theorems
  (L (implies (and (matrixp m))
              (equal (col-car (row-cdr L))
                     (col-car (row-cdr m))))
     :name col-car-row-cdr-get-L)
  (L (implies (and (matrixp m) (not (m-emptyp m))) 
              (equal (row-car L) (cons 1 (vzero (1- (col-count m))))))
     :name row-car-get-L))

 (defthm m-emptyp-row-cdr-get-l
  (implies (and (matrixp m) (not (m-emptyp (row-cdr m))))
           (not (m-emptyp (row-cdr (get-l m))))))

 (verify-guards get-L))

;; Move "unwrapping" to inside get-L
(defthm col-cdr-row-cdr-get-L
 (implies (matrixp m)
          (equal (col-cdr (row-cdr (get-L m))) (get-L (col-cdr (row-cdr m)))))
 :hints (("Goal" :in-theory (enable get-l))))

;; Typical "right-looking" LU factorization algorithm
;;
;; Idea sketch: View A = LU as
;;
;; [ alph | a12 ]   [ 1 | 0 ] [ alph | u ]
;; [ ---------- ] = [ ----- ] [ -------- ]
;; [ a21  | A22 ]   [ l | L ] [  0   | U ]
;;
;; Then we want to set:
;;      a21 := l                = a21 / alph
;;      A22 := LU - out-*(l, u) = A22 - out-*(a21, a12)
(define lu ((A matrixp))
 :measure (and (col-count A) (row-count A))
 :verify-guards nil
 (b* (((unless (matrixp A)) (m-empty))
      ((if (m-emptyp A)) A)
      (alph (car (col-car A)))
      ((if (zerop alph)) 
       (mzero (row-count A) 
              (col-count A)))
      ;; A = [ a1 ] = [   1   ] [ a1 ]
      ;;     [ a2 ]   [ a2/a1 ]
      ;;     [ ...]   [  ...  ]
      ((if (m-emptyp (col-cdr A))) 
       (row-cons (list alph) 
                 (sm* (/ alph) 
                      (row-cdr A))))
      ;; Base case:
      ;; m = [ a1 a2 ... ] = [ 1 ] [ a1 a2 ... ]
      ((if (m-emptyp (row-cdr A))) A)

      (a21 (col-car (row-cdr A)))
      (a12 (row-car (col-cdr A)))
      (A22 (col-cdr (row-cdr A)))
      ;; Want to set:
      ;;  a21 = a21 / alpha 
      ;;  A22 = A22 - out-*(a21, a12)
      (a21 (sv* (/ alph) a21))
      (A22 (m+ A22 (sm* -1 (out-* a21 a12)))))
     (row-cons (row-car A)
               (col-cons a21 (lu A22))))
 ///
 (defthm row-count-lu
  (implies (matrixp m)
           (equal (row-count (lu m)) (row-count m))))
 
 (defthm col-count-lu
  (implies (matrixp m)
           (equal (col-count (lu m)) (col-count m))))
 
 (defthm matrixp-of-lu
           (matrixp (lu m))
  :rule-classes :type-prescription)
 
 (verify-guards lu)

 (defthm m-emptyp-lu
  (equal (m-emptyp (lu m))
         (or (m-emptyp m) (not (matrixp m)))))

 (defthm m-emptyp-row-cdr-/-col-cdr-lu
  (implies (and (matrixp m) 
                (equal (col-count m) (row-count m))
                (or (not (m-emptyp (row-cdr m)))
                    (not (m-emptyp (col-cdr m)))))
           (and (not (m-emptyp (row-cdr (lu m))))
                (not (m-emptyp (col-cdr (lu m)))))))

 (defthm row-car-of-lu
  (implies (and (not (zerop (car (row-car m)))) (matrixp m))
           (equal (row-car (lu m)) (row-car m))))
 
 (defthm row-car-get-u-of-lu
  (implies (and (not (zerop (car (row-car m)))) (matrixp m))
           (equal (row-car (get-u (lu m)))   
                  (row-car m))))

 (defthm lu-correctness-base-case
  (b* ((alph (car (row-car m)))
       (LU   (lu m))
       (L    (get-l LU))
       (U    (get-u LU)))
      (implies (and (matrixp m) 
                    (not (zerop alph)) 
                    (equal (row-count m) 1))
               (equal (m* L U) m)))
  :hints (("Goal" :in-theory (enable lu)))))
;; end define

;; Formal derivation of 'right-looking' LU algorithm
;; Same idea as before: View A = LU as
;;
;; [ alph | a12 ]   [ 1 | 0 ] [ alph | u ]
;; [ ---------- ] = [ ----- ] [ -------- ]
;; [ a21  | A22 ]   [ l | L ] [  0   | U ]
;;
;; Our assumption was that A22 would be handled by the algorithm recursively:
;;      a21 := l                = a21 / alph
;;      A22 := LU - out-*(l, u) = A22 - out-*(a21, a12)
;;
;; This means that if A22 = LU, after the updates, then algorithm suceeds.
;;
(encapsulate
 ()

 (local (in-theory (enable lu)))

 ;; M = LU
 ;;
 ;; M = [  m1  ]
 ;;     [ ---- ]
 ;;     [  M'  ]
 ;;
 ;; L = [  l1  ]
 ;;     [ ---- ]
 ;;     [  L'  ]
 ;;
 ;; L * U = [   m1   ]
 ;;         [ ------ ]             
 ;;         [ L' * U ]
 (local (defthm LU-expand-one-row
  (b* ((L       (get-L (lu m)))
       (U       (get-U (lu m))))
      (implies (and (not (zerop (car (row-car m)))) (matrixp m) (not (m-emptyp m)))
               (equal (m* L U)
                      (row-cons (row-car m) 
                                (m* (row-cdr L) U)))))))

 ;; [ alph | a01 ]   [ 1 | 0 ] [ alph | u ]
 ;; [ ---------- ] = [ ----- ] [ -------- ]
 ;; [ a10  | A11 ]   [ l | L ] [  0   | U ]
 ;;
 ;; get-L ( LU (M) ) * get-U ( LU (M) ) =
 ;;
 ;;  [     m01     ]
 ;;  [ ----------- ]
 ;;  [  m10 | L*U  ]
 (local (defthm LU-expand-layer-one
  (b* ((alph    (car (col-car m)))
       (L       (get-L (lu m)))
       (U       (get-U (lu m))))
      (implies (and (matrixp m) 
                    (not (m-emptyp m))
                    (equal (col-count m) (row-count m))
                    (not (m-emptyp (col-cdr U)))
                    (not (m-emptyp (row-cdr L)))
                    (not (zerop alph)))
               (equal (m* L U)
                      (row-cons (row-car m)
                                (col-cons (col-car (row-cdr m))
                                          (m* (row-cdr L) (col-cdr U)))))))
  :hints (("Goal" :in-theory (disable col-car-get-u)))))

 ;; [ alph | a01 ]   [ 1 | 0 ] [ alph | u ]
 ;; [ ---------- ] = [ ----- ] [ -------- ]
 ;; [ a10  | A11 ]   [ l | L ] [  0   | U ]
 ;;
 ;; A11 = (l o u) + L * U
 ;; where o denotes the outer product
 (local 
  (defthm LU-expand-layer-two
   (b* ((L (get-L (lu m)))
        (U (get-U (lu m))))
       (implies (and (matrixp m) 
                     (not (m-emptyp m))
                     (equal (col-count m) (row-count m))
                     (m*-guard (col-cdr (row-cdr L)) (row-cdr (col-cdr U)))
                     (not (m-emptyp (row-cdr U)))
                     (not (m-emptyp (row-cdr L)))
                     (not (m-emptyp (col-cdr L))))
                (equal (m* (row-cdr L) (col-cdr U))
                       (m+ (out-* (col-car (row-cdr L)) (row-car (col-cdr U)))
                           (m* (col-cdr (row-cdr L)) (row-cdr (col-cdr U)))))))
   :hints (("Goal" :in-theory (e/d (m*-m*-by-out-* m*-by-out-*) (m* row-car-col-cdr-get-u row-cdr-col-cdr-get-u col-cdr-row-cdr-get-l))
                   :use ((:instance m*-m*-by-out-* 
                                    (m (col-cdr (row-cdr (get-L (lu m)))))
                                    (n (row-cdr (col-cdr (get-U (lu m)))))))))))

 ;; Combine the previous two theorems to state the equality
 ;; 
 ;; get-L ( LU (M) ) * get-U ( LU (M) ) =
 ;;
 ;;  [           m01          ]
 ;;  [ ---------------------- ]
 ;;  [  m10 | (l o u) + L * U ]
 ;;
 (local (defthm LU-expand-twice-1
   (b* ((alph    (car (col-car m)))
        (L       (get-L (lu m)))
        (U       (get-U (lu m))))
       (implies (and (matrixp m) 
                     (not (m-emptyp m))
                     (equal (col-count m) (row-count m))
                     (not (m-emptyp (col-cdr U)))
                     (not (m-emptyp (row-cdr L)))
                     (not (m-emptyp (col-cdr L)))
                     (not (zerop alph))
                     (m*-guard (col-cdr (row-cdr L)) (row-cdr (col-cdr U))))
                (equal (m* L U)
                       (row-cons (row-car m)
                                 (col-cons (col-car (row-cdr m))
                                           (m+ (out-* (col-car (row-cdr L)) (row-car (col-cdr U)))
                                               (m* (col-cdr (row-cdr L)) (row-cdr (col-cdr U)))))))))
   :hints (("Goal" :in-theory (disable row-cdr-col-cdr-get-u col-cdr-row-cdr-get-l)
                   :use ((:instance LU-expand-layer-two))))))

 ;; Exposing "recursive-ness" by replacing submatrices with calls to LU algorithm
 ;;
 ;; [ alph | a12 ]   [ 1 | 0 ] [ alph | u ]
 ;; [ ---------- ] = [ ----- ] [ -------- ]
 ;; [ a21  | A22 ]   [ l | L ] [  0   | U ]
 ;;
 ;; 
 ;; get-L ( LU (M) ) * get-U ( LU (M) ) =
 ;;
 ;;  [           m01        ]
 ;;  [ -------------------- ]
 ;;  [  m10 | (l o u) + A22 ]
 (local (defthm LU-expand-twice-2
  (b* ((alph    (car (col-car m)))
       (L       (get-L (lu m)))
       (U       (get-U (lu m)))
       (a21     (col-car (row-cdr m)))
       (a12     (row-car (col-cdr m)))
       (A22     (col-cdr (row-cdr m)))
       (a21     (sv* (/ alph) a21))
       (A22     (m+ A22 (sm* -1 (out-* a21 a12)))))
      (implies (and (matrixp m) 
                    (not (m-emptyp m))
                    (equal (col-count m) (row-count m))
                    (not (m-emptyp (col-cdr U)))
                    (not (m-emptyp (row-cdr L)))
                    (not (m-emptyp (col-cdr L)))
                    (consp a21)
                    (not (zerop alph))
                    (m*-guard (col-cdr (row-cdr L)) (row-cdr (col-cdr U))))
               (equal (m* L U)
                      (row-cons (row-car m)
                                (col-cons (col-car (row-cdr m))
                                          (m+ (out-* a21 a12)
                                              (m* (get-L (lu A22)) (get-U (lu A22)))))))))))

 ;; Some "type" lemmas that really should be handled by more sophisticated ACL2 mechanisms

 (local (defthm col-count-col-cdr-lu
  (implies (and (matrixp m) )
           (equal (col-count (col-cdr (lu m)))
                  (col-count (col-cdr m))))))

 (local (defthm row-count-row-cdr-lu
  (implies (and (matrixp m) )
           (equal (row-count (row-cdr (lu m)))
                  (row-count (row-cdr m))))))

 (local (in-theory (disable lu)))

 (local (defthm big-type-lemma
  (implies (and (matrixp m) 
                (equal (col-count m) (row-count m)) 
                (not (m-emptyp (row-cdr m)))) 
           (and (not (m-emptyp m))      
                (not (m-emptyp (col-cdr m)))
                (not (m-emptyp (lu m)))
                (not (m-emptyp (row-cdr (lu m))))
                (not (m-emptyp (col-cdr (lu m))))
                (not (m-emptyp (get-L (lu m))))
                (not (m-emptyp (get-U (lu m))))
                (not (m-emptyp (row-cdr (get-l (lu m)))))
                (not (m-emptyp (col-cdr (get-l (lu m)))))
                (not (m-emptyp (row-cdr (get-U (lu m)))))
                (not (m-emptyp (col-cdr (get-U (lu m)))))))
  :hints (("Goal" :in-theory (enable get-u get-l)
                  :use ((:instance col-count-get-u (m (lu m)))
                        (:instance row-count-get-u (m (lu m)))
                        (:instance col-count-get-l (m (lu m)))
                        (:instance row-count-get-l (m (lu m)))
                        (:instance m-emptyp-get-u (m (lu m))))))))

 (local (defthm lemma-1
  (implies (and (matrixp m) 
                (equal (col-count m) (row-count m)))
           (m*-guard (col-cdr (row-cdr (get-l (lu m)))) (row-cdr (col-cdr (get-u (lu m))))))))

 ;; N + M - N = M
 (local (defthm lemma-2
  (implies (and (matrixp m) (matrixp n) (m+-guard m n))
           (equal (m+ n (m+ m (sm* -1 n))) m))))

 (local (defthm lemma-3
  (b* ((alph    (car (col-car m)))
       (L       (get-L (lu m)))
       (U       (get-U (lu m)))
       (a21     (col-car (row-cdr m)))
       (a12     (row-car (col-cdr m)))
       (A22     (col-cdr (row-cdr m)))
       (a21     (sv* (/ alph) a21))
       (A22     (m+ A22 (sm* -1 (out-* a21 a12)))))
      (implies (and (matrixp m) 
                    (not (m-emptyp (row-cdr m)))
                    (equal (col-count m) (row-count m))
                    (consp a21)
                    (not (zerop alph))
                    (m*-guard (col-cdr (row-cdr L)) (row-cdr (col-cdr U)))
                    (equal (m* (get-L (lu A22)) (get-U (lu A22))) A22))
               (equal (m* L U) m)))
  :hints (("Goal" :use ((:instance rewrap-matrix))))))

 (defthm lu-correctness-induction-step
  (b* ((alph (car (col-car A)))
       (LU   (lu A))
       (L    (get-L LU))
       (U    (get-U LU))
       (a21  (col-car (row-cdr A)))
       (a12  (row-car (col-cdr A)))
       (A22  (col-cdr (row-cdr A)))
       (a21  (sv* (/ alph) a21))
       (A22  (m+ A22 (sm* -1 (out-* a21 a12)))))
      (implies (and (matrixp A) 
                    (not (m-emptyp (row-cdr A)))
                    (equal (col-count A) (row-count A))
                    (not (zerop alph))
                    (equal (m* (get-L (lu A22)) (get-U (lu A22))) A22))
               (equal (m* L U) A)))
  :hints (("Goal" :use ((:instance lemma-3 (m A)))))))
;; end of encapsulation

;; Nonsingular leading principal submatrices
;; Idea sketch: View A = LU as
;; [ alph | a12 ]   
;; [ ---------- ] 
;; [ a21  | A22 ]   
;;
;; Look at Schur complement:
;;      S = A22 - out-*(a21/alph,a12)
;;
;; and create:
;; [ alph | a12 ]   
;; [ ---------- ] 
;; [      | S   ]   
;; 
;; Asuming alph nonzero, S nonsingular iff A nonsingular so recurse along S
(define nonsingular-leading-principal-submatrices-p ((A matrixp))
 :measure (and (row-count A) (col-count A))
 (b* (((unless (matrixp A)) nil)
      ((if (m-emptyp A)) t)
      (alph (car (col-car A)))
      ((if (zerop alph)) nil)
      ((if (or (m-emptyp (row-cdr A))
               (m-emptyp (col-cdr A))))
       t)
      ;; Compute S = A22 - out-*(a21/alph,a12)
      (a21     (col-car (row-cdr A)))
      (a12     (row-car (col-cdr A)))
      (A22     (col-cdr (row-cdr A)))
      (a21/a   (sv* (/ alph) a21))
      (S       (m+ A22 (sm* -1 (out-* a21/a a12)))))
     (nonsingular-leading-principal-submatrices-p S))
 ///
 (defthm lu-correctness
  (b* ((LU (lu A))
       (L  (get-L LU))
       (U  (get-U LU)))
      (implies (and (equal (col-count A) (row-count A))
                    (nonsingular-leading-principal-submatrices-p A))
               (equal (m* L U) A)))))

;; Gaussian elimination
(defun ge (A) (get-U (lu A)))
