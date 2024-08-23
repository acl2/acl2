;; Copyright (C) 2024 Carl Kwan
;;
;; Some basic theorems about mtrans and symmetric matrices
;;
;; Requires:
(in-package "ACL2")
(include-book "mout")

(encapsulate
 nil

 (defthm row-car-mtrans
  (implies (matrixp A)
           (equal (row-car (mtrans A)) (col-car A))))

 (defthm col-car-mtrans
  (implies (matrixp A)
           (equal (col-car (mtrans A)) (row-car A))))

 (defthm row-car-col-cdr-mtrans
  (implies (and (matrixp A) (not (m-emptyp A)))
           (equal (row-car (col-cdr (mtrans A)))
                  (col-car (row-cdr A)))))

 (defthm mtrans-row-car-col-car
  (implies (and (matrixp A) (equal (mtrans A) A) (not (m-emptyp A)))
           (equal (row-car A) (col-car A)))
  :rule-classes :forward-chaining)

 (defthm col-cdr-row-cdr-mtrans
  (implies (and (matrixp A) (not (m-emptyp A)))
           (equal (col-cdr (row-cdr (mtrans A)))
                  (mtrans (row-cdr (col-cdr A))))))

 (defthm row-cdr-col-cdr-mtrans
  (implies (and (matrixp A) (not (m-emptyp A)))
           (equal (row-cdr (col-cdr (mtrans A)))
                  (mtrans (row-cdr (col-cdr A))))))

 (defthm sym-monotonicity
  (implies (and (matrixp A)
                (not (m-emptyp (row-cdr (col-cdr A))))
                (equal (mtrans A) A))
           (equal (mtrans (col-cdr (row-cdr A)))
                  (col-cdr (row-cdr A))))))
;; end encapsulate

(defthm sym-out-*-self
 (implies (mvectorp v) (equal (mtrans (out-* v v)) (out-* v v))))

(defthm sum-of-sym
 (implies (and (matrixp A) (matrixp B)
               (equal (mtrans A) A)
               (equal (mtrans B) B))
          (equal (mtrans (m+ A B)) (m+ A B))))

(defthm sm*-of-sym
 (implies (and (equal (mtrans A) A) (matrixp A))
          (equal (mtrans (sm* c A)) (sm* c A))))

(defthm m--of-sym
 (implies (and (equal (mtrans A) A) (matrixp A))
          (equal (mtrans (sm* -1 A)) (sm* -1 A))))

(defthm sym-of-syr1-update
 (implies (and (mvectorp v)
               (matrixp A)
               (equal (mtrans A) A)
               (equal (len v) (row-count A))
               (equal (col-count A) (row-count A)))
          (equal (mtrans (m+ A (out-* v v)))
                 (m+ A (out-* v v)))))

(defthm sym-of-syr1-update-minus
 (implies (and (mvectorp v)
               (matrixp A)
               (equal (mtrans A) A)
               (equal (len v) (row-count A))
               (equal (col-count A) (row-count A)))
          (equal (mtrans (m+ A (sm* -1 (out-* v v))))
                 (m+ A (sm* -1 (out-* v v))))))

(in-theory (disable sym-out-*-self
                    sum-of-sym
                    sm*-of-sym
                    m--of-sym
                    sym-of-syr1-update
                    sym-of-syr1-update-minus))
