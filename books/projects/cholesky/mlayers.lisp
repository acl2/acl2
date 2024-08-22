;; Copyright (C) 2024 Carl Kwan
;;
;; Theorems for partitioning a matrix along the first "layer"
;;
;; Requires:
(in-package "ACL2")
(include-book "mout")

(local (set-induction-depth-limit 1))

(defthmd rewrap-matrix
 (implies (and (matrixp m) (not (m-emptyp (row-cdr m))))
          (equal (row-cons (row-car m)
                           (col-cons (col-car (row-cdr m))
                                     (col-cdr (row-cdr m))))
                 m))
 :hints (("Goal" :use ((:instance col-cons-elim (m (row-cdr m)))
                       (:instance row-cons-elim)))))


(defthmd m*-expand-row
 (implies (and (m*-guard A B) (not (m-emptyp A)))
          (equal (m* A B)
                 (row-cons (col* (row-car A) B)
                           (m* (row-cdr A) B))))
  :hints (("Goal" :use ((:instance m* (M A) (N B))))))

(defthm m*-expand-layer
 (implies (and (matrixp A) (matrixp B)
               (equal (col-count A) (row-count B))
               (not (m-emptyp (row-cdr A))))
          (equal (m* A B)
                 (row-cons (col* (row-car A) B)
                           (col-cons (row* (col-car B) (row-cdr A))
                                     (m* (row-cdr A) (col-cdr B))))))
  :hints (("Goal" :use ((:instance m*-expand-row)))))

(encapsulate
 nil
 (local (in-theory (disable m+-comm)))
 (local
  (defthm m*-m*-by-out-*-cdr
   (implies (and (matrixp A)
                 (matrixp B)
                 (equal (col-count A) (row-count B))
                 (not (m-emptyp (col-cdr (row-cdr A))))
                 (not (m-emptyp (row-cdr (col-cdr B)))))
            (equal (m* (row-cdr A) (col-cdr B))
                   (m+ (out-* (col-car (row-cdr A)) (row-car (col-cdr B)))
                       (m* (col-cdr (row-cdr A)) (row-cdr (col-cdr B))))))
  :hints (("Goal" :use ((:instance m*-m*-by-out-* (m (row-cdr A)) (n (col-cdr B)))
                        (:instance m*-m*-by-out-*
                                   (m (col-cdr (row-cdr A)))
                                   (n (row-cdr (col-cdr B))))
                        (:instance m*-by-out-* (m (row-cdr A)) (n (col-cdr B))))))))

 (defthm m*-expand-2-layers
  (implies (and (matrixp A)
                (matrixp B)
                (equal (col-count A) (row-count B))
                (not (m-emptyp (col-cdr (row-cdr A))))
                (not (m-emptyp (row-cdr (col-cdr B)))))
           (equal (m* A B)
                  (row-cons (col* (row-car A) B)
                            (col-cons (row* (col-car B) (row-cdr A))
                                      (m+ (out-* (col-car (row-cdr A))
                                                 (row-car (col-cdr B)))
                                          (m* (col-cdr (row-cdr A))
                                              (row-cdr (col-cdr B))))))))
   :hints (("Goal" :use ((:instance m*-m*-by-out-* (m (row-cdr A)) (n (col-cdr B)))
                         (:instance m*-expand-layer)
                         (:instance m*-by-out-* (m (row-cdr A)) (n (col-cdr B))))
                   :in-theory (e/d nil (m*-m*-by-out-* m*-by-out-* m* m+))))))
