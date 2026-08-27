; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "primitives-evaluation-on-types")
(include-book "primitives-evaluation-on-ispaces")
(include-book "primitives-evaluation-tests")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation length:
; instantiation stage transitions and application of the final stage.

(defconst *tv-int* (type-value-base (base-type-int)))

(defconst *vec3*
  (expr-value-vector (list (iv 1) (iv 2) (iv 3))))

(defconst *mat23*
  (expr-value-vector
   (list (expr-value-vector (list (iv 1) (iv 2) (iv 3)))
         (expr-value-vector (list (iv 4) (iv 5) (iv 6))))))

; Type application: length applied to one atom type value.

(acl2::assert-equal
 (eval-primop-tfun (primop-value-length) *tv-int*)
 (expr-value-primop (primop-value-length-t *tv-int*)))

; Array type value where an atom one is expected.
(acl2::assert-event
 (reserrp (eval-primop-tfun (primop-value-length)
                            (make-type-value-array :elem *tv-int*
                                                   :dims (list 3)))))

; Ispace application: length-t applied to a dimension,
; then length-t-d applied to a shape.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-length-t *tv-int*)
                   (ispace-value-dim 2))
 (expr-value-primop (make-primop-value-length-t-d :tval *tv-int*
                                                  :dval 2)))

(acl2::assert-equal
 (eval-primop-ifun (make-primop-value-length-t-d :tval *tv-int*
                                                 :dval 2)
                   (ispace-value-shape (list 3)))
 (expr-value-primop (make-primop-value-length-t-d-s :tval *tv-int*
                                                    :dval 2
                                                    :sval (list 3))))

; A shape where a dimension is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-length-t *tv-int*)
                            (ispace-value-shape (list 3)))))

; A dimension where a shape is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (make-primop-value-length-t-d :tval *tv-int*
                                                          :dval 2)
                            (ispace-value-dim 3))))

; Application of the fully instantiated length to argument cells.

; The same 2x3 matrix under the two instantiation splits.

; With d = 2 and s = (3), the whole matrix is the cell, and its length is 2.
(acl2::assert-equal (prim-length *tv-int* 2 (list 3) *mat23*) (iv 2))

; With d = 3 and s = (), the cells are the rows, each of length 3
; (the assembly of the results [3 3] is done by the evaluator's lifting).
(acl2::assert-equal (prim-length *tv-int* 3 nil *vec3*) (iv 3))

; An empty vector has length 0.
(acl2::assert-equal
 (prim-length *tv-int* 0 nil (make-expr-value-vector-empty :dims nil
                                                           :elem *tv-int*))
 (iv 0))

; Cell dimensions not matching the instantiation.
(acl2::assert-event (reserrp (prim-length *tv-int* 3 nil *mat23*)))
(acl2::assert-event (reserrp (prim-length *tv-int* 2 nil *vec3*)))
(acl2::assert-event (reserrp (prim-length *tv-int* 0 nil (iv 5))))

; Via eval-primop-fun-fo.

(acl2::assert-equal
 (eval-primop-fun-fo (make-primop-value-length-t-d-s :tval *tv-int*
                                                     :dval 3
                                                     :sval nil)
                     *vec3*)
 (iv 3))

; Wrong number of argument cells:
; one cell already yields a final result,
; not an operation applicable to another cell.
(acl2::assert-event
 (not (expr-value-case
       (eval-primop-fun-fo (make-primop-value-length-t-d-s :tval *tv-int*
                                                           :dval 3
                                                           :sval nil)
                           *vec3*)
       :primop)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation head:
; instantiation stage transitions and application of the final stage.

(defconst *vec1*
  (expr-value-vector (list (iv 1))))

; Type application: head applied to one atom type value.

(acl2::assert-equal
 (eval-primop-tfun (primop-value-head) *tv-int*)
 (expr-value-primop (primop-value-head-t *tv-int*)))

; Array type value where an atom one is expected.
(acl2::assert-event
 (reserrp (eval-primop-tfun (primop-value-head)
                            (make-type-value-array :elem *tv-int*
                                                   :dims (list 3)))))

; Ispace application: head-t applied to a dimension,
; then head-t-d applied to a shape.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-head-t *tv-int*)
                   (ispace-value-dim 1))
 (expr-value-primop (make-primop-value-head-t-d :tval *tv-int*
                                                :dval 1)))

(acl2::assert-equal
 (eval-primop-ifun (make-primop-value-head-t-d :tval *tv-int*
                                               :dval 1)
                   (ispace-value-shape (list 3)))
 (expr-value-primop (make-primop-value-head-t-d-s :tval *tv-int*
                                                  :dval 1
                                                  :sval (list 3))))

; A shape where a dimension is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-head-t *tv-int*)
                            (ispace-value-shape (list 3)))))

; A dimension where a shape is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (make-primop-value-head-t-d :tval *tv-int*
                                                        :dval 1)
                            (ispace-value-dim 3))))

; Application of the fully instantiated head to argument cells.

; With d = 1 and s = (3), the whole matrix is the cell,
; and its head is the first row.
(acl2::assert-equal
 (prim-head *tv-int* 1 (list 3) *mat23*)
 (expr-value-vector (list (iv 1) (iv 2) (iv 3))))

; With d = 2 and s = (), the cells are vectors of length 3,
; and the head of a cell is its first element.
(acl2::assert-equal (prim-head *tv-int* 2 nil *vec3*) (iv 1))

; A one-element vector has a head.
(acl2::assert-equal (prim-head *tv-int* 0 nil *vec1*) (iv 1))

; Cell dimensions not matching the instantiation.
(acl2::assert-event (reserrp (prim-head *tv-int* 2 nil *mat23*)))
(acl2::assert-event (reserrp (prim-head *tv-int* 1 nil *vec3*)))
(acl2::assert-event (reserrp (prim-head *tv-int* 0 nil (iv 5))))

; Via eval-primop-fun-fo.

(acl2::assert-equal
 (eval-primop-fun-fo (make-primop-value-head-t-d-s :tval *tv-int*
                                                   :dval 2
                                                   :sval nil)
                     *vec3*)
 (iv 1))

; Wrong number of argument cells:
; one cell already yields a final result,
; not an operation applicable to another cell.
(acl2::assert-event
 (not (expr-value-case
       (eval-primop-fun-fo (make-primop-value-head-t-d-s :tval *tv-int*
                                                         :dval 2
                                                         :sval nil)
                           *vec3*)
       :primop)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation tail:
; instantiation stage transitions and application of the final stage.

; Type application: tail applied to one atom type value.

(acl2::assert-equal
 (eval-primop-tfun (primop-value-tail) *tv-int*)
 (expr-value-primop (primop-value-tail-t *tv-int*)))

; Array type value where an atom one is expected.
(acl2::assert-event
 (reserrp (eval-primop-tfun (primop-value-tail)
                            (make-type-value-array :elem *tv-int*
                                                   :dims (list 3)))))

; Ispace application: tail-t applied to a dimension,
; then tail-t-d applied to a shape.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-tail-t *tv-int*)
                   (ispace-value-dim 1))
 (expr-value-primop (make-primop-value-tail-t-d :tval *tv-int*
                                                :dval 1)))

(acl2::assert-equal
 (eval-primop-ifun (make-primop-value-tail-t-d :tval *tv-int*
                                               :dval 1)
                   (ispace-value-shape (list 3)))
 (expr-value-primop (make-primop-value-tail-t-d-s :tval *tv-int*
                                                  :dval 1
                                                  :sval (list 3))))

; A shape where a dimension is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-tail-t *tv-int*)
                            (ispace-value-shape (list 3)))))

; A dimension where a shape is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (make-primop-value-tail-t-d :tval *tv-int*
                                                        :dval 1)
                            (ispace-value-dim 3))))

; Application of the fully instantiated tail to argument cells.

; With d = 1 and s = (3), the whole matrix is the cell,
; and its tail is the matrix without the first row.
(acl2::assert-equal
 (prim-tail *tv-int* 1 (list 3) *mat23*)
 (expr-value-vector
  (list (expr-value-vector (list (iv 4) (iv 5) (iv 6))))))

; With d = 2 and s = (), the cells are vectors of length 3,
; and the tail of a cell is the vector without the first element.
(acl2::assert-equal
 (prim-tail *tv-int* 2 nil *vec3*)
 (expr-value-vector (list (iv 2) (iv 3))))

; A one-element vector has an empty tail.
(acl2::assert-equal
 (prim-tail *tv-int* 0 nil *vec1*)
 (make-expr-value-vector-empty :dims nil :elem *tv-int*))

; Cell dimensions not matching the instantiation.
(acl2::assert-event (reserrp (prim-tail *tv-int* 2 nil *mat23*)))
(acl2::assert-event (reserrp (prim-tail *tv-int* 1 nil *vec3*)))
(acl2::assert-event (reserrp (prim-tail *tv-int* 0 nil (iv 5))))

; Via eval-primop-fun-fo.

(acl2::assert-equal
 (eval-primop-fun-fo (make-primop-value-tail-t-d-s :tval *tv-int*
                                                   :dval 2
                                                   :sval nil)
                     *vec3*)
 (expr-value-vector (list (iv 2) (iv 3))))

; Wrong number of argument cells:
; one cell already yields a final result,
; not an operation applicable to another cell.
(acl2::assert-event
 (not (expr-value-case
       (eval-primop-fun-fo (make-primop-value-tail-t-d-s :tval *tv-int*
                                                         :dval 2
                                                         :sval nil)
                           *vec3*)
       :primop)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation append:
; instantiation stage transitions and application of the final stage.

; Type application: append applied to one atom type value.

(acl2::assert-equal
 (eval-primop-tfun (primop-value-append) *tv-int*)
 (expr-value-primop (primop-value-append-t *tv-int*)))

;; ; Wrong number of type values.
;; (acl2::assert-event
;;  (reserrp (eval-primop-tfun (primop-value-append)
;;                             (list *tv-int* *tv-int*))))

; Array type value where an atom one is expected.
(acl2::assert-event
 (reserrp (eval-primop-tfun (primop-value-append)
                            (make-type-value-array :elem *tv-int*
                                                   :dims (list 3)))))

; Ispace application: append-t applied to two dimensions and a shape.

;; (acl2::assert-equal
;;  (eval-primop-ifun (primop-value-append-t *tv-int*)
;;                    (list (ispace-value-dim 2)
;;                          (ispace-value-dim 3)
;;                          (ispace-value-shape (list 3))))
;;  (expr-value-primop (make-primop-value-append-t-m-n-s :tval *tv-int*
;;                                                       :mval 2
;;                                                       :nval 3
;;                                                       :sval (list 3))))

;; ; Dimensions and shape in the wrong order.
;; (acl2::assert-event
;;  (reserrp (eval-primop-ifun (primop-value-append-t *tv-int*)
;;                             (list (ispace-value-shape (list 3))
;;                                   (ispace-value-dim 2)
;;                                   (ispace-value-dim 3)))))

;; ; Wrong number of ispace values.
;; (acl2::assert-event
;;  (reserrp (eval-primop-ifun (primop-value-append-t *tv-int*)
;;                             (list (ispace-value-dim 2)
;;                                   (ispace-value-dim 3)))))

; Application of the fully instantiated append to argument cells.

; With m = 3, n = 1, and s = (), the cells are vectors,
; and appending them concatenates their elements.
(acl2::assert-equal
 (prim-append *tv-int* 3 1 nil *vec3* *vec1*)
 (expr-value-vector (list (iv 1) (iv 2) (iv 3) (iv 1))))

; With m = 2, n = 2, and s = (3), the cells are 2x3 matrices,
; and appending them stacks their rows into a 4x3 matrix.
(acl2::assert-equal
 (prim-append *tv-int* 2 2 (list 3) *mat23* *mat23*)
 (expr-value-vector
  (list (expr-value-vector (list (iv 1) (iv 2) (iv 3)))
        (expr-value-vector (list (iv 4) (iv 5) (iv 6)))
        (expr-value-vector (list (iv 1) (iv 2) (iv 3)))
        (expr-value-vector (list (iv 4) (iv 5) (iv 6))))))

; Appending an empty vector is the identity.
(acl2::assert-equal
 (prim-append *tv-int* 0 3 nil
              (make-expr-value-vector-empty :dims nil :elem *tv-int*)
              *vec3*)
 *vec3*)
(acl2::assert-equal
 (prim-append *tv-int* 3 0 nil
              *vec3*
              (make-expr-value-vector-empty :dims nil :elem *tv-int*))
 *vec3*)

; Appending two empty vectors yields an empty vector.
(acl2::assert-equal
 (prim-append *tv-int* 0 0 nil
              (make-expr-value-vector-empty :dims nil :elem *tv-int*)
              (make-expr-value-vector-empty :dims nil :elem *tv-int*))
 (make-expr-value-vector-empty :dims nil :elem *tv-int*))

; Cell dimensions not matching the instantiation.
(acl2::assert-event (reserrp (prim-append *tv-int* 2 3 nil *vec3* *vec3*)))
(acl2::assert-event (reserrp (prim-append *tv-int* 3 3 nil *vec3* *mat23*)))
(acl2::assert-event (reserrp (prim-append *tv-int* 0 0 nil (iv 5) (iv 5))))

; Via eval-primop-fun-fo* and eval-primop-fun-fo.

(acl2::assert-equal
 (eval-primop-fun-fo* (make-primop-value-append-t-m-n-s :tval *tv-int*
                                                        :mval 3
                                                        :nval 1
                                                        :sval nil)
                      *vec3* *vec1*)
 (expr-value-vector (list (iv 1) (iv 2) (iv 3) (iv 1))))

; One argument cell yields the next stage (partial application).
(acl2::assert-equal
 (eval-primop-fun-fo (make-primop-value-append-t-m-n-s :tval *tv-int*
                                                       :mval 3
                                                       :nval 1
                                                       :sval nil)
                     *vec3*)
 (expr-value-primop (make-primop-value-append-t-m-n-s-x :tval *tv-int*
                                                        :mval 3
                                                        :nval 1
                                                        :sval nil
                                                        :xval *vec3*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation reverse:
; instantiation stage transitions and application of the final stage.

; Type application: reverse applied to one atom type value.

(acl2::assert-equal
 (eval-primop-tfun (primop-value-reverse) *tv-int*)
 (expr-value-primop (primop-value-reverse-t *tv-int*)))

;; ; Wrong number of type values.
;; (acl2::assert-event
;;  (reserrp (eval-primop-tfun (primop-value-reverse)
;;                             (list *tv-int* *tv-int*))))

; Array type value where an atom one is expected.
(acl2::assert-event
 (reserrp (eval-primop-tfun (primop-value-reverse)
                            (make-type-value-array :elem *tv-int*
                                                   :dims (list 3)))))

; Ispace application: reverse-t applied to a dimension and a shape.

;; (acl2::assert-equal
;;  (eval-primop-ifun (primop-value-reverse-t *tv-int*)
;;                    (list (ispace-value-dim 2)
;;                          (ispace-value-shape (list 3))))
;;  (expr-value-primop (make-primop-value-reverse-t-d-s :tval *tv-int*
;;                                                      :dval 2
;;                                                      :sval (list 3))))

;; ; Dimension and shape in the wrong order.
;; (acl2::assert-event
;;  (reserrp (eval-primop-ifun (primop-value-reverse-t *tv-int*)
;;                             (list (ispace-value-shape (list 3))
;;                                   (ispace-value-dim 2)))))

;; ; Wrong number of ispace values.
;; (acl2::assert-event
;;  (reserrp (eval-primop-ifun (primop-value-reverse-t *tv-int*)
;;                             (list (ispace-value-dim 2)))))

; Application of the fully instantiated reverse to argument cells.

; With d = 3 and s = (), the cells are vectors,
; and reversing a cell reverses its elements.
(acl2::assert-equal
 (prim-reverse *tv-int* 3 nil *vec3*)
 (expr-value-vector (list (iv 3) (iv 2) (iv 1))))

; With d = 2 and s = (3), the whole matrix is the cell,
; and reversing it reverses the order of its rows.
(acl2::assert-equal
 (prim-reverse *tv-int* 2 (list 3) *mat23*)
 (expr-value-vector
  (list (expr-value-vector (list (iv 4) (iv 5) (iv 6)))
        (expr-value-vector (list (iv 1) (iv 2) (iv 3))))))

; A one-element vector is its own reverse.
(acl2::assert-equal (prim-reverse *tv-int* 1 nil *vec1*) *vec1*)

; An empty vector is its own reverse.
(acl2::assert-equal
 (prim-reverse *tv-int* 0 nil
               (make-expr-value-vector-empty :dims nil :elem *tv-int*))
 (make-expr-value-vector-empty :dims nil :elem *tv-int*))

; Cell dimensions not matching the instantiation.
(acl2::assert-event (reserrp (prim-reverse *tv-int* 2 nil *vec3*)))
(acl2::assert-event (reserrp (prim-reverse *tv-int* 3 nil *mat23*)))
(acl2::assert-event (reserrp (prim-reverse *tv-int* 0 nil (iv 5))))

; Via eval-primop-fun-fo.

(acl2::assert-equal
 (eval-primop-fun-fo (make-primop-value-reverse-t-d-s :tval *tv-int*
                                                      :dval 3
                                                      :sval nil)
                     *vec3*)
 (expr-value-vector (list (iv 3) (iv 2) (iv 1))))

; Wrong number of argument cells:
; one cell already yields a final result,
; not an operation applicable to another cell.
(acl2::assert-event
 (not (expr-value-case
       (eval-primop-fun-fo (make-primop-value-reverse-t-d-s :tval *tv-int*
                                                            :dval 3
                                                            :sval nil)
                           *vec3*)
       :primop)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation index:
; instantiation stage transitions and application of the final stage.

; Type application: index applied to one atom type value.

(acl2::assert-equal
 (eval-primop-tfun (primop-value-index) *tv-int*)
 (expr-value-primop (primop-value-index-t *tv-int*)))

; Ispace application: index-t applied to a dimension.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-index-t *tv-int*)
                   (ispace-value-dim 3))
 (expr-value-primop (make-primop-value-index-t-m :tval *tv-int*
                                                 :mval 3)))

; A shape where a dimension is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-index-t *tv-int*)
                            (ispace-value-shape (list 3)))))

; Application of the fully instantiated index to argument cells.

(acl2::assert-equal (prim-index *tv-int* 3 *vec3* (iv 0)) (iv 1))
(acl2::assert-equal (prim-index *tv-int* 3 *vec3* (iv 2)) (iv 3))

; Index out of bounds.
(acl2::assert-event (reserrp (prim-index *tv-int* 3 *vec3* (iv 3))))
(acl2::assert-event (reserrp (prim-index *tv-int* 3 *vec3* (iv -1))))

; Cell dimensions not matching the instantiation.
(acl2::assert-event (reserrp (prim-index *tv-int* 2 *vec3* (iv 0))))
(acl2::assert-event (reserrp (prim-index *tv-int* 3 *mat23* (iv 0))))

; Non-integer index.
(acl2::assert-event (reserrp (prim-index *tv-int* 3 *vec3* (bv t))))

; Via eval-primop-fun-fo*.

(acl2::assert-equal
 (eval-primop-fun-fo* (make-primop-value-index-t-m :tval *tv-int*
                                                   :mval 3)
                      *vec3* (iv 1))
 (iv 2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation index2d:
; instantiation stage transitions and application of the final stage.

; Type application: index2d applied to one atom type value.

(acl2::assert-equal
 (eval-primop-tfun (primop-value-index2d) *tv-int*)
 (expr-value-primop (primop-value-index2d-t *tv-int*)))

; Ispace application: index2d-t applied to a dimension,
; then index2d-t-m applied to another dimension.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-index2d-t *tv-int*)
                   (ispace-value-dim 2))
 (expr-value-primop (make-primop-value-index2d-t-m :tval *tv-int*
                                                   :mval 2)))

(acl2::assert-equal
 (eval-primop-ifun (make-primop-value-index2d-t-m :tval *tv-int*
                                                  :mval 2)
                   (ispace-value-dim 3))
 (expr-value-primop (make-primop-value-index2d-t-m-n :tval *tv-int*
                                                     :mval 2
                                                     :nval 3)))

; Application of the fully instantiated index2d to argument cells.

(acl2::assert-equal
 (prim-index2d *tv-int* 2 3 *mat23*
               (expr-value-vector (list (iv 0) (iv 0))))
 (iv 1))
(acl2::assert-equal
 (prim-index2d *tv-int* 2 3 *mat23*
               (expr-value-vector (list (iv 1) (iv 2))))
 (iv 6))

; Indices out of bounds.
(acl2::assert-event
 (reserrp (prim-index2d *tv-int* 2 3 *mat23*
                        (expr-value-vector (list (iv 2) (iv 0))))))
(acl2::assert-event
 (reserrp (prim-index2d *tv-int* 2 3 *mat23*
                        (expr-value-vector (list (iv 0) (iv 3))))))
(acl2::assert-event
 (reserrp (prim-index2d *tv-int* 2 3 *mat23*
                        (expr-value-vector (list (iv -1) (iv 0))))))

; Index vector of the wrong length.
(acl2::assert-event
 (reserrp (prim-index2d *tv-int* 2 3 *mat23*
                        (expr-value-vector (list (iv 0))))))

; Cell dimensions not matching the instantiation.
(acl2::assert-event
 (reserrp (prim-index2d *tv-int* 3 2 *mat23*
                        (expr-value-vector (list (iv 0) (iv 0))))))
(acl2::assert-event
 (reserrp (prim-index2d *tv-int* 2 3 *vec3*
                        (expr-value-vector (list (iv 0) (iv 0))))))

; Via eval-primop-fun-fo*.

(acl2::assert-equal
 (eval-primop-fun-fo* (make-primop-value-index2d-t-m-n :tval *tv-int*
                                                       :mval 2
                                                       :nval 3)
                      *mat23*
                      (expr-value-vector (list (iv 1) (iv 0))))
 (iv 4))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation sum:
; instantiation stage transition and application of the final stage.
; This operation has no type stage,
; because it is monomorphic in the element type.

; Ispace application: sum applied to a shape.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-sum) (ispace-value-shape (list 3)))
 (expr-value-primop (make-primop-value-sum-s :sval (list 3))))

; A dimension where a shape is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-sum) (ispace-value-dim 3))))

; Application of the fully instantiated operation.

; Summing a vector.
(acl2::assert-equal (prim-sum (list 3) *vec3*) (iv 6))

; Summing a matrix adds all of its elements.
(acl2::assert-equal (prim-sum (list 2 3) *mat23*) (iv 21))

; Summing a scalar yields the scalar.
(acl2::assert-equal (prim-sum nil (iv 5)) (iv 5))

; Summing an empty vector yields zero.
(acl2::assert-equal
 (prim-sum (list 0) (make-expr-value-vector-empty :dims nil :elem *tv-int*))
 (iv 0))

; Cell dimensions not matching the instantiation.
(acl2::assert-event (reserrp (prim-sum (list 2) *vec3*)))
(acl2::assert-event (reserrp (prim-sum nil *vec3*)))

; A cell whose atoms are not integers.
(acl2::assert-event
 (reserrp (prim-sum (list 2) (expr-value-vector (list (bv t) (bv nil))))))

; Via eval-primop-fun-fo.

(acl2::assert-equal
 (eval-primop-fun-fo (make-primop-value-sum-s :sval (list 3)) *vec3*)
 (iv 6))

; Wrong number of argument cells:
; one cell already yields a final result,
; not an operation applicable to another cell.
(acl2::assert-event
 (not (expr-value-case
       (eval-primop-fun-fo (make-primop-value-sum-s :sval (list 3))
                           *vec3*)
       :primop)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation reshape:
; instantiation stage transitions and application of the final stage.

; Type application: reshape applied to one atom type value.

(acl2::assert-equal
 (eval-primop-tfun (primop-value-reshape) *tv-int*)
 (expr-value-primop (primop-value-reshape-t *tv-int*)))

; Ispace applications: reshape-t applied to a shape,
; then reshape-t-s1 applied to another shape.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-reshape-t *tv-int*)
                   (ispace-value-shape (list 2 3)))
 (expr-value-primop (make-primop-value-reshape-t-s1 :tval *tv-int*
                                                    :s1val (list 2 3))))

(acl2::assert-equal
 (eval-primop-ifun (make-primop-value-reshape-t-s1 :tval *tv-int*
                                                   :s1val (list 2 3))
                   (ispace-value-shape (list 6)))
 (expr-value-primop (make-primop-value-reshape-t-s1-s2 :tval *tv-int*
                                                       :s1val (list 2 3)
                                                       :s2val (list 6))))

; A dimension where a shape is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-reshape-t *tv-int*)
                            (ispace-value-dim 3))))

; Application of the fully instantiated operation.

; Flattening a matrix into a vector.
(acl2::assert-equal
 (prim-reshape *tv-int* (list 2 3) (list 6) *mat23*)
 (expr-value-vector
  (list (iv 1) (iv 2) (iv 3) (iv 4) (iv 5) (iv 6))))

; Reshaping a matrix into its transpose's shape
; (note: NOT a transpose; atoms stay in row-major order).
(acl2::assert-equal
 (prim-reshape *tv-int* (list 2 3) (list 3 2) *mat23*)
 (expr-value-vector
  (list (expr-value-vector (list (iv 1) (iv 2)))
        (expr-value-vector (list (iv 3) (iv 4)))
        (expr-value-vector (list (iv 5) (iv 6))))))

; Reshaping a vector to itself.
(acl2::assert-equal
 (prim-reshape *tv-int* (list 3) (list 3) *vec3*) *vec3*)

; Reshaping a one-element vector into a scalar and back.
(acl2::assert-equal (prim-reshape *tv-int* (list 1) nil *vec1*) (iv 1))
(acl2::assert-equal
 (prim-reshape *tv-int* nil (list 1) (iv 1)) *vec1*)

; Reshaping an empty vector into another empty shape.
(acl2::assert-equal
 (prim-reshape *tv-int* (list 0) (list 0 2)
               (make-expr-value-vector-empty :dims nil :elem *tv-int*))
 (make-expr-value-vector-empty :dims (list 2) :elem *tv-int*))

; Shapes with different products.
(acl2::assert-event
 (reserrp (prim-reshape *tv-int* (list 2 3) (list 5) *mat23*)))
(acl2::assert-event
 (reserrp (prim-reshape *tv-int* (list 3) (list 0) *vec3*)))

; Cell dimensions not matching the first shape.
(acl2::assert-event
 (reserrp (prim-reshape *tv-int* (list 6) (list 2 3) *mat23*)))

; Via eval-primop-fun-fo.

(acl2::assert-equal
 (eval-primop-fun-fo (make-primop-value-reshape-t-s1-s2 :tval *tv-int*
                                                        :s1val (list 2 3)
                                                        :s2val (list 6))
                     *mat23*)
 (expr-value-vector
  (list (iv 1) (iv 2) (iv 3) (iv 4) (iv 5) (iv 6))))

; Wrong number of argument cells:
; one cell already yields a final result,
; not an operation applicable to another cell.
(acl2::assert-event
 (not (expr-value-case
       (eval-primop-fun-fo (make-primop-value-reshape-t-s1-s2 :tval *tv-int*
                                                              :s1val (list 2 3)
                                                              :s2val (list 6))
                           *mat23*)
       :primop)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation flatten:
; instantiation stage transitions and application of the final stage.

(defconst *mat222*
  (expr-value-vector
   (list (expr-value-vector
          (list (expr-value-vector (list (iv 1) (iv 2)))
                (expr-value-vector (list (iv 3) (iv 4)))))
         (expr-value-vector
          (list (expr-value-vector (list (iv 5) (iv 6)))
                (expr-value-vector (list (iv 7) (iv 8))))))))

; Type application: flatten applied to one atom type value.

(acl2::assert-equal
 (eval-primop-tfun (primop-value-flatten) *tv-int*)
 (expr-value-primop (primop-value-flatten-t *tv-int*)))

; Ispace applications: flatten-t applied to a dimension,
; flatten-t-m applied to another dimension,
; then flatten-t-m-n applied to a shape.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-flatten-t *tv-int*)
                   (ispace-value-dim 2))
 (expr-value-primop (make-primop-value-flatten-t-m :tval *tv-int*
                                                   :mval 2)))

(acl2::assert-equal
 (eval-primop-ifun (make-primop-value-flatten-t-m :tval *tv-int*
                                                  :mval 2)
                   (ispace-value-dim 3))
 (expr-value-primop (make-primop-value-flatten-t-m-n :tval *tv-int*
                                                     :mval 2
                                                     :nval 3)))

(acl2::assert-equal
 (eval-primop-ifun (make-primop-value-flatten-t-m-n :tval *tv-int*
                                                    :mval 2
                                                    :nval 3)
                   (ispace-value-shape nil))
 (expr-value-primop (make-primop-value-flatten-t-m-n-s :tval *tv-int*
                                                       :mval 2
                                                       :nval 3
                                                       :sval nil)))

; A shape where a dimension is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-flatten-t *tv-int*)
                            (ispace-value-shape (list 3)))))
(acl2::assert-event
 (reserrp (eval-primop-ifun (make-primop-value-flatten-t-m :tval *tv-int*
                                                           :mval 2)
                            (ispace-value-shape (list 3)))))

; A dimension where a shape is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (make-primop-value-flatten-t-m-n :tval *tv-int*
                                                             :mval 2
                                                             :nval 3)
                            (ispace-value-dim 3))))

; Application of the fully instantiated flatten to argument cells.

; With m = 2, n = 3, and s = (), the whole matrix is the cell,
; and flattening it combines its two dimensions into one of size 6.
(acl2::assert-equal
 (prim-flatten *tv-int* 2 3 nil *mat23*)
 (expr-value-vector
  (list (iv 1) (iv 2) (iv 3) (iv 4) (iv 5) (iv 6))))

; With m = 2, n = 2, and s = (2), the cells are the 2x2x2 cube's rows,
; and flattening combines the outer two dimensions into one of size 4,
; keeping the trailing shape (2) unchanged.
(acl2::assert-equal
 (prim-flatten *tv-int* 2 2 (list 2) *mat222*)
 (expr-value-vector
  (list (expr-value-vector (list (iv 1) (iv 2)))
        (expr-value-vector (list (iv 3) (iv 4)))
        (expr-value-vector (list (iv 5) (iv 6)))
        (expr-value-vector (list (iv 7) (iv 8))))))

; Flattening with a zero dimension yields an empty vector.
; An expr-value-vector-empty's :dims field holds the dimensions
; *after* the implicit leading 0 (see dims-of-expr-value):
; here the argument has dimensions (0 3) and the result (0).
(acl2::assert-equal
 (prim-flatten *tv-int* 0 3 nil
               (make-expr-value-vector-empty :dims (list 3) :elem *tv-int*))
 (make-expr-value-vector-empty :dims nil :elem *tv-int*))

; Cell dimensions not matching the instantiation.
(acl2::assert-event (reserrp (prim-flatten *tv-int* 3 2 nil *mat23*)))
(acl2::assert-event (reserrp (prim-flatten *tv-int* 2 3 (list 1) *mat23*)))

; Via eval-primop-fun-fo.

(acl2::assert-equal
 (eval-primop-fun-fo (make-primop-value-flatten-t-m-n-s :tval *tv-int*
                                                        :mval 2
                                                        :nval 3
                                                        :sval nil)
                     *mat23*)
 (expr-value-vector
  (list (iv 1) (iv 2) (iv 3) (iv 4) (iv 5) (iv 6))))

; Wrong number of argument cells:
; one cell already yields a final result,
; not an operation applicable to another cell.
(acl2::assert-event
 (not (expr-value-case
       (eval-primop-fun-fo (make-primop-value-flatten-t-m-n-s :tval *tv-int*
                                                              :mval 2
                                                              :nval 3
                                                              :sval nil)
                           *mat23*)
       :primop)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation transpose2d:
; instantiation stage transitions and application of the final stage.

; Type application: transpose2d applied to one atom type value.

(acl2::assert-equal
 (eval-primop-tfun (primop-value-transpose2d) *tv-int*)
 (expr-value-primop (primop-value-transpose2d-t *tv-int*)))

; Array type value where an atom one is expected.
(acl2::assert-event
 (reserrp (eval-primop-tfun (primop-value-transpose2d)
                            (make-type-value-array :elem *tv-int*
                                                   :dims (list 3)))))

; Ispace applications: transpose2d-t applied to a dimension,
; then transpose2d-t-m applied to another dimension.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-transpose2d-t *tv-int*)
                   (ispace-value-dim 2))
 (expr-value-primop (make-primop-value-transpose2d-t-m :tval *tv-int*
                                                       :mval 2)))

(acl2::assert-equal
 (eval-primop-ifun (make-primop-value-transpose2d-t-m :tval *tv-int*
                                                      :mval 2)
                   (ispace-value-dim 3))
 (expr-value-primop (make-primop-value-transpose2d-t-m-n :tval *tv-int*
                                                         :mval 2
                                                         :nval 3)))

; A shape where a dimension is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-transpose2d-t *tv-int*)
                            (ispace-value-shape (list 2)))))

; Application of the fully instantiated operation.

; Transposing a 2x3 matrix yields the 3x2 matrix
; with the atoms rearranged column-first.
(acl2::assert-equal
 (prim-transpose2d *tv-int* 2 3 *mat23*)
 (expr-value-vector
  (list (expr-value-vector (list (iv 1) (iv 4)))
        (expr-value-vector (list (iv 2) (iv 5)))
        (expr-value-vector (list (iv 3) (iv 6))))))

; Transposing twice gives back the original matrix.
(acl2::assert-equal
 (prim-transpose2d *tv-int* 3 2 (prim-transpose2d *tv-int* 2 3 *mat23*))
 *mat23*)

; Transposing a 1x3 matrix yields the 3x1 matrix.
(acl2::assert-equal
 (prim-transpose2d *tv-int* 1 3 (expr-value-vector (list *vec3*)))
 (expr-value-vector
  (list (expr-value-vector (list (iv 1)))
        (expr-value-vector (list (iv 2)))
        (expr-value-vector (list (iv 3))))))

; Transposing a 1x1 matrix yields the same matrix.
(acl2::assert-equal
 (prim-transpose2d *tv-int* 1 1
                   (expr-value-vector (list (expr-value-vector (list (iv 7))))))
 (expr-value-vector (list (expr-value-vector (list (iv 7))))))

; Transposing a 0x3 matrix yields the 3x0 matrix.
(acl2::assert-equal
 (prim-transpose2d *tv-int* 0 3
                   (make-expr-value-vector-empty :dims (list 3)
                                                 :elem *tv-int*))
 (expr-value-vector
  (list (make-expr-value-vector-empty :dims nil :elem *tv-int*)
        (make-expr-value-vector-empty :dims nil :elem *tv-int*)
        (make-expr-value-vector-empty :dims nil :elem *tv-int*))))

; Transposing a 2x0 matrix yields the 0x2 matrix.
(acl2::assert-equal
 (prim-transpose2d *tv-int* 2 0
                   (expr-value-vector
                    (list (make-expr-value-vector-empty :dims nil
                                                        :elem *tv-int*)
                          (make-expr-value-vector-empty :dims nil
                                                        :elem *tv-int*))))
 (make-expr-value-vector-empty :dims (list 2) :elem *tv-int*))

; Cell dimensions not matching the instantiation.
(acl2::assert-event (reserrp (prim-transpose2d *tv-int* 3 2 *mat23*)))
(acl2::assert-event (reserrp (prim-transpose2d *tv-int* 2 3 *vec3*)))

; Via eval-primop-fun-fo.

(acl2::assert-equal
 (eval-primop-fun-fo (make-primop-value-transpose2d-t-m-n :tval *tv-int*
                                                          :mval 2
                                                          :nval 3)
                     *mat23*)
 (expr-value-vector
  (list (expr-value-vector (list (iv 1) (iv 4)))
        (expr-value-vector (list (iv 2) (iv 5)))
        (expr-value-vector (list (iv 3) (iv 6))))))

; Wrong number of argument cells:
; one cell already yields a final result,
; not an operation applicable to another cell.
(acl2::assert-event
 (not (expr-value-case
       (eval-primop-fun-fo (make-primop-value-transpose2d-t-m-n :tval *tv-int*
                                                                :mval 2
                                                                :nval 3)
                           *mat23*)
       :primop)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation iota/static:
; a single ispace application directly yields the final array.

; Ispace application to a matrix shape:
; the result is the row-major enumeration, not a next-stage operation.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-iota/static)
                   (ispace-value-shape (list 2 3)))
 (expr-value-vector
  (list (expr-value-vector (list (iv 0) (iv 1) (iv 2)))
        (expr-value-vector (list (iv 3) (iv 4) (iv 5))))))

; Ispace application to the scalar shape: the rank-0 array holding 0.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-iota/static)
                   (ispace-value-shape nil))
 (iv 0))

; Ispace application to a shape with a zero dimension: the empty array.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-iota/static)
                   (ispace-value-shape (list 0)))
 (expr-value-with-empty-dim (list 0) *tv-int*))

; A dimension where a shape is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-iota/static)
                            (ispace-value-dim 3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation reduce:
; instantiation stage transitions and storage of the function value.
; The application of the final stage executes Remora code,
; so it is tested with the evaluator (see evaluation-tests.lisp).

; Type application: reduce applied to one atom type value.

(acl2::assert-equal
 (eval-primop-tfun (primop-value-reduce) *tv-int*)
 (expr-value-primop (primop-value-reduce-t *tv-int*)))

; Array type value where an atom one is expected.
(acl2::assert-event
 (reserrp (eval-primop-tfun (primop-value-reduce)
                            (make-type-value-array :elem *tv-int*
                                                   :dims (list 3)))))

; Ispace applications: reduce-t applied to a dimension,
; then reduce-t-d applied to a shape.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-reduce-t *tv-int*)
                   (ispace-value-dim 2))
 (expr-value-primop (make-primop-value-reduce-t-d :tval *tv-int*
                                                  :dval 2)))

(acl2::assert-equal
 (eval-primop-ifun (make-primop-value-reduce-t-d :tval *tv-int*
                                                 :dval 2)
                   (ispace-value-shape nil))
 (expr-value-primop (make-primop-value-reduce-t-d-s :tval *tv-int*
                                                    :dval 2
                                                    :sval nil)))

; A shape where a dimension is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-reduce-t *tv-int*)
                            (ispace-value-shape nil))))

; A dimension where a shape is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (make-primop-value-reduce-t-d :tval *tv-int*
                                                          :dval 2)
                            (ispace-value-dim 3))))

; Value application: reduce-t-d-s stores the function value.

(defconst *add-fun*
  (expr-value-primop (primop-value-int-binary (int-binary-primop-add))))

(acl2::assert-equal
 (eval-primop-fun-fo (make-primop-value-reduce-t-d-s :tval *tv-int*
                                                     :dval 2
                                                     :sval nil)
                     *add-fun*)
 (expr-value-primop (make-primop-value-reduce-t-d-s-f :tval *tv-int*
                                                      :dval 2
                                                      :sval nil
                                                      :fval *add-fun*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation fold:
; instantiation stage transitions and storage of
; the function and initial values.
; The application of the final stage executes Remora code,
; so it is tested with the evaluator (see evaluation-tests.lisp).

(acl2::assert-equal
 (eval-primop-tfun (primop-value-fold) *tv-int*)
 (expr-value-primop (primop-value-fold-t *tv-int*)))

(acl2::assert-equal
 (eval-primop-tfun (primop-value-fold-t *tv-int*) *tv-int*)
 (expr-value-primop (make-primop-value-fold-t-t2 :tval *tv-int*
                                                 :t2val *tv-int*)))

(acl2::assert-event
 (reserrp (eval-primop-tfun (primop-value-fold)
                            (make-type-value-array :elem *tv-int*
                                                   :dims (list 3)))))

(acl2::assert-equal
 (eval-primop-ifun (make-primop-value-fold-t-t2 :tval *tv-int*
                                                :t2val *tv-int*)
                   (ispace-value-dim 2))
 (expr-value-primop (make-primop-value-fold-t-t2-d :tval *tv-int*
                                                   :t2val *tv-int*
                                                   :dval 2)))

(acl2::assert-equal
 (eval-primop-ifun (make-primop-value-fold-t-t2-d :tval *tv-int*
                                                  :t2val *tv-int*
                                                  :dval 2)
                   (ispace-value-shape nil))
 (expr-value-primop (make-primop-value-fold-t-t2-d-s :tval *tv-int*
                                                     :t2val *tv-int*
                                                     :dval 2
                                                     :sval nil)))

(acl2::assert-equal
 (eval-primop-ifun (make-primop-value-fold-t-t2-d-s :tval *tv-int*
                                                    :t2val *tv-int*
                                                    :dval 2
                                                    :sval nil)
                   (ispace-value-shape nil))
 (expr-value-primop (make-primop-value-fold-t-t2-d-s-s2 :tval *tv-int*
                                                        :t2val *tv-int*
                                                        :dval 2
                                                        :sval nil
                                                        :s2val nil)))

(acl2::assert-event
 (reserrp (eval-primop-ifun (make-primop-value-fold-t-t2 :tval *tv-int*
                                                         :t2val *tv-int*)
                            (ispace-value-shape nil))))

(acl2::assert-event
 (reserrp (eval-primop-ifun (make-primop-value-fold-t-t2-d :tval *tv-int*
                                                           :t2val *tv-int*
                                                           :dval 2)
                            (ispace-value-dim 3))))

(acl2::assert-equal
 (eval-primop-fun-fo (make-primop-value-fold-t-t2-d-s-s2 :tval *tv-int*
                                                         :t2val *tv-int*
                                                         :dval 2
                                                         :sval nil
                                                         :s2val nil)
                     *add-fun*)
 (expr-value-primop (make-primop-value-fold-t-t2-d-s-s2-f :tval *tv-int*
                                                          :t2val *tv-int*
                                                          :dval 2
                                                          :sval nil
                                                          :s2val nil
                                                          :fval *add-fun*)))

(acl2::assert-equal
 (eval-primop-fun-fo (make-primop-value-fold-t-t2-d-s-s2-f :tval *tv-int*
                                                           :t2val *tv-int*
                                                           :dval 2
                                                           :sval nil
                                                           :s2val nil
                                                           :fval *add-fun*)
                     (iv 10))
 (expr-value-primop (make-primop-value-fold-t-t2-d-s-s2-f-z :tval *tv-int*
                                                            :t2val *tv-int*
                                                            :dval 2
                                                            :sval nil
                                                            :s2val nil
                                                            :fval *add-fun*
                                                            :zval (iv 10))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation reify-dim:
; a single ispace application directly yields the integer scalar.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-reify-dim)
                   (ispace-value-dim 3))
 (iv 3))

(acl2::assert-equal
 (eval-primop-ifun (primop-value-reify-dim)
                   (ispace-value-dim 0))
 (iv 0))

; A shape where a dimension is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-reify-dim)
                            (ispace-value-shape (list 3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation reify-shape:
; a single ispace application directly yields a boxed integer vector.

(defconst *reify-shape-sigma*
  (make-type-value-sigma
   :param (ispace-var-dim "r")
   :body (t[] :int (shp "$r"))
   :denv (make-type-denv :ienv (make-ispace-denv :ispaces nil)
                         :types nil)))

(acl2::assert-equal
 (eval-primop-ifun (primop-value-reify-shape)
                   (ispace-value-shape (list 2 3)))
 (make-expr-value-box
  :ispace (ispace-value-dim 2)
  :array (expr-value-vector (list (iv 2) (iv 3)))
  :type *reify-shape-sigma*))

; The empty shape reifies to a box of the empty vector, with rank 0.
(acl2::assert-equal
 (eval-primop-ifun (primop-value-reify-shape)
                   (ispace-value-shape nil))
 (make-expr-value-box
  :ispace (ispace-value-dim 0)
  :array (expr-value-with-empty-dim (list 0) *tv-int*)
  :type *reify-shape-sigma*))

; A shape with zero dimensions still reifies to their vector.
(acl2::assert-equal
 (eval-primop-ifun (primop-value-reify-shape)
                   (ispace-value-shape (list 0 3)))
 (make-expr-value-box
  :ispace (ispace-value-dim 2)
  :array (expr-value-vector (list (iv 0) (iv 3)))
  :type *reify-shape-sigma*))

; A dimension where a shape is expected.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-reify-shape)
                            (ispace-value-dim 3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The polymorphic operation iota:
; instantiation stage transition and application of the final stage.

(defconst *iota-sigma*
  (make-type-value-sigma
   :param (ispace-var-shape "s")
   :body (t[] :int "@s")
   :denv (make-type-denv :ienv (make-ispace-denv :ispaces nil)
                         :types nil)))

(acl2::assert-equal
 (eval-primop-ifun (primop-value-iota) (ispace-value-dim 2))
 (expr-value-primop (make-primop-value-iota-d :dval 2)))

(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-iota)
                            (ispace-value-shape (list 2)))))

; The shape comes from the argument cell: [2 3] yields the 2x3 enumeration.
(acl2::assert-equal
 (prim-iota 2 (expr-value-vector (list (iv 2) (iv 3))))
 (make-expr-value-box
  :ispace (ispace-value-shape (list 2 3))
  :array (expr-value-vector
          (list (expr-value-vector (list (iv 0) (iv 1) (iv 2)))
                (expr-value-vector (list (iv 3) (iv 4) (iv 5)))))
  :type *iota-sigma*))

; An empty argument vector yields the scalar shape, i.e. the scalar 0.
(acl2::assert-equal
 (prim-iota 0 (make-expr-value-vector-empty :dims nil :elem *tv-int*))
 (make-expr-value-box
  :ispace (ispace-value-shape nil)
  :array (iv 0)
  :type *iota-sigma*))

; Argument cell dimensions not matching the instantiation.
(acl2::assert-event
 (reserrp (prim-iota 3 (expr-value-vector (list (iv 2) (iv 3))))))

; Negative dimensions are rejected.
(acl2::assert-event
 (reserrp (prim-iota 2 (expr-value-vector (list (iv 2) (iv -3))))))

; Via eval-primop-fun-fo.
(acl2::assert-equal
 (eval-primop-fun-fo (make-primop-value-iota-d :dval 1)
                     (expr-value-vector (list (iv 3))))
 (make-expr-value-box
  :ispace (ispace-value-shape (list 3))
  :array (expr-value-vector (list (iv 0) (iv 1) (iv 2)))
  :type *iota-sigma*))
