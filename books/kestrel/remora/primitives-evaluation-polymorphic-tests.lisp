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

; Via eval-primop-fun, including the arity check.

(acl2::assert-equal
 (eval-primop-fun (make-primop-value-length-t-d-s :tval *tv-int*
                                                  :dval 3
                                                  :sval nil)
                  (list *vec3*))
 (iv 3))

; Wrong number of argument cells.
(acl2::assert-event
 (reserrp (eval-primop-fun (make-primop-value-length-t-d-s :tval *tv-int*
                                                           :dval 3
                                                           :sval nil)
                           (list *vec3* *vec3*))))

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

; Via eval-primop-fun, including the arity check.

(acl2::assert-equal
 (eval-primop-fun (make-primop-value-head-t-d-s :tval *tv-int*
                                                :dval 2
                                                :sval nil)
                  (list *vec3*))
 (iv 1))

; Wrong number of argument cells.
(acl2::assert-event
 (reserrp (eval-primop-fun (make-primop-value-head-t-d-s :tval *tv-int*
                                                         :dval 2
                                                         :sval nil)
                           (list *vec3* *vec3*))))

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

; Via eval-primop-fun, including the arity check.

(acl2::assert-equal
 (eval-primop-fun (make-primop-value-tail-t-d-s :tval *tv-int*
                                                :dval 2
                                                :sval nil)
                  (list *vec3*))
 (expr-value-vector (list (iv 2) (iv 3))))

; Wrong number of argument cells.
(acl2::assert-event
 (reserrp (eval-primop-fun (make-primop-value-tail-t-d-s :tval *tv-int*
                                                         :dval 2
                                                         :sval nil)
                           (list *vec3* *vec3*))))

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

; Via eval-primop-fun, including the arity check.

(acl2::assert-equal
 (eval-primop-fun (make-primop-value-append-t-m-n-s :tval *tv-int*
                                                    :mval 3
                                                    :nval 1
                                                    :sval nil)
                  (list *vec3* *vec1*))
 (expr-value-vector (list (iv 1) (iv 2) (iv 3) (iv 1))))

; Wrong number of argument cells.
(acl2::assert-event
 (reserrp (eval-primop-fun (make-primop-value-append-t-m-n-s :tval *tv-int*
                                                             :mval 3
                                                             :nval 1
                                                             :sval nil)
                           (list *vec3*))))

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

; Via eval-primop-fun, including the arity check.

(acl2::assert-equal
 (eval-primop-fun (make-primop-value-reverse-t-d-s :tval *tv-int*
                                                   :dval 3
                                                   :sval nil)
                  (list *vec3*))
 (expr-value-vector (list (iv 3) (iv 2) (iv 1))))

; Wrong number of argument cells.
(acl2::assert-event
 (reserrp (eval-primop-fun (make-primop-value-reverse-t-d-s :tval *tv-int*
                                                            :dval 3
                                                            :sval nil)
                           (list *vec3* *vec3*))))

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

; Via eval-primop-fun.

(acl2::assert-equal
 (eval-primop-fun (make-primop-value-index-t-m :tval *tv-int*
                                               :mval 3)
                  (list *vec3* (iv 1)))
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

; Via eval-primop-fun.

(acl2::assert-equal
 (eval-primop-fun (make-primop-value-index2d-t-m-n :tval *tv-int*
                                                   :mval 2
                                                   :nval 3)
                  (list *mat23*
                        (expr-value-vector (list (iv 1) (iv 0)))))
 (iv 4))
