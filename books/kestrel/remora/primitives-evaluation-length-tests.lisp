; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

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
 (eval-primop-tfun (primop-value-length) (list *tv-int*))
 (expr-value-primop (primop-value-length-t *tv-int*)))

; Wrong number of type values.
(acl2::assert-event
 (reserrp (eval-primop-tfun (primop-value-length)
                            (list *tv-int* *tv-int*))))

; Array type value where an atom one is expected.
(acl2::assert-event
 (reserrp (eval-primop-tfun (primop-value-length)
                            (list (make-type-value-array :elem *tv-int*
                                                         :dims (list 3))))))

; Ispace application: length-t applied to a dimension and a shape.

(acl2::assert-equal
 (eval-primop-ifun (primop-value-length-t *tv-int*)
                   (list (ispace-value-dim 2)
                         (ispace-value-shape (list 3))))
 (expr-value-primop (make-primop-value-length-t-d-s :tval *tv-int*
                                                    :d 2
                                                    :s (list 3))))

; Dimension and shape in the wrong order.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-length-t *tv-int*)
                            (list (ispace-value-shape (list 3))
                                  (ispace-value-dim 2)))))

; Wrong number of ispace values.
(acl2::assert-event
 (reserrp (eval-primop-ifun (primop-value-length-t *tv-int*)
                            (list (ispace-value-dim 2)))))

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
                                                  :d 3
                                                  :s nil)
                  (list *vec3*))
 (iv 3))

; Wrong number of argument cells.
(acl2::assert-event
 (reserrp (eval-primop-fun (make-primop-value-length-t-d-s :tval *tv-int*
                                                           :d 3
                                                           :s nil)
                           (list *vec3* *vec3*))))
