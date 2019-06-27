; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "implementation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Below are examples in the ACL2-2015 Workshop talk
; "Second-Order Functions and Theorems in ACL2"
; that are not already in the ACL2-2015 Workshop paper with the same title.
; The examples look slightly different from the sides
; due to the changes to SOFT since the Workshop
; (see :DOC UPDATES-TO-WORKSHOP-MATERIAL).

; Unary function variable.

(defunvar ?f (*) => *)

; Apply function to elements of list.

(defun2 map[?f] (l)
  (declare (xargs :guard t))
  (cond ((atom l) nil)
        (t (cons (?f (car l))
                 (map[?f] (cdr l))))))

; MAP[?F] preserves length.

(defthm len-of-map[?f]
  (equal (len (map[?f] l))
         (len l)))

; Instantiate MAP[?F] and use to define another function.

(defun-inst map[fix]
  (map[?f] (?f . fix)))

(defun rev-fix-cons (a x)
  (declare (xargs :guard t))
  (cons a (map[fix] (rev x))))

; Instantiate LEN-OF-MAP[?F] and use to prove a theorem about REV-FIX-CONS.

(defthm-inst len-of-map[fix]
  (len-of-map[?f] (?f . fix)))

(defthm len-of-rev-fix-cons
  (equal (len (rev-fix-cons a x))
         (1+ (len x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Function variable for binary operation.

(defunvar ?op (* *) => *)

; Function variable for unary inverse operation.

(defunvar ?inv (*) => *)

; Semigroup with operation ?OP.

(defun-sk2 semigroup[?op] ()
  (forall (x y z)
          (equal (?op (?op x y) z)
                 (?op x (?op y z)))))

(verify-guards semigroup[?op])

; Identity ID for operation ?OP.

(defun-sk2 identity[?op] (id)
  (forall x (and (equal (?op id x) x)
                 (equal (?op x id) x))))

(verify-guards identity[?op])

; Monoid with operation ?OP and identity ID.

(defun2 monoid[?op] (id)
  (declare (xargs :guard t))
  (and (semigroup[?op])
       (identity[?op] id)))

; Inverse ?INV for identity ID of operation ?OP.

(defun-sk2 inverse[?op][?inv] (id)
  (forall x (and (equal (?op x (?inv x)) id)
                 (equal (?op (?inv x) x) id))))

(verify-guards inverse[?op][?inv])

; Group with operation ?OP, inverse ?INV, and identity ID.

(defun2 group[?op][?inv] (id)
  (declare (xargs :guard t))
  (and (monoid[?op] id)
       (inverse[?op][?inv] id)))
