; SOFT ('Second-Order Functions and Theorems) -- Workshop Talk Examples
;
; Copyright (C) 2015-2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains the SOFT ('Second-Order Functions and Theorems') examples
; in the ACL2-2015 Workshop talk "Second-Order Functions and Theorems in ACL2"
; that are not already in the ACL2-2015 Workshop paper with the same title.

; SOFT is documented in documentation.lisp
; and implemented in implementation.lisp.
; Other examples of use of SOFT are in workshop-paper-examples.lisp.
; Other tests are in tests.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "implementation")

; Avoid ACL2(p) error in DEFUN2 pertaining to override hints.
(local (set-waterfall-parallelism nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unary function variable.

(defunvar ?f (*) => *)

; Apply function to elements of list.

(defun2 map[?f] (?f) (l)
  (cond ((atom l) nil)
        (t (cons (?f (car l))
                 (map[?f] (cdr l))))))

(verify-guards map[?f]) ; omitted from the presentation, for brevity

; MAP[?F] preserves length.

(defthm len-of-map[?f]
  (equal (len (map[?f] l))
         (len l)))

; Instantiate MAP[?F] and use to define another function.

(defun-inst map[fix]
  (map[?f] (?f . fix)))

(defun rev-fix-cons (a x)
  (cons a (map[fix] (rev x))))

(verify-guards rev-fix-cons) ; omitted from the presentation, for brevity

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

(defun-sk2 semigroup[?op] (?op) ()
  (forall (x y z)
          (equal (?op (?op x y) z)
                 (?op x (?op y z)))))

(verify-guards semigroup[?op]) ; omitted from the presentation, for brevity

; Identity ID for operation ?OP.

(defun-sk2 identity[?op] (?op) (id)
  (forall x (and (equal (?op id x) x)
                 (equal (?op x id) x))))

(verify-guards identity[?op]) ; omitted from the presentation, for brevity

; Monoid with operation ?OP and identity ID.

(defun2 monoid[?op] (?op) (id)
  (and (semigroup[?op])
       (identity[?op] id)))

(verify-guards monoid[?op]) ; omitted from the presentation, for brevity

; Inverse ?INV for identity ID of operation ?OP.

(defun-sk2 inverse[?op_?inv] (?op ?inv) (id)
  (forall x (and (equal (?op x (?inv x)) id)
                 (equal (?op (?inv x) x) id))))

(verify-guards inverse[?op_?inv]) ; omitted from the presentation, for brevity

; Group with operation ?OP, inverse ?INV, and identity ID.

(defun2 group[?op_?inv] (?op ?inv) (id)
  (and (monoid[?op] id)
       (inverse[?op_?inv] id)))

(verify-guards group[?op_?inv]) ; omitted from the presentation, for brevity
