
; num.lisp                                      Vivek & Warren

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; This file defines our rational/floating-point numbers.

; cert_param: (non-acl2r)

(in-package "ACL2")

; Used to assist with our "cheating" (i.e., using floating point).

(defun nump (x)
  (declare (xargs :guard t))
  ;; In the ACL2 logic, the body below is equivalent to
  ;; (real/rationalp x), which is probably also what we want for
  ;; ACL2(r).  However, we want nump to do "the right thing" even in
  ;; raw lisp, when handed a double-float; so real/rationalp (and
  ;; rationalp) don't work for us.
  (and (acl2-numberp x)
       (zerop (imagpart x))))

; Consider making a compound-recognizer rule (probably overkill).
(defthm nump-is-rationalp (equal (nump x) (rationalp x)))

;; prove that nump compound recognizer
;; (defthm nump-rewrite-rationalp
;;   (equal (nump x)
;;          (rationalp x)))

;; (defthm nump-forward-to-rationalp
;;   (implies (nump x)
;;            (rationalp x))
;;   :rule-classes :forward-chaining)

(in-theory (disable nump))

; Sparse-matrix operators

; Layered definition of matrices and their operations.

(defun num-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (nump (car x))
         (num-listp (cdr x)))))

(defthm num-listp-is-rational-listp
  ;; we rewrite num-listp to rational-listp to "hide" the
  ;; "floating-point lists" from ACL2.
  (equal (num-listp l)
         (rational-listp l)))

(defun symbol-num-list-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (let ((pair (car x)))
           (and (consp pair)
                (symbolp (car pair))
                (num-listp (cdr pair))))
         (symbol-num-list-alistp (cdr x)))))


