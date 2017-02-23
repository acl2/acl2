; Copyright (C) 2017, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Portcullis:
; (include-book "apply")

(in-package "MODAPP")

; ---
; G1 functions

(defun$ square (x) (* x x))

(defun$ nats (n)
  (if (zp n)
      nil
      (cons n (nats (- n 1)))))

; ---
; G2

(defun$ sumlist (lst fn)
  (cond ((endp lst) 0)
        (t (+ (apply$ fn (list (car lst)))
              (sumlist (cdr lst) fn)))))

(defun$ foldr (lst fn init)
  (if (endp lst)
      init
      (apply$ fn
              (list (car lst)
                    (foldr (cdr lst) fn init)))))

(defun$ prow (lst fn)
  (cond ((or (endp lst) (endp (cdr lst)))
         nil)
        (t (cons (apply$ fn (list (car lst) (cadr lst)))
                 (prow (cdr lst) fn)))))

(defun$ prow* (lst fn)
  (declare (xargs :measure (len lst)))
  (cond ((or (endp lst)
             (endp (cdr lst)))
         (apply$ fn (list lst lst)))
        (t (prow* (prow lst fn) fn))))

(defun$ collect-a (lst fn)
  (cond ((endp lst) nil)
        (t (cons (apply$ fn (list
                             (sumlist (nats (car lst))
                                      '(lambda (i)
                                         (foldr (nats i)
                                                '(lambda (j k)
                                                   (binary-* (square j) k))
                                                '1)))))
                 (collect-a (cdr lst) fn)))))

(defun$ sum-of-products (lst)
  (sumlist lst
           '(LAMBDA (X)
                    (FOLDR X
                           '(LAMBDA (I A)
                                    (BINARY-* I A))
                           '1))))
