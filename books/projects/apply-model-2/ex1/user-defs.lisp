; Copyright (C) 2019, ForrestHunt, Inc.
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

; The following demonstrates that we can model a G1 function that uses a local
; stobj.  This also shows that not every subfunction of a tame function need be
; badged (i.e., count-atoms1 is unbadgeable because it traffics in stobjs, but
; its caller, count-atoms, can be badged).

(defstobj st (counter :type integer :initially 0))

(defun count-atoms1 (x st)
  (declare (xargs :stobjs (st)))
  (cond ((atom x)
         (update-counter (+ 1 (counter st)) st))
        (t (let ((st (count-atoms1 (car x) st)))
             (count-atoms1 (cdr x) st)))))

(defun$ count-atoms (x)
  (with-local-stobj
    st
    (mv-let (val st)
      (let ((st (count-atoms1 x st)))
        (mv (counter st) st))
      val)))

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

; And two lexicographic measures, one of length 2 and the other of length 3.

(defun$ ack$ (fn k n m)
  (declare (xargs :measure (llist k m)
                  :well-founded-relation l<))
  (if (zp k)
      (apply$ fn (list (+ 1 n)))
      (if (zp m)
          (if (equal k 2)
              0
              (if (equal k 3)
                  1
                  n))
          (ack$ fn
                (- k 1)
                (ack$ fn k n (- m 1))
                n))))

(defun$ silly$ (fn k n m)
  (declare (xargs :measure (llist k n m)
                  :well-founded-relation l<))
  (if (zp k)
      (apply$ fn (list n))
      (if (zp n)
          (apply$ fn (list k))
          (if (zp m)
              (apply$ fn (list n))
              (silly$ fn
                      (- k 1)
                      (silly$ fn
                              k
                              (- n 1)
                              (silly$ fn
                                      k
                                      n
                                      (- m 1)))
                      m)))))
