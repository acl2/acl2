
; expt10.lisp

; Copyright (C) 2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; Written by Matt Kaufmann

(in-package "ACL2")

(defun expt10-alist (n)

; Return an alist ((0 . 10^-100) (1 . 10^-99) ... (100 . 10^0) (101 . 10^1)
; ... (200 . 10^n)).

  (cond ((zp n) (acons 0 (expt 10 -100) nil))
        (t (acons n (expt 10 (- n 100)) (expt10-alist (1- n))))))

(defconst *expt10*
  (compress1 'expt10
             (cons (list :HEADER
                         :DIMENSIONS (list 201)
                         :MAXIMUM-LENGTH 202
                         :DEFAULT 0
                         :NAME 'expt10)
                   (expt10-alist 200))))

(defmacro expt10 (x)
; The value of x should be an integer.
  (declare (xargs :guard (atom x))) ; avoid re-evaluation
  `(if (and (<= -100 ,x) (<= ,x 100))
       (aref1 'expt10 *expt10* (the (integer 0 200) (+ 100 ,x)))
     (expt 10 (the integer ,x))))

