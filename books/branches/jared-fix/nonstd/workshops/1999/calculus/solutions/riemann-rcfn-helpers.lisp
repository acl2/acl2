(in-package "ACL2")

; Solution to Exercise 6.8.

; Here is a direct way to define dotprod.  Source file
; riemann-defuns.lisp provides another definition.

(defun dotprod (x y)
  (if (consp x)
      (+ (* (car x) (car y))
         (dotprod (cdr x) (cdr y)))
    0))

(defstub rcfn (x) t)

(defun map-rcfn (p)
  ;; map rcfn over the list p
  (if (consp p)
      (cons (rcfn (car p)) (map-rcfn (cdr p)))
    nil))

