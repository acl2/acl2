(in-package "ACL2")

; Here is an alternative to xtr.lisp.

; ---------------------------------------------------------------------------
; Exercise 11.52

(include-book "arithmetic/top-with-meta" :dir :system)

(defun xtr (map lst)
  (if (endp map)
      nil
    (cons (nth (car map) lst)
	  (xtr (cdr map) lst))))

(defun nats (n)
  (if (zp n)
      nil
    (cons (- n 1) (nats (- n 1)))))

(defun app (x y)
  (if (endp x)
      y
    (cons (car x)
          (app (cdr x) y))))

(defun rev (x)
  (if (endp x)
      nil
    (app (rev (cdr x)) (list (car x)))))

(defun rev2 (x y)
  (if (zp x)
      nil
    (cons (nth (- x 1) y)
	  (rev2 (- x 1) y))))

; This is not needed by ACL2, but it is added to make all
; inductive proofs explicit.
(defthm rev2-nth
  (equal (cons (nth y (cons x1 x2)) (rev2 y (cons x1 x2)))
	 (app (rev2 y x2) (list x1))))

(defthm rev2-rev
  (equal (rev2 (len x) x)
	 (rev x)))

(defthm main0
  (equal (xtr (nats y) x)
	 (rev2 y x)))

(defthm main
  (equal (xtr (nats (len x)) x)
	 (rev x)))
