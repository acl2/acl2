(in-package "ACL2")

(make-event '(defun f (x) x))

(encapsulate
 ()
 (local (make-event '(defun g (x) x)))
 (defun h (x) x))
