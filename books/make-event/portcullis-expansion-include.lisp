; Do more testing of redundancy for encapsulate.

(in-package "ACL2")

; Already in certification world.
(encapsulate
 ((local-fn (x) t))
 (local (defun local-fn (x) x))
 (make-event '(defun bar4 (x) (cons x x))
             :check-expansion nil)
 (defthm bar4-prop
   (consp (bar4 x))))

; Includes an encapsulate redundant with the above.
(include-book "portcullis-expansion")

; Let's do that former one again.
(encapsulate
 ((local-fn (x) t))
 (local (defun local-fn (x) x))
 (make-event '(defun bar4 (x) (cons x x))
             :check-expansion nil)
 (defthm bar4-prop
   (consp (bar4 x))))
