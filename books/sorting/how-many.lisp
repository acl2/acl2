(in-package "ACL2")

(defun how-many (e x)
  (cond
   ((endp x)
    0)
   ((equal e (car x))
    (1+ (how-many e (cdr x))))
   (t
    (how-many e (cdr x)))))
