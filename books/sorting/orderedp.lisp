(in-package "ACL2")

(defun orderedp (x)
  (if (endp x)
      t
    (if (endp (cdr x))
        t
      (and (lexorder (car x) (car (cdr x)))
           (orderedp (cdr x))))))
