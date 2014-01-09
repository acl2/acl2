; (certify-book "isort")

(in-package "ACL2")

(include-book "perm")
(include-book "ordered-perms")
(include-book "convert-perm-to-how-many")

(defun insert (e x)
       (if (endp x)
           (cons e x)
         (if (lexorder e (car x))
             (cons e x)
           (cons (car x)
                 (insert e (cdr x))))))

(defun isort (x)
       (if (endp x)
           nil
         (insert (car x)
                 (isort (cdr x)))))

(defthm orderedp-isort
       (orderedp (isort x)))

(defthm true-listp-isort
  (true-listp (isort x)))

(defthm how-many-isort
  (equal (how-many e (isort x))
         (how-many e x)))

; (defthm perm-isort
;        (perm (isort x) x))