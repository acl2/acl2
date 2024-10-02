(in-package "HANOI")

(acl2::set-verify-guards-eagerness 2)

(defun app (a b)
  (if (not (consp a))
      b
    (cons (car a) (app (cdr a) b))))


;; (defun tower (n)
;;   (declare (xargs :guard (natp n)))
;;   (if (zp n)
;;       nil
;;     (app (tower (- n 1)) (list n))))
