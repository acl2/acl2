(in-package "ACL2")

;;; Define basic notions.
(include-book "riemann-defuns")

(defun make-partition-rec (a delta n)
  (if (zp n)
      (list a)
    (cons a
          (make-partition-rec (+ a delta) delta (1- n)))))

(defun make-partition (a b n)
  (make-partition-rec a (/ (- b a) n) n))



