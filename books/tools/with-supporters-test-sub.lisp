(in-package "ACL2")

(defun g1 (x)
  (declare (xargs :guard t))
  x)

(defun g2 (x)
  (declare (xargs :guard (g1 x)))
  x)

(defun g3 (x)
  (g2 x))

