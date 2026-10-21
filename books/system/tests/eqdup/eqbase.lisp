(in-package "ACL2")
(defun ee (x y) (declare (xargs :guard t)) (equal (nfix x) (nfix y)))
(defun ff (x) (declare (xargs :guard t)) (nfix x))
