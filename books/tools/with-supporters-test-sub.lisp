(in-package "ACL2")

(defmacro mac1 (x)
  x)

(defun g1 (x)
  (declare (xargs :guard t))
  (mac1 x))

(defun mac2-fn (x)
  x)

(defmacro mac2 (x)
  (mac2-fn x))

(defun g2 (x)
  (declare (xargs :guard (g1 x)))
  (mac2 x))

(defun g3 (x)
  (g2 x))

