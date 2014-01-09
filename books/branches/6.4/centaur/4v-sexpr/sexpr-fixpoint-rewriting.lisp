
(in-package "ACL2")

(defttag sexpr-fixpoint-rewriting)

(defun sexpr-fixpoint-rewriting (x)
  (declare (xargs :guard t))
  x)

(progn!
 (set-raw-mode t)
 (defun sexpr-fixpoint-rewriting (x)
   (setq *sexpr-fixpoint-rewrite* x)))

