; Book WA: relation MYREL shown well-founded on domain DOM1.
(in-package "ACL2")
(defun dom1 (x) (declare (xargs :guard t)) (natp x))
(defun myrel (x y) (declare (xargs :guard t)) (and (natp x) (natp y) (< x y)))
(defun emb1 (x) (declare (xargs :guard t)) (if (natp x) x 0))
(defthm myrel-wf-dom1
  (and (implies (dom1 x) (o-p (emb1 x)))
       (implies (and (dom1 x) (dom1 y) (myrel x y))
                (o< (emb1 x) (emb1 y))))
  :rule-classes ((:well-founded-relation)))
