; Book WB: the SAME relation MYREL shown well-founded on a DIFFERENT domain DOM2.
; WB does not include WA, so at WB's certification time MYREL has no entry and
; chk-acceptable-well-founded-relation-rule is satisfied.
(in-package "ACL2")
(defun dom2 (x) (declare (xargs :guard t)) (or (natp x) (equal x :tag)))
(defun myrel (x y) (declare (xargs :guard t)) (and (natp x) (natp y) (< x y)))
(defun emb2 (x) (declare (xargs :guard t)) (if (natp x) x 0))
(defthm myrel-wf-dom2
  (and (implies (dom2 x) (o-p (emb2 x)))
       (implies (and (dom2 x) (dom2 y) (myrel x y))
                (o< (emb2 x) (emb2 y))))
  :rule-classes ((:well-founded-relation)))
