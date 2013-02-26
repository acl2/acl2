(in-package "ACL2")

;; (include-book "log")

(set-enforce-redundancy nil)

(include-book "../lib1/top")

(set-inhibit-warnings "theory") ; avoid warning in the next event

;;; add on extra definition to bits

(defun bitvec (x n)
  (if (bvecp x n) x 0))

