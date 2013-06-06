(in-package "ACL2")

;; (include-book "log")

(set-enforce-redundancy nil)

(include-book "../lib1/top")

(set-inhibit-warnings "theory") ; avoid warning in the next event


(defthm bcevp-nencode
  (implies (and (equal k (+ p q))
                (natp p)
                (natp q))
           (bvecp (nencode x p q) k))
  :hints (("Goal" :in-theory (enable nencode))))
