(in-package "ACL2")

;I believe this theorem is used to admit model.lisp when it contains -aux functions

(include-book "rtl")

(local (include-book "bits"))

(defthmd bits-reduce
  (implies (and (< x (expt 2 (+ 1 i)))
                (case-split (integerp x))
                (case-split (<= 0 x))
                (case-split (integerp i))
                )
           (equal (bits x i 0) x)))



