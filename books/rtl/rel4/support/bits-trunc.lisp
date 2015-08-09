;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

;BOZO include less...
(include-book "log")
(include-book "float")
(include-book "trunc")
(include-book "land")
(local (include-book "bits-trunc-proofs"))

(defthm bits-trunc-2
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp k)
                (> k 0)
                )
           (= (trunc x k)
              (* (expt 2 (- n k))
                 (bits x (1- n) (- n k)))))
  :rule-classes ())

(defthm bits-trunc
  (implies (and (>= x (expt 2 (1- n)))
                (< x (expt 2 n))
                (integerp x) (> x 0)
                (integerp m) (>= m n)
                (integerp n) (> n k)
                (integerp k) (> k 0)
                )
           (= (trunc x k)
              (land x (- (expt 2 m) (expt 2 (- n k))) n)))
  :rule-classes ())
