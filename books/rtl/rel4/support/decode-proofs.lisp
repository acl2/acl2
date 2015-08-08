(in-package "ACL2")

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(include-book "ground-zero")

#|(defun decode (x n)
  (if (< x n) (ash 1 x) 0))
(in-theory (disable decode))
|#

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(local (include-book "../arithmetic/fl"))
(local (include-book "ash"))
(local (include-book "bvecp"))

(defund decode (x n)
  (declare (xargs :guard (rationalp n)))
  (if (and (natp x) (< x n))
      (ash 1 x)
    0))

(defthm decode-nonnegative-integer-type
  (and (integerp (decode x n))
       (<= 0 (decode x n)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable decode))))

;this rule is no better than decode-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription decode)))

(defthm decode-natp
  (natp (decode x n)))

(defthm decode-bvecp
  (implies (and (<= n k)
                (case-split (integerp k))
                )
           (bvecp (decode x n) k))
  :hints (("Goal" :in-theory (enable decode))))
