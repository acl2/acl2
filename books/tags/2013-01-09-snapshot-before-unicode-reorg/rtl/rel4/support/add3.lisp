(in-package "ACL2")

(include-book "merge") ;BOZO yuck
(local (include-book "add3-proofs"))

(defund add3-measure (x y z)
  (acl2-count (+ x y z)))

(defthm add3-1
  (implies (and (integerp x)
                (> x 0))
           (and (>= (fl (/ x 2)) 0)
                (< (fl (/ x 2)) x)))
  :rule-classes ())

(include-book "land")
(include-book "lior")
(include-book "lxor")

(in-theory (enable bits-tail)) ;BOZO

(defthm add-3
  (implies (and (not (zp n))
                (bvecp x n)
                (bvecp y n)
                (bvecp z n))
           (equal (+ x y z)
                  (+ (lxor x (lxor y z n) n)
                     (* 2 (lior (land x y n)
                                (lior (land x z n)
                                      (land y z n)
                                      n)
                                n)))))
  :rule-classes ())

(defthm add-2
  (implies (and (not (zp n))
                (bvecp x n)
                (bvecp y n))
           (equal (+ x y)
                  (+ (lxor x y n)
                     (* 2 (land x y n)))))
  :rule-classes ())