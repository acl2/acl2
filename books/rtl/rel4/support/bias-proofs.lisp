(in-package "ACL2")

(local (include-book "../arithmetic/expt"))
(local (include-book "bvecp"))
(local (include-book "../arithmetic/integerp"))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

; bias of a q bit exponent field is 2^(q-1)-1
(defund bias (q) (- (expt 2 (- q 1)) 1) )

(defthm bias-non-negative-integerp-type-prescription
  (implies (and (case-split (integerp q))
                (case-split (< 0 q))
                )
           (and (integerp (bias q))
                (<= 0 (bias q))))
  :hints (("Goal" :in-theory (enable bias)))
  :rule-classes :TYPE-PRESCRIPTION
  )

(encapsulate
 ()
 (local (defthm bias-bvecp-aux
          (implies (and (< 0 q)
                        (integerp q))
                   (BVECP (BIAS Q) (1- Q)))
          :rule-classes nil
          :hints (("Goal" :in-theory (set-difference-theories
                                      (enable bias bvecp expt ;-split
                                              )
                                      '())))))

 (defthm bias-bvecp
   (implies (and (<= (1- q) q2)
                 (case-split (< 0 q))
                 (case-split (integerp q))
                 (case-split (integerp q2))
                 )
            (BVECP (BIAS Q) q2))
   :hints (("Goal" :in-theory (enable bvecp-longer)
            :use bias-bvecp-aux)))
 )

(defthm bias-integerp-rewrite
  (equal (integerp (bias q))
         (or (and (acl2-numberp q) (not (integerp q)))
             (<= 1 q)))
  :hints (("Goal" :in-theory (enable bias))))

;where's bias-integerp?
(defthm bias-integerp
  (implies (case-split (< 0 k))
           (integerp (bias k)))
  :hints (("Goal" :in-theory (enable bias))))

(defthm bias-with-q-an-acl2-number-but-not-an-integer
  (implies (and (not (integerp q))
                (case-split (acl2-numberp q)))
           (equal (bias q)
                  0))
  :hints (("Goal" :in-theory (enable bias))))

(defthm bias-with-q-not-an-acl2-number
  (implies (not (acl2-numberp q))
           (equal (bias q)
                  -1/2))
  :hints (("Goal" :in-theory (enable bias))))