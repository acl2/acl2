(in-package "ACL2")

(local (include-book "../support/bias"))

;; Necessary defuns

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

;; Start of new stuff

; bias of a q bit exponent field is 2^(q-1)-1
(defund bias (q) (- (expt 2 (- q 1)) 1) )

(defthm bias-non-negative-integerp-type-prescription
  (implies (and (case-split (integerp q))
                (case-split (< 0 q))
                )
           (and (integerp (bias q))
                (<= 0 (bias q))))
  :rule-classes :TYPE-PRESCRIPTION)

;BOZO rename q2 to k?
(defthm bias-bvecp
   (implies (and (<= (+ -1 q) q2)
                 (case-split (< 0 q))
                 (case-split (integerp q))
                 (case-split (integerp q2))
                 )
            (bvecp (bias q) q2)))

(defthm bias-integerp-rewrite
  (equal (integerp (bias q))
         (or (and (acl2-numberp q) (not (integerp q)))
             (<= 1 q))))

;where's bias-integerp?
(defthm bias-integerp
  (implies (case-split (< 0 k))
           (integerp (bias k))))

(defthm bias-with-q-an-acl2-number-but-not-an-integer
  (implies (and (not (integerp q))
                (case-split (acl2-numberp q)))
           (equal (bias q)
                  0)))

(defthm bias-with-q-not-an-acl2-number
  (implies (not (acl2-numberp q))
           (equal (bias q)
                  -1/2)))