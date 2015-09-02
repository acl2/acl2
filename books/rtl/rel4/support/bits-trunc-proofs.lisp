;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(local (include-book "trunc"))
(include-book "log")
(include-book "float")
(include-book "trunc")
(local (include-book "bits"))
(local (include-book "../arithmetic/top"))
(local (in-theory (enable expt-minus)))

(defthm bits-trunc-2
  (implies (and (= n (1+ (expo x)))
;(rationalp x) ;(integerp x)
                (>= x 0)
                ;(integerp n)
;                (>= n k)
                (integerp k)
                (> k 0)
                )
           (= (trunc x k)
              (* (expt 2 (- n k))
                 (bits x (1- n) (- n k)))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable bits trunc-rewrite expt-split))))


(local
 (defthm bits-trunc-3
   (implies (and (integerp x)
                 (> x 0)
                 (integerp n) (> n k)
                 (integerp k) (> k 0)
                 (= (expo x) (1- n)))
            (= (trunc x k)
               (logand x (- (expt 2 n) (expt 2 (- n k))))))
   :rule-classes ()
   :hints (("goal" :use ((:instance bits-trunc-2)
                         (:instance logand-slice (k (- n k)))))
           )))

(local
 (defthm bits-trunc-4
   (implies (and (integerp x) (> x 0)
                 (integerp n) (> n k)
                 (integerp k) (> k 0)
                 (>= x (expt 2 (1- n)))
                 (< x (expt 2 n)))
            (= (trunc x k)
               (logand x (- (expt 2 n) (expt 2 (- n k))))))
   :rule-classes ()
   :hints (("goal" :use ((:instance bits-trunc-3)
                         (:instance expo-unique (n (1- n))))))))

(local
 (defthm bits-trunc-5
   (implies (and (integerp x) (> x 0)
                 (integerp m) (>= m n)
                 (integerp n) (> n k)
                 (integerp k) (> k 0)
                 (>= x (expt 2 (1- n)))
                 (< x (expt 2 n)))
            (= (trunc x k)
               (logand x (mod (- (expt 2 m) (expt 2 (- n k))) (expt 2 n)))))
   :rule-classes ()
   :hints (("goal" :use ((:instance bits-trunc-4)
                         ;(:instance mod-2m-2n-k)
                         )))))

(include-book "land")
(include-book "merge")

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
  :rule-classes ()
  :hints (("goal" :in-theory (e/d (bits-tail land expt-split) (expt-minus))
		  :use ((:instance bits-trunc-5)))))

#|
(defthm bits-trunc-6
  (implies (and (integerp x) (> x 0)
                (integerp m) (>= m n)
                (integerp n) (> n k)
                (integerp k) (> k 0)
                (>= x (expt 2 (1- n)))
                (< x (expt 2 n)))
           (= (trunc x k)
              (logand x (- (expt 2 m) (expt 2 (- n k))))))
  :rule-classes ()
  :hints (("goal" :use (;(:instance hack-82)
                        (:instance bits-trunc-5)
			(:instance expt-weak-monotone (n (- n k)))
			(:instance and-dist-d (y (- (expt 2 m) (expt 2 (- n k)))))))))
|#





