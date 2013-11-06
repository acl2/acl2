#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "ihs/ihs-lemmas" :dir :system)

(local (include-book "arithmetic"))
(include-book "evenp")

(in-theory (disable logcar))

(defthm logcar-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logcar i) 
                  0))
  :hints (("goal" :in-theory (enable logcar ifix))))

;generalize the 1?
(defthm unsigned-byte-p-logcar
  (unsigned-byte-p 1 (logcar x))
  :hints (("goal" :in-theory (enable logcar)))
  :rule-classes ((:forward-chaining :trigger-terms ((logcar x)))
                 (:rewrite)))

;note the backchain-limit
(defthm logcar-identity
  (implies (unsigned-byte-p 1 x)
           (equal (logcar x)
                  x))
  :hints (("goal" :in-theory (enable logcar)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm logcar--
  (implies (integerp x)
           (equal (logcar (- x))
                  (logcar x)))
  :hints (("goal" :in-theory (enable logcar))))

(defthm logcar-expt
  (implies (<= 0 n)
           (equal (logcar (expt 2 n))
                  (if (zp n) 1 0)))
  :hints (("goal" :in-theory (enable expt))))

;improve this?
(defthm logcar-+
  (implies (integerp i)
           (equal (logcar (+ i j))
                  (if (integerp j)
                      (b-xor (logcar j) (logcar i))
                    (if (acl2-numberp j)
                        0
                      (logcar i)))))
  :hints (("Goal" ;:do-not '(generalize eliminate-destructors)
           :in-theory (enable oddp logcar b-xor))))

(defthm logcar-+-alt
  (implies (integerp j)
           (equal (logcar (+ i j))
                  (if (integerp i)
                      (b-xor (logcar i) (logcar j))
                    (if (acl2-numberp i)
                        0
                      (logcar j)))))
  :hints (("Goal" :use (:instance logcar-+ (i j) (j i)) 
           :in-theory (disable logcar-+))))

(defthm logcar-evenp
  (implies (evenp x)
           (equal (logcar x)
                  0))
  :hints (("goal" :in-theory (enable logcar))))

(defthm logcar-*-1/2-expt
  (implies (< 0 n)
           (equal (logcar (* 1/2 (expt 2 n)))
                  (if (equal n 1)
                      1 0)))
  :hints (("goal" :in-theory (enable logcar))))

;or is LOGCAR-+ good enough?
(defthmd logcar-i+j+2*k
  (implies (and (integerp i)
                (integerp j)
                (integerp k))
           (equal (logcar (+ i j (* 2 k)))
                  (logcar (+ i j))))
  :hints (("Goal" 
           :use ((:instance logcar-i+2*j (i (+ i j)) (j k))))))

(defthm logcar-range
  (and (<= (logcar i) 1)
       (<= 0 (logcar i))))


(defthm logcar-range-linear
  (and (<= (logcar i) 1)
       (<= 0 (logcar i)))
  :rule-classes :linear)

(defthm logcar-of-logcar
  (equal (logcar (logcar i))
         (logcar i))
  :hints (("Goal" :in-theory (enable logcar))))

(defthmd oddp-to-logcar
  (implies (integerp i)
           (equal (oddp i)
                  (equal 1 (logcar i))))
  :hints (("Goal" :in-theory (enable oddp))))

(defthmd oddp-rewrite-to-logcar-fact
  (implies (integerp x)
           (equal (oddp x)
                  (not (equal 0 (logcar x))))))

(defthm logcar-ash-pos
  (implies (and (< 0 n)
                (integerp n))
           (equal (logcar (ash x n))
                  0))
  :hints (("goal" :in-theory (enable logcar ash))))

(defthm evenp-of-logcar
  (equal (evenp (logcar m))
         (evenp (ifix m))))


;move
;think more about this
;might loop??
(defthm logcar-0-rewrite
  (equal (equal (logcar i) 0)
         (or (not (integerp i))
             (evenp i))))


(defthm logcar-of-times
  (implies (and (integerp x)
                (integerp y))
           (equal (logcar (* x y))
                  (if (or (evenp x)
                          (evenp y))
                      0
                    1))))
