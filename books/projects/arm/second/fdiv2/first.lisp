;; Cuong Chau <cuong.chau@arm.com>

;; January 2021

;; Establish the relationship between the partial remainder and
;; (rs57 + rc57). From this relationship, prove the remainder bound invariant.

;; rmd(j) = 2^-55 * (si(rs57(j), 57) + si(rc57(j), 57)),

;; -d <= rmd(j) < d,

;; where j >= 1.

;; We handle the first SRT iteration in this book.

(in-package "RTL")

(include-book "algorithm")

(local (arith-5-for-rtl))

;; ======================================================================

;; Remainder approximation

(defundd approx (i)
  (+ (si (bits (rs57 i) 56 54) 3)
     (si (bits (rc57 i) 56 54) 3)))

(defthm fmtrem-bounds
  (and (<= 1 (fmtrem))
       (<= (fmtrem) 3))
  :hints (("Goal" :in-theory (enable fmtrem bits)))
  :rule-classes :linear)

(bvecthm bvecp57-rs-0
  (bvecp (rs-0) 57)
  :hints (("Goal" :in-theory (enable rs-0))))

(bvecthm bvecp57-rc-0
  (bvecp (rc-0) 57)
  :hints (("Goal" :in-theory (enable rc-0))))

(defthmd rs-0-rewrite
  (implies (not (specialp))
           (equal (rs-0)
                  (case (fmtrem)
                    (3 (+ *2^2* (* *2^55* (x))))
                    (2 (+ *2^31* (* *2^55* (x))))
                    (1 (+ *2^44* (* *2^55* (x)))))))
  :hints (("Goal"
           :use (natp-2^prec-1*x
                 (:instance bits-shift-up-1
                            (x (* *2^52* (x)))
                            (i 56)
                            (j 3)
                            (k 3))
                 (:instance bits-shift-up-1
                            (x (* *2^23* (x)))
                            (i 56)
                            (j 32)
                            (k 32))
                 (:instance bits-shift-up-1
                            (x (* *2^10* (x)))
                            (i 56)
                            (j 45)
                            (k 45))
                 (:instance bits-shift-up-2
                            (x (* *2^52* (x)))
                            (i -2)
                            (k 3))
                 (:instance bits-shift-up-2
                            (x (* *2^23* (x)))
                            (i -2)
                            (k 32))
                 (:instance bits-shift-up-2
                            (x (* *2^10* (x)))
                            (i -2)
                            (k 45)))
           :in-theory (enable rs-0 fmtrem x57-rewrite f cat))))

(local
 (defthm-nl aux-1
   (implies (and (integerp x)
                 (natp m)
                 (integerp n)
                 (< x (expt 2 m))
                 (< y (expt 2 n)))
            (< (+ (* (expt 2 n) x) y)
               (expt 2 (+ m n))))
   :rule-classes :linear))

(defthm rs-0-lower-bounds
  (and (implies (and (not (specialp))
                     (equal (fmtrem) 3))
                (<= (+ *2^2* *2^55*) (rs-0)))
       (implies (and (not (specialp))
                     (equal (fmtrem) 2))
                (<= (+ *2^31* *2^55*) (rs-0)))
       (implies (and (not (specialp))
                     (equal (fmtrem) 1))
                (<= (+ *2^44* *2^55*) (rs-0))))
  :hints (("Goal" :in-theory (enable rs-0-rewrite)))
  :rule-classes :linear)

(defthm rs-0-upper-bound
  (implies (not (specialp))
           (< (rs-0) *2^56*))
  :hints (("Goal"
           :use (natp-2^prec-1*x
                 (:instance aux-1
                            (x (* (expt 2 (1- (prec (f))))
                                  (x)))
                            (y (expt 2 (- 55 (prec (f)))))
                            (m (prec (f)))
                            (n (- 56 (prec (f))))))
           :in-theory (enable rs-0-rewrite fmtrem f)))
  :rule-classes :linear)

(defthmd rc-0-rewrite
  (implies (not (specialp))
           (equal (rc-0)
                  (case (fmtrem)
                    (3 (+ (- *2^2*)
                          *2^57*
                          (- (* *2^55* (q 1) (d)))))
                    (2 (+ (- *2^31*)
                          *2^57*
                          (- (* *2^55* (q 1) (d)))))
                    (1 (+ (- *2^44*)
                          *2^57*
                          (- (* *2^55* (q 1) (d))))))))
  :hints (("Goal"
           :use (natp-2^prec-1*d
                 (:instance bits-plus-mult-1
                            (x (1- *2^2*))
                            (y (+ -1 *2^55* (- (* *2^53* (d)))))
                            (k 2)
                            (n 56)
                            (m 2))
                 (:instance bits-plus-mult-1
                            (x (1- *2^31*))
                            (y (+ -1 *2^26* (- (* *2^24* (d)))))
                            (k 31)
                            (n 56)
                            (m 31))
                 (:instance bits-plus-mult-1
                            (x (1- *2^44*))
                            (y (+ -1 *2^13* (- (* *2^11* (d)))))
                            (k 44)
                            (n 56)
                            (m 44)))
           :in-theory (enable rc-0
                              fmtrem
                              q
                              d57-rewrite
                              f
                              bits-lognot
                              cat
                              bvecp))))

(defthm rc-0-lower-bound
  (implies (not (specialp))
           (< (expt 2 56) (rc-0)))
  :hints (("Goal"
           :use (natp-2^prec-1*d
                 (:instance aux-1
                            (x (* (expt 2 (1- (prec (f))))
                                  (d)))
                            (y (expt 2 (- 55 (prec (f)))))
                            (m (prec (f)))
                            (n (- 56 (prec (f))))))
           :in-theory (enable rc-0-rewrite fmtrem f q)))
  :rule-classes :linear)

(defthm rc-0-upper-bounds
  (and (implies (and (not (specialp))
                     (equal (fmtrem) 3))
                (<= (rc-0) (+ (- *2^2*) *2^57* (- *2^55*))))
       (implies (and (not (specialp))
                     (equal (fmtrem) 2))
                (<= (rc-0) (+ (- *2^31*) *2^57* (- *2^55*))))
       (implies (and (not (specialp))
                     (equal (fmtrem) 1))
                (<= (rc-0) (+ (- *2^44*) *2^57* (- *2^55*)))))
  :hints (("Goal" :in-theory (enable rc-0-rewrite q)))
  :rule-classes :linear)

(defthm natp-2^55*x
  (implies (not (specialp))
           (natp (* *2^55* (x))))
  :hints (("Goal"
           :use siga-rewrite
           :in-theory (enable x)))
  :rule-classes :type-prescription)

(defthm integerp-2^55*-d
  (implies (not (specialp))
           (integerp (* (- *2^55*) (d))))
  :hints (("Goal"
           :use sigb-rewrite
           :in-theory (enable d)))
  :rule-classes :type-prescription)

(defthmd rmd1-rewrite
  (implies (not (specialp))
           (equal (rmd 1)
	          (* (/ *2^55*)
                     (+ (si (rs57 1) 57)
                        (si (rc57 1) 57)))))
  :hints (("Goal"
           :use (rs-0-upper-bound
                 rc-0-lower-bound)
           :in-theory (enable rmd-recurrence
                              rmd0-rewrite
                              rs57
                              rc57
                              rs-0-rewrite
                              rc-0-rewrite
                              q
                              si
                              bvecp))))

(defthm rmd1-bounds
  (implies (not (specialp))
           (and (< (- (d)) (rmd 1))
                (< (rmd 1) (d))))
  :hints (("Goal" :in-theory (enable rmd-recurrence rmd0-rewrite q)))
  :rule-classes :linear)

(defthmd bits-siga-0
  (implies (equal n (- 52 (prec (f))))
           (equal (bits (siga) n 0)
                  0))
  :hints (("Goal"
           :use ((:instance bits-shift-up-1
                            (x (mana))
                            (i (- 52 (prec (f))))
                            (j 0)
                            (k (- 53 (prec (f)))))
                 (:instance bits-shift-up-1
                            (x (mana))
                            (i (- 52 (prec (f))))
                            (j 0)
                            (k (+ 53
                                  (bits (clz53 (* (expt 2 (- 53 (prec (f))))
                                                  (mana)))
                                        5 0)
                                  (- (prec (f)))))))
           :in-theory (enable f
                              siga
                              cat-for-gl
                              bits-logior
                              bvecp
                              normalize))))

(defthmd bits-sigb-0
  (implies (equal n (- 52 (prec (f))))
           (equal (bits (sigb) n 0)
                  0))
  :hints (("Goal"
           :use ((:instance bits-shift-up-1
                            (x (manb))
                            (i (- 52 (prec (f))))
                            (j 0)
                            (k (- 53 (prec (f)))))
                 (:instance bits-shift-up-1
                            (x (manb))
                            (i (- 52 (prec (f))))
                            (j 0)
                            (k (+ 53
                                  (bits (clz53 (* (expt 2 (- 53 (prec (f))))
                                                  (manb)))
                                        5 0)
                                  (- (prec (f)))))))
           :in-theory (enable f
                              sigb
                              cat-for-gl
                              bits-logior
                              bvecp
                              normalize))))

(defthmd bits-x57-0
  (implies (equal n (- 55 (prec (f))))
           (equal (bits (x57) n 0)
                  0))
  :hints (("Goal" :in-theory (enable x57 f bits-siga-0))))

(defthmd bits-d57-0
  (implies (equal n (- 55 (prec (f))))
           (equal (bits (d57) n 0)
                  0))
  :hints (("Goal" :in-theory (enable d57 f bits-sigb-0))))

(defthmd bits-rs-0-0
  (implies (equal n (case (fmtrem)
                      (3 1)
                      (2 30)
                      (1 43)))
           (equal (bits (rs-0) n 0)
                  0))
  :hints (("Goal"
           :use ((:instance bits-x57-0
                            (n (- 55 (prec (f)))))
                 (:instance bits-plus-bits
                            (x (x57))
                            (m 0)
                            (n (- 55 (prec (f))))
                            (p 2))
                 (:instance bitn-plus-bits
                            (x (x57))
                            (m 0)
                            (n (- 55 (prec (f))))))
           :in-theory (enable rs-0 fmtrem f))))

(defthmd bits-rc-0-0
  (implies (equal n (case (fmtrem)
                      (3 1)
                      (2 30)
                      (1 43)))
           (equal (bits (rc-0) n 0)
                  0))
  :hints (("Goal" :in-theory (enable rc-0))))
