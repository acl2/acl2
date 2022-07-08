(in-package "ACL2")

;; Attempt to connect the ideas in our spec to similar ideas in the RTL library

(include-book "ieee-floats")
(include-book "rtl/rel11/lib/reps" :dir :system)
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(defthm expo-becomes-log2
  (implies (and (< 0 rat)
                (rationalp rat))
           (equal (rtl::expo rat)
                  (log2 rat)))
  :hints (("Goal" :in-theory (enable rtl::expo log2))))

(defthm expo-becomes-log2-when-negative
  (implies (and (< rat 0)
                (rationalp rat))
           (equal (rtl::expo rat)
                  (log2 (- rat))))
  :hints (("Goal" :in-theory (enable rtl::expo log2))))

(defthm representable-normalp-becomes-nrepp
  (implies (and (rationalp rat)
                (formatp k p)
)
           (equal (representable-normalp k p rat)
                  (rtl::nrepp rat (list nil ; formal doesn't store the leading bit of significand
                                        p   ; precision
                                        (wfn k p) ; exponent width
                                        ))))
  :hints (("Goal" :in-theory (enable formatp representable-normalp emin emax wfn
                                     rtl::nrepp
                                     rtl::formatp rtl::bias rtl::expw rtl::prec rtl::sig rtl::exactp
                                     representable-positive-normalp))))

(local (include-book "ieee-floats-helpers")) ;todo: move up, but that may break a proof

(defthmd *-of-expt-and-/-of-expt
  (implies (and (integerp i)
                (integerp j))
           (equal (* (expt 2 i) (/ (expt 2 j)))
                  (expt 2 (- i j))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm <=-of-log2-when-<=-of-expt2-linear
  (implies (and (<= (expt 2 i) rat)
                (integerp i)
                (rationalp rat))
           (<= i (log2 rat)))
  :rule-classes :linear)

(defthm <-of-log2-when-<-of-expt2-linear
  (implies (and (< rat (expt 2 i))
                (integerp i)
                (rationalp rat)
                (< 0 rat))
           (< (log2 rat) i))
  :rule-classes :linear)


;; (defthmd *-of-/-of-expt-and-expt
;;   (implies (and (integerp i)
;;                 (integerp j))
;;            (equal (* (/ (expt 2 i)) (expt 2 j))
;;                   (expt 2 (- j i))))
;;   :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm not-integer-of-*-of-expt2-when-<-of-expt2-of--
  (implies (and (< rat (expt 2 (- i)))
                (rationalp rat)
                (< 0 rat))
           (not (integerp (* rat (expt 2 i))))))

(defthm <-of-log2-arg2
  (implies (and (integerp i)
                (< 0 rat)
                (rationalp rat))
           (equal (< i (log2 rat))
                  (<= (expt 2 (+ 1 i)) rat))))

(defthm <-of-+-of-log2
  (implies (and (integerp i1)
                (integerp i2)
                (< 0 rat)
                (rationalp rat))
           (equal (< i1 (+ (log2 rat) i2))
                  (<= (expt 2 (+ 1 (- i1 i2))) rat))))

(defthm <-of-+-of-log2-arg1
  (implies (and (integerp i1)
                (integerp i2)
                (< 0 rat)
                (rationalp rat))
           (equal (< (+ (log2 rat) i1) i2)
                  (< rat (expt 2 (- i2 i1)))))
  :hints (("Goal" :use (:instance <-of-log2-arg1 (i (- i2 i1)))
           :in-theory (disable <-of-log2-arg1))))

(defthm representable-subnormalp-becomes-drepp
  (implies (and (rationalp rat)
                (formatp k p))
           (equal (representable-subnormalp k p rat)
                  (rtl::drepp rat (list nil ; formal doesn't store the leading bit of significand
                                        p   ; precision
                                        (wfn k p) ; exponent width
                                        ))))
  :hints (("Goal"
           :use ((:instance not-integer-of-*-of-expt2-when-<-of-expt2-of-- (i (+ -3 p (expt 2 (+ -1 k (- p))))))
                 (:instance not-integer-of-*-of-expt2-when-<-of-expt2-of-- (rat (- rat)) (i (+ -3 p (expt 2 (+ -1 k (- p)))))))
           :in-theory (e/d (formatp representable-subnormalp representable-positive-subnormalp emin emax wfn
                                     rtl::drepp
                                     rtl::formatp
                                     rtl::bias
                                     rtl::expw rtl::prec rtl::sig rtl::exactp
                                     *-of-expt-and-/-of-expt
                                     *-of-/-of-expt-and-expt)
                           (not-integer-of-*-of-expt2-when-<-of-expt2-of--)))))
