;; Cuong Chau <cuong.chau@arm.com>

;; March 2021

(in-package "RTL")

(include-book "normalize")

(local (arith-5-for-rtl))

;; ======================================================================

;; Define the normalized dividend x and normalized divisor d satisfying
;; 1 <= x < 2 and 1 <= d < 2.

(defundd x () (sig (a)))

(defundd d () (sig (b)))

(defthm x-bounds
  (and (implies (not (specialp))
                (<= 1 (x)))
       (< (x) 2))
  :hints (("Goal" :in-theory (enable x)))
  :rule-classes :linear)

(defthm d-bounds
  (and (implies (not (specialp))
                (<= 1 (d)))
       (< (d) 2))
  :hints (("Goal" :in-theory (enable d)))
  :rule-classes :linear)

(defthm natp-2^prec-1*x
  (implies (not (specialp))
           (natp (* (expt 2 (1- (prec (f))))
                    (x))))
  :hints (("Goal"
           :use ((:instance exactp-sig
                            (x (bits (opa) 9 0))
                            (n 10))
                 (:instance exactp-sig
                            (x (bits (opa) 22 0))
                            (n 23))
                 (:instance exactp-sig
                            (x (bits (opa) 51 0))
                            (n 52)))
           :in-theory (e/d (specialp
                            a-class
                            f
                            x
                            a
                            opaz
                            opaw
                            fmtw
                            snanp
                            qnanp
                            nanp
                            infp
                            zerp
                            decode
                            sig-ndecode
                            normp
                            denormp
                            encodingp
                            pseudop
                            unsupp
                            exactp2
                            manf)
                           (exactp-sig))))
  :rule-classes :type-prescription)

(defthm natp-2^prec-1*d
  (implies (not (specialp))
           (natp (* (expt 2 (1- (prec (f))))
                    (d))))
  :hints (("Goal"
           :use ((:instance exactp-sig
                            (x (bits (opb) 9 0))
                            (n 10))
                 (:instance exactp-sig
                            (x (bits (opb) 22 0))
                            (n 23))
                 (:instance exactp-sig
                            (x (bits (opb) 51 0))
                            (n 52)))
           :in-theory (e/d (specialp
                            b-class
                            f
                            d
                            b
                            opbz
                            opbw
                            fmtw
                            snanp
                            qnanp
                            nanp
                            infp
                            zerp
                            decode
                            sig-ndecode
                            normp
                            denormp
                            encodingp
                            pseudop
                            unsupp
                            exactp2
                            manf)
                           (exactp-sig))))
  :rule-classes :type-prescription)

(defthmd x57-rewrite
  (implies (not (specialp))
           (equal (x57)
                  (* *2^55* (x))))
  :hints (("Goal"
           :use siga-rewrite
           :in-theory (enable x57 x cat bvecp))))

(defthm x57-bounds
  (and (implies (not (specialp))
                (<= *2^55* (x57)))
       (< (x57) *2^56*))
  :hints (("Goal"
           :use x57-rewrite
           :in-theory (enable x57 cat)))
  :rule-classes :linear)

(bvecthm bvecp56-x57
  (bvecp (x57) 56)
  :hints (("Goal" :in-theory (enable bvecp))))

(defthmd d57-rewrite
  (implies (not (specialp))
           (equal (d57) (* *2^55* (d))))
  :hints (("Goal"
           :use sigb-rewrite
           :in-theory (enable d57 d cat bvecp))))

(defthm d57-bounds
  (and (implies (not (specialp))
                (<= *2^55* (d57)))
       (< (d57) *2^56*))
  :hints (("Goal"
           :use d57-rewrite
           :in-theory (enable d57 cat)))
  :rule-classes :linear)

(bvecthm bvecp56-d57
  (bvecp (d57) 56)
  :hints (("Goal" :in-theory (enable bvecp))))

;; Partial quotients

(defundd quotient (i)
  (if (zp i)
      0
    (+ (quotient (1- i))
       (* (expt 2 (- 1 i)) (q i)))))

(local (in-theory (enable quotient)))

;; Partial remainders

(defundd rmd (i)
  (* (expt 2 (1- i))
     (- (x) (* (d) (quotient i)))))

(defthmd rmd0-rewrite
  (equal (rmd 0) (/ (x) 2))
  :hints (("Goal" :in-theory (enable rmd))))

(defthm rmd0-bound
  (implies (not (specialp))
           (< (abs (rmd 0)) (d)))
  :hints (("Goal" :in-theory (enable rmd0-rewrite)))
  :rule-classes :linear)

(defthmd rmd-recurrence
  (implies (posp j)
           (equal (rmd j)
                  (- (* 2 (rmd (1- j)))
                     (* (q j) (d)))))
  :hints (("Goal" :in-theory (enable rmd))))

(defthm q-bounds
  (and (<= -1 (q j))
       (<= (q j) 1))
  :hints (("Goal"
           :expand (q j)
           :in-theory (enable nextdigit)))
  :rule-classes :linear)
