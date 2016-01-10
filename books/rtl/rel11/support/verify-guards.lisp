(in-package "RTL")

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))
(local (in-theory (acl2::enable-arith5)))

(include-book "definitions")
(local (include-book "basic"))
(local (include-book "bits"))

;; From bits.lisp:

(verify-guards digit-diff
  :hints (("goal" :in-theory (e/d (digitn digits fl)
                                  (digits-n-n-rewrite digit-diff)))))

(defn digit-diff (x y b)
  (declare (xargs :measure (:? x y)))
  (if (or (not (integerp x))
          (not (integerp y))
          (not (radixp b))
          (= x y))
      ()
    (if (= (digitn x 0 b) (digitn y 0 b))
        (1+ (digit-diff (fl (/ x b)) (fl (/ y b)) b))
      0)))

(verify-guards bit-diff
  :hints (("goal" :cases ((equal (fl (/ x 2)) (fl (/ y 2))))
           :in-theory (e/d (bitn bits fl)
                           (bits-n-n-rewrite bit-diff)))))

(defn bit-diff (x y)
  (declare (xargs :measure (:? x y)))
  (if (or (not (integerp x)) (not (integerp y)) (= x y))
      ()
    (if (= (bitn x 0) (bitn y 0))
        (1+ (bit-diff (fl (/ x 2)) (fl (/ y 2))))
      0)))

(verify-guards binary-cat)

(defund binary-cat (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

(verify-guards mulcat-r)

(defund mulcat-r (l n x b)
  (declare (xargs :guard (and (natp n)
                              (dvecp x l b))))
  (if (and (integerp n) (> n 0))
      (cat-r b (mulcat-r l (1- n) x b)
             (* l (1- n))
             x
             l)
    0))

(verify-guards mulcat)

(defund mulcat (l n x)
  (declare (xargs :guard (and (natp l)
                              (natp n)
                              (natp x))
                  :verify-guards nil))
  (if (and (integerp n) (> n 0))
      (cat (mulcat l (1- n) x)
           (* l (1- n))
           x
           l)
    0))

; reps.lisp

(local (include-book "reps"))

(verify-guards nencode
  :hints (("goal" :in-theory (enable nrepp exactp))))

(defund nencode (x f)
  (declare (xargs :guard (nrepp x f)))
  (cat (if (= (sgn x) 1) 0 1)
       1
       (+ (expo x) (bias f))
       (expw f)
       (* (sig x) (expt 2 (1- (prec f))))
       (sigw f)))

(verify-guards zencode)

(defund zencode (sgn f)
  (declare (xargs :guard (and (bvecp sgn 1)
                              (formatp f))))
  (cat sgn 1 0 (+ (sigw f) (expw f))))

(verify-guards dencode
  :hints (("goal" :in-theory (enable drepp exactp))))

(defund dencode (x f)
  (declare (xargs :guard (drepp x f)))
  (cat (if (= (sgn x) 1) 0 1)
       1
       0
       (expw f)
       (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f))))
       (sigw f)))

(verify-guards iencode)

(defun iencode (sgn f)
  (declare (xargs :guard (and (bvecp sgn 1)
                              (formatp f))))
  (if (explicitp f)
      (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 1 1 0 (1- (sigw f)))
    (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 0 (sigw f))))

(verify-guards indef
  :hints (("goal" :in-theory (enable formatp sigw prec))))

(defund indef (f)
  (declare (xargs :guard (formatp f)))
  (if (explicitp f)
      (cat (1- (expt 2 (+ (expw f) 3)))
           (+ (expw f) 3)
           0
           (- (sigw f) 2))
    (cat (1- (expt 2 (+ (expw f) 2)))
         (+ (expw f) 2)
         0
         (1- (sigw f)))))
