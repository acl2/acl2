(in-package "RTL")

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))

(include-book "definitions")
(local (include-book "basic"))
(local (include-book "bits"))
(local (include-book "float"))

;; From bits.lisp:

(acl2::with-arith5-help
 (verify-guards digit-diff
   :hints (("goal" :in-theory (e/d (digitn digits fl)
                                   (digits-n-n-rewrite digit-diff))))))

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

(acl2::with-arith5-help
 (verify-guards bit-diff
   :hints (("goal" :cases ((equal (fl (/ x 2)) (fl (/ y 2))))
            :in-theory (e/d (bitn bits fl)
                            (bits-n-n-rewrite bit-diff))))))

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

(acl2::with-arith5-help
 (verify-guards mulcat-r))

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

;; From float.lisp:

(local (defnd expo-exec(x)
  (if (rationalp x)
      (let* ((n (abs (numerator x)))
             (d (denominator x))
             (ln (integer-length n))
             (ld (integer-length d))
             (l (- ln ld)))
        (if (>= ln ld)
            (if (>= (ash n (- l)) d) l (1- l))
          (if (> ln 1)
              (if (> n (ash d l)) l (1- l))
            (- (integer-length (1- d))))))
    0)))

(defruled expo-exec-thm
  (equal (expo-exec x) (expo x))
 :enable (expo-exec
          integer-length-when-posp
          expo-exec-1
          expo-exec-2
          expo-exec-3
          expo-exec-4
          expo-exec-5
          acl2::|arith (- (+ x y))|
          acl2::|arith (- (- x))|)
 :local t
 :disable (abs expo ash)
 :use lemma1
 :prep-lemmas
 ((defrule bounds-by-integer-length
     (implies (posp n)
              (and (<= (expt 2 (1- (integer-length n))) n)
                   (< n (expt 2 (integer-length n)))))
     :rule-classes ()
     :prep-books ((local (include-book "centaur/bitops/integer-length" :dir :system)))
     :disable (expt integer-length))

   (defruled integer-length-when-posp
     (implies (posp n)
              (equal (integer-length n)
                     (1+ (expo n))))
     :use (bounds-by-integer-length
           (:instance expo-unique
                      (x n)
                      (n (1- (integer-length n)))))
     :disable (expt integer-length))

   (defruled expo-quot-by-sig
     (let* ((n (abs (numerator x)))
            (d (denominator x))
            (en (expo n))
            (ed (expo d)))
       (implies
        (and (rationalp x)
             (not (= x 0)))
        (and (implies (>= (sig n) (sig d))
                      (equal (equal (+ (- ed) en) (expo x)) t))
             (implies (< (sig n) (sig d))
                      (equal (equal (+ -1 (- ed) en) (expo x)) t)))))
     :enable acl2::|arith (- (- x))|
     :disable (abs rational-implies2)
     :use (rational-implies2
           (:instance lemma
                      (n (numerator x))
                      (d (denominator x))))
     :prep-lemmas
     ((acl2::with-arith5-nonlinear++-help
       (defrule lemma
         (let ((en (expo (abs n)))
               (ed (expo d)))
           (implies (and (rationalp n) (not (= n 0))
                         (rationalp d) (> d 0))
                    (equal (expo (* (/ d) n))
                           (if (>= (sig (abs n)) (sig d))
                               (- en ed)
                             (1- (- en ed))))))
         :rule-classes ()
         :enable sig
         :use ((:instance expo-unique
                          (x (/ n d))
                          (n (if (>= (* (abs n) (expt 2 (- (expo n))))
                                     (* d (expt 2 (- (expo d)))))
                                 (- (expo n) (expo d))
                               (1- (- (expo n) (expo d))))))
               (:instance expo-lower-bound (x n))
               (:instance expo-upper-bound (x n))
               (:instance expo-lower-bound (x d))
               (:instance expo-upper-bound (x d)))))))

   (defruled expo-quot-by-sig>=
     (let* ((n (abs (numerator x)))
            (d (denominator x))
            (en (expo n))
            (ed (expo d)))
       (implies
        (and (rationalp x)
             (not (= x 0))
             (>= (sig n) (sig d)))
        (equal (equal (+ (- ed) en) (expo x)) t)))
     :use expo-quot-by-sig)

   (defruled expo-quot-by-sig<
     (let* ((n (abs (numerator x)))
            (d (denominator x))
            (en (expo n))
            (ed (expo d)))
       (implies
        (and (rationalp x)
             (not (= x 0))
             (< (sig n) (sig d)))
        (equal (equal (+ -1 (- ed) en) (expo x)) t)))
     :use expo-quot-by-sig)

   (acl2::with-arith5-help
    (defruled expo-guard-shift-n
      (implies (and (rationalp n) (>= n 0)
                    (rationalp d) (> d 0))
               (equal (< (sig n) (sig d))
                      (< (* n (expt 2 (- (expo d) (expo n)))) d)))
      :enable sig))

   (acl2::with-arith5-nonlinear++-help
    (defruled expo-guard-shift-d
      (implies (and (rationalp n) (>= n 0)
                    (rationalp d) (> d 0))
               (equal (< (sig n) (sig d))
                      (< n (* d (expt 2 (- (expo n) (expo d)))))))
      :enable sig))

   (defruled abs-posp-type
     (implies (and (integerp x)
                   (not (= x 0)))
              (posp (abs x)))
     :rule-classes :type-prescription)

   (defruled expo-exec-1
     (let* ((n (abs (numerator x)))
            (d (denominator x))
            (en (expo n))
            (ed (expo d)))
       (implies (and (rationalp x)
                     (not (= x 0))
                     (< en ed)
                     (> en 0)
                     (<= n (ash d (+ (- ed) en))))
                (equal (+ -1 (- ed) en)
                       (expo x))))
     :enable (expo-guard-shift-d abs-posp-type)
     :use expo-quot-by-sig<
     :disable (abs ash)
     :prep-lemmas
     ((acl2::with-arith5-help
       (defrule lemma
         (implies (and (integerp x)
                       (integerp n))
                  (<= (ash x n)
                      (* x (expt 2 n))))
         :rule-classes ((:linear :trigger-terms ((ash x n))))))
      (acl2::with-arith5-nonlinear-help
       (defruled lemma2
         (let* ((n (abs (numerator x)))
                (d (denominator x)))
           (implies (and (integerp k)
                         (< k 0)
                         (> n 1)
                         )
                    (not (equal (* d (expt 2 k)) n))))
         :use (:instance lowest-terms
                         (x (abs x))
                         (n (abs (numerator x)))
                         (r 1)
                         (q (expt 2 (- k))))))
      (defrule lemma4
        (let* ((n (abs (numerator x)))
               (d (denominator x)))
          (implies (and (integerp en)
                        (integerp ed)
                        (< en ed)
                        (>= (expo n) 1))
                   (equal (equal (* d (expt 2 (+ (- ed) en))) n) nil)))
        :use (:instance lemma2 (k (- en ed))))))

   (defrule expo-exec-2
     (let* ((n (abs (numerator x)))
            (d (denominator x))
            (en (expo n))
            (ed (expo d)))
       (implies (and (rationalp x)
                     (not (= x 0))
                     (< en ed)
                     (> en 0)
                     (> n (ash d (+ (- ed) en))))
                (equal (+ (- ed) en)
                       (expo x))))
     :enable (expo-guard-shift-d abs-posp-type)
     :use expo-quot-by-sig>=
     :disable (abs ash)
     :prep-lemmas
     ((acl2::with-arith5-help
       (defrule lemma
         (implies (and (integerp x)
                       (integerp n))
                  (< (* x (expt 2 n))
                     (1+ (ash x n))))
         :rule-classes ((:linear :trigger-terms ((ash x n))))))))

   (defruled expo-exec-3
     (let* ((n (abs (numerator x)))
         (d (denominator x))
         (en (expo n)))
       (implies
        (and (rationalp x)
             (<= en 0))
        (equal (equal (- (integer-length (+ -1 d)))
                      (expo x))
               t)))
     :cases ((= x 0) (= (abs (numerator x)) 1))
     :disable abs
     :hints
     (("subgoal 3" :in-theory (enable abs)
       :use (:instance expo>=
                       (x (abs (numerator x)))
                       (n 1)))
      ("subgoal 1" :cases ((>= (denominator x) 2))
       :use (:instance rational-implies2))
      ("subgoal 1.2" :in-theory (enable abs))
      ("subgoal 1.1" :in-theory (enable integer-length-when-posp)
       :cases ((= (sig (denominator x)) 1)
               (> (sig (denominator x)) 1)))
      ("subgoal 1.1.3" :in-theory (enable sig-lower-bound))
      ("subgoal 1.1.2" :use expo-quot-by-sig>=)
      ("subgoal 1.1.1" :use expo-quot-by-sig<))
     :prep-lemmas
     ((acl2::with-arith5-nonlinear-help
       (defrule lemma1
         (implies (and (integerp d)
                       (>= d 2)
                       (equal (sig d) 1))
                  (equal (expo (1- d))
                         (1- (expo d))))
         :enable (sig expo-lower-bound expo-upper-bound)
         :use (:instance expo-unique
                         (x (1- d))
                         (n (1- (expo d))))))
      (acl2::with-arith5-help
       (defrule lemma2
         (implies (posp x)
                  (posp (expt 2 (expo x))))
         :rule-classes :type-prescription
         :cases ((>= (expo x) 0))
         :hints (("subgoal 2" :use (:instance expo>=
                                              (n 0))))))
      (acl2::with-arith5-nonlinear-help
       (defrule lemma3
         (implies (and (integerp d)
                       (>= d 2)
                       (> (sig d) 1))
                  (equal (expo (1- d))
                         (expo d)))
         :enable (sig expo-lower-bound expo-upper-bound)
         :cases ((= d (expt 2 (expo d)))
                 (>= d (1+ (expt 2 (expo d)))))
         :hints (("subgoal 3" :use (:instance expo-lower-bound
                                              (x d))))
         :use (:instance expo-unique
                         (x (1- d))
                         (n (expo d)))))))

   (defruled expo-exec-4
     (let* ((n (abs (numerator x)))
            (d (denominator x))
            (en (expo n))
            (ed (expo d)))
       (implies (and (rationalp x)
                     (not (= x 0))
                     (>= en ed)
                     (< (ash n (- ed en)) d))
                (equal (+ -1 (- ed) en)
                       (expo x))))
     :enable (expo-quot-by-sig< expo-guard-shift-n abs-posp-type)
     :disable (abs ash)
     :prep-lemmas
     ((acl2::with-arith5-help
       (defrule lemma
         (implies (and (integerp x)
                       (integerp n))
                  (< (* x (expt 2 n))
                     (1+ (ash x n))))
         :rule-classes ((:linear :trigger-terms ((ash x n))))))))

   (defruled expo-exec-5
     (let* ((n (abs (numerator x)))
            (d (denominator x))
            (en (expo n))
            (ed (expo d)))
       (implies (and (rationalp x)
                     (not (= x 0))
                     (>= en ed)
                     (>= (ash n (+ (- en) ed)) d))
                (equal (+ (- ed) en)
                       (expo x))))
     :enable (expo-quot-by-sig>= expo-guard-shift-n abs-posp-type)
     :disable (abs ash)
     :prep-lemmas
     ((acl2::with-arith5-help
       (defrule lemma
         (implies (and (integerp x)
                       (integerp n))
                  (<= (ash x n)
                      (* x (expt 2 n))))
         :rule-classes ((:linear :trigger-terms ((ash x n))))))))

   (defruled lemma1
     (implies (or (not (rationalp x))
                  (= x 0))
              (equal (expo x) 0))
     :enable expo)
   (defrule lemma2
     (implies (and (rationalp x)
                   (not (equal x 0)))
              (posp (abs (numerator x))))
     :rule-classes (:rewrite :type-prescription))
   (acl2::with-arith5-help
    (defrule lemma3
      (implies (and (integerp x)
                    (integerp n))
               (<= (ash x n)
                   (* x (expt 2 n))))
      :rule-classes ((:linear :trigger-terms ((ash x n))))))))

(verify-guards expo
  :hints (("subgoal 2" :use expo-exec-thm :expand ((expo-exec x) (expo x)))))

(defnd expo(x)
  (declare (xargs :measure (:? x)))
  (mbe
   :logic
   (cond ((or (not (rationalp x)) (equal x 0)) 0)
         ((< x 0) (expo (- x)))
         ((< x 1) (1- (expo (* 2 x))))
         ((< x 2) 0)
         (t (1+ (expo (/ x 2)))))
   :exec
   (if (rationalp x)
       (let* ((n (abs (numerator x)))
              (d (denominator x))
              (ln (integer-length n))
              (ld (integer-length d))
              (l (- ln ld)))
         (if (>= ln ld)
             (if (>= (ash n (- l)) d) l (1- l))
           (if (> ln 1)
               (if (> n (ash d l)) l (1- l))
             (- (integer-length (1- d))))))
     0)))
#|
(defund bench-expo (x n checksum)
  (declare (xargs :guard (and (natp n)
                              (integerp checksum))))
  (if (zp n)
      checksum
    (bench-expo x (1- n) (+ (expo x) checksum))))

(time$ (bench-expo #fx1p1 #f1e6 0))
(time$ (bench-expo #fx1.8p1 #f1e6 0))
(time$ (bench-expo #fx1p1023 #f1e6 0))
(time$ (bench-expo #fx1.8p1023 #f1e6 0))
(time$ (bench-expo #fx-1p1023 #f1e6 0))
(time$ (bench-expo #fx-1.8p1023 #f1e6 0))
(time$ (bench-expo #fx1p-1022 #f1e6 0))
(time$ (bench-expo #fx1.8p-1022 #f1e6 0))
(time$ (bench-expo #fx1.000000000001p-1022 #f1e6 0))
(time$ (bench-expo #fx1p-1022 #f1e6 0))
(time$ (bench-expo #fx1.8p-1022 #f1e6 0))
(time$ (bench-expo #fx1.000000000001p-1022 #f1e6 0))
|#


(verify-guards sig)
(verify-guards exactp)
(verify-guards fp+)
(verify-guards fp-)

; reps.lisp

(local (include-book "reps"))

(verify-guards nrepp)

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

(verify-guards drepp)

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

(acl2::with-arith5-help
 (verify-guards iencode))

(defun iencode (sgn f)
  (declare (xargs :guard (and (bvecp sgn 1)
                              (formatp f))))
  (if (explicitp f)
      (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 1 1 0 (1- (sigw f)))
    (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 0 (sigw f))))

(acl2::with-arith5-help
 (verify-guards indef
   :hints (("goal" :in-theory (enable formatp sigw prec)))))

(defund indef (f)
  (declare (xargs :guard (formatp f)))
  (if (explicitp f)
      (cat (1- (expt 2 (+ (expw f) 2)))
           (+ (expw f) 2)
           0
           (- (sigw f) 2))
    (cat (1- (expt 2 (+ (expw f) 1)))
         (+ (expw f) 1)
         0
         (1- (sigw f)))))

(verify-guards rtz)
(verify-guards raz)
(verify-guards rne)
(verify-guards rna)
(verify-guards rto)
(verify-guards rup)
(verify-guards rdn)

(verify-guards rnd)
(verify-guards drnd)

;; from sqrt.lisp:

(verify-guards rtz-sqrt)
(verify-guards rto-sqrt)
(verify-guards qsqrt)
