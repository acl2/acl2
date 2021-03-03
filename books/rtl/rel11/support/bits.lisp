(in-package "RTL")

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))
(local (in-theory (acl2::enable-arith5)))

(local (include-book "basic"))
(include-book "definitions")

;;;**********************************************************************
;;;				DVECP
;;;**********************************************************************

; (defund dvecp (x k b) ... )

(defrule dvecp-forward
  (implies (dvecp x k b)
           (and (natp x)
                (natp k)
                (radixp b)
                (< x (expt b k))))
  :enable (dvecp)
  :rule-classes :forward-chaining)

(local
 (defrule |dvecp when not posp k|
   (implies (and (not (posp k))
                 (radixp b))
            (equal (dvecp x k b)
                   (and (equal x 0) (equal k 0))))
   :enable dvecp))

(defrule dvecp-0
  (implies (and (natp k)
                (radixp b))
           (dvecp 0 k b))
  :enable dvecp)

(defrule dvecp-member
  (implies (and (dvecp x n b)
                (natp n)
                (radixp b))
           (member x (nats (expt b n))))
  :prep-lemmas (
    (defrule lemma
      (implies (and (natp x)
                    (natp n)
                    (< x n))
               (member-equal x (nats n)))
      :induct (nats n)))
  :enable dvecp
  :rule-classes ())

(defruled dvecp-monotone
  (implies (and (dvecp x n b)
                (<= n m)
                (case-split (integerp m))
                (radixp b))
           (dvecp x m b))
  :enable dvecp)

(acl2::with-arith5-nonlinear-help
 (defruled dvecp-shift-down
   (implies (and (dvecp x n b)
                 (integerp k)
                 (>= n k)
                 (radixp b))
            (dvecp (fl (/ x (expt b k))) (- n k) b))
   :enable dvecp))

(acl2::with-arith5-nonlinear++-help
 (defruled dvecp-shift-up
  (implies (and (dvecp x (- n k) b)
                (natp k)
                (integerp n)
                (radixp b))
           (dvecp (* x (expt b k)) n b))
  :enable dvecp))

(acl2::with-arith5-nonlinear-help
 (defrule dvecp-product
  (implies (and (dvecp x m b)
                (dvecp y n b)
                (radixp b))
           (dvecp (* x y) (+ m n) b))
  :enable (dvecp radixp)
  :rule-classes ()))

;;;**********************************************************************
;;;				BVECP
;;;**********************************************************************

; (defund bvecp (x k) ... )

(local
 (defrule bvecp-as-dvecp
  (equal (bvecp x k)
         (if (natp k)
             (dvecp x k 2)
           (equal x 0)))
  :enable (bvecp dvecp)))

(defrule bvecp-forward
  (implies (bvecp x k)
	   (and (integerp x)
		(<= 0 x)
		(< x (expt 2 k))))
  :rule-classes :forward-chaining)

; (defun nats (n) ... )

(defrule bvecp-member
  (implies (and (natp n)
                (bvecp x n))
           (member x (nats (expt 2 n))))
  :use (:instance dvecp-member (b 2))
  :rule-classes ())

(defruled bvecp-monotone
    (implies (and (bvecp x n)
		  (<= n m)
		  (case-split (integerp m)))
	     (bvecp x m))
    :enable dvecp-monotone)

(acl2::with-arith5-nonlinear-help
 (defruled bvecp-shift-down
    (implies (and (bvecp x n)
		  (natp n)
		  (natp k))
	     (bvecp (fl (/ x (expt 2 k))) (- n k)))
    :cases ((>= n k))
    :hints (("subgoal 2" :use (:instance fl-unique
                                (x (* x (expt 2 (- k))))
                                (n 0)))
            ("subgoal 1" :use (:instance dvecp-shift-down
                                (b 2))))))

(defruled bvecp-shift-up
    (implies (and (bvecp x (- n k))
		  (natp k)
		  (integerp n))
	     (bvecp (* x (expt 2 k)) n))
    :enable dvecp-shift-up)

(defrule bvecp-product
    (implies (and (bvecp x m)
		  (bvecp y n))
	     (bvecp (* x y) (+ m n)))
  :use (:instance dvecp-product (b 2))
  :rule-classes ())

(defrule bvecp-1-0
  (implies (and (bvecp x 1)
		(not (equal x 1)))
	   (equal x 0))
  :rule-classes :forward-chaining)

(defrule bvecp-0-1
  (implies (and (bvecp x 1)
		(not (equal x 0)))
	   (equal x 1))
  :rule-classes :forward-chaining)

;;;**********************************************************************
;;;			    DIGITS
;;;**********************************************************************

; (defund digits (x i j b) ... )

(defruled digits-def-2
  (implies (radixp b)
           (equal (digits x i j b)
                  (if (or (not (integerp i)) (not (integerp j)))
                      0
                    (mod (fl (* x (expt b (- j))))
                         (expt b (+ 1 i (- j)))))))
  :prep-lemmas (
    (defrule mod-fl
      (implies (and (real/rationalp x)
                    (integerp n)
                    (radixp b))
               (equal (mod (fl x) (expt b n))
                      (fl (mod x (expt b n)))))
      :cases ((natp n))))
  :enable (digits)
  :cases ((real/rationalp x))
  :hints (("subgoal 2" :in-theory (enable fl))))

(local
 (defrule digits-default
   (implies
    (or (and (not (real/rationalp x))
             (radixp b))
        (not (integerp i))
        (not (integerp j)))
    (equal (digits x i j b) 0))
   :enable (digits fl)))

(defrule digits-reverse-indices
  (implies (and (< i j)
                (radixp b))
           (equal (digits x i j b)
                  0))
  :enable digits-def-2)

(defrule digits-dvecp
  (implies (and (<= (+ 1 i (- j)) k)
                (case-split (natp k))
                (radixp b))
           (dvecp (digits x i j b) k b))
  :prep-lemmas (
    (defrule lemma
      (implies (and (real/rationalp x)
                    (<= m n)
                    (integerp m)
                    (integerp n)
                    (radixp b))
               (< (mod x (expt b m))
                  (expt b n)))))
  :enable (dvecp digits-def-2)
  :cases ((not (natp (+ 1 i (- j))))
          (not (real/rationalp x))))

;;Here is a variation of digits-dvecp that is less general but does not
;;require an integerp hypothesis:

(defrule digits-dvecp-simple
  (implies (and (equal k (+ 1 i (* -1 j)))
                (natp k)
                (radixp b))
           (dvecp (digits x i j b) k b))
  :cases ((and (integerp i) (integerp j)))
  :hints (("subgoal 2" :in-theory (enable dvecp))))

(defrule digits-bounds
    (implies (and (integerp i)
                  (integerp j)
                  (radixp b))
             (and (natp (digits x i j b))
                  (< (digits x i j b) (expt b (1+ (- i j))))))
  :enable (dvecp)
  :cases ((natp (1+ (- i j))))
  :hints (("subgoal 1" :cases ((dvecp (digits x i j b) (1+ (- i j)) b))))
  :rule-classes ())

(defrule mod-digits-equal
  (implies (and (= (mod x (expt b (1+ i)))
                   (mod y (expt b (1+ i))))
                (radixp b))
           (= (digits x i j b) (digits y i j b)))
  :enable digits
  :rule-classes ())

(defruled mod-digits-equal-cor
  (implies (and (< i n)
                (integerp n)
                (integerp i)
                (integerp j)
                (radixp b))
           (equal (digits (mod x (expt b n)) i j b)
                  (digits x i j b)))
  :cases ((natp (+ 1 i (- j))))
  :hints (("subgoal 1" :in-theory (enable digits-def-2))))

(defruled digits-mod
  (implies (and (case-split (integerp x))
                (case-split (integerp i))
                (radixp b))
           (equal (digits x i 0 b)
                  (mod x (expt b (1+ i)))))
  :enable digits-def-2)

(defrule digits-diff-equal
    (implies (and (natp n)
                  (integerp x)
                  (integerp y)
                  (< (abs (- x y)) (expt b n))
                  (radixp b))
             (iff (= x y)
                  (= (digits (- x y) (1- n) 0 b) 0)))
  :enable (digits-mod)
  :disable (abs)
  :use (:instance mod-force-equal
         (a (- x y))
         (b 0)
         (n (expt b n)))
  :rule-classes ())

(defrule digits-tail
  (implies (and (dvecp x (1+ i) b)
                (case-split (acl2-numberp i))
                (radixp b))
           (equal (digits x i 0 b) x))
  :enable digits-def-2)

(defrule digits-tail-gen
  (implies (and (integerp x)
                (natp i)
                (< x (expt b (1+ i)))
                (>= x (- (expt b (1+ i))))
                (radixp b))
           (equal (digits x i 0 b)
                  (if (>= x 0)
                      x
                    (+ x (expt b (1+ i))))))
  :enable digits-mod
  :use (:instance mod-force
         (m x)
         (n (expt b (1+ i)))
         (a -1)))

(defruled neg-digits-1
  (implies (and (integerp x)
                (natp i)
                (natp j)
                (< x 0)
                (>= x (- (expt b j)))
                (>= i j)
                (radixp b))
           (equal (digits x i j b)
                  (1- (expt b (1+ (- i j))))))
  :prep-lemmas (
    (acl2::with-arith5-nonlinear-help
     (defrule lemma
       (implies (and (real/rationalp x)
                     (< x 0)
                     (>= x (- (expt b j)))
                     (radixp b))
                (equal (fl (* x (expt b (- j)))) -1))
       :use (:instance fl-unique
                       (x (* x (expt b (- j))))
                       (n -1)))))
  :enable digits-def-2)

(defruled digits-minus-1
  (implies (and (natp i)
                (natp j)
                (>= i j)
                (radixp b))
           (equal (digits -1 i j b)
                  (1- (expt b (1+ (- i j))))))
  :enable neg-digits-1)

(defrule digits-digits-sum
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= j 0)
                (>= k i)
                (radixp b))
           (equal (digits (+ (digits x k 0 b) y) i j b)
                  (digits (+ x y) i j b)))
  :enable (digits-mod)
  :use ((:instance mod-digits-equal
          (x (+ (digits x k 0 b) y))
          (y (+ x y)))
        (:instance  mod-sum
          (a y)
          (b (mod x (expt b (1+ k))))
          (n (expt b (1+ i))))
        (:instance  mod-sum
          (a y)
          (b x)
          (n (expt b (1+ i))))))

(defrule digits-digits-sum-alt
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= j 0)
                (>= k i)
                (radixp b))
           (equal (digits (+ x (digits y k 0 b)) i j b)
                  (digits (+ x y) i j b)))
  :use (:instance digits-digits-sum
         (x y)
         (y x)))

(defruled digits-digits-diff
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= j 0)
                (>= k i)
                (radixp b))
           (equal (digits (+ x (- (digits y k 0 b))) i j b)
                  (digits (- x y) i j b)))
 :enable digits-mod
  :use ((:instance mod-digits-equal
          (x (- x (digits y k 0 b)))
          (y (- x y)))
        (:instance  mod-diff
          (a x)
          (b (mod y (expt b (1+ k))))
          (n (expt b (1+ i))))
        (:instance  mod-diff
          (a x)
          (b y)
          (n (expt b (1+ i))))))

(defruled digits-digits-prod
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= j 0)
                (>= k i)
                (radixp b))
           (equal (digits (* x (digits y k 0 b)) i j b)
                  (digits (* x y) i j b)))
  :enable digits-mod
  :use (:instance mod-digits-equal
          (x (* x (digits y k 0 b)))
          (y (* x y))))

(defrule digits-fl-diff
  (implies (and (real/rationalp x)
                (integerp i)
                (integerp j)
                (>= i j)
                (radixp b))
           (equal (digits x (1- i) j b)
                  (- (fl (* x (expt b (- j))))
                     (* (fl (* x (expt b (- i)))) (expt b (- i j))))))
  :prep-lemmas (
    (defrule lemma1
      (implies
       (and (acl2-numberp x)
            (radixp b))
        (equal (mod x (expt b n))
               (- x (* (fl (/ x (expt b n))) (expt b n)))))
      :use ((:instance mod-def
              (x x)
              (y (expt b n)))))
    (defrule lemma2
      (implies (and (integerp k)
                    (<= k 0)
                    (radixp b))
               (equal (fl (* (expt b k) (fl x)))
                      (fl (* x (expt b k)))))
      :use (:instance fl/int-rewrite
                      (n (expt b (- k))))
      :cases ((real/rationalp x))
      :hints (("subgoal 2" :in-theory (enable fl)))))
  :cases ((natp (- i j)))
  :hints (("subgoal 1" :in-theory (enable digits-def-2)))
  :rule-classes ())

(defruled digits-mod-fl-rewrite
  (implies (radixp b)
           (equal (digits x i j b)
                  (if (and (integerp i) (integerp j))
                      (mod (fl (/ x (expt b j)))
                           (expt b (+ 1 i (- j))))
                    0)))
  :enable digits
  :cases ((and (integerp i) (integerp j)))
  :hints
  (("subgoal 1" :cases ((>= (- i j) -1)))
   ("subgoal 1.2" :use lemma)
   ("subgoal 1.1" :cases ((real/rationalp x)))
   ("subgoal 1.1.2" :in-theory (enable fl))
   ("subgoal 1.1.1" :use (:instance fl-mod
                                    (a x)
                                    (n (expt b j))
                                    (m (expt b (+ 1 i (- j)))))))
  :prep-lemmas
  ((acl2::with-arith5-nonlinear++-help
    (defruled lemma
     (implies (and (integerp j)
                   (integerp i)
                   (radixp b)
                   (< (- i j) -1))
              (equal (fl (* (expt b (- j)) (mod x (expt b (1+ i))))) 0))
     :enable fl))))

(defrule digits-mod-fl
  (implies (and (integerp i)
                (integerp j)
                (radixp b))
           (equal (digits x (1- i) j b)
                  (mod (fl (/ x (expt b j)))
                       (expt b (- i j)))))
  :rule-classes ()
  :enable digits-mod-fl-rewrite)

(defrule digits-neg-indices
  (implies (and (< i 0)
                (integerp x)
                (radixp b))
           (equal (digits x i j b) 0))
  :enable digits)

(defruled dvecp-digits-0
  (implies (and (dvecp x j b)
                (radixp b))
           (equal (digits x i j b) 0))
  :prep-lemmas (
    (acl2::with-arith5-nonlinear-help
     (defrule lemma
       (implies (and (dvecp x j b)
                     (integerp j)
                     (radixp b))
                (< (* x (expt b (- j))) 1)))))
  :enable digits-def-2
  :use (:instance fl-unique
                  (x (* x (expt b (- j))))
                  (n 0)))

(defrule digits-0
  (equal (digits 0 i j b) 0)
  :enable digits)

(defruled digits-fl
  (implies (and (>= j 0)
                (radixp b))
           (equal (digits (fl x) i j b)
                  (digits x i j b)))
  :enable (digits-def-2 fl-default)
  :use (:instance fl/int-rewrite
         (x x)
         (n (expt b j))))

(defruled digits-shift-down-1
  (implies (and (integerp i)
                (integerp j)
                (integerp k)
                (radixp b))
           (equal (digits (/ x (expt b k)) i j b)
                  (digits x (+ i k) (+ j k) b)))
  :enable digits-def-2)

(defruled digits-shift-down-2
  (implies (and (integerp x)
                (natp i)
                (natp k)
                (radixp b))
           (equal (fl (/ (digits x (+ i k) 0 b) (expt b k)))
                  (digits (/ x (expt b k)) i 0 b)))
  :enable digits)

(defruled digits-shift-up-1
  (implies (and (integerp k)
                (integerp i)
                (integerp j)
                (radixp b))
           (equal (digits (* x (expt b k)) i j b)
                          (digits x (- i k) (- j k) b)))
  :enable digits-def-2)

(defruled digits-shift-up-2
  (implies (and (integerp x)
                (natp k)
                (integerp i)
                (radixp b))
           (equal (* (digits x i 0 b) (expt b k))
                  (digits (* x (expt b k)) (+ i k) 0 b)))
  :enable digits-mod)

(defruled digits-plus-mult-1
  (implies (and (dvecp x k b)
                (<= k m)
                (integerp y)
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp k))
                (radixp b))
           (equal (digits (+ x (* y (expt b k))) n m b)
                  (digits y (- n k) (- m k) b)))
  :prep-lemmas (
    (acl2::with-arith5-nonlinear++-help
     (defrule lemma
       (implies (and (real/rationalp x)
                     (>= x 0)
                     (< x (expt b i))
                     (integerp y)
                     (integerp i)
                     (<= i 0)
                     (radixp b))
                (equal (fl (+ x (* y (expt b i))))
                       (fl (* y (expt b i)))))
       :cases ((<= y (1- (* (1+ (fl (* y (expt b i))))
                            (expt b (- i))))))
       :hints (
         ("subgoal 2" :cases ((< y (* (1+ (fl (* y (expt b i))))
                                      (expt b (- i))))))
         ("subgoal 2.2" :use (:instance fl-def
                                        (x (* y (expt b i)))))
         ("subgoal 1" :use (:instance fl-unique
                                      (x (+ x (* y (expt b i))))
                                      (n (fl (* y (expt b i))))))))))
  :enable digits-def-2)

(defruled digits-plus-mult-1-alt
  (implies (and (dvecp x k b)
                (<= k m)
                (integerp y)
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp k))
                (radixp b))
           (equal (digits (+ x (* (expt b k) y)) n m b)
                  (digits y (- n k) (- m k) b)))
  :use digits-plus-mult-1)

(defruled digits-plus-mult-2
  (implies (and (< n k)
                (integerp y)
                (integerp k)
                (radixp b))
           (equal (digits (+ x (* y (expt b k))) n m b)
                  (digits x n m b)))
  :enable digits
  :cases ((not (acl2-numberp x))
          (real/rationalp x)))

(defruled digits-plus-mult-2-alt
  (implies (and (< n k)
                (integerp y)
                (integerp k)
                (radixp b))
           (equal (digits (+ x (* (expt b k) y)) n m b)
                  (digits x n m b)))
  :use digits-plus-mult-2)

(defruled digits-plus-mult-2-rewrite
  (implies (and (syntaxp (quotep c))
                (equal (mod c (expt b (1+ n))) 0)
                (radixp b))
           (equal (digits (+ c x) n m b)
                  (digits x n m b)))
  :enable digits
  :cases ((and (integerp m) (integerp n)))
  :hints (
    ("subgoal 1" :cases ((real/rationalp x)))
    ("subgoal 1.2" :in-theory (enable fl))))

(defrule digits-plus-digits
    (implies (and (integerp m)
                  (integerp p)
                  (integerp n)
                  (<= m p)
                  (<= p n)
                  (radixp b))
             (= (digits x n m b)
                (+ (digits x (1- p) m b)
                   (* (digits x n p b) (expt b (- p m))))))
  :cases ((real/rationalp x))
  :use (
    (:instance digits-fl-diff
      (i (1+ n))
      (j m))
    (:instance digits-fl-diff
      (i p)
      (j m))
    (:instance digits-fl-diff
      (i (1+ n))
      (j p)))
  :rule-classes ())

(defrule digits-digits
  (implies (and (case-split (<= 0 l))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                (case-split (integerp l))
              (radixp b))
           (equal (digits (digits x i j b) k l b)
                  (if (<= k (- i j))
                      (digits x (+ k j) (+ l j) b)
                    (digits x i (+ l j) b))))
  :prep-lemmas (
    (defrule lemma1
      (implies (and (integerp m)
                    (integerp n)
                    (<= m n)
                    (radixp b))
               (equal (mod (mod x (expt b m)) (expt b n))
                      (mod x (expt b m)))))
    (defrule lemma2
      (implies (and (integerp i)
                    (integerp j)
                    (<= i k)
                    (integerp k)
                    (radixp b))
               (equal (digits (mod x (expt b (1+ i))) k j b)
                      (digits x i j b)))
      :enable digits
      :cases ((<= (expt b (1+ i)) (expt b (1+ k))))))
  :enable (digits-fl mod-digits-equal-cor)
  :cases ((<= k (- i j)))
  :expand (digits x i j b)
  :use (:instance digits-shift-up-1
         (x (mod x (expt b (1+ i))))
         (k (- j))
         (i k)
         (j l)))

;;digits-match can prove things like this:
;;(thm (implies (equal 12 (digits x 15 6 2))
;;		(equal 4 (digits x 8 6 2))))

(defruled digits-match
  (implies (and (syntaxp (and (quotep i)
                              (quotep j)
                              (quotep k)))
                (equal (digits x i2 j2 b) k2) ;i2, j2, and k2 are free variables
                (syntaxp (and (quotep i2)
                              (quotep j2)
                              (quotep k2)))
                (<= j2 j) (<= j i) (<= i i2)
                (equal k (digits k2 (+ i (- j2)) (+ (- j2) j) b))
                (<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
                (integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2)
                (radixp b))
           (equal (equal k (digits x i j b))
                  t)))

;;digits-dont-match can prove things like this:
;;(thm (implies (equal 7 (digits x 8 6 2))
;;		(not (equal 4 (digits x 15 6 2)))))

(defruled digits-dont-match
  (implies (and (syntaxp (and (quotep i)
                              (quotep j)
                              (quotep k)))
                (equal (digits x i2 j2 b) k2) ;i2, j2, and k2 are free vars
                (syntaxp (and (quotep i2)
                              (quotep j2)
                              (quotep k2)))
                (<= j2 j) (<= j i) (<= i i2)
                (not (equal k (digits k2 (+ i (- j2)) (+ (- j2) j) b)))
                (<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
                (integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2)
                (radixp b))
           (equal (equal k (digits x i j b))
                  nil)))

;;;**********************************************************************
;;;			    BITS
;;;**********************************************************************

; (defund bits-exec (x i j) ...
; (defund bits (x i j) ...

(local
 (defrule bits-as-digits
  (equal
   (bits x i j)
   (digits x i j 2))
  :enable (bits digits)))

(defrule bits-bvecp
    (implies (and (<= (+ 1 i (- j)) k)
		  (case-split (integerp k)))
	     (bvecp (bits x i j) k)))

;;Here is a variation of bits-bvecp that is less general but does not
;;require an integerp hypothesis:

(defrule bits-bvecp-simple
  (implies (equal k (+ 1 i (* -1 j)))
           (bvecp (bits x i j) k))
  :cases ((not (integerp i))
          (not (integerp j))
          (< k 0)))

(defrule bits-bounds
    (implies (and (integerp i)
		  (integerp j))
	     (and (natp (bits x i j))
		  (< (bits x i j) (expt 2 (1+ (- i j))))))
  :use (:instance digits-bounds (b 2))
  :rule-classes())

(defthmd bits-upper-bound
  (implies (and (integerp i)
                (integerp j))
           (< (bits x i j)
              (expt 2 (1+ (- i j)))))
  :hints (("Goal" :use bits-bounds))
  :rule-classes :linear)

(defrule mod-bits-equal
  (implies (= (mod x (expt 2 (1+ i)))
	      (mod y (expt 2 (1+ i))))
	   (= (bits x i j) (bits y i j)))
  :use (:instance mod-digits-equal (b 2))
  :rule-classes ())

(defruled mod-bits-equal-cor
    (implies (and (integerp x)
		  (integerp n)
		  (integerp i)
		  (integerp j)
		  (< i n))
	     (equal (bits (mod x (expt 2 n)) i j)
		    (bits x i j)))
    :enable mod-digits-equal-cor)

(defruled bits-mod
  (implies (and (case-split (integerp x))
		(case-split (integerp i)))
	   (equal (bits x i 0)
		  (mod x (expt 2 (1+ i)))))
  :enable digits-mod)

(defrule bits-diff-equal
    (implies (and (natp n)
		  (integerp x)
		  (integerp y)
		  (< (abs (- x y)) (expt 2 n)))
	     (iff (= x y)
		  (= (bits (- x y) (1- n) 0) 0)))
  :use (:instance digits-diff-equal (b 2))
  :rule-classes ())

(defrule bits-tail
  (implies (and (bvecp x (1+ i))
		(case-split (acl2-numberp i)))
	   (equal (bits x i 0) x)))

(defrule bits-tail-gen
    (implies (and (integerp x)
		  (natp i)
		  (< x (expt 2 i))
		  (>= x (- (expt 2 (+ 1 i)))))
	     (equal (bits x i 0)
		    (if (>= x 0)
			x
		      (+ x (expt 2 (+ 1 i))))))
    :prep-lemmas (
      (defrule lemma
        (implies (and (natp i)
                      (< x (expt 2 i)))
                 (< x (expt 2 (1+ i))))
        :cases ((<= (expt 2 i) (expt 2 (1+ i))))))
    :use (:instance digits-tail-gen (b 2)))

(defruled neg-bits-1
    (implies (and (integerp x)
		  (natp i)
		  (natp j)
		  (< x 0)
		  (>= x (- (expt 2 j)))
		  (>= i j))
	     (equal (bits x i j)
                    (1- (expt 2 (1+ (- i j))))))
    :enable neg-digits-1)

(defthmd bits-top-ones
  (implies (and (natp i)
                (natp j)
		(>= i j)
		(natp x)
		(< x (expt 2 (1+ i)))
		(>= x (- (expt 2 (1+ i)) (expt 2 j))))
	   (equal (bits x i j)
	          (1- (expt 2 (- (1+ i) j)))))
  :hints (("Goal" :use ((:instance neg-bits-1 (x (- x (expt 2 (1+ i)))))
			(:instance mod-bits-equal (y (- x (expt 2 (1+ i)))))
			(:instance mod-mult (m x) (n (expt 2 (1+ i))) (a -1))))))

(defruled bits-minus-1
    (implies (and (natp i)
		  (natp j)
		  (>= i j))
	     (equal (bits -1 i j)
                    (1- (expt 2 (1+ (- i j))))))
    :enable digits-minus-1)

(defrule bits-bits-sum
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= j 0)
                (>= k i))
	   (equal (bits (+ (bits x k 0) y) i j)
		  (bits (+ x y) i j))))

(defrule bits-bits-sum-alt
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= j 0)
                (>= k i))
	   (equal (bits (+ x (bits y k 0)) i j)
		  (bits (+ x y) i j))))

(defruled bits-bits-diff
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= j 0)
                (>= k i))
	   (equal (bits (+ x (- (bits y k 0))) i j)
		  (bits (- x y) i j)))
  :enable digits-digits-diff)

(defruled bits-bits-prod
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= j 0)
                (>= k i))
	   (equal (bits (* x (bits y k 0)) i j)
		  (bits (* x y) i j)))
  :enable digits-digits-prod)

(defrule bits-fl-diff
  (implies (and (integerp x)
                (integerp i)
                (integerp j)
                (>= i j))
           (equal (bits x (1- i) j)
                  (- (fl (/ x (expt 2 j)))
                     (* (expt 2 (- i j))
                        (fl (/ x (expt 2 i)))))))
  :use (:instance digits-fl-diff (b 2))
  :rule-classes ())

(defthmd bits-fl-diff-alt
  (implies (and (integerp x)
                (integerp i)
                (integerp j)
                (>= i (1- j)))
           (equal (bits x i j)
                  (- (fl (/ x (expt 2 j)))
                     (* (expt 2 (- (1+ i) j))
                        (fl (/ x (expt 2 (1+ i))))))))
  :hints (("Goal" :use (:instance bits-fl-diff (i (1+ i))))))

(defrule bits-mod-fl
  (implies (and (integerp i)
                (integerp j))
           (equal (bits x (1- i) j)
                  (mod (fl (/ x (expt 2 j)))
                       (expt 2 (- i j)))))
  :use (:instance digits-mod-fl (b 2))
  :rule-classes ())

(defrule bits-neg-indices
  (implies (and (< i 0)
                (integerp x))
           (equal (bits x i j) 0)))

(defrule bits-reverse-indices
  (implies (< i j)
	   (equal (bits x i j)
		  0)))

(defruled bvecp-bits-0
  (implies (bvecp x j)
	   (equal (bits x i j) 0))
  :enable dvecp-digits-0)

(defrule bits-0
  (equal (bits 0 i j) 0))

(defruled bits-shift-down-1
  (implies (and (<= 0 j)
		(integerp i)
		(integerp j)
		(integerp k))
	   (equal (bits (fl (/ x (expt 2 k))) i j)
		  (bits x (+ i k) (+ j k))))
  :enable digits-fl
  :use (:instance digits-shift-down-1 (b 2)))

(defruled bits-shift-down-2
  (implies (and (integerp x)
		(natp i)
		(natp k))
	   (equal (fl (/ (bits x (+ i k) 0) (expt 2 k)))
		  (bits (fl (/ x (expt 2 k))) i 0)))
  :enable digits-fl
  :use (:instance digits-shift-down-2 (b 2)))

(defruled bits-shift-up-1
  (implies (and (integerp k)
		(integerp i)
		(integerp j))
	   (equal (bits (* (expt 2 k) x) i j)
		  (bits x (- i k) (- j k))))
  :use (:instance digits-shift-up-1 (b 2)))

(defruled bits-shift-up-2
  (implies (and (integerp x)
		(natp k)
		(integerp i))
	   (equal (* (expt 2 k) (bits x i 0))
		  (bits (* (expt 2 k) x) (+ i k) 0)))
  :use (:instance digits-shift-up-2 (b 2)))

(defruled bits-plus-mult-1
  (implies (and (bvecp x k)
		(<= k m)
		(integerp y)
		(case-split (integerp m))
		(case-split (integerp n))
		(case-split (integerp k)))
	   (equal (bits (+ x (* y (expt 2 k))) n m)
		  (bits y (- n k) (- m k))))
  :enable (digits-plus-mult-1 digits-shift-up-1)
  :cases ((natp k)))

(defruled bits-plus-mult-2
  (implies (and (< n k)
		(integerp y)
		(integerp k))
	   (equal (bits (+ x (* y (expt 2 k))) n m)
		  (bits x n m)))
  :use (:instance digits-plus-mult-2 (b 2)))

(defruled bits-plus-mult-2-rewrite
   (implies (and (syntaxp (quotep c))
                 (equal (mod c (expt 2 (1+ n))) 0))
            (equal (bits (+ c x) n m)
                   (bits x n m)))
   :use (:instance digits-plus-mult-2-rewrite (b 2)))

(defrule bits-plus-bits
    (implies (and (integerp m)
		  (integerp p)
		  (integerp n)
		  (<= m p)
		  (<= p n))
	     (= (bits x n m)
		(+ (bits x (1- p) m)
		   (* (expt 2 (- p m)) (bits x n p)))))
  :use (:instance digits-plus-digits (b 2))
  :rule-classes ())

(defrule bits-bits
  (implies (and (case-split (<= 0 l))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k))
		(case-split (integerp l)))
	   (equal (bits (bits x i j) k l)
		  (if (<= k (- i j))
		      (bits x (+ k j) (+ l j))
		    (bits x i (+ l j))))))

;;bits-match can prove things like this:
;;(thm (implies (equal 12 (bits x 15 6))
;;		(equal 4 (bits x 8 6))))

(defruled bits-match
  (implies (and (syntaxp (and (quotep i)
			      (quotep j)
			      (quotep k)))
		(equal (bits x i2 j2) k2) ;i2, j2, and k2 are free variables
		(syntaxp (and (quotep i2)
			      (quotep j2)
			      (quotep k2)))
		(<= j2 j) (<= j i) (<= i i2)
		(equal k (bits k2 (+ i (- j2)) (+ (- j2) j)))
		(<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
		(integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2))
	   (equal (equal k (bits x i j))
		  t)))

;;bits-dont-match can prove things like this:
;;(thm (implies (equal 7 (bits x 8 6))
;;		(not (equal 4 (bits x 15 6)))))

(defruled bits-dont-match
  (implies (and (syntaxp (and (quotep i)
			      (quotep j)
			      (quotep k)))
		(equal (bits x i2 j2) k2) ;i2, j2, and k2 are free vars
		(syntaxp (and (quotep i2)
			      (quotep j2)
			      (quotep k2)))
		(<= j2 j) (<= j i) (<= i i2)
		(not (equal k (bits k2 (+ i (- j2)) (+ (- j2) j))))
		(<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
		(integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2))
	   (equal (equal k (bits x i j))
		  nil)))

;;;**********************************************************************
;;;				DIGITN
;;;**********************************************************************

; (defund digitn (x n b) ... )

(local
 (defrule digitn-default
   (implies
    (or (and (not (real/rationalp x))
             (radixp b))
        (not (integerp n)))
    (equal (digitn x n b) 0))
   :enable digitn))

(defrule digitn-bounds
   (implies (radixp b)
            (< (digitn x n b) b))
   :enable digitn
   :use (:instance digits-bounds (i n) (j n))
   :rule-classes :linear)

(defrule digits-n-n-rewrite
  (equal (digits x n n radix)
         (digitn x n radix))
  :enable digitn)

(local (in-theory (disable digits-n-n-rewrite)))

(defruled digitn-def
  (implies (and (case-split (integerp n))
                (radixp b))
           (equal (digitn x n b)
                  (mod (fl (* x (expt b (- n)))) b)))
  :enable (digitn digits-def-2))

(defruled digitn-fl
  (implies (and (>= n 0)
                (radixp b))
           (equal (digitn (fl x) n b)
                  (digitn x n b)))
  :enable (digitn digits-fl))

;;A recursive formulation:

(defruled digitn-rec-0
  (implies (and (integerp x)
                (radixp b))
           (equal (digitn x 0 b) (mod x b)))
  :enable digitn-def)

(defruled digitn-rec
  (implies (radixp b)
           (equal (digitn x n b)
                  (cond ((not (integerp n)) 0)
                        ((> n 0) (digitn (/ x b) (1- n) b))
                        ((< n 0) (digitn (* x b) (1+ n) b))
                        (t (mod (fl x) b)))))
  :enable (radixp digitn digits-def-2)
  :rule-classes ((:definition :controller-alist ((digitn t t nil)))))

(defrule digitn-dvecp
  (implies (and (<= 1 k)
                (case-split (integerp k))
                (radixp b))
           (dvecp (digitn x n b) k b))
  :enable (digitn dvecp))

;;The following is a special case of bitn-bvecp.
;;It is useful as a :forward-chaining rule in concert with dvecp-1.

(defrule digitn-dvecp-forward
  (implies (radixp b)
           (dvecp (digitn x n b) 1 b))
  :rule-classes ((:forward-chaining :trigger-terms ((digitn x n b)))))

(defrule digitn-neg
  (implies (and (< n 0)
                (integerp x)
                (radixp b))
           (equal (digitn x n b) 0))
  :enable digitn)

(defrule digitn-0
  (equal (digitn 0 k b) 0)
  :enable digitn)

(defrule digitn-dvecp-1
  (implies (and (dvecp x 1 b)
                (radixp b))
           (equal (digitn x 0 b) x))
  :enable digitn)

(defrule digitn-digitn-0
  (implies (radixp b)
           (equal (digitn (digitn x n b) 0 b)
                  (digitn x n b))))

(defruled digitn-mod
  (implies (and (< k n)
                (integerp n)
                (integerp k)
                (radixp b))
           (equal (digitn (mod x (expt b n)) k b)
                  (digitn x k b)))
  :enable (digitn digits))

(defrule dvecp-digitn-0
  (implies (and (dvecp x n b)
                (radixp b))
           (equal (digitn x n b) 0))
  :enable (digitn dvecp-digits-0))

(defrule neg-digitn-1
  (implies (and (integerp x)
                (integerp n)
                (< x 0)
                (>= x (- (expt b n)))
                (radixp b))
           (equal (digitn x n b) (1- b)))
  :enable (digitn neg-digits-1)
  :cases ((natp n)))

(defruled digitn-minus-1
  (implies (and (natp i)
                (radixp b))
           (equal (digitn -1 i b) (1- b))))

;; The rewrite rule neg-digitn-2 has the hypotheses (integerp n) and (< x (- (expt b k) (expt b n))),
;; where n does not occur in the lhs.  When n is bound to a large integer, (expt b n) blows up.

(defruled neg-digitn-2
  (implies (and (integerp x)
                (integerp n)
                (integerp k)
                (< k n)
                (< x (- (expt b k) (expt b n)))
                (>= x (- (expt b n)))
                (radixp b))
           (equal (digitn x k b) 0))
  :prep-lemmas (
    (acl2::with-arith5-nonlinear++-help
     (defrule lemma
       (implies (and (real/rationalp x)
                     (natp k)
                     (integerp n)
                     (< k n)
                     (< x (- (expt b k) (expt b n)))
                     (>= x (- (expt b n)))
                     (radixp b))
                (equal (fl (* x (expt b (- k))))
                       (- (expt b (- n k)))))
       :use (:instance fl-unique
                       (x (* x (expt b (- k))))
                       (n (- (expt b (- n k))))))))
  :cases ((and (real/rationalp x) (natp k)))
  :hints (("subgoal 2" :in-theory (enable digitn))
          ("subgoal 1" :in-theory (enable digitn-def))))

(defrule neg-digitn-0
    (implies (and (integerp x)
                  (natp n)
                  (< x (- (* (1- b) (expt b n))))
                  (>= x (- (expt b (1+ n))))
                (radixp b))
             (equal (digitn x n b) 0))
  :use (:instance neg-digitn-2
                      (k n)
                      (n (1+ n))))

(defruled digitn-shift-up
  (implies (and (integerp n)
                (integerp k)
                (radixp b))
           (equal (digitn (* x (expt b k)) (+ n k) b)
                  (digitn x n b)))
  :enable (digitn digits-shift-up-1))

(defruled digitn-shift-down
  (implies (and (natp i)
                (integerp k)
                (radixp b))
           (equal (digitn (/ x (expt b k)) i b)
                  (digitn x (+ i k) b)))
  :enable (digitn digits-shift-up-1))

(defruled digitn-digits
  (implies (and (<= k (- i j))
                (case-split (<= 0 k))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                (radixp b))
           (equal (digitn (digits x i j b) k b)
                  (digitn x (+ j k) b)))
  :enable digitn)

(defrule digitn-plus-digits
    (implies (and (<= m n)
                  (integerp m)
                  (integerp n)
                  (radixp b))
             (= (digits x n m b)
                (+ (* (digitn x n b) (expt b (- n m)))
                   (digits x (1- n) m b))))
  :enable digitn
  :use (:instance digits-plus-digits
         (p n))
  :rule-classes ())

(defrule digits-plus-digitn
    (implies (and (<= m n)
                  (integerp m)
                  (integerp n)
                  (radixp b))
             (= (digits x n m b)
                (+ (digitn x m b)
                   (* b (digits x n (1+ m) b)))))
  :enable (digitn)
  :use (:instance digits-plus-digits
         (p (1+ m)))
  :rule-classes ())

; (defun sumdigits (x n b) ... )

(defruled sumdigits-digits
  (implies (and (integerp x)
                (posp n)
                (radixp b))
           (equal (sumdigits x n b)
                  (digits x (1- n) 0 b)))
  :prep-lemmas (
    (defrule lemma1
      (equal (digitn x 0 b) (digits x 0 0 b))
      :enable digitn)
    (defrule lemma2
      (implies
        (and (> (+ -1 n) 0) (integerp n) (radixp b))
        (equal
          (+ (digits x (+ -2 n) 0 b)
             (* (expt b (1- n)) (digitn x (+ -1 n) b)))
          (digits x (+ -1 n) 0 b)))
        :use (:instance digitn-plus-digits
               (n (1- n))
               (m 0))))
  :induct (sumdigits x n b))

(defruled sumdigits-thm
  (implies (and (dvecp x n b)
                (natp n)
                (> n 0)
                (radixp b))
           (equal (sumdigits x n b)
                  x))
  :enable sumdigits-digits)

; (defnd all-digits-p (list k b) ... )

(defrule digitp-of-all-digits-p
  (implies (and (all-digits-p list n b)
                (< k n)
                (natp k)
                (natp n))
           (digitp (nth k list) b))
  :use (:instance nth-all-digits-p
         (k n)
         (i k))
  :rule-classes ())

; (defun sum-d (list k b) ... )

(defruled dvecp-sum-d
   (implies (all-digits-p list k b)
            (dvecp (sum-d list k b) k b))
   :prep-lemmas (
     (acl2::with-arith5-nonlinear-help
      (defrule lemma
        (implies (and (all-digits-p list k b)
                      (natp n)
                      (<= n k))
                 (dvecp (sum-d list n b) n b))
        :enable (dvecp)
        :induct (sub1-induction n)
        :hints (("subgoal *1/2" :use (:instance nth-all-digits-p (i (1- n)))))
        :rule-classes ())))
   :use (:instance lemma (n k)))

(defruled sum-digitn
  (implies (and (all-digits-p list n b)
                (natp k)
                (< k n))
           (equal (digitn (sum-d list n b) k b)
                  (nth k list)))
  :prep-lemmas (
    (defrule lemma1
      (implies (and (all-digits-p list n b)
                    (not (equal n 0)))
               (all-digits-p list (1- n) b))
      :enable all-digits-p
      :induct (all-digits-p list n b))
    (defrule lemma2
      (implies (and (natp k)
                    (dvecp x k b)
                    (digitp d b)
                    (radixp b))
               (equal (digitn (+ x (* (expt b k) d)) k b) d))
      :enable (digitn-def fl))
    (defrule lemma3
      (implies (and
                (natp k)
                (natp n)
                (< k n)
                (integerp dn)
                (dvecp sum n b)
                (radixp b))
               (equal (digitn (+ sum (* (expt b n) dn)) k b)
                      (digitn sum k b)))
      :enable digitn-def))
  :enable (dvecp-sum-d)
  :induct (sub1-induction n)
  :hints (("subgoal *1/2" :cases ((= k (1- n)))
                          :use (:instance nth-all-digits-p
                                 (i (1- n))
                                 (k n)))))

;; The next lemma can be used to prove equality of two digit vectors by
;; proving that they have the same value at digit n for all n.

; (defn digit-diff (x y b) ... )

(defrule digit-diff-diff
  (implies (and (integerp x)
                (integerp y)
                (not (= x y))
                (radixp b))
           (let ((n (digit-diff x y b)))
             (and (natp n)
                  (not (= (digitn x n b) (digitn y n b))))))
  :prep-lemmas (
    (defrule bdd-2
      (implies (and (integerp x)
                    (radixp b))
               (equal (digitn x 0 b)
                      (- x (* b (fl (/ x b))))))
      :enable (digitn)
      :use (:instance digits-fl-diff
             (i 1)
             (j 0))))
  :enable (digitn-fl bdd-2)
  :induct (digit-diff x y b)
  :hints (("subgoal *1/1"
           :use ((:instance digitn-shift-down
                            (k 1)
                            (i (digit-diff (fl (/ x b)) (fl (/ y b)) b)))
                 (:instance digitn-shift-down
                            (k 1)
                            (x y)
                            (i (digit-diff (fl (/ x b)) (fl (/ y b)) b))))))
  :rule-classes ())

(defruled dvecp-digitn-1
  (implies (and (dvecp x (1+ n) b)
                (<= (expt b n) x)
                (natp n)
                (radixp b))
           (>= (digitn x n b) 1))
  :cases ((= (digitn x n b) 0))
  :hints (("subgoal 1" :use (
    (:instance digitn-plus-digits
      (m 0))
    (:instance digits-dvecp
      (i (1- n))
      (j 0)
      (k n))))))

(defruled dvecp-digitn-2
  (implies (and (dvecp x n b)
                (< k n)
                (<= (- (expt b n) (expt b k)) x)
                (integerp n)
                (integerp k)
                (radixp b))
           (= (digitn x k b) (1- b)))
  :prep-lemmas (
    (acl2::with-arith5-nonlinear-help
     (defrule lemma1
       (implies (and (natp k)
                     (posp n)
                     (< k n)
                     (real/rationalp x)
                     (<= (- (expt b n) (expt b k)) x)
                     (< x (expt b n))
                     (radixp b))
                (equal (fl (* x (expt b (- k))))
                       (1- (expt b (- n k)))))
       :use (:instance fl-unique
                       (x (* x (expt b (- k))))
                       (n (1- (expt b (- n k))))))))
  :enable (radixp digitn-def)
  :cases ((not (natp k))
          (not (real/rationalp x)))
  :hints (
    ("subgoal 2" :cases ((<= x (1- (expt b n)))))
    ("subgoal 2.2" :cases ((natp n))
                   :in-theory (enable dvecp)))
  :rule-classes ((:rewrite :match-free :all)))

(defruled digitn-expt
  (implies (and (case-split (integerp n))
                (radixp b))
           (equal (digitn (expt b n) n b)
                  1))
  :enable digitn-def)
(defruled digitn-expt-0
  (implies (and (not (equal i n))
                (case-split (integerp i))
                (radixp b))
           (equal (digitn (expt b i) n b)
                  0))
  :enable digitn
  :cases ((integerp n))
  :hints (
    ("subgoal 1" :cases ((<= i (1- n))
                         (>= i (1+ n))))
    ("subgoal 1.2" :in-theory (enable digits-def-2))
    ("subgoal 1.1" :in-theory (enable digits))))

(defrule digitn-plus-expt-1
  (implies (and (real/rationalp x)
                (integerp n)
                (radixp b))
           (not (equal (digitn (+ x (expt b n)) n b)
                       (digitn x n b))))
  :enable (digitn digits-def-2)
  :use (:instance fl+int-rewrite
                  (x (* x (expt b (- n))))
                  (n 1))
  :rule-classes ())

(defruled digitn-plus-mult
  (implies (and (< n m)
                (integerp m)
                (integerp k)
                (radixp b))
           (equal (digitn (+ x (* k (expt b m))) n b)
                  (digitn x n b)))
  :enable (digitn digits-plus-mult-2 digits)
  :cases ((real/rationalp x))
  :hints (("subgoal 2" :in-theory (enable fl))))

(defruled digitn-plus-mult-rewrite
    (implies (and (syntaxp (quotep c))
		  (equal (mod c (expt b (1+ n))) 0)
                  (radixp b))
	     (equal (digitn (+ c x) n b)
		    (digitn x n b)))
    :use (:instance digitn-plus-mult
           (k (/ c (expt b (1+ n))))
           (m (1+ n))))

;;;**********************************************************************
;;;				BITN
;;;**********************************************************************

; (defund bitn-exec (x n) ... )
; (defund bitn (x n) ... )

(local
 (defrule bitn-as-digitn
   (equal (bitn x n)
          (digitn x n 2))
   :enable (bitn digitn)))

(defrule bits-n-n-rewrite
  (equal (bits x n n)
	 (bitn x n))
  :enable digits-n-n-rewrite)

(local (in-theory (disable bits-n-n-rewrite)))

(defruled bitn-def
  (implies (case-split (integerp n))
	   (equal (bitn x n)
		  (mod (fl (/ x (expt 2 n))) 2)))
  :enable digitn-def)

;;A recursive formulation:

(defruled bitn-rec-0
  (implies (integerp x)
	   (equal (bitn x 0) (mod x 2)))
  :enable digitn-rec-0)

(defruled bitn-rec-pos
    (implies (< 0 n)
	     (equal (bitn x n)
		    (bitn (fl (/ x 2)) (1- n))))
  :enable (digitn-rec digitn-fl)
  :cases ((integerp n))
  :disable digits-n-n-rewrite
  :rule-classes ((:definition :controller-alist ((bitn t t)))))

;;Use this to induce case-splitting:

(defrule bitn-0-1
    (or (equal (bitn x n) 0)
	(equal (bitn x n) 1))
  :rule-classes ())

(defrule bitn-bvecp
  (implies (and (<= 1 k)
		(case-split (integerp k)))
	   (bvecp (bitn x n) k)))

;;The following is a special case of bitn-bvecp.
;;It is useful as a :forward-chaining rule in concert with bvecp-0-1 and
;;bvecp-1-0.

(defrule bitn-bvecp-forward
  (bvecp (bitn x n) 1)
  :rule-classes ((:forward-chaining :trigger-terms ((bitn x n)))))

(defrule bitn-neg
  (implies (and (< n 0)
                (integerp x))
           (equal (bitn x n) 0)))

(defrule bitn-0
  (equal (bitn 0 k) 0))

(defrule bitn-bvecp-1
    (implies (bvecp x 1)
	     (equal (bitn x 0) x)))

(defrule bitn-bitn-0
    (equal (bitn (bitn x n) 0)
	   (bitn x n)))

(defruled bitn-mod
    (implies (and (< k n)
		  (integerp n)
		  (integerp k))
	     (equal (bitn (mod x (expt 2 n)) k)
		    (bitn x k)))
    :use (:instance digitn-mod (b 2)))

(defrule bvecp-bitn-0
    (implies (bvecp x n)
	     (equal (bitn x n) 0)))

(defrule neg-bitn-1
    (implies (and (integerp x)
                  (integerp n)
                  (< x 0)
		  (>= x (- (expt 2 n))))
	     (equal (bitn x n) 1)))

(defruled bitn-minus-1
    (implies (natp i)
	     (equal (bitn -1 i) 1)))

;; The rewrite rule neg-bitn-2 has the hypotheses (integerp n) and (< x (- (expt 2 k) (expt 2 n))),
;; where n does not occur in the lhs.  When n is bound to a large integer, (expt 2 n) blows up.

(defruled neg-bitn-2
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (< k n)
		  (< x (- (expt 2 k) (expt 2 n)))
		  (>= x (- (expt 2 n))))
	     (equal (bitn x k) 0))
    :enable neg-digitn-2)

(defrule neg-bitn-0
    (implies (and (integerp x)
		  (natp n)
		  (< x (- (expt 2 n)))
		  (>= x (- (expt 2 (1+ n)))))
	     (equal (bitn x n) 0)))

(defruled bitn-shift-up
  (implies (and (integerp n)
		(integerp k))
	   (equal (bitn (* x (expt 2 k)) (+ n k))
		  (bitn x n)))
  :use (:instance digitn-shift-up (b 2)))

(defruled bitn-shift-down
  (implies (and (natp i)
		(integerp k))
	   (equal (bitn (fl (/ x (expt 2 k))) i)
		  (bitn x (+ i k))))
  :enable digitn-fl
  :use (:instance digitn-shift-down (b 2)))

(defruled bitn-bits
  (implies (and (<= k (- i j))
		(case-split (<= 0 k))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k)))
	   (equal (bitn (bits x i j) k)
		  (bitn x (+ j k))))
  :enable digitn-digits)

(defrule bitn-plus-bits
    (implies (and (<= m n)
		  (integerp m)
		  (integerp n))
	     (= (bits x n m)
		(+ (* (bitn x n) (expt 2 (- n m)))
		   (bits x (1- n) m))))
  :use (:instance digitn-plus-digits (b 2))
  :rule-classes ())

(defrule bits-plus-bitn
    (implies (and (<= m n)
		  (integerp m)
		  (integerp n))
	     (= (bits x n m)
		(+ (bitn x m)
		   (* 2 (bits x n (1+ m))))))
  :use (:instance digits-plus-digitn (b 2))
  :rule-classes ())

; (defun sumbits (x n) ... )

(local
 (defrule sumbits-as-sumdigits
   (equal (sumbits x n)
          (sumdigits x n 2))))

(defruled sumbits-bits
    (implies (and (integerp x)
		  (natp n)
		  (> n 0))
	     (equal (sumbits x n)
		    (bits x (1- n) 0)))
    :enable sumdigits-digits)

(defruled sumbits-thm
    (implies (and (bvecp x n)
		  (natp n)
		  (> n 0))
	     (equal (sumbits x n)
		    x))
    :enable sumdigits-thm)

; (defnd all-bits-p (b k) ... )

(local
 (defrule all-bits-p-as-all-digits-p
   (equal (all-bits-p b k)
          (all-digits-p b k 2))
   :enable (all-bits-p all-digits-p)
   :induct (all-bits-p b k)))

; (defun sum-b (b k) ... )

(local
 (defrule sum-b-as-sum-d
   (equal (sum-b b k)
          (sum-d b k 2))
   :induct (sum-b b k)))

(defruled sum-bitn
  (implies (and (all-bits-p b n)
	        (natp k)
		(< k n))
           (equal (bitn (sum-b b n) k)
	          (nth k b)))
  :enable sum-digitn)

;; The next lemma can be used to prove equality of two bit vectors by
;; proving that they have the same value at bit n for all n.

; (defn bit-diff (x y) ... )

(local
 (defrule bit-diff-as-digit-diff
   (equal (bit-diff x y)
          (digit-diff x y 2))))

(defrule bit-diff-diff
  (implies (and (integerp x)
                (integerp y)
                (not (= x y)))
           (let ((n (bit-diff x y)))
             (and (natp n)
                  (not (= (bitn x n) (bitn y n))))))
  :use (:instance digit-diff-diff (b 2))
  :rule-classes ())

(defruled bvecp-bitn-1
    (implies (and (bvecp x (1+ n))
		  (<= (expt 2 n) x)
		  (natp n))
	     (equal (bitn x n) 1))
    :enable dvecp-digitn-1)

(defruled bvecp-bitn-2
  (implies (and (bvecp x n)
		(< k n)
		(<= (- (expt 2 n) (expt 2 k)) x)
		(integerp n)
		(integerp k))
	   (equal (bitn x k) 1))
  :enable dvecp-digitn-2
  :rule-classes ((:rewrite :match-free :all)))

(defruled bitn-expt
    (implies (case-split (integerp n))
	     (equal (bitn (expt 2 n) n)
		    1))
    :enable digitn-expt)

(defruled bitn-expt-0
  (implies (and (not (equal i n))
		(case-split (integerp i)))
	   (equal (bitn (expt 2 i) n)
		  0))
  :enable digitn-expt-0)

(defrule bitn-plus-expt-1
    (implies (and (real/rationalp x)
		  (integerp n))
	     (not (equal (bitn (+ x (expt 2 n)) n)
			 (bitn x n))))
  :use (:instance digitn-plus-expt-1 (b 2))
  :rule-classes ())

(defruled bitn-plus-mult
    (implies (and (< n m)
		  (integerp m)
		  (integerp k))
	     (equal (bitn (+ x (* k (expt 2 m))) n)
		    (bitn x n)))
    :use (:instance digitn-plus-mult (b 2)))

(defruled bitn-plus-mult-rewrite
    (implies (and (syntaxp (quotep c))
		  (equal (mod c (expt 2 (1+ n))) 0))
	     (equal (bitn (+ c x) n)
		    (bitn x n)))
    :use (:instance digitn-plus-mult-rewrite (b 2)))

;;;**********************************************************************
;;;			     CAT-R
;;;**********************************************************************

; (defund radix-cat (b x m y n) ... )

(local
 (defruled radix-cat-aux
   (implies (and (natp m)
                 (natp n)
                 (dvecp x m b)
                 (dvecp y n b)
                 (radixp b))
            (equal (radix-cat b x m y n)
                   (+ (* x (expt b n)) y)))
   :enable radix-cat))

; (defn formal-+ (x y) ... )

; (defun cat-size (x) ... )

; (defmacro cat-r (b &rest x) ... )

(defrule cat-r-dvecp
  (implies (and (<= (+ m n) k)
                (case-split (natp k))
                (radixp b))
           (dvecp (cat-r b x m y n) k b))
  :prep-lemmas (
   (acl2::with-arith5-nonlinear-help
    (defrule lemma
      (implies (and (natp m)
                    (natp n)
                    (integerp x)
                    (integerp y)
                    (< x (expt b m))
                    (< y (expt b n))
                    (radixp b))
               (< (+ y (* (expt b n) x)) (expt b (+ m n))))
      ))
    )
  :enable (radix-cat dvecp)
  :cases ((and (natp m) (natp n)))
  :hints (("subgoal 1" :use (
    (:instance lemma
      (x (digits x (1- m) 0 b))
      (y (digits y (1- n) 0 b)))
    (:instance digits-bounds
      (x x)
      (i (1- m))
      (j 0))
    (:instance digits-bounds
      (x y)
      (i (1- n))
      (j 0))))))

(defrule cat-r-with-n-0
  (implies (radixp b)
           (equal (radix-cat b x m y 0)
                  (digits x (1- m) 0 b)))
  :enable radix-cat)

(defrule cat-r-with-m-0
  (implies (radixp b)
           (equal (radix-cat b x 0 y n)
                  (digits y (1- n) 0 b)))
  :enable radix-cat)

(defruled cat-r-0
  (implies (and (case-split (dvecp y n b))
                (case-split (integerp n))
                (case-split (integerp m))
                (case-split (<= 0 m))
                (radixp b))
           (equal (cat-r b 0 m y n) y))
  :enable radix-cat)

(defruled cat-r-digits-1
  (implies (radixp b)
           (equal (cat-r b (digits x (1- m) 0 b) m y n)
                  (cat-r b x m y n)))
  :enable radix-cat)

(defruled cat-r-digits-2
  (implies (radixp b)
           (equal (cat-r b x m (digits y (1- n) 0 b) n)
                  (cat-r b x m y n)))
  :enable radix-cat)

(defrule cat-r-digits-3
  (implies (and (radixp b) (integerp i) (integerp m) (>= i (1- m)))
           (equal (cat-r b (digits x i 0 b) m y n)
                  (cat-r b x m y n)))
  :enable radix-cat)

(defrule cat-r-digits-4
  (implies (and  (radixp b)(integerp i) (integerp n) (>= i (1- n)))
           (equal (cat-r b x m (digits y i 0 b) n)
                  (cat-r b x m y n)))
  :enable radix-cat)

(defrule cat-r-associative
  (implies (and (case-split (<= (+ m n) p))
                (case-split (<= 0 m))
                (case-split (<= 0 n))
                (case-split (<= 0 q))
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp p))
                (case-split (integerp q))
                (radixp b))
           (equal (cat-r b (cat-r b x m y n) p z q)
                  (cat-r b x m (cat-r b y n z q) (+ n q))))
  :prep-lemmas (
   (defrule lemma
     (implies (and (natp m)
                   (natp n)
                   (natp q)
                   (integerp p)
                   (<= (+ m n) p)
                   (dvecp x m b)
                   (dvecp y n b)
                   (dvecp z q b)
                   (radixp b))
              (equal (cat-r b (cat-r b x m y n) p z q)
                     (cat-r b x m (cat-r b y n z q) (+ n q))))
     :cases ((not (dvecp (cat-r b x m y n) p b))
             (not (dvecp (cat-r b y n z q) (+ n q) b)))
     :hints (("subgoal 3" :in-theory (enable radix-cat-aux)))
     :rule-classes ()))
  :enable (cat-r-digits-1 cat-r-digits-2)
  :use ((:instance lemma
          (x (digits x (1- m) 0 b))
          (y (digits y (1- n) 0 b))
          (z (digits z (1- q) 0 b)))))

(defruled cat-r-equal-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep m)
                              (quotep n)))
                (case-split (dvecp y n b))
                (case-split (dvecp x m b))
                (case-split (< k (expt b (+ m n)))) ;not a problem hyp, since k, m and n are constants
                (case-split (integerp k))
                (case-split (<= 0 k))
                (case-split (integerp m))
                (case-split (<= 0 m))
                (case-split (integerp n))
                (case-split (<= 0 n))
                (radixp b))
           (equal (equal k (cat-r b x m y n))
                  (and (equal y (digits k (1- n) 0 b))
                       (equal x (digits k (+ -1 m n) n b)))))
  :enable radix-cat-aux
  :cases ((equal k (cat-r b x m y n)))
   :hints (
    ("subgoal 2"
     :in-theory (enable dvecp)
     :use ((:instance digits-plus-digits
                      (x k)
                      (n (+ -1 m n))
                      (p n)
                      (m 0))))
    ("subgoal 1" :in-theory (enable digits-plus-mult-1 digits-plus-mult-2))))

(defruled cat-r-equal-rewrite
  (implies (and (case-split (dvecp x1 m b))
                (case-split (dvecp y1 n b))
                (case-split (dvecp x2 m b))
                (case-split (dvecp y2 n b))
                (case-split (integerp n))
                (case-split (<= 0 n))
                (case-split (integerp m))
                (case-split (<= 0 m))
                (radixp b))
           (equal (equal (cat-r b x1 m y1 n)
                         (cat-r b x2 m y2 n))
                  (and (equal x1 x2)
                       (equal y1 y2))))
  :disable cat-r-dvecp
  :cases ((equal (cat-r b x1 m y1 n) (cat-r b x2 m y2 n)))
  :hints (("subgoal 1" :use (
    (:instance cat-r-dvecp
      (k (+ m n))
      (x x1)
      (y y1))
    (:instance cat-r-equal-constant
      (k (cat-r b x2 m y2 n))
      (x x1)
      (y y1))
    (:instance cat-r-equal-constant
      (k (cat-r b x1 m y1 n))
      (x x2)
      (y y2))))))

(defrule cat-r-digits-digits
  (implies (and (equal j (1+ k))
                (equal n (+ 1 (- l) k))
                (case-split (<= (+ 1 (- j) i) m))
                (case-split (<= j i))
                (case-split (<= l k))
                (case-split (integerp i))
                (case-split (integerp k))
                (case-split (integerp l))
                (case-split (integerp m))
                (radixp b))
           (equal (cat-r b (digits x i j b) m (digits x k l b) n)
                  (digits x i l b)))
  :enable radix-cat-aux
  :use (:instance digits-plus-digits
         (n i)
         (m l)
         (p (1+ k))))

(defrule cat-r-digitn-digits
    (implies (and (equal j (1+ k))
                  (equal n (+ 1 (- l) k))
                  (case-split (<= 1 m))
                  (case-split (<= l k))
                  (case-split (integerp j))
                  (case-split (integerp k))
                  (case-split (integerp l))
                  (case-split (integerp m))
                  (radixp b))
             (equal (cat-r b (digitn x j b) m (digits x k l b) n)
                    (digits x j l b)))
    :enable digitn)

(defrule cat-r-digits-digitn
  (implies (and (equal j (1+ k))
                (case-split (<= (+ 1 (- j) i) m))
                (case-split (<= j i))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                (case-split (integerp m))
                (radixp b))
           (equal (cat-r b (digits x i j b) m (digitn x k b) 1)
                  (digits x i k b)))
  :enable digitn)

(defrule cat-r-digitn-digitn
  (implies (and (equal i (1+ j))
                (case-split (integerp i))
                (case-split (integerp j))
                (radixp b))
           (equal (cat-r b (digitn x i b) 1 (digitn x j b) 1)
                  (digits x i j b)))
  :enable digitn)

(defruled digits-cat-r
  (implies (and (case-split (natp n))
                (case-split (natp m))
                (case-split (natp i))
                (case-split (natp j))
                (radixp b))
           (equal (digits (cat-r b x m y n) i j b)
                  (if (< i n)
                      (digits y i j b)
                    (if (>= j n)
                        (digits x (if (< i (+ m n))
                                      (- i n)
                                    (1- m))
                                (- j n) b)
                      (cat-r b (digits x (if (< i (+ m n))
                                             (- i n)
                                           (1- m)) 0 b)
                             (1+ (- i n))
                             (digits y (1- n) j b)
                             (- n j))))))
  :enable (radix-cat digits-plus-mult-1-alt digits-plus-mult-2-alt)
  :cases ((< i n)
          (>= j n))
  :hints (("subgoal 3" :use (:instance digits-plus-digits
                                       (x (cat-r b x m y n))
                                       (n i)
                                       (m j)
                                       (p n)))))

(defrule digits-cat-r-constants
  (implies (and (syntaxp (quotep n))
                (syntaxp (quotep m))
                (syntaxp (quotep i))
                (syntaxp (quotep j))
                (natp n)
                (natp m)
                (natp i)
                (natp j)
                (radixp b))
           (equal (digits (cat-r b x m y n) i j b)
                  (if (< i n)
                      (digits y i j b)
                    (if (>= j n)
                        (digits x (if (< i (+ m n))
                                      (- i n)
                                    (1- m))
                                (- j n) b)
                      (cat-r b (digits x (if (< i (+ m n))
                                             (- i n)
                                           (1- m)) 0 b)
                             (1+ (- i n))
                             (digits y (1- n) j b)
                             (- n j))))))
  :use digits-cat-r)

(defruled digitn-cat-r
  (implies (and (case-split (natp n))
                (case-split (natp m))
                (case-split (natp i))
                (radixp b))
           (equal (digitn (cat-r b x m y n) i b)
                  (if (< i n)
                      (digitn y i b)
                    (if (< i (+ m n))
                        (digitn x (- i n) b)
                      0))))
  :enable (digitn digits-cat-r))

(defrule digitn-cat-r-constants
  (implies (and (syntaxp (quotep n))
                (syntaxp (quotep m))
                (syntaxp (quotep i))
                (natp n)
                (natp m)
                (natp i)
                (radixp b))
           (equal (digitn (cat-r b x m y n) i b)
                  (if (< i n)
                      (digitn y i b)
                    (if (< i (+ m n))
                        (digitn x (- i n) b)
                      0))))
  :use digitn-cat-r)

; (defund mulcat-r (l n x b) ... )

(defruled mulcat-r-digits
  (implies (and (integerp l)
                (integerp x)
                (radixp b))
           (equal (mulcat-r l n (digits x (1- l) 0 b) b)
                  (mulcat-r l n x b)))
  :enable (mulcat-r cat-r-digits-2)
  :induct (sub1-induction n))

(defrule mulcat-r-dvecp
  (implies (and (>= p (* l n))
                (case-split (natp p))
                (case-split (natp l))
                (radixp b))
           (dvecp (mulcat-r l n x b) p b))
  :enable mulcat-r
  :induct (sub1-induction n))

(defrule mulcat-r-1
  (implies (and (natp l)
                (radixp b))
           (equal (mulcat-r l 1 x b)
                  (digits x (1- l) 0 b)))
  :enable mulcat-r)

(defrule mulcat-r-0
  (equal (mulcat-r l n 0 b) 0)
  :enable (mulcat-r radix-cat)
  :induct (sub1-induction n))

(defrule mulcat-r-n-b1
  (implies (and (case-split (<= 0 n))
                (= b1 (1- b))
                (radixp b))
	   (equal (mulcat-r 1 n b1 b)
		  (1- (expt b n))))
  :enable (mulcat-r radix-cat)
  :induct (sub1-induction n))

(defrule digbitn-mulcat-r-1
  (implies (and (< m n)
                (case-split (dvecp x 1 b))
                (case-split (natp m))
                (case-split (integerp n))
                (radixp b))
           (equal (digitn (mulcat-r 1 n x b) m b)
                  x))
  :prep-lemmas (
    (defrule lemma
      (implies (and (dvecp x 1 b)
                    (natp m)
                    (posp k)
                    (radixp b))
               (equal (digitn (mulcat-r 1 (+ k m) x b) m b)
                      x))
      :enable (mulcat-r digitn-cat-r)
      :induct (sub1-induction m)))
  :use (:instance lemma (k (- n m))))

;;;**********************************************************************
;;;			     CAT
;;;**********************************************************************

; (defund binary-cat (x m y n) ... )

(local
 (defrule binary-cat-as-radix-cat
   (equal (binary-cat x m y n)
          (radix-cat 2 x m y n))
   :enable (binary-cat radix-cat)))

(defrule cat-bvecp
  (implies (and (<= (+ m n) k)
		(case-split (integerp k)))
	   (bvecp (cat x m y n) k))
  :cases ((and (natp m) (natp n)))
  :hints (("subgoal 2" :in-theory (enable radix-cat))))

(defrule cat-with-n-0
  (equal (binary-cat x m y 0)
	 (bits x (1- m) 0)))

(defrule cat-with-m-0
  (equal (binary-cat x 0 y n)
	 (bits y (1- n) 0)))

(defruled cat-0
  (implies (and (case-split (bvecp y n))
		(case-split (integerp n))
		(case-split (integerp m))
		(case-split (<= 0 m)))
	   (equal (cat 0 m y n) y))
  :enable cat-r-0
  :cases ((natp n))
  :hints (("subgoal 2" :in-theory (enable radix-cat))))

(defruled cat-bits-1
    (equal (cat (bits x (1- m) 0) m y n)
	   (cat x m y n))
    :use (:instance cat-r-digits-1 (b 2)))

(defruled cat-bits-2
    (equal (cat x m (bits y (1- n) 0) n)
	   (cat x m y n))
    :use (:instance cat-r-digits-2 (b 2)))

(defrule cat-bits-3
  (implies (and (integerp i) (integerp m) (>= i (1- m)))
           (equal (cat (bits x i 0) m y n)
                  (cat x m y n)))
    :use (:instance cat-r-digits-3 (b 2)))

(defrule cat-bits-4
  (implies (and (integerp i) (integerp n) (>= i (1- n)))
           (equal (cat x m (bits y i 0) n)
                  (cat x m y n)))
    :use (:instance cat-r-digits-4 (b 2)))

(defrule cat-associative
  (implies (and (case-split (<= (+ m n) p))
		(case-split (<= 0 m))
		(case-split (<= 0 n))
		(case-split (<= 0 q))
		(case-split (integerp m))
		(case-split (integerp n))
		(case-split (integerp p))
		(case-split (integerp q)))
	   (equal (cat (cat x m y n) p z q)
		  (cat x m (cat y n z q) (+ n q)))))

(defruled cat-equal-constant
  (implies (and (syntaxp (and (quotep k)
			      (quotep m)
			      (quotep n)))
		(case-split (bvecp y n))
		(case-split (bvecp x m))
		(case-split (< k (expt 2 (+ m n)))) ;not a problem hyp, since k, m and n are constants
		(case-split (integerp k))
		(case-split (<= 0 k))
		(case-split (integerp m))
		(case-split (<= 0 m))
		(case-split (integerp n))
		(case-split (<= 0 n)))
	   (equal (equal k (cat x m y n))
		  (and (equal y (bits k (1- n) 0))
		       (equal x (bits k (+ -1 m n) n)))))
  :use (:instance cat-r-equal-constant (b 2)))

(defruled cat-equal-rewrite
  (implies (and (case-split (bvecp x1 m))
		(case-split (bvecp y1 n))
		(case-split (bvecp x2 m))
		(case-split (bvecp y2 n))
		(case-split (integerp n))
		(case-split (<= 0 n))
		(case-split (integerp m))
		(case-split (<= 0 m)))
	   (equal (equal (cat x1 m y1 n)
			 (cat x2 m y2 n))
		  (and (equal x1 x2)
		       (equal y1 y2))))
  :enable cat-r-equal-rewrite)

(defrule cat-bits-bits
  (implies (and (equal j (1+ k))
		(equal n (+ 1 (- l) k))
		(case-split (<= (+ 1 (- j) i) m))
		(case-split (<= j i))
		(case-split (<= l k))
		(case-split (integerp i))
		(case-split (integerp k))
		(case-split (integerp l))
		(case-split (integerp m)))
	   (equal (cat (bits x i j) m (bits x k l) n)
		  (bits x i l))))

(defrule cat-bitn-bits
    (implies (and (equal j (1+ k))
		  (equal n (+ 1 (- l) k))
		  (case-split (<= 1 m))
		  (case-split (<= l k))
		  (case-split (integerp j))
		  (case-split (integerp k))
		  (case-split (integerp l))
		  (case-split (integerp m)))
	     (equal (cat (bitn x j) m (bits x k l) n)
		    (bits x j l))))

(defrule cat-bits-bitn
  (implies (and (equal j (1+ k))
	(case-split (<= (+ 1 (- j) i) m))
		(case-split (<= j i))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k))
		(case-split (integerp m)))
	   (equal (cat (bits x i j) m (bitn x k) 1)
		  (bits x i k))))

(defrule cat-bitn-bitn
  (implies (and (equal i (1+ j))
		(case-split (integerp i))
		(case-split (integerp j)))
	   (equal (cat (bitn x i) 1 (bitn x j) 1)
		  (bits x i j))))

(defruled bits-cat
  (implies (and (case-split (natp n))
		(case-split (natp m))
		(case-split (natp i))
		(case-split (natp j)))
	   (equal (bits (cat x m y n) i j)
		  (if (< i n)
		      (bits y i j)
		    (if (>= j n)
			(bits x (if (< i (+ m n))
				    (- i n)
				  (1- m))
			      (- j n))
		      (cat (bits x (if (< i (+ m n))
					(- i n)
				      (1- m)) 0)
			    (1+ (- i n))
			    (bits y (1- n) j)
			    (- n j))))))
  :enable digits-cat-r)

(defrule bits-cat-constants
  (implies (and (syntaxp (quotep n))
		(syntaxp (quotep m))
		(syntaxp (quotep i))
		(syntaxp (quotep j))
		(natp n)
		(natp m)
		(natp i)
		(natp j))
	   (equal (bits (cat x m y n) i j)
		  (if (< i n)
		      (bits y i j)
		    (if (>= j n)
			(bits x (if (< i (+ m n))
				    (- i n)
				  (1- m))
			      (- j n))
		      (cat (bits x (if (< i (+ m n))
				       (- i n)
				     (1- m)) 0)
			   (1+ (- i n))
			   (bits y (1- n) j)
			   (- n j))))))
  :use bits-cat)

(defruled bitn-cat
  (implies (and (case-split (natp n))
		(case-split (natp m))
		(case-split (natp i)))
	   (equal (bitn (cat x m y n) i)
		  (if (< i n)
		      (bitn y i)
		    (if (< i (+ m n))
		      (bitn x (- i n))
                      0))))
  :enable digitn-cat-r)

(defrule bitn-cat-constants
  (implies (and (syntaxp (quotep n))
		(syntaxp (quotep m))
		(syntaxp (quotep i))
		(natp n)
		(natp m)
		(natp i))
	   (equal (bitn (cat x m y n) i)
		  (if (< i n)
		      (bitn y i)
		    (if (< i (+ m n))
		      (bitn x (- i n))
                      0))))
  :use bitn-cat)

; (defund mulcat (l n x) ... )

(local
 (defrule mulcat-as-mulcat-r
   (equal (mulcat l n x)
          (mulcat-r l n x 2))
   :enable (mulcat mulcat-r)))

(defruled mulcat-bits
    (implies (and (integerp l)
		  (integerp x))
	     (equal (mulcat l n (bits x (1- l) 0))
		    (mulcat l n x)))
    :enable mulcat-r-digits)

(defrule mulcat-bvecp
  (implies (and (>= p (* l n))
		(case-split (integerp p))
		(case-split (natp l)))
	   (bvecp (mulcat l n x) p))
  :cases ((natp n))
  :hints (("subgoal 2" :in-theory (enable mulcat-r))))

(defrule mulcat-1
    (implies (natp l)
	     (equal (mulcat l 1 x)
		    (bits x (1- l) 0))))

(defrule mulcat-0
  (equal (mulcat l n 0) 0))

(defrule mulcat-n-1
  (implies (case-split (<= 0 n))
	   (equal (mulcat 1 n 1)
		  (1- (expt 2 n)))))

(defrule bitn-mulcat-1
  (implies (and (< m n)
		(case-split (bvecp x 1))
		(case-split (natp m))
		(case-split (integerp n)))
	   (equal (bitn (mulcat 1 n x) m)
		  x)))

;;;**********************************************************************
;;;		      Signed Integer Encodings with Radix
;;;**********************************************************************

; (defund ui-r (r n b) ... )

(defrule ui-r-range
  (implies (radixp b)
           (< (ui-r r n b) (expt b n)))
  :rule-classes :linear
  :enable ui-r)

(defruled ui-r-def
  (implies (and (real/rationalp r)
                (radixp b))
           (equal (ui-r r n b)
                  (- r (chop-r r (- n) b))))
  :enable (ui-r chop-r)
  :use (:instance mod-def
                  (x r)
                  (y (expt b n))))

(defrule ui-r-does-nothing
  (implies (and (real/rationalp r)
                (<= 0 r)
                (< r (expt b n)))
           (equal (ui-r r n b) r))
  :enable ui-r)

(defruled ui-r-mod
  (implies (and (integerp k)
                (integerp n)
                (radixp b)
                (<= n k))
           (equal (ui-r (mod r (expt b k)) n b)
                  (ui-r r n b)))
  :enable ui-r)

; (defund si-r (r n b) ... )

(defrule si-r-range
  (implies (radixp b)
           (and (< (si-r r n b) (/ (expt b n) 2))
                (>= (si-r r n b) (- (/ (expt b n) 2)))))
  :enable si-r
  :rule-classes :linear)

(defrule si-r-does-nothing
  (implies (and (real/rationalp r)
                (<= (* -1/2 (expt b n)) r)
                (< r (* 1/2 (expt b n))))
           (equal (si-r r n b) r))
  :enable si-r)

(acl2::with-arith5-nonlinear-help
 (defruled si-r-def
   (implies (and (real/rationalp r)
                 (radixp b))
           (equal (si-r r n b)
                  (- r (chop-r (+ r (/ (expt b n) 2)) (- n) b))))
  :enable (si-r chop-r)
  :cases ((< r (* (expt b n)
                  (fl (+ 1/2 (* r (expt b (- n))))))))
  :hints
  (("subgoal 2" :use (:instance mod-force
                                (m r)
                                (n (expt b n))
                                (a (fl (+ 1/2 (* r (expt b (- n))))))))
   ("subgoal 1" :use (:instance mod-force
                                (m r)
                                (n (expt b n))
                                (a (1- (fl (+ 1/2 (* r (expt b (- n))))))))))))

(defruled si-r-mod
  (implies (and (integerp k)
                (integerp n)
                (radixp b)
                (<= n k))
           (equal (si-r (mod r (expt b k)) n b)
                  (si-r r n b)))
  :enable si-r)

(acl2::with-arith5-nonlinear-help
 (defruled si-r-even-b
  (implies (and (radixp b)
                (evenp b))
           (equal (si-r r n b)
                  (let ((r (realfix r))
                        (b^n (expt b n)))
                    (if (>= (digitn r (1- (ifix n)) b) (/ b 2))
                        (- (mod r b^n) b^n)
                    (mod r b^n)))))
  :prep-lemmas (
    (acl2::with-arith5-nonlinear-help
     (defrule lemma
       (implies (and (real/rationalp r)
                     (integerp n)
                     (integerp d)
                     (radixp b))
                (equal (< (digitn r (1- n) b) d)
                       (< (mod r (expt b n)) (* d (expt b (1- n))))))
       :enable (digitn digits)
       :use (:instance fl-def
                       (x (* (mod r (expt b n)) (expt b (- 1 n)))))
       :rule-classes ())))
  :enable si-r
  :use (:instance lemma
         (r (realfix r))
         (n (ifix n))
         (d (/ b 2)))))

(defrule si-r-digits
  (implies (and (integerp x)
                (< x (/ (expt b n) 2))
                (>= x (- (/ (expt b n) 2)))
                (radixp b))
           (= (si-r (digits x (1- n) 0 b) n b)
              x))
  :rule-classes ()
  :enable (digits-mod si-r-mod))

(defruled digits-si-r
  (implies (and (integerp n)
                (< i n)
                (radixp b))
           (equal (digits (si-r r n b) i j b)
                  (digits r i j b)))
  :enable si-r
  :cases ((and (integerp i) (integerp j)))
  :hints (("subgoal 1" :in-theory (enable mod-digits-equal-cor)
          :use (:instance digits-plus-mult-2-rewrite
                          (x (mod r (expt b n)))
                          (c (- (expt b n)))
                          (n i)
                          (m j)))))

(defruled si-r-shift
  (implies (and (natp n)
                (natp k)
                (dvecp r n b))
           (equal (si-r (* (expt b k) r) (+ k n) b)
                  (* (expt b k) (si-r r n b))))
  :enable si-r
  :use (:instance digitn-shift-up (x r) (n (1- n))))


; (defund sextend-r (m n r b) ... )

(defruled si-r-sextend-r
  (implies (and (real/rationalp r)
                (integerp n)
                (integerp m)
                (<= n m)
                (radixp b))
           (equal (si-r (sextend-r m n r b) m b)
                  (si-r r n b)))
  :enable (si-r sextend-r))

(acl2::with-arith5-nonlinear-help
 (defruled si-r-approx-lemma
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (integerp n)
                (radixp b)
                (< (abs (si-r x n b))
                   (- (/ (expt b n) 2) (abs (- x y)))))
           (equal (- (si-r x n b)
                     (si-r y n b))
                  (- x y)))
  :enable (si-r-def chop-r)
  :use (:instance fl-unique
                  (x (+ 1/2 (* y (expt b (- n)))))
                  (n (fl (+ 1/2 (* x (expt b (- n)))))))))

(defruled si-r-approx
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (integerp n)
                (radixp b)
                (< (abs (si-r (mod x (expt b n)) n b))
                   (- (/ (expt b n) 2) (abs (- x y)))))
           (equal (- (si-r (mod x (expt b n)) n b)
                     (si-r (mod y (expt b n)) n b))
                  (- x y)))
  :enable (si-r-mod si-r-approx-lemma))

;;;**********************************************************************
;;;		      Signed Integer Encodings
;;;**********************************************************************

; (defnd ui (r) ... )

; (defund si (r n) ... )

(defthm int-si
  (implies (and (integerp r)
                (natp n))
	   (integerp (si r n)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable si))))

(defrulel si-as-si-r
  (implies (bvecp r n)
           (equal (si r n)
                  (si-r r n 2)))
  :enable (si si-r-even-b)
  :disable digits-n-n-rewrite
  :cases ((integerp n))
  :hints (("subgoal 2" :in-theory (enable digitn digits dvecp))))

(defrule si-bits
  (implies (and (integerp x)
                (natp n)
                (< x (expt 2 (1- n)))
                (>= x (- (expt 2 (1- n)))))
           (= (si (bits x (1- n) 0) n)
              x))
  :rule-classes ()
  :use (:instance si-r-digits (b 2))
  :cases ((bvecp (bits x (1- n) 0) n)))

(defruled bits-si
  (implies (and (integerp n)
                (< i n))
           (equal (bits (si r n) i j)
                  (bits r i j)))
  :enable (si bits)
  :use (:instance bits-plus-mult-2-rewrite
                  (x r)
                  (c (- (expt 2 n)))
                  (n i)
                  (m j)))

(defruled si-shift
  (implies (and (natp n)
                (natp k)
                (bvecp r n))
           (equal (si (* (expt 2 k) r) (+ k n))
                  (* (expt 2 k) (si r n))))
  :use ((:instance si-r-shift (b 2))
        (:instance bvecp-shift-up (x r) (n (+ k n)))))

; (defund sextend (m n r) ... )

(local
 (defrule sextend-as-sextend-r
   (implies (and (natp n)
                 (<= n m)
                 (bvecp r n))
            (equal (sextend m n r)
                   (sextend-r m n r 2)))
   :enable (sextend-r sextend digits-mod)))

(defruled si-sextend
  (implies (and (natp n)
                (natp m)
                (<= n m)
                (bvecp r n))
           (equal (si (sextend m n r) m)
                  (si r n)))
  :enable si-r-sextend-r
  :cases ((bvecp (sextend m n r) m))
  :hints (("subgoal 2" :in-theory (enable dvecp sextend-r))))

(defruled si-approx
  (implies (and (not (zp n))
                (integerp x)
                (integerp y)
                (< (abs (si (mod x (expt 2 n)) n))
                   (- (expt 2 (1- n)) (abs (- x y)))))
           (equal (- (si (mod x (expt 2 n)) n)
                     (si (mod y (expt 2 n)) n))
                  (- x y)))
  :cases ((and (bvecp (mod x (expt 2 n)) n)
               (bvecp (mod y (expt 2 n)) n)))
  :hints
  (("subgoal 2" :in-theory (enable dvecp))
   ("subgoal 1" :in-theory (enable si-r-approx))))

(defthmd si-to-fl-mod
  (implies (and (real/rationalp x)
                (integerp m)
                (integerp n)
                (< m n))
           (equal (si x n)
                  (+ (* (expt 2 m)
                        (si (fl (/ x (expt 2 m)))
                            (- n m)))
                     (mod x (expt 2 m)))))
  :hints (("Goal" :in-theory (enable si bitn-def))))

;;;**********************************************************************
;;;                      Fixed-Point Registers with radix
;;;**********************************************************************

; (defund uf-r (r n m b) ... )

(acl2::with-arith5-nonlinear-help
 (defrule uf-r-range
   (implies (and (integerp n)
                 (integerp m)
                 (radixp b))
            (< (uf-r r n m b) (expt b m)))
   :rule-classes :linear
   :enable uf-r))

(defruled uf-r-mod
  (implies (and (integerp k)
                (integerp n)
                (radixp b)
                (<= n k))
           (equal (uf-r (mod r (expt b k)) n m b)
                  (uf-r r n m b)))
  :enable (uf-r ui-r-mod)
  :cases ((real/rationalp r))
  :hints (("subgoal 2" :in-theory (enable ui-r))))

; (defund sf-r (r n m b) ... )

(acl2::with-arith5-nonlinear-help
 (defrule sf-r-range
   (implies (and (integerp n)
                 (integerp m)
                 (radixp b))
            (and (< (sf-r r n m b) (/ (expt b m) 2))
                 (<= (- (/ (expt b m) 2)) (sf-r r n m b))))
   :rule-classes :linear
   :enable sf-r))

(defruled sf-r-mod
  (implies (and (integerp k)
                (integerp n)
                (radixp b)
                (<= n k))
           (equal (sf-r (mod r (expt b k)) n m b)
                  (sf-r r n m b)))
  :enable (sf-r si-r-mod)
  :cases ((real/rationalp r))
  :hints (("subgoal 2" :in-theory (enable si-r))))

(defruled digits-uf-r
  (let ((x (uf-r r n m b))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (dvecp r n b)
                  (natp i)
                  (natp j)
                  (<= j i))
             (equal (digits r i j b)
                    (* (expt b (- f j))
                       (- (chop-r x (- f j) b)
                          (chop-r x (- f (1+ i)) b))))))
  :enable (uf-r ui-r chop-r)
  :use (:instance digits-fl-diff (x r) (i (1+ i))))

(defruled digits-sf-r
  (let ((x (sf-r r n m b))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (dvecp r n b)
                  (natp i)
                  (natp j)
                  (<= j i)
                  (< i n))
             (equal (digits r i j b)
                    (* (expt b (- f j))
                       (- (chop-r x (- f j) b)
                          (chop-r x (- f (1+ i)) b))))))
  :enable (sf-r si-r chop-r)
  :use ((:instance digits-fl-diff (x r) (i (1+ i)))
        (:instance digits-fl-diff (x (- r (expt 2 n))) (i (1+ i)))
        (:instance digits-plus-mult-2 (x r) (k n) (y -1) (n i) (m j))))

(defrule chop-r-uf-r
  (let ((x (uf-r r n m b))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (dvecp r n b)
                  (integerp k)
                  (<= (- f n) k)
                  (< k f))
             (iff (= (chop-r x k b) x)
                  (= (digits r (1- (- f k)) 0 b) 0))))
  :rule-classes ()
  :enable (uf-r ui-r-def chop-r digits-mod))

(defrule chop-r-sf-r
  (let ((x (sf-r r n m b))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (dvecp r n b)
                  (integerp k)
                  (<= (- f n) k)
                  (< k f))
             (iff (= (chop-r x k b) x)
                  (= (digits r (1- (- f k)) 0 b) 0))))
  :rule-classes ()
  :enable (sf-r si-r-def chop-r digits-mod)
  :use (:instance mod-def
                  (x r)
                  (y (expt b (- (- n m) k)))))

(defruled sf-r-val
  (implies (and (natp n)
                (natp m)
                (<= m n)
                (dvecp r n b)
                (integerp y)
                (= (mod y (expt b n)) r)
                (<= (- (/ (expt b n) 2)) y)
                (< y (/ (expt b n) 2)))
            (equal (sf-r r n m b)
                   (* (expt b (- m n)) y)))
  :enable (sf-r digits-mod)
  :use (:instance si-r-digits (x y)))

;;;**********************************************************************
;;;                      Fixed-Point Registers
;;;**********************************************************************

; (defund uf (r n m) ... )

(defrulel uf-as-uf-r
  (implies (bvecp r n)
           (equal (uf r n m)
                  (uf-r r n m 2)))
  :enable (uf uf-r ui))

; (defund sf (r n m) ... )

(defrulel sf-as-sf-r
  (implies (bvecp r n)
           (equal (sf r n m)
                  (sf-r r n m 2)))
  :enable (sf sf-r))

(defrulel |chop as chop-r|
  (equal (chop x k)
         (chop-r x k 2))
  :enable (chop chop-r))

(defruled bits-uf
  (let ((x (uf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp i)
                  (natp j)
                  (<= j i))
             (equal (bits r i j)
                    (* (expt 2 (- f j))
                       (- (chop x (- f j))
                          (chop x (- f (1+ i))))))))
  :enable digits-uf-r)

(defruled bits-sf
  (let ((x (sf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp i)
                  (natp j)
                  (<= j i)
                  (< i n))
             (equal (bits r i j)
                    (* (expt 2 (- f j))
                       (- (chop x (- f j))
                          (chop x (- f (1+ i))))))))
  :use (:instance digits-sf-r (b 2)))

(defrule chop-uf
  (let ((x (uf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (integerp k)
                  (<= (- f n) k)
                  (< k f))
             (iff (= (chop x k) x)
                  (= (bits r (1- (- f k)) 0) 0))))
  :rule-classes ()
  :use (:instance chop-r-uf-r (b 2)))

(defrule chop-sf
  (let ((x (sf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (integerp k)
                  (<= (- f n) k)
                  (< k f))
             (iff (= (chop x k) x)
                  (= (bits r (1- (- f k)) 0) 0))))
  :rule-classes ()
  :use (:instance chop-r-sf-r (b 2)))

(defruled sf-val
  (implies (and (natp n)
                (natp m)
                (<= m n)
                (bvecp r n)
                (integerp y)
                (= (mod y (expt 2 n)) r)
                (<= (- (expt 2 (1- n))) y)
                (< y (expt 2 (1- n))))
            (equal (sf r n m)
                   (* (expt 2 (- m n)) y)))
  :enable sf-r-val)
