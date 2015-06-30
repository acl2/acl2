(in-package "RTL")

(include-book "../rel9-rtl-pkg/lib/util")

(include-book "../rel9-rtl-pkg/lib/basic")
(include-book "../rel9-rtl-pkg/lib/bits")
(include-book "../rel9-rtl-pkg/lib/float")

(local (include-book "../rel9-rtl-pkg/lib/reps"))

(defund bias$ (q) (- (expt 2 (- q 1)) 1) )

(defund drepp$ (x p q)
  (and (rationalp x)
       (not (= x 0))
       (<= (- 2 p) (+ (expo x) (bias$ q)))
       (<= (+ (expo x) (bias$ q)) 0)
       ;number of bits available in the sig field = p - 1 - ( - bias - expo(x))
       (exactp x (+ -2 p (expt 2 (- q 1)) (expo x)))))

(defund spd$ (p q)
     (expt 2 (+ 2 (- (bias$ q)) (- p))))

(local-defthm bias$-rewrite
  (equal (bias$ q) (bias q))
  :hints (("Goal" :in-theory (enable bias bias$))))

(local-defthm drepp$-rewrite
  (equal (drepp$ x p q) (drepp x p q))
  :hints (("Goal" :in-theory (enable drepp drepp$))))

(local-defthm spd$-rewrite
  (equal (spd$ p q) (spd p q))
  :hints (("Goal" :in-theory (enable spd spd$))))

(defthmd spd-mult$
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (> r 0)
		(rationalp r)
		(= m (/ r (spd$ p q))))
	   (iff (drepp$ r p q)
		(and (natp m)
		     (<= 1 m)
		     (< m (expt 2 (1- p))))))
  :hints (("Goal" :use spd-mult)))

(defund rebias$ (expo old new)
  (+ expo (- (bias$ new) (bias$ old))))

(local-defthm rebias$-rewrite
  (equal (rebias$ expo old new) (rebias-expo expo old new))
  :hints (("Goal" :in-theory (enable rebias-expo rebias$))))

(defthm natp-rebias-up$
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (natp (rebias$ x m n)))
  :hints (("Goal" :use natp-rebias-up)))

(defthm natp-rebias-down$
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (natp (rebias$ x n m)))
  :hints (("Goal" :use natp-rebias-down)))

(defthm bvecp-rebias-up$
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (bvecp (rebias$ x m n) n))
  :hints (("Goal" :use bvecp-rebias-up)))

(defthm bvecp-rebias-down$
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (bvecp (rebias$ x n m) m))
  :hints (("Goal" :use bvecp-rebias-down)))

(defthmd rebias-lower$
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (equal (rebias$ x n m)
		    (cat (bitn x (1- n))
			 1
			 (bits x (- m 2) 0)
			 (1- m))))
  :hints (("Goal" :use rebias-lower)))

(defthmd rebias-higher$
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x m))
	     (equal (rebias$ x m n)
		    (cat (cat (bitn x (1- m))
			      1
			      (mulcat 1 (- n m) (bitn (lognot x) (1- m)))
			      (- n m))
			 (1+ (- n m))
			 (bits x (- m 2) 0)
			 (1- m))))
  :hints (("Goal" :use rebias-higher)))


