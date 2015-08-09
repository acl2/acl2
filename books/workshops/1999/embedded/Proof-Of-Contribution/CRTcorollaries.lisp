



(in-package "ACL2")

(include-book "CRT")

(in-theory (disable g-c-d))

(defthm pg-hack-1
	(implies (and (integerp v) (= gcd 1)) (= (* v gcd) v))
	:rule-classes nil)

(defthm pg-hack-2
 (implies
  (and
   (natp x)
   (natp y)
   (integerp v)
   (= (g-c-d x y) 1))
 (= (* v (+ (* (A X Y) X) (* (B X Y) Y))) v))
 :hints (("Goal" :in-theory '((:definition natp))
	:use (a-b-thm
	      (:instance pg-hack-1 (gcd (+ (* (A X Y) X) (* (B X Y) Y)))))))
 :rule-classes nil)


(defthm pg-hack-3
 (implies
  (and
   (integerp a)
   (integerp b)
   (natp x)
   (natp y)
   (> x 0)
   (> y 0)
   (integerp v))
 (= (* v (+ (* A X) (* B Y)) (/ (* x y)))
    (+ (* (/ v y) a) (* (/ v x) b))))
 :rule-classes nil)


(defthm pg-hack-4
 (implies
  (and
   (natp x)
   (natp y)
   (> x 0)
   (> y 0)
   (integerp v))
 (= (* v (+ (* (A X Y) X) (* (B X Y) Y)) (/ (* x y)))
    (+ (* (/ v y) (a x y)) (* (/ v x) (b x y)))))
 :hints (("Goal" :use ((:instance pg-hack-3 (a (a x y)) (b (b x y)))
	               (:type-prescription a)
	               (:type-prescription b))))
 :rule-classes nil)


(defthm pg-hack-5
 (implies
   (and
     (integerp v1)
     (integerp v2)
     (integerp v3)
     (integerp v4))
   (integerp (+ (* v1 v2) (* v3 v4))))
 :rule-classes nil)


(defthm pg-hack-6
 (implies
  (and
   (integerp (/ v y))
   (integerp (/ v x)))
   (integerp (+ (* (/ v y) (a x y)) (* (/ v x) (b x y)))))
	 :hints (("Goal" :use ( (:instance pg-hack-5 (v1 (/ v y)) (v2 (a x y)) (v3 (/ v x)) (v4 (b x y)))
	               (:type-prescription a)
	               (:type-prescription b))))
  :rule-classes nil)

(defthm pg-hack-7
(IMPLIES
 (AND
  (equal decomp-a-b
	 V)
  (equal (* decomp-a-b
	    div)
	 res)
  (INTEGERP res))
 (INTEGERP (* V div)))
:hints (("Goal" :in-theory nil))
:rule-classes nil)



(defthm divides-both
 (implies
  (and
   (natp x)
   (natp y)
   (> x 0)
   (> y 0)
   (integerp v)
   (integerp (/ v y))
   (integerp (/ v x))
   (rel-prime x y))
  (integerp (/ v (* x y))))
 :hints (("Goal" :in-theory (current-theory 'ground-zero)
        :use (rel-prime
              pg-hack-2
              pg-hack-4
              pg-hack-6
	     (:instance pg-hack-7 (div (/ (* X Y)))
                                  (res  (+ (* (* V (/ Y)) (A X Y)) (* (* V (/ X)) (B X Y))))
	                          (decomp-a-b (* V (+ (* (A X Y) X) (* (B X Y) Y)))))))))

(defun posp-all (l)
  (if (endp l)
      t
    (and (posp (car l))
	 (posp-all (cdr l)))))





(defthm mod-0-intp
  (implies
   (and
    (natp n)
    (posp d))
   (equal (integerp (/ n d)) (equal (nonneg-int-mod n d) 0)))
  :hints (("Goal" :use (:instance Left-nonneg-int-mod-* (n d) (j (/ n d))))))



(defthm only-divisor-of-coprimes-is-1
 (implies
  (and
   (natp y)
   (natp x)
   (posp z)
   (rel-prime x y)
   (integerp (/ x z))
   (integerp (/ y z)))
  (= z 1))
 :hints (("Goal" :use (rel-prime g-c-d
		       (:instance Nonneg-int-gcd-is-LARGEST-common-divisor-<= (d z)))))
 :rule-classes nil)


(defthm integer-div-of-factor
 (implies
  (and
   (natp a)
   (natp b)
   (natp c)
   (rel-prime a b)
   (integerp (/ (* b c) a)))
  (integerp (/ c a)))
  :hints (("Goal" :use
	   ((:instance rel-prime (x a) (y b))
            (:instance g-c-d (x a) (y b))
	    (:instance mod-0-intp (n c) (d a))
	    (:instance mod-0-intp (n (* b c)) (d a))
	    (:instance Divisor-of-product-divides-factor (y b) (z a) (x c))))))



(defthm ck1
 (implies
  (and
   (integerp x)
   (posp y)
   (integerp (/ x y)))
  (= x (* (/ x y) y)))
 :rule-classes nil)

(defthm ck2
 (implies
  (and
   (integerp c)
   (= (+ (* a x) (* b y)) 1))
   (= (* c (+ (* a x) (* b y))) c))
 :rule-classes nil)

(defthm ck3
 (implies
  (and
   (integerp c))
   (= (+ (* c a x) (* c b y))
      (* c (+ (* a x) (* b y)))))
 :rule-classes nil)

(defthm ck4
 (implies
  (and
   (integerp c)
   (= (+ (* a x) (* b y)) 1))
   (= (+ (* c a x) (* c b y)) c))
 :hints (("Goal" :use (ck2 ck3)))
 :rule-classes nil)




(defthm ck5
 (implies
  (and
   (natp m)
   (natp n)
   (natp k)
   (rel-prime m n))
  (= k (+ (* k (a m n) m) (* k (b m n) n))))
 :hints (("Goal" :use (
		       (:instance ck4 (a (a m n)) (b (b m n)) (x m) (y n) (c k))
		       (:instance a-b-thm (x m) (y n))
		       (:instance rel-prime (x m) (y n)))))
 :rule-classes nil)

(defthm ck6
 (implies
  (and
   (natp m)
   (natp n)
   (natp k)
   (posp cd)
   (integerp (/ m cd))
   (integerp (/ (* n k) cd))
   (rel-prime m n))
  (= k (+ (* k (a m n) (/ m cd) cd) (* (b m n) (/ (* n k) cd) cd))))
 :hints (("Goal" :use (
		       ck5
		       (:instance ck1 (x m) (y cd))
		       (:instance ck1 (x (* n k)) (y cd)))))
 :rule-classes nil)

(defthm ck7
 (implies
  (and
   (natp m)
   (natp n)
   (natp k)
   (posp cd)
   (integerp (/ m cd))
   (integerp (/ (* n k) cd))
   (rel-prime m n))
  (= k (* cd (+ (* k (a m n) (/ m cd) ) (* (b m n) (/ (* n k) cd))))))
 :hints (("Goal" :use ck6))
 :rule-classes nil)

(defthm ck8
 (implies
  (and
   (natp m)
   (natp n)
   (natp k)
   (posp cd)
   (integerp (/ m cd))
   (integerp (/ (* n k) cd))
   (rel-prime m n))
  (integerp (+ (* k (a m n) (/ m cd) ) (* (b m n) (/ (* n k) cd)))))
 :rule-classes nil)

(defthm ck9
 (implies
  (and
   (natp m)
   (natp n)
   (natp k)
   (posp cd)
   (integerp (/ m cd))
   (integerp (/ (* n k) cd))
   (rel-prime m n))
  (= (/ k cd) (+ (* k (a m n) (/ m cd) ) (* (b m n) (/ (* n k) cd)))))
 :hints (("Goal" :use ( ck8 ck7)))
 :rule-classes nil)


(defthm integer-div-of-factor-due
 (implies
  (and
   (natp m)
   (natp n)
   (natp k)
   (posp cd)
   (integerp (/ m cd))
   (integerp (/ (* n k) cd))
   (rel-prime m n))
  (integerp (/ k cd)))
 :hints (("Goal" :in-theory nil :use ( ck8 ck9)))
 :rule-classes nil)



(defthm gcd-divides-both
 (implies
  (and
   (natp x)
   (posp y))
  (and
   (integerp (/ x (g-c-d x y)))
   (integerp (/ y (g-c-d x y)))))
 :hints (("Goal" :in-theory (enable g-c-d))))


(defthm divboth1
  (implies
  (and
   (posp x)
   (posp y)
   (natp v)
   (rel-prime v x)
   (rel-prime v y))
  (and
   (integerp (/ v       (g-c-d v (* x y))))
   (integerp (/ (* x y) (g-c-d v (* x y))))))
   :hints (("Goal" :use  ((:instance gcd-divides-both (x v) (y (* x y)))))))


(defthm divboth2
  (implies
  (and
   (posp n)
   (posp k)
   (natp m)
   (rel-prime m n)
   (rel-prime m k))
  (and
   (integerp (/ m       (g-c-d m (* n k))))
   (integerp (/ k       (g-c-d m (* n k))))))
   :hints (("Goal" :use  (
			  (:instance g-c-d (x m) (y (* n k)))
			  (:instance Nonneg-int-gcd->-0 (n m) (d (* n k)))
			  (:instance divboth1 (v m) (x n) (y k))
			  (:instance integer-div-of-factor-due (cd (g-c-d m (* n k))))))))


(defthm prime-of-product
   (implies
  (and
   (posp n)
   (posp k)
   (natp m)
   (rel-prime m n)
   (rel-prime m k))
  (rel-prime m (* n k)))
   :hints (("Goal" :in-theory (enable rel-prime)
	   :use ( divboth2
		  (:instance g-c-d (x m) (y (* n k)))
		  (:instance Nonneg-int-gcd->-0 (n m) (d (* n k)))
		  (:instance only-divisor-of-coprimes-is-1
			     (z (g-c-d m (* n k)))
			     (x m)
			     (y k))))))




(defun divided-by-all (k m)
  (if (endp m)
      t
    (and
     (integerp (/ k (car m)))
     (divided-by-all k (cdr m)))))


(in-theory (enable prod rel-prime rel-prime-moduli))

(defthm helper
 (implies
  (and
   (not (endp m))
   (posp-all m))
  (and
    (posp-all (cdr m))
    (posp (car m))
    (posp (prod m))
    (posp (prod (cdr m)))))
 :rule-classes nil)

(defthm helper2
 (implies
  (and
   (not (endp m))
   (rel-prime-all el m))
  (and
   (rel-prime el (car m))
   (rel-prime-all el (cdr m))))
 :hints (("Goal" :use (:instance rel-prime-all (x el) (l m))))
 :rule-classes nil)


(defthm rel-prime-of-product
 (implies
   (and
   (posp-all m)
   (natp el)
   (rel-prime-all el m))
   (rel-prime el (prod m)))
 :hints ( ("Goal" :in-theory (disable rel-prime natp) :induct (len m))
	  ("Subgoal *1/2''" :use ( (:instance rel-prime (x el) (y 1))
				   (:instance g-c-d (x el) (y 1))
				   (:instance Nonneg-int-gcd-1-right (x el))))
	  ("Subgoal *1/1'" :use
	   (helper
	    helper2
	    (:instance prod (l m))
	    (:instance prime-of-product (n (car m)) (k (prod (cdr m))) (m el))))))


(defthm helper3
 (implies
  (and
   (not (endp m))
   (rel-prime-moduli m))
  (and
   (rel-prime-moduli (cdr m))
   (posp-all (cdr m))
   (natp (car m))
   (< 0 (car m)))))



(defthm diff-prod-means-cong-all-mod-list-inv-00
  (implies
   (and
    (rel-prime-moduli m)
    (integerp v)
    (divided-by-all v m))
  (integerp (/ v (prod m))))
 :hints (("Goal" :induct (len m))
	 ("Subgoal *1/1"
	  :in-theory '((:definition posp) (:definition natp))
	  :use
	  (
           helper
           helper3
	   (:instance natp-all (l m))
	   (:instance posp-all (l m))
	   (:instance prod (l m))
	   (:instance rel-prime-moduli (l m))
	   (:instance divided-by-all (k v))
	   (:instance rel-prime-of-product (el (car m)) (m (cdr m)))
	   (:instance divides-both (x (car m)) (y (prod (cdr m))))))))





(in-theory
 (union-theories (current-theory 'ground-zero)
		 '((:definition prod)
		   (:definition natp)
		   (:definition natp-all)
		   (:definition congruent)
		   (:definition congruent-all)
		   (:definition posp)
		   (:executable-counterpart prod)
		   (:type-prescription prod)
		   (:induction prod)
		   (:executable-counterpart posp)
		   (:type-prescription posp)
		   (:definition posp-all)
		   (:executable-counterpart posp-all)
		   (:type-prescription posp-all)
		   (:induction posp-all)
		   (:definition divided-by-all)
		   (:executable-counterpart divided-by-all)
		   (:type-prescription divided-by-all)
		   (:induction divided-by-all) )))


(include-book "../../../../arithmetic/top-with-meta")

(include-book "Minimal-Mod-Lemmas")

(in-theory (disable mod-x-y-=-x-exp))

(in-theory (disable mod))

(defthm r-mod-mod
  (implies
   (and
    (integerp x)
    (integerp z)
    (integerp i)
    (> i 0)
    (> z 0))
   (equal (mod (mod x (* i z)) z)
	  (mod x z)))
  :hints (("Goal" :use (:instance rewrite-mod-mod-exp (y (* i z))))))

(defthm r-mod-mod-cancel
 (implies
   (and
    (integerp x)
    (integerp z)
    (> z 0))
   (equal (mod (mod x z) z) (mod x z))))





(defun posp-all (l)
  (if (endp l)
      t
    (and (posp (car l))
	 (posp-all (cdr l)))))



(defun divided-by-all (k m)
  (if (endp m)
      t
    (and
     (integerp (/ k (car m)))
     (divided-by-all k (cdr m)))))




(defthm product-divided-by-all
 (implies
  (posp-all m)
  (divided-by-all (prod m) m))
 :hints (("Subgoal *1/1.2''"
	  :induct t)
	 ("Goal"
	  :in-theory (disable commutativity-of-*)
	  :induct (len m))))



(defthm prod-is-pos
 (implies
  (posp-all m)
  (posp (prod m))))

(defun congruent-mod (x y m)
  (= (mod x m) (mod y m)))


(defun congruent-all-mod (x a m)
  (declare (xargs :measure (len m)))
  (if (endp m)
      t
    (and (congruent-mod x (car a) (car m))
	 (congruent-all-mod x (cdr a) (cdr m)))))

(defthm any-number-which-divided-by-all-has-same-congruence
 (implies
  (and
   (equal (len y) (len m))
   (integerp x)
   (posp k)
   (posp-all m)
   (divided-by-all k m))
  (equal
   (congruent-all-mod (mod x k) y m)
   (congruent-all-mod x y m))))


(defthm modulo-prod-has-same-congruence
 (implies
  (and
   (equal (len y) (len m))
   (integerp x)
   (posp-all m))
  (equal
   (congruent-all-mod (mod x (prod m)) y m)
   (congruent-all-mod x y m))))




(defthm nonint-equ-modneg-2
  (implies
   (and
    (integerp x)
    (integerp y)
    (not (integerp (/ x y))))
   (equal (mod (- x) y) (- y (mod x y))))
  :hints (("Goal" :in-theory (enable mod)))
  :rule-classes nil)

(defthm int-equ-modneg
  (implies
   (and
    (integerp x)
    (integerp y)
    (not (equal y 0))
    (integerp (/ x y)))
   (and
    (equal (mod x y) 0)
    (equal (mod (- x) y) 0)))
  :rule-classes nil)





(defthm mod--nin
  (implies
   (and (integerp x)
	(integerp y)
	(integerp z)
	(not (integerp (/ y z)))
	(not (equal z 0)))
   (equal (mod (- x y) z)
	  (mod (- (mod x z) (mod y z)) z)))
  :hints (("Goal"
	 :use (
		 (:instance mod-+-exp (y (- y)))
		 (:instance nonint-equ-modneg-2 (x y) (y z))
		 (:instance cancel-mod-+-exp
			    (i (/ z z))
			    (x z)
			    (y (- (mod x z) (mod y z))))
		 (:instance integerp-mod-exp (i x) (j z))
		 (:instance integerp-mod-exp (i y) (j z)) )
	 :in-theory '(
		      (:rewrite inverse-of-*)
		      (:rewrite associativity-of-+)
		      (:rewrite commutativity-of-+))))
  :rule-classes nil)


(defthm mod--in
  (implies
   (and (integerp x)
	(integerp y)
	(integerp z)
	(integerp (/ y z))
	(not (equal z 0)))
   (equal (mod (- x y) z)
	  (mod (- (mod x z) (mod y z)) z)))
  :hints (("Goal" :in-theory (enable mod)))
  :rule-classes nil)

(defthm mod--
  (implies
   (and (force (integerp x))
	(force (integerp y))
	(force (integerp z))
	(force (not (equal z 0))))
   (equal (mod (- x y) z)
	  (mod (- (mod x z) (mod y z)) z)))
  :hints (("Goal" :use (mod--nin mod--in))))

;;; new stuff

#|

(defthm mod-of-0-is-0
 (implies
  (and
   (integerp m)
   (not (equal m 0)))
  (= (mod 0 m) 0))
 :rule-classes nil)


(defthm int-as-int2-+-diff-times-k2
 (implies
  (and
   (integerp a)
   (integerp b1)
   (integerp b2)
   (integerp m)
   (not (equal m 0)))
  (= (* a b1) (+ (* a b2) (* a (/ (- b1 b2) m) m))))
 :rule-classes nil)


(defthm integerp-k-dividing
 (implies
  (and
   (= (- (mod b1 m) (mod b2 m)) 0)
   (integerp b1)
   (integerp b2)
   (integerp m)
   (not (equal m 0)))
  (integerp (/ (- b1 b2) m)))
 :hints (("Goal" :in-theory nil
	  :use (mod-of-0-is-0
		       (:instance mod-=-0-exp (x (- b1 b2)) (y m))
		       (:instance mod-- (x b1) (y b2) (z m)))))
 :rule-classes nil)

(defthm integerp-k-dividing2
 (implies
  (and
   (= (- (mod b1 m) (mod b2 m)) 0)
   (integerp a)
   (integerp b1)
   (integerp b2)
   (integerp m)
   (not (equal m 0)))
  (integerp (* a (/ (- b1 b2) m))))
 :hints (("Goal" :in-theory nil :use integerp-k-dividing))
 :rule-classes nil)


(defthm congruence-holds-on-product
 (implies
  (and
   (= (mod b1 m) (mod b2 m))
   (integerp a)
   (integerp b1)
   (integerp b2)
   (integerp m)
   (not (equal m 0)))
  (equal (mod (* a b1) m) (mod (* a b2) m)))
 :hints (("Goal"
	  :use
	  (integerp-k-dividing2
	   int-as-int2-+-diff-times-k2
	   (:instance mod-x+i*y-y-exp (x (* a b2)) (y m) (i (* a (/ (- b1 b2) m))))))))

(thm
 (implies
  (and
   (integerp a)
   (integerp b)
   (integerp m)
   (not (equal m 0)))
  (= (mod (mod b m) m) (mod b m)))
 :hints (("Goal"
	  :use
	  ( (:instance fix (x m))
	    (:instance r-mod-mod (x b) (i 1) (z m))))))

(defthm congruence-holds-on-product-i
 (implies
  (and
   (integerp a)
   (integerp b)
   (posp m))    ;;; per rilassare questo in m <> 0 va rilassato rewrite-mod-mod-exp, e quindi r-mod-mod
  (equal (mod (* a (mod b m)) m) (mod (* a b) m)))
 :hints (("Goal"
	  :use
	  (
	    (:instance r-mod-mod (x b) (i 1) (z m))
	    (:instance congruence-holds-on-product (b1 (mod b m)) (b2 b))))))



(defun times (a b)
  (if (zp b)
      0
    (+ a (times a (1- b)))))

(defthm times-is-*
 (implies
  (and
   (integerp a)
   (natp b))
   (= (times a b) (* a b)))
 :rule-classes nil)

(defun times2 (a b)
  (if (< 0 b)
      (times a (- b))
    (times a b)))

(defthm openup-times
 (implies
  (not (zp y))
  (equal (times x y) (+ (times x (1- y)) x)))
 :rule-classes nil)



(thm
 (IMPLIES
  (AND
   (integerp y)
   (integerp z)
   (posp z)) ;;; see before
   (equal (mod (times (mod x z) (mod y z)) z)
	  (mod (times (mod x z) (mod (+ (mod (1- y) z) (mod 1 z)) z)) z)))
 :hints (("Subgoal 2" :in-theory '((:definition posp)))
	 ("Goal" :use (
		       (:theorem (implies (integerp y) (equal y (+ (1- y) 1))))
		       (:instance mod-+-exp (x (1- y)) (y 1) (z z))))))



(defthm h1
 (implies
  (and
   (integerp x)
   (posp z))
  (natp (mod x z)))
 :rule-classes nil)


(defthm h2
 (IMPLIES
  (AND
   (integerp x)
   (integerp y)
   (integerp z)
   (posp z)) ;;; see before
(and
   (integerp (mod x z))
   (INTEGERP (+ (MOD (+ -1 Y) Z) (MOD 1 Z)))
   (natp (mod (+ (mod (1- y) z) (mod 1 z)) z))))
:hints (("Goal" :in-theory '((:definition posp) (:definition natp) )
	 :use ( h1
		 (:instance h1 (x (1- y)))
		 (:instance h1 (x 1))
		 (:instance h1 (x (+ (mod (1- y) z) (mod 1 z)))))))
:rule-classes nil)

(defthm h3
 (IMPLIES
  (AND
   (integerp x)
   (integerp y)
   (integerp z)
   (posp z)) ;;; see before
  (equal
   (mod (times (mod x z) (mod (+ (mod (1- y) z) (mod 1 z)) z)) z)
   (mod (* (mod x z) (+ (mod (1- y) z) (mod 1 z)) ) z)))
  :hints (("Goal"
	   :in-theory '((:definition natp) (:definition posp))
	   :use
	   ( h2
	     (:instance times-is-* (b (mod (+ (mod (1- y) z) (mod 1 z)) z)) (a (mod x z)))
	     (:instance congruence-holds-on-product-i (b (+ (mod (1- y) z) (mod 1 z))) (a (mod x z)) (m z)))))
  :rule-classes nil)


(defthm mod-of-1-is-1
 (implies
  (and
   (integerp z)
   (> z 1))
  (equal (mod 1 z) 1))
 :hints (("Goal" :use (:instance mod-x-y-=-x-exp (x 1) (y z))))
 :rule-classes nil)

(defthm sss1
  (implies
   (integerp x)
   (equal (* x 1) x))
  :rule-classes nil)

(defthm h5->1
 (IMPLIES
  (AND
   (integerp x)
   (integerp y)
   (integerp z)
   (> z 1))
   (equal (mod (times (mod x z) (mod y z)) z)
	  (mod (+ (* (mod x z) (mod (1- y) z)) (mod x z) ) z)))
 :hints (("Subgoal 2" :in-theory '((:definition posp)
				   (:rewrite distributivity)
				   (:rewrite commutativity-of-*)
				   (:rewrite unicity-of-1)))
	  ("Goal" :use ( mod-of-1-is-1
			 h3
			 h2
			 (:instance sss1 (x (mod x z)))
			 (:theorem (implies (integerp y) (equal y (+ (1- y) 1))))
			 (:instance mod-+-exp (x (1- y)) (y 1) (z z))))))


(defthm h5-=1
 (IMPLIES
  (AND
   (integerp x)
   (integerp y)
   (integerp z)
   (= z 1))
   (equal (mod (times (mod x z) (mod y z)) z)
	  (mod (+ (* (mod x z) (mod (1- y) z)) (mod x z) ) z))))


(defthm h5->=1
 (IMPLIES
  (AND
   (integerp x)
   (integerp y)
   (posp z))
   (equal (mod (times (mod x z) (mod y z)) z)
	  (mod (+ (* (mod x z) (mod (1- y) z)) (mod x z) ) z)))
 :hints (("Goal" :in-theory '((:definition posp)) :use (h5-=1 h5->1))))


(defthm h6
 (implies
  (and
   (integerp a)
   (integerp b)
   (posp m))
  (equal (mod (+ a b) m)
	 (mod (+ (mod a m) b) m)))
  :hints (("Goal"
	   :in-theory '((:definition fix)
			(:rewrite unicity-of-1)
			(:definition posp))
	   :use
	  ( (:instance integerp-mod-exp (i a) (j m))
	    (:instance mod-+-exp (x (mod a m)) (y b) (z m))
	    (:instance mod-+-exp (x a) (y b) (z m))
	    (:instance r-mod-mod (x a) (i 1) (z m)))))
  :rule-classes nil)



;;; here now.

(defthm h7
 (IMPLIES
  (AND
   (NOT (ZP Y))
   (EQUAL (MOD (TIMES X (+ -1 Y)) Z)
	  (MOD (TIMES (MOD X Z) (MOD (+ -1 Y) Z)) Z))
   (integerp x)
   (integerp y) (INTEGERP (* (MOD X Z) (MOD (+ -1 Y) Z)))
   (posp z))
   (equal (mod (times (mod x z) (mod y z)) z)
	  (mod (+ (mod (* (mod x z) (mod (1- y) z)) z) (mod x z) ) z)))
 :hints (("Goal"
	  :in-theory nil
	  :use
	  (h5->=1
	   h2
	   ;h3
	  (:instance h6
		     (a (* (mod x z) (mod (1- y) z)))
		     (b (mod x z))
		     (m z))))))



(thm
 (IMPLIES
  (AND
   (NOT (ZP Y))
   (EQUAL (MOD (TIMES X (+ -1 Y)) Z)
	  (MOD (TIMES (MOD X Z) (MOD (+ -1 Y) Z)) Z))
   (equal (mod (times x y) z) (mod (times (mod x z) (mod y z)) z))))

(thm
 (implies
  (and
   (integerp x)
   (integerp y)
   (integerp z)
   (not (equal z 0)))
  (equal (mod (times x y) z) (mod (times (mod x z) (mod y z)) z)))
 :hints (("Subgoal *1/3" :use
	  ( openup-times
	    (:instance mod-+-exp (x (times x (1- y))) (y x) (z z))

;;; end new stuff

|#

(defun congruent-all-mod-list (l1 l2 m)
  (declare (xargs :measure (len m)))
  (if (endp m)
      t
    (and
     (congruent-mod (car l1) (car l2) (car m))
     (congruent-all-mod-list (cdr l1) (cdr l2) (cdr m)))))

(defthm cong-all-mod-implies-cong-all-mod-list
 (implies
  (and
   (congruent-all-mod v1 l1 m)
   (congruent-all-mod v1 l2 m))
  (congruent-all-mod-list l1 l2 m)))


(defthm rel-prime-is-pos
 (implies
  (rel-prime-moduli m)
  (and
   (posp-all m)
   (posp (prod m))))
 :hints (("Goal" :in-theory (enable rel-prime-moduli)))
 :rule-classes :forward-chaining)


(defthm s-sily
 (implies
  (integerp (/ a b))
  (integerp (/ (- a) b)))
 :rule-classes nil)


(defthm axp1
  (implies
   (and
    (integerp v1)
    (integerp v2)
    (posp (prod m))
    (integerp (/ (- v1 v2) (prod m))))
   (and
    (integerp (/ (- v2 v1) (prod m)))
    (equal  v2 (+ v1 (* (/ (- v2 v1) (prod m)) (prod m))))))
  :hints (("Goal" :use (:instance s-sily (a (- v1 v2)) (b (prod m)))))
  :rule-classes nil)


(defthm diff-prod-means-cong-all-mod-list
  (implies
   (and
    (rel-prime-moduli m)
    (integerp v1)
    (integerp v2)
    (natp-all l1)
    (natp-all l2)
    (equal (len l1) (len m))
    (equal (len l2) (len m))
    (congruent-all-mod v1 l1 m)
    (congruent-all-mod v2 l2 m)
    (integerp (/ (- v1 v2) (prod m))))
   (congruent-all-mod-list l1 l2 m))
  :hints (("Goal"
	   :in-theory '((:definition posp)
			(:rewrite unicity-of-1))
	   :use
	   ( axp1
	     rel-prime-is-pos
	     cong-all-mod-implies-cong-all-mod-list
	     (:instance mod-x+i*y-y-exp (i (/ (- v2 v1) (prod m))) (x v1) (y (prod m)))
	     (:instance r-mod-mod (x v1) (i 1) (z (prod m)))
	     (:instance modulo-prod-has-same-congruence (x v1) (y l2))
	     (:instance modulo-prod-has-same-congruence (x v2) (y l2))))))


(defthm same-congruence-over-conglist
 (implies
  (congruent-all-mod-list l1 l2 m)
 (equal
    (congruent-all-mod v l1 m)
    (congruent-all-mod v l2 m)))
 :rule-classes nil)

(defun cong-sg-val (v1 v2 m)
  (if
      (endp m)
      t
    (and
     (congruent-mod v1 v2 (car m))
     (cong-sg-val   v1 v2 (cdr m)))))


(defthm same-cong-lists-means-same-mods
 (implies
  (and
   (equal (len l) (len m))
   (congruent-all-mod v1 l m)
   (congruent-all-mod v2 l m))
  (cong-sg-val v1 v2 m)))

(defthm mod-of-0
 (implies (posp carm) (equal (mod 0 carm) 0))
 :rule-classes nil)


(defthm same-cong-vals-implies-diff-has-cong-to-zero
 (implies
  (and
   (posp-all m)
   (integerp v1)
   (integerp v2))
   (implies
    (cong-sg-val v1 v2 m)
    (cong-sg-val (- v1 v2) 0 m)))
 :hints (("Goal"
	  :in-theory (disable mod-=-0-exp mod-- mod-+-exp cancel-mod-+-exp rewrite-mod-mod-exp r-mod-mod-cancel integerp-mod-exp)
	  :induct (len m))
	 ("Subgoal *1/1" :use  (
				(:instance mod-of-0 (carm (car m)))
				(:instance mod-- (x v1) (y v2) (z (car m)))))))


(defthm cong-0-is-divided-by-all
 (implies
  (and
   (integerp v)
   (posp-all m))
  (equal (cong-sg-val v 0 m) (divided-by-all v m)))
 :hints (("Goal" :induct (len m))
	 ("Subgoal *1/1" :use ((:instance mod-of-0 (carm (car m)))
			       (:instance mod-=-0-exp (x v) (y (car m))))
                         :in-theory (disable MOD-=-0-EXP)))
 :rule-classes nil)




(in-theory (enable diff-prod-means-cong-all-mod-list-inv-00))




(defthm diff-prod-means-cong-all-mod-list-inv
  (implies
   (and
    (rel-prime-moduli m)
    (integerp v1)
    (integerp v2)
    (natp-all l1)
    (natp-all l2)
    (equal (len l1) (len m))
    (equal (len l2) (len m))
    (congruent-all-mod v1 l1 m)
    (congruent-all-mod v2 l2 m)
    (congruent-all-mod-list l1 l2 m))
  (integerp (/ (- v1 v2) (prod m))))
  :hints (("Goal" :use ( rel-prime-is-pos
			 (:instance cong-0-is-divided-by-all (v (- v1 v2)))
			 (:instance same-congruence-over-conglist (v v2))
			 (:instance same-cong-vals-implies-diff-has-cong-to-zero (v1 v1) (v2 v2))
			 (:instance diff-prod-means-cong-all-mod-list-inv-00 (v (- v1 v2)))))))



(defthm myax
  (implies
   (and
    (rel-prime-moduli m)
    (integerp v1)
    (integerp v2)
    (natp-all l1)
    (natp-all l2)
    (equal (len l1) (len m))
    (equal (len l2) (len m))
    (congruent-all-mod v1 l1 m)
    (congruent-all-mod v2 l2 m))
   (equal
    (congruent-all-mod-list l1 l2 m)
    (integerp (/ (- v1 v2) (prod m)))))
  :hints (("Goal" :use (diff-prod-means-cong-all-mod-list
			diff-prod-means-cong-all-mod-list-inv))))


(defthm sil1
 (implies
  (and
   (integerp a)
   (posp b)
   (integerp (/ a b)))
  (equal a (* (/ a b) b)))
 :rule-classes nil)

(defthm casesofresdiv
 (implies
  (and
   (posp prod)
   (integerp resdiv))
  (and
   (implies (equal resdiv 0) (equal (* resdiv prod) 0))
   (implies (< resdiv 0)     (<     (* resdiv prod) 0))
   (implies (> resdiv 0)     (>=    (* resdiv prod) prod)))))


(defthm a-number-in-arange-is-0-if-no-rest
 (implies
  (and
    (natp v)
    (posp prod)
    (< v prod)
    (integerp (/ v prod)))
  (equal v 0))
 :hints (("Goal" :use (:instance sil1 (a v) (b prod)))
	 ("Goal''" :use (:instance casesofresdiv (resdiv (/ v prod)))))
 :rule-classes nil)


(defthm equality-in-range-1
 (implies
  (and
    (posp prod)
    (natp v1)
    (natp v2)
    (< v1 prod)
    (< v2 prod)
    (integerp (/ (abs (- v1 v2)) prod)))
  (equal v1 v2))
 :hints (("Goal" :use (:instance a-number-in-arange-is-0-if-no-rest
				 (v (abs (- v1 v2))))))
 :rule-classes nil)


(defthm sil2
  (iff (integerp (/ (abs a) b)) (integerp (/ a b)))
  :rule-classes nil)

(defthm equality-in-range-2
 (implies
  (and
    (posp prod)
    (natp v1)
    (natp v2)
    (< v1 prod)
    (< v2 prod)
    (integerp (/ (- v1 v2) prod)))
  (equal v1 v2))
 :hints (("Goal" :use (equality-in-range-1
		       (:instance sil2 (a (- v1 v2)) (b prod)))))
 :rule-classes nil)


(defthm unique-inversion
  (implies
   (and
    (rel-prime-moduli m)
    (natp v1)
    (natp v2)
    (< v1 (prod m))
    (< v2 (prod m))
    (natp-all l)
    (equal (len l) (len m))
    (congruent-all-mod v1 l m)
    (congruent-all-mod v2 l m))
   (equal v1 v2))
  :hints (("Goal" :use
	   ( (:instance myax (l1 l) (l2 l))
	     (:instance equality-in-range-2 (prod (prod m))))))
  :rule-classes nil)

(defun build-values-by-rns (gem-value rns)
 (if (endp rns)
     nil
     (cons (mod gem-value (car rns))
           (build-values-by-rns gem-value (cdr rns)))))


(defthm values-built-by-rns-are-congruent-indeed
 (implies
  (and
   (integerp val)
   (posp-all m))
  (congruent-all-mod val (build-values-by-rns val m) m)))


(defthm congruent-all-same-with-mod
 (implies
  (and
   (natp-all l)
   (posp-all m)
   (natp x))
  (equal
   (congruent-all x l m)
   (congruent-all-mod x l m)))
 :hints (("Goal" :in-theory (enable mod rem)))
 :rule-classes nil)

(defun crtmod (a m)
  (mod (crt a m) (prod m)))


(defthm sils2
 (implies
  (and
   (posp (prod m))
   (natp (crt a m)))
  (< (crtmod a m) (prod m))))

(defthm sils1
 (implies
  (and
   (posp m)
   (natp a))
  (natp (mod a m)))
 :hints (("Goal" :in-theory '((:rewrite integerp-mod-exp)
			      (:definition natp)
			      (:definition posp))
	  :use ( (:instance mod-type-exp (x a) (y m))
			(:instance mod-=-0-exp  (x a) (y m))))))



(defthm chinese-remainder-2
 (implies
  (and
   (natp-all a)
   (rel-prime-moduli m)
   (= (len a) (len m)))
  (and
   (natp (crtmod a m))
   (< (crtmod a m) (prod m))
   (congruent-all-mod (crtmod a m) a m)))
 :hints (("Goal" :use
	  ( (:instance chinese-remainder-theorem (values a) (rns m))
	    sils2
	    (:instance congruent-all-same-with-mod
		       (l a)
		       (x (crt a m)))
	    (:instance modulo-prod-has-same-congruence
		       (y a)
		       (x (crt a m)))))))


(defthm lemma-x
 (implies
  (and
   (natp val)
   (rel-prime-moduli m))
  (and
   (natp-all (build-values-by-rns val m))
   (= (len (build-values-by-rns val m)) (len m))))
 :hints (("Goal" :in-theory (enable rel-prime-moduli))))


(defthm crt-inversion
 (implies
  (and
   (rel-prime-moduli rns)
   (natp val)
   (< val (prod rns)))
  (equal (crtmod (build-values-by-rns val rns) rns) val))
 :hints (("Goal"
	  :use ( (:instance chinese-remainder-2 (a (build-values-by-rns val rns)) (m rns))
		 (:instance lemma-x (m rns))
		 (:instance values-built-by-rns-are-congruent-indeed (m rns))
		 (:instance unique-inversion
                            (m rns)
			    (v1 val)
			    (v2 (crtmod (build-values-by-rns val rns) rns))
			    (l  (build-values-by-rns val rns)))))))







;;;;;;;;;; Corollaries for inversion
;;;;; They are further developed/used in Proof-Of-Plus and Proof-Of-Minus


(defthm any-number-which-divides-makes-same-residues
 (implies
  (and
   (integerp x)
   (posp k)
   (posp-all m)
   (divided-by-all k m))
  (equal
   (build-values-by-rns (mod x k) m)
   (build-values-by-rns x m))))

(defthm mod-prod-makes-same-residues
 (implies
  (and
   (integerp x)
   (posp-all m))
  (equal
   (build-values-by-rns (mod x (prod m)) m)
   (build-values-by-rns x m))))


