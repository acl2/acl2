(in-package "ACL2")
; cert_param: (uses-acl2r)
(include-book "nonstd/nsa/ln" :dir :system)
(include-book "arithmetic/top" :dir :system)
(include-book "arithmetic/realp" :dir :system)
(include-book "nonstd/nsa/exp" :dir :system)
(include-book "nonstd/nsa/raise" :dir :system)

#|
Claim: For all eps > 0, there exists some d > 0 such that
       N > d -> a^N < eps.

Proof:
    Let d = ln(eps)/ln(a)
    N > d -> N > ln(eps)/ln(a)
    Claim ln(eps) < 0
    Claim ln(a) < 0
    -> N log(a) < log(eps)
    -> log(a^N) < log(eps)
    -> e^log(a^N) < e^log(eps)
    -> a^N < eps
    QED
|#
(defun d (eps a) (/ (acl2-ln eps) (acl2-ln a)))

#|
Claim: Suppose x^y < x.  Then y < 0.
|#
(defthm e^y<1->y<0
  (implies (and (realp y)
		(< (acl2-exp y) 1))
	   (< y 0)))

#|
Claim: 0 < x < 1 -> ln(x) < 0

Proof:
    Suppose 0 < x < 1.
    e^ln(x) = x.
    So 0 < e^ln(x) < 1.
    By { e^y<1->y<0 with y=ln(x) }, ln(x) < 0.
|#
(defthm ln-<
  (implies (and (realp x)
		(< x 1)
		(< 0 x))
	   (< (acl2-ln x) 0)))

#|
Claim: c < 0 and a < b -> b(c) < a(c)
|#
(defthm <-flips 
  (implies (and (realp a)
		(realp b)
		(realp c)
		(< a b)
		(< c 0))
	   (< (* b c) (* a c))))

(defthm a/x*x=a
  (implies (and (realp a) (realp x) (not (equal x 0)))
	   (equal (* (/ a x) x) a)))

#|
To use a/x*x=1 on ln(eps)/ln(a) * ln(a), we need to prove ln(a) ~= 0.
Obviously this follows from { ln-< with x=a }.
|#
(defthm a<1->lna~=0
  (implies (and (realp a)
		(< 0 a)
		(< a 1))
	   (not (equal (acl2-ln a) 0))))

#|
0 < a < 1 -> ln(eps)/ln(a) * ln(a) = ln(eps)
|#
(defthm simplify-lneps/lna*lna
  (implies (and (realp eps)
		(realp a)
		(< 0 a)
		(< a 1))
	   (equal (* (/ (acl2-ln eps) (acl2-ln a)) (acl2-ln a))
		  (acl2-ln eps))))


#|
Claim: Let 0 < eps, a < 1.
       Let N > ln(eps)/ln(a).
       Then N ln(a) < ln(eps).

Proof:
    ln(eps) < 0 by { ln-< with x=eps }
    ln(a) < 0 by { ln-< with x=a }
    N ln(a) < ln(a) ln(eps) / ln(a) by 
        { <-flips with a=N, b=ln(eps)/ln(a), c=ln(a) }
|#
(defthm 0<eps-a<1^N>lneps/lna->Nlna<lneps
  (implies (and (realp eps)
		(realp a)
		(< 0 eps)
		(< 0 a)
		(< eps 1)
		(< a 1)
		(natp N)
		(< (d eps a) N))
	   (< (* (acl2-ln a) N) (acl2-ln eps)))
  :hints (("Goal" :use (:instance <-flips
				  (a (d eps a))
				  (b N)
				  (c (acl2-ln a))))))

(defthm x<y->e^x<e^y
  (implies (and (realp x)
		(realp y)
		(< x y))
	   (< (acl2-exp x) (acl2-exp y))))

#|
Claim: Let 0 < eps, a < 1.
       Let N > ln(eps)/ln(a).
       Then e^{N ln(a)} < e^{ln(eps)} = eps
|#
(defthm 0<eps-a<1^N>lneps/lna->exp-Nlna<eps
  (implies (and (realp eps)
		(realp a)
		(< 0 eps)
		(< 0 a)
		(< eps 1)
		(< a 1)
		(natp N)
		(< (d eps a) N))
	   (< (acl2-exp (* (acl2-ln a) N))
	      eps))
  :hints (("Goal" :use ((:instance x<y->e^x<e^y
				   (x (* (acl2-ln a) N))
				   (y (acl2-ln eps)))
			(:instance 0<eps-a<1^N>lneps/lna->Nlna<lneps
				   (eps eps)
				   (a a)
				   (N N))))))

;; ln(a^N) = ln(raise a N) = ln(e^{N ln(a)})
(defthm simplify-inner-raise-lem1
  (implies (and (realp a)
		(realp N)
		(< 0 N)
		(< 0 a))
	   (equal (acl2-ln (raise a N))
		  (acl2-ln (acl2-exp (* N (acl2-ln a)))))))

(defthm real-has-no-imagpart
  (implies (realp x) (equal (imagpart x) 0)))

(defthm nat-has-no-imagpart
  (implies (natp N) (equal (imagpart N) 0)))

(defthm simplify-inner-raise-lem2
  (implies (and (realp a)
		(realp N)
		(< 0 N)
		(< 0 a)
		(< a 1))
	   (and (acl2-numberp (* N (acl2-ln a)))
                (<= 0 (imagpart (* N (acl2-ln a))))
                (< (imagpart (* N (acl2-ln a))) (* 2 (acl2-pi))))))

#|
Claim: N ln(a) = ln(a^N)
Proof:
    ln(a^N) = ln(raise a N)
            = ln(e^{N ln(a)})
            = N ln(a)
|#
(defthm simplify-inner-raise-lem3
  (implies (and (realp a)
		(realp N)
		(< 0 N)
		(< 0 a))
	   (equal (acl2-ln (acl2-exp (* N (acl2-ln a))))
		  (* N (acl2-ln a))))
  :hints (("Goal" :use (:instance ln-exp (x (* N (acl2-ln a)))))))

;; e^{N ln(a)} = a^N
(defthm e^Nlna=a^N
  (implies (and (realp a)
		(realp N)
		(< 0 N)
		(< 0 a))
	   (equal (acl2-exp (* N (acl2-ln a)))
		  (raise a N))))

(defthm a^n->0
  (implies (and (realp eps)
		(realp a)
		(< 0 eps)
		(< 0 a)
		(< eps 1)
		(< a 1)
		(natp N)
		(< (d eps a) N))
	   (< (raise a N)
	      eps))
  :hints (("Goal" :use ((:instance e^Nlna=a^N (a a) (N N))
			(:instance 0<eps-a<1^N>lneps/lna->exp-Nlna<eps
				   (a a)
				   (N N)
				   (eps eps))))))

(defun-sk lim-0 (a e n)
  (exists (d)
    (implies (and (realp e)
		  (< 0 e)
		  (< d n))
	     (< (raise a n) e))))

(defthm lim-a^n->0
  (implies (and (realp a)
		(realp e)
		(< 0 e)
		(< 0 a)
		(< a 1)
		(natp n))
	   (lim-0 a e n))
    :INSTRUCTIONS
  (:PRO (:CASESPLIT (< E 1))
        (:USE (:INSTANCE A^N->0 (EPS E) (A A) (N N)))
        :PRO
        (:USE (:INSTANCE LIM-0-SUFF (D (D E A))))
        (:USE (:INSTANCE A^N->0 (EPS (/ E (* 2 E)))
                         (A A)
                         (N N)))
        :PRO
        (:CLAIM (AND (REALP (* E (/ (* 2 E))))
                     (REALP A)
                     (< 0 (* E (/ (* 2 E))))
                     (< 0 A)
                     (< (* E (/ (* 2 E))) 1)
                     (< A 1)
                     (NATP N)))
        (:CLAIM (IMPLIES (< (D (* E (/ (* 2 E))) A) N)
                         (< (RAISE A N) (* E (/ (* 2 E))))))
        (:DROP 1)
        (:USE (:INSTANCE LIM-0-SUFF (D (D (* E (/ (* 2 E))) A))))
        :PRO :PROVE))
