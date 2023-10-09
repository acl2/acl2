(in-package "ACL2S")
#|
This file contains a formal proof that if 0 <= a < 1 then lim n->inf a^n = 0.
The proof is only defined over the rationals but quite clearly applied equally to
irrationals.  This proof first appeared in "A Formal Analysis of Karn's Algorithm",
to appear in NETYS 2023, and is being further developed and elucidated in this project.
|#

#|
We begin with an important property of the ceiling function.  The important part here
is condition (ii), but we get two birds with one stone, since we also need the (rather
obvious) condition (i) for the next proof.

Thm: ceil(x) < ceil(y) -> 
     (i) x <= ceil(x) and
     (ii) ciel(x) < y.
|#

(property cx<cy->cx<y (x y :pos-rational)
  :h (< (ceiling x 1) (ceiling y 1))
  (^ (<= x (ceiling x 1))
     (< (ceiling x 1) y))
  :instructions (:pro (:claim (<= x (ceiling x 1)))
                      (:casesplit (<= y x))
                      (:claim (= x y))
                      :prove
                      (:claim (implies (<= y (ceiling x 1))
                                       (= (ceiling y 1) (ceiling x 1))))
                      :prove))

#|
Next we prove another important property of the ceiling function, showing how repeated
division inside a ceiling can be unfolded to repeated applications of ceiling-division.
This proof was adapted from: 
https://math.stackexchange.com/questions/233670/nested-division-in-the-ceiling-function

Thm: ceil(x/mn) = ceil(ceil(x/m)/n)
|#

(property ceiling-division-lemma (m n :pos x :pos-rational)
  (= (ceiling (/ x (* m n)) 1)
     (ceiling (/ (ceiling (/ x m) 1) n) 1))
  :instructions
  (:pro (:claim (< (- (ceiling (/ x m) 1) 1) (/ x m)))
        (:claim (<= (/ x m) (ceiling (/ x m) 1)))
        (:claim (< (/ (- (ceiling (/ x m) 1) 1) n)
                   (/ x (* m n))))
        (:claim (<= (/ x (* m n))
                    (/ (ceiling (/ x m) 1) n)))
        (:claim (<= (ceiling (/ x (* m n)) 1)
                    (ceiling (/ (ceiling (/ x m) 1) n) 1)))
        (:use (:instance cx<cy->cx<y
                         (x (* x (/ (* m n))))
                         (y (* (ceiling (* x (/ m)) 1) (/ n)))))
        :pro
        (:casesplit (< (ceiling (* x (/ (* m n))) 1)
                       (ceiling (* (ceiling (* x (/ m)) 1) (/ n))
                                1)))
        (:claim (^ (<= (* x (/ (* m n)))
                       (ceiling (* x (/ (* m n))) 1))
                   (< (ceiling (* x (/ (* m n))) 1)
                      (* (ceiling (* x (/ m)) 1) (/ n)))))
        (:drop 1)
        (:claim (<= (/ x m)
                    (* n (ceiling (* x (/ (* m n))) 1))))
        (:claim (< (* n (ceiling (* x (/ (* m n))) 1))
                   (ceiling (/ x m) 1)))
        :prove :prove))

#|
The following two properties are quite obvious yet, we need to formulate them
explicitly in order to guide the prover without it getting stuck in some kind of
loop, in subsequent proofs.
|#
(property divide-ineq (x y z :pos-rational)
  :h (^ (< 0 x) (<= y z))
  (<= (/ y x) (/ z x)))

(property multiply-ineq (x y z :pos-rational)
  :h (^ (< 0 x) (<= y z))
  (<= (* y x) (* z x)))

;; Claim: k a^k / k = a^k.
(property k*a^k/k=a^k (k :pos a :pos-rational)
  (= (/ (* k (expt a k)) k)
     (expt a k)))

(property div-lem-ind-step (k n :nat)
  :h (<= k n)
  (<= (/ k (1+ k))
      (/ n (1+ n))))

(property repl-mul-<= (a b x z :pos-rational)
  :h (^ (<= a b)
        (<= x (* a z)))
  (<= x (* b z)))

#|
Thm: 0 < b0 <= b1 -> a/b0 <= a/b1
(This is just a helper Lemma, because otherwise prover gets stuck in next proof.)
|#
(property div-<=-prop (a b0 b1 :pos-rational)
  (=> (<= b0 b1)
      (<= (/ a b1) (/ a b0))))

#|
Thm: The ceiling's codomain are the positive rationals.
(This is another helper Lemma for where otherwise the prover would get stuck.)
|#
(property pos-rationalp-ceil (x :pos-rational)
  (pos-rationalp (ceiling x 1)))

#|
Thm: x/ceiling(x/y) <= y.
This is a very important helper lemma that explains essentially how we can pull
the y out of the ceiling-wrapped denominator ...
|#
(property inequality-over-ceil-frac (x y :pos-rational)
  (<= (/ x (ceiling (/ x y) 1)) y)
  :instructions (:pro (:claim (<= (/ x y) (ceiling (/ x y) 1)))
                      (:claim (<= (/ (ceiling (/ x y) 1))
                                  (/ (/ x y))))
                      (:claim (<= (/ x (ceiling (/ x y) 1))
                                  (/ x (/ x y))))
                      :prove))

(definecd fn (a n :pos-rational) :pos-rational
  :ic (< a 1)
  (let ((k (ceiling (/ a (- 1 a)) 1)))
    (/ (* k (expt a k)) n)))

#|
Thm: a^{n+1} <= a * (k a^k / n) -> a^{n+1} <= k a^k / (1+n)
|#
(property incr-denom-lemma (n k :pos a :pos-rational)
  :h (^ (<= (expt a (+ 1 n))
            (* (* k (expt a k)) (/ n) a))
        (<= a (/ n (1+ n))))
  (<= (expt a (+ 1 n))
      (* k (expt a k) (/ (1+ n))))
  :instructions (:pro (:use (:instance repl-mul-<= (x (expt a (+ 1 n)))
                                       (a a)
                                       (b (* n (/ (+ 1 n))))
                                       (z (* k (expt a k) (/ n)))))
                      :pro
                      (:claim (<= (expt a (+ 1 n))
                                  (* (* n (/ (+ 1 n)))
                                     k (expt a k)
                                     (/ n))))
                      (:drop 1)
                      (:claim (= (* (* n (/ (+ 1 n))) k (expt a k) (/ n))
                                 (* (* (/ (+ 1 n))) k (expt a k))))
                      :prove))

#|
The remainder of this proof follows a proof sketch written by Ken McMillan (in 
unpublished correspondence, as part of the above-mentioned NETYS 2023 paper).
Note however that Ken's sketch skipped many intermediary steps and small details
which we naturally are forced (by the prover) to flush out in full detail here.
|#

(property step-1-kens-proof (a :pos-rational k :rational)
  :h (^ (< a 1)
        (= k (ceiling (/ a (- 1 a)) 1)))
  (<= a (/ k (1+ k)))
  :instructions (:pro (:claim (<= (/ a (- 1 a)) k))
                      (:use (:instance multiply-ineq (x (- 1 a))
                                       (y (* a (/ (+ 1 (- a)))))
                                       (z k)))
                      :pro
                      (:claim (<= (* (* a (/ (+ 1 (- a)))) (+ 1 (- a)))
                                  (* k (+ 1 (- a)))))
                      (:drop 1)
                      (:claim (<= a (* k (- 1 a))))
                      (:drop 5)
                      (:claim (= (* k (+ 1 (- a))) (- k (* k a))))
                      (:claim (<= a (+ k (- (* k a)))))
                      (:drop 5 6)
                      (:claim (<= (+ a (* k a)) k))
                      (:claim (= (+ a (* k a)) (* a (1+ k))))
                      (:claim (<= (* a (1+ k)) k))
                      (:use (:instance divide-ineq (x (1+ k))
                                       (y (* a (1+ k)))
                                       (z k)))
                      :pro
                      (:claim (<= (* (* a (+ 1 k)) (/ (+ 1 k)))
                                  (* k (/ (+ 1 k)))))
                      (:drop 1)
                      :prove))

(property base-case-kens-proof (a :pos-rational)
  :h (< a 1)
  (let ((k (ceiling (/ a (- 1 a)) 1)))
    (= (fn a k) (expt a k)))
  :instructions
  (:pro (:claim (posp (ceiling (* a (/ (+ 1 (- a)))) 1)))
        (:use (:instance k*a^k/k=a^k
                         (k (ceiling (* a (/ (+ 1 (- a)))) 1))
                         (a a)))
        :pro
        (:claim (= (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
                         (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
                      (/ (ceiling (* a (/ (+ 1 (- a)))) 1)))
                   (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))))
        (:drop 1)
        (:use (:instance fn-definition-rule (a a)
                         (n (ceiling (/ a (- 1 a)) 1))))
        :pro
        (:claim (= (fn a (ceiling (* a (/ (+ 1 (- a)))) 1))
                   (let ((k (ceiling (* a (/ (+ 1 (- a)))) 1))
                         (n (ceiling (* a (/ (+ 1 (- a)))) 1)))
                     (* (* k (expt a k)) (/ n)))))
        (:drop 1)
        (:claim (= (fn a (ceiling (* a (/ (+ 1 (- a)))) 1))
                   (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
                         (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
                      (/ (ceiling (* a (/ (+ 1 (- a)))) 1)))))
        (:claim (iff (let ((k (ceiling (* a (/ (+ 1 (- a)))) 1)))
                       (= (fn a k) (expt a k)))
                     (= (fn a (ceiling (* a (/ (+ 1 (- a)))) 1))
                        (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))))
        (:claim (= (fn a (ceiling (* a (/ (+ 1 (- a)))) 1))
                   (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))))
        :prove))

#|
Thm: [ a^n <= f_n(a, n) and ceil(a/(1-a)) <= n ] -> a^{1+n} <= f_n(a, 1+n)
|#
(property inductive-step-kens-proof (a :pos-rational k fnk :rational n :nat)
  :h  (^ (< a 1)
         (= k (ceiling (/ a (- 1 a)) 1))
         (<= k n)
         (= fnk (fn a n))
         (<= (expt a n) fnk))
  (<= (expt a (1+ n)) (fn a (1+ n)))
  :instructions
  (:pro (:use (:instance step-1-kens-proof (a a)))
        :pro (:claim (<= a (* k (/ (+ 1 k)))))
        (:drop 1)
        (:use (:instance div-lem-ind-step (k k)
                         (n n)))
        :pro
        (:claim (<= (/ k (1+ k)) (/ n (1+ n))))
        (:drop 1)
        (:claim (<= a (/ n (1+ n))))
        (:use (:instance multiply-ineq (x a)
                         (y (expt a n))
                         (z fnk)))
        :pro
        (:claim (<= (* (expt a n) a) (* fnk a)))
        (:drop 1)
        (:claim (= (* (expt a n) a)
                   (expt a (1+ n))))
        (:use (:instance fn-definition-rule (a a)
                         (n n)))
        :pro
        (:claim (= (fn a n)
                   (let ((k (ceiling (* a (/ (+ 1 (- a)))) 1)))
                     (* (* k (expt a k)) (/ n)))))
        (:drop 1)
        (:claim (= (* fnk a)
                   (* (* k (expt a k)) (/ n) a)))
        (:claim (<= (expt a (+ 1 n))
                    (* (* k (expt a k)) (/ n) a)))
        (:use (:instance incr-denom-lemma (a a)
                         (k k)
                         (n n)))
        :pro
        (:claim (^ (posp k)
                   (posp n)
                   (pos-rationalp a)
                   (<= (expt a (+ 1 n))
                       (* (* k (expt a k)) (/ n) a))
                   (<= a (* n (/ (+ 1 n))))))
        (:claim (<= (expt a (+ 1 n))
                    (* k (expt a k) (/ (+ 1 n)))))
        (:drop 1)
        (:use (:instance fn-definition-rule (a a)
                         (n (1+ n))))
        :pro
        (:claim (= (fn a (+ 1 n))
                   (let ((k (ceiling (* a (/ (+ 1 (- a)))) 1))
                         (n (+ 1 n)))
                     (* (* k (expt a k)) (/ n)))))
        (:drop 1)
        (:claim (= (let ((k (ceiling (* a (/ (+ 1 (- a)))) 1))
                         (n (+ 1 n)))
                     (* (* k (expt a k)) (/ n)))
                   (* (* k (expt a k)) (/ (1+ n)))))
        (:claim (<= (expt a (1+ n)) (fn a (1+ n))))
        :prove))

#|
This is the inductive scheme we will use to prove the inductive case for Ken's
argument.
|#
(definec induct-ken (a :pos-rational n :nat) :nat
  :ic (< a 1)
  (if (> (ceiling (/ a (- 1 a)) 1) n) 0
    (1+ (induct-ken a (- n 1)))))

#|
Now, we induct using induct-ken on the argument laid out in inductive-step-kens-proof.
|#
(property n>=k->a^n<=fn (a :pos-rational n :nat)
  :h (^ (< a 1)
        (<= (ceiling (/ a (- 1 a)) 1) n))
  (<= (expt a n) (fn a n))
  :instructions
  (:pro (:induct (induct-ken a n))
        :pro
        (:casesplit (<= (ceiling (* a (/ (+ 1 (- a)))) 1)
                        (+ -1 n)))
        (:claim (natp (+ -1 n)))
        (:claim (<= (expt a (+ -1 n)) (fn a (+ -1 n))))
        (:use (:instance inductive-step-kens-proof (a a)
                         (n (- n 1))
                         (k (ceiling (* a (/ (+ 1 (- a)))) 1))
                         (fnk (fn a (+ -1 n)))))
        :pro
        (:claim (<= (expt a (+ 1 -1 n))
                    (fn a (+ 1 -1 n))))
        :prove (:claim (natp (+ -1 n)))
        (:claim (= (ceiling (* a (/ (+ 1 (- a)))) 1)
                   n))
        (:use (:instance base-case-kens-proof (a a)))
        :pro
        (:claim (= (fn a (ceiling (* a (/ (+ 1 (- a)))) 1))
                   (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))))
        :prove))

#|
Finally, the epsilon-delta proof.  Our proof sketch will go as follows:

Let e > 0 arbitrarily.
Let:
k = ceil(a/(1-a))
d = ceil(ka^k/e)
Suppose:
n >= max(k, d)
NTS:
a^n <= e
Proof:
By prior result, a^n <= f(n) = ka^k/n
Our proof strategy will be to show f(n) <= e.
As n >= d, clearly ...
ka^k/n <= ka^k/d 
= ka^k/ceil(ka^k/e)
<= [ ka^k/ceil(ka^k) ] * e
<= [ 1 ] * e
= e
The result immediately follows and we are done.
|#
(definec delta (a e :pos-rational) :nat
  :ic (< a 1)
  (max (ceiling (/ a (- 1 a)) 1)
       (ceiling (/ (* (ceiling (/ a (- 1 a)) 1)
		      (expt a (ceiling (/ a (- 1 a)) 1)))
		   e)
		1)))

(property n>=d->n>=k (e a :pos-rational n :nat)
  :h (^ (< a 1) (<= (delta a e) n))
  (<= (ceiling (/ a (- 1 a)) 1) n)
  :instructions
  ((:use (:instance delta-definition-rule (a a)
		    (e e)))
   :pro
   (:claim (<= (ceiling (* a (/ (+ 1 (- a)))) 1)
	       (max (ceiling (* a (/ (+ 1 (- a)))) 1)
		    (ceiling (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
				   (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
				(/ e))
			     1))))
   (:claim (<= (max (ceiling (* a (/ (+ 1 (- a)))) 1)
		    (ceiling (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
				   (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
				(/ e))
			     1))
	       n))
   :prove))

(property a^n->fan (e a :pos-rational n :nat)
  :h (^ (< a 1) (<= (delta a e) n))
  (<= (expt a n) (fn a n))
  :hints (("Goal" :use ((:instance delta-definition-rule (a a) (e e))
			(:instance fn-definition-rule (a a) (n n))
			(:instance n>=k->a^n<=fn (a a) (n n))
			(:instance n>=d->n>=k (e e) (a a) (n n))))))

(property fan->0 (e a :pos-rational n :nat)
  :h (^ (< a 1) (<= (delta a e) n))
  (<= (fn a n) e)
  :instructions
  ((:use (:instance delta-definition-rule (a a)
		    (e e)))
   (:use (:instance fn-definition-rule (a a)
		    (n n)))
   :pro
   (:claim (and (pos-rationalp a)
		(pos-rationalp n)
		(< a 1)))
   (:claim (equal (fn a n)
		  (let ((k (ceiling (* a (/ (+ 1 (- a)))) 1)))
		    (* (* k (expt a k)) (/ n)))))
   (:drop 1)
   (:claim
    (equal (delta a e)
	   (max (ceiling (* a (/ (+ 1 (- a)))) 1)
		(ceiling (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
			       (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
			    (/ e))
			 1))))
   (:drop 1)
   (:claim (equal (fn a n)
		  (* (ceiling (* a (/ (+ 1 (- a)))) 1)
		     (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))
		     (/ n))))
   (:drop 9)
   (:use (:instance div-<=-prop
		    (a (* (ceiling (/ a (- 1 a)) 1)
			  (expt a (ceiling (/ a (- 1 a)) 1))))
		    (b0 (ceiling (* (ceiling (/ a (- 1 a)) 1)
				    (expt a (ceiling (/ a (- 1 a)) 1))
				    (/ e))
				 1))
		    (b1 n)))
   :pro
   (:use (:instance pos-rationalp-ceil
		    (x (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
			     (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
			  (/ e)))))
   :pro
   (:claim
    (pos-rationalp (ceiling (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
                                  (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
                               (/ e))
                            1)))
   (:drop 1)
   (:claim (pos-rationalp (* (ceiling (* a (/ (+ 1 (- a)))) 1)
			     (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))))
   (:claim (<= (ceiling (* (ceiling (* a (/ (+ 1 (- a)))) 1)
			   (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))
			   (/ e))
			1)
	       (max (ceiling (* a (/ (+ 1 (- a)))) 1)
		    (ceiling (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
				   (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
				(/ e))
			     1))))
   (:claim (<= (ceiling (* (ceiling (* a (/ (+ 1 (- a)))) 1)
			   (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))
			   (/ e))
			1)
	       (delta a e)))
   (:claim
    (and (pos-rationalp (* (ceiling (* a (/ (+ 1 (- a)))) 1)
			   (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))))
	 (pos-rationalp (ceiling (* (ceiling (* a (/ (+ 1 (- a)))) 1)
				    (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))
				    (/ e))
				 1))
	 (pos-rationalp n)
	 (<= (ceiling (* (ceiling (* a (/ (+ 1 (- a)))) 1)
			 (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))
			 (/ e))
		      1)
	     n)))
   (:claim (<= (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
		     (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
		  (/ n))
	       (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
		     (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
		  (/ (ceiling (* (ceiling (* a (/ (+ 1 (- a)))) 1)
				 (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))
				 (/ e))
			      1)))))
   (:drop 1)
   (:use (:instance inequality-over-ceil-frac
		    (x (* (ceiling (* a (/ (+ 1 (- a)))) 1)
			  (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))))
		    (y e)))
   :pro
   (:claim
    (<= (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
	      (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
	   (/ (ceiling (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
			     (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
			  (/ e))
		       1)))
	e))
   :prove))

(property a^n->0 (e a :pos-rational n :nat)
  :h (^ (< a 1) (<= (delta a e) n))
  (<= (expt a n) e)
  :instructions ((:use (:instance a^n->fan (e e) (a a) (n n)))
                 (:use (:instance fan->0 (e e) (a a) (n n)))
                 :pro (:claim (<= (fn a n) e))
                 (:claim (<= (expt a n) (fn a n)))
                 :prove))
  

;; Rephrase the theorem using defun-sk.  Note: a, e, and n are all implicitly
;; universally quantified.
(defun-sk lim-0 (a e n)
  (declare (xargs :guard (and (pos-rationalp a)
			      (< a 1)
			      (pos-rationalp e)
			      (natp n))
		  :verify-guards t))
  (exists (d)
    (and (natp d)
	 (implies (< d n) (< (expt a n) e)))))

(property lim-a^n->0 (a e :pos-rational n :nat)
  :hyps (< a 1)
  (lim-0 a e n)
  :instructions ((:use (:instance lim-0-suff (d (delta a (/ e 2)))))
                 (:use (:instance a^n->0 (a a) (e (/ e 2)) (n n)))
                 :pro :prove))


