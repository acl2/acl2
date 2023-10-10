(in-package "ACL2")
(include-book "kestrel/arithmetic-light/ceiling" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

(defun pos-rationalp (x)
  (and (rationalp x)
       (< 0 x)))

#|
We begin with an important property of the ceiling function.  The important part here
is condition (ii), but we get two birds with one stone, since we also need the (rather
obvious) condition (i) for the next proof.

Thm: ceil(x) < ceil(y) -> 
     (i) x <= ceil(x) and
     (ii) ciel(x) < y.
|#
(defthm
  cx<cy->cx<y
   (implies (and (pos-rationalp x)
                 (pos-rationalp y)
                 (< (ceiling x 1) (ceiling y 1)))
            (and (<= x (ceiling x 1))
                 (< (ceiling x 1) y)))
   :instructions (:pro (:claim (<= x (ceiling x 1)))
                       (:casesplit (<= y x))
                       (:claim (equal x y))
                       :prove
                       (:claim (implies (<= y (ceiling x 1))
                                        (equal (ceiling y 1) (ceiling x 1))))
                       :prove))

(defthm a<=b->n*a<=n*b
  (implies (and (<= a b)
		(posp n))
	   (<= (* n a) (* n b))))

(defthm a<b->n*a<n*b
  (implies (and (< a b)
		(posp n))
	   (< (* n a) (* n b)))
  :hints (("Goal" :in-theory (disable a<=b->n*a<=n*b))))

#|
Next we prove another important property of the ceiling function, showing how repeated
division inside a ceiling can be unfolded to repeated applications of ceiling-division.
This proof was adapted from: 
https://math.stackexchange.com/questions/233670/nested-division-in-the-ceiling-function

Thm: ceil(x/mn) = ceil(ceil(x/m)/n)
|#
(defthm ceiling-division-lemma
  (implies (and (posp M)
                (posp N)
                (pos-rationalp X))
           (equal (ceiling (/ X (* M N)) 1)
                  (ceiling (/ (ceiling (/ X M) 1) N) 1)))
  :INSTRUCTIONS
  (:PRO (:CLAIM (< (- (CEILING (/ X M) 1) 1) (/ X M)))
        (:CLAIM (<= (/ X M) (CEILING (/ X M) 1)))
        (:CLAIM (< (/ (- (CEILING (/ X M) 1) 1) N)
                   (/ (/ X M) N)))
        (:CLAIM (< (* (+ -1 (CEILING (* X (/ M)) 1)) (/ N))
                   (* (* X (/ M)) (/ N))))
        (:CLAIM (<= (/ X (* M N))
                    (/ (CEILING (/ X M) 1) N)))
        (:CLAIM (<= (CEILING (/ X (* M N)) 1)
                    (CEILING (/ (CEILING (/ X M) 1) N) 1)))
        (:USE (:INSTANCE CX<CY->CX<Y (X (* X (/ (* M N))))
                         (Y (* (CEILING (* X (/ M)) 1) (/ N)))))
        :PRO
        (:CASESPLIT (< (CEILING (* X (/ (* M N))) 1)
                       (CEILING (* (CEILING (* X (/ M)) 1) (/ N))
                                1)))
        (:CLAIM (AND (<= (* X (/ (* M N)))
                         (CEILING (* X (/ (* M N))) 1))
                     (< (CEILING (* X (/ (* M N))) 1)
                        (* (CEILING (* X (/ M)) 1) (/ N)))))
        (:DROP 1)
        (:CLAIM (EQUAL (* N (* X (/ (* M N)))) (/ X M)))
        (:USE (:INSTANCE A<=B->N*A<=N*B (A (* X (/ (* M N))))
                         (B (CEILING (* X (/ (* M N))) 1))
                         (N N)))
        :PRO
        (:CLAIM (<= (* N X (/ (* M N)))
                    (* N (CEILING (* X (/ (* M N))) 1))))
        (:DROP 1)
        (:CLAIM (<= (* X (/ M))
                    (* N (CEILING (* X (/ (* M N))) 1))))
        (:DROP 14)
        (:USE (:INSTANCE A<B->N*A<N*B
                         (A (CEILING (* X (/ (* M N))) 1))
                         (B (* (CEILING (* X (/ M)) 1) (/ N)))
                         (N N)))
        :PRO
        (:CLAIM (< (* N (CEILING (* X (/ (* M N))) 1))
                   (* N (CEILING (* X (/ M)) 1) (/ N))))
        (:DROP 1)
        (:CLAIM (EQUAL (* N (CEILING (* X (/ M)) 1) (/ N))
                       (CEILING (* X (/ M)) 1)))
        (:CLAIM (< (* N (CEILING (* X (/ (* M N))) 1))
                   (CEILING (* X (/ M)) 1)))
        :PROVE :PROVE))

(in-theory (disable a<=b->n*a<=n*b))

(defthm divide-ineq
  (implies (and (pos-rationalp x)
		(pos-rationalp y)
		(pos-rationalp z)
		(<= y z))
	   (<= (/ y x) (/ z x))))

(defthm multiply-ineq
  (implies (and (pos-rationalp x)
		(pos-rationalp y)
		(pos-rationalp z)
		(<= y z))
	   (<= (* y x) (* z x))))

#|
The remainder of this proof follows a proof sketch written by Ken McMillan (in 
unpublished correspondence, as part of the above-mentioned NETYS 2023 paper).
Note however that Ken's sketch skipped many intermediary steps and small details
which we naturally are forced (by the prover) to flush out in full detail here.
|#
(defthm step-1-kens-proof
        (implies (and (pos-rationalp a)
                      (< a 1)
                      (equal k (ceiling (/ a (- 1 a)) 1)))
                 (<= a (/ k (1+ k))))
        :instructions (:pro (:claim (<= (/ a (- 1 a)) k))
                            (:use (:instance multiply-ineq (x (- 1 a))
                                             (y (* a (/ (+ 1 (- a)))))
                                             (z k)))
                            :pro
                            (:claim (<= (* (* a (/ (+ 1 (- a)))) (+ 1 (- a)))
                                        (* k (+ 1 (- a)))))
                            (:drop 1)
                            (:claim (<= a (* k (- 1 a)))) ;; <-- here
                            (:drop 5)
                            (:claim (equal (* k (+ 1 (- a))) (- k (* k a))))
                            (:claim (<= a (+ k (- (* k a)))))
                            (:drop 5 6)
                            (:claim (<= (+ a (* k a)) k))
                            (:claim (equal (+ a (* k a)) (* a (1+ k))))
                            (:claim (<= (* a (1+ k)) k))
                            (:use (:instance divide-ineq (x (1+ k))
                                             (y (* a (1+ k)))
                                             (z k)))
                            :pro
                            (:claim (<= (* (* a (+ 1 k)) (/ (+ 1 k)))
                                        (* k (/ (+ 1 k)))))
                            (:drop 1)
                            :prove))

(defun fn (a n)
  (let ((k (ceiling (/ a (- 1 a)) 1)))
    (/ (* k (expt a k)) n)))

;; Claim: k a^k / k = a^k.
(defthm k*a^k/k=a^k
  (implies (and (posp k)
		(pos-rationalp a))
	   (equal (/ (* k (expt a k)) k)
		  (expt a k))))

(defthm fn-definition-rule
  (implies (and (pos-rationalp a)
		(posp n))
	   (equal (fn a n)
		  (/ (* (ceiling (/ a (- 1 a)) 1)
			(expt a (ceiling (/ a (- 1 a)) 1)))
		     n))))

(defthm
     base-case-kens-proof
     (implies (and (pos-rationalp a) (< a 1))
              (let ((k (ceiling (/ a (- 1 a)) 1)))
                   (equal (fn a k) (expt a k))))
     :instructions
     (:pro (:claim (posp (ceiling (* a (/ (+ 1 (- a)))) 1)))
           (:use (:instance k*a^k/k=a^k
                            (k (ceiling (* a (/ (+ 1 (- a)))) 1))
                            (a a)))
           :pro
           (:claim (equal (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
                                (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
                             (/ (ceiling (* a (/ (+ 1 (- a)))) 1)))
                          (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))))
           (:drop 1)
           (:use (:instance fn-definition-rule (a a)
                            (n (ceiling (/ a (- 1 a)) 1))))
           :pro
           (:claim (equal (fn a (ceiling (* a (/ (+ 1 (- a)))) 1))
                          (let ((k (ceiling (* a (/ (+ 1 (- a)))) 1))
                                (n (ceiling (* a (/ (+ 1 (- a)))) 1)))
                               (* (* k (expt a k)) (/ n)))))
           (:drop 1)
           (:claim (equal (fn a (ceiling (* a (/ (+ 1 (- a)))) 1))
                          (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
                                (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
                             (/ (ceiling (* a (/ (+ 1 (- a)))) 1)))))
           (:claim (iff (let ((k (ceiling (* a (/ (+ 1 (- a)))) 1)))
                             (equal (fn a k) (expt a k)))
                        (equal (fn a (ceiling (* a (/ (+ 1 (- a)))) 1))
                               (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))))
           (:claim (equal (fn a (ceiling (* a (/ (+ 1 (- a)))) 1))
                          (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))))
           :prove))

;; Suppose 0 <= k <= n.
;; -> k + nk <= n + nk
;; -> k + nk <= n + kn
;; -> (1+n)k <= (1+k)n
;; -> k <= (1+k)n/(1+n)
;; -> k/(1+k) <= n/(1+n)
(defthm div-lem-ind-step
  (implies (and (natp k)
		(natp n)
		(<= k n))
	   (<= (/ k (1+ k))
	       (/ n (1+ n))))
  :INSTRUCTIONS (:PRO (:CLAIM (<= (* (1+ N) K) (* (1+ K) N)))
                      (:USE (:INSTANCE DIVIDE-INEQ (Y (* (+ 1 N) K))
                                       (Z (* (+ 1 K) N))
                                       (X (+ 1 N))))
                      :PRO
                      (:CLAIM (<= (* (* (+ 1 N) K) (/ (+ 1 N)))
                                  (* (* (+ 1 K) N) (/ (+ 1 N)))))
                      (:DROP 1)
                      (:CLAIM (<= K (* (* (+ 1 K) N) (/ (+ 1 N)))))
                      (:DROP 5)
                      (:USE (:INSTANCE DIVIDE-INEQ (Y K)
                                       (Z (* (* (+ 1 K) N) (/ (+ 1 N))))
                                       (X (+ 1 K))))
                      :PRO
                      (:CLAIM (<= (* K (/ (+ 1 K)))
                                  (* (* (* (+ 1 K) N) (/ (+ 1 N)))
                                     (/ (+ 1 K)))))
                      (:DROP 1)
                      :PROVE))

;; Suppose 0 <= a, b, c, z
;; Suppose further, a <= b, and x <= a(z).
;; -> x/z <= a
;; -> x/z <= b
;; -> x <= bz
(defthm repl-mul-<=
  (implies (and (pos-rationalp a)
		(pos-rationalp b)
		(pos-rationalp x)
		(pos-rationalp z)
		(<= a b)
		(<= x (* a z)))
	   (<= x (* b z)))
  :INSTRUCTIONS (:PRO (:USE (:INSTANCE DIVIDE-INEQ (X Z)
                                       (Y X)
                                       (Z (* A Z))))
                      :PRO
                      (:CLAIM (<= (* X (/ Z)) (* (* A Z) (/ Z))))
                      (:DROP 1)
                      (:CLAIM (EQUAL (* (* A Z) (/ Z)) A))
                      (:CLAIM (<= (/ X Z) A))
                      (:DROP 7 8)
                      (:CLAIM (<= (/ X Z) B))
                      (:DROP 7)
                      (:USE (:INSTANCE MULTIPLY-INEQ (Y (* X (/ Z)))
                                       (Z B)
                                       (X Z)))
                      :PRO
                      (:CLAIM (<= (* (* X (/ Z)) Z) (* B Z)))
                      (:DROP 1)
                      :PROVE))

#|
Thm: a^{n+1} <= a * (k a^k / n) -> a^{n+1} <= k a^k / (1+n)
|#
(defthm
  incr-denom-lemma
  (implies (and (posp k)
                (posp n)
                (pos-rationalp a)
                (<= (expt a (+ 1 n))
                    (* (* k (expt a k)) (/ n) a))
                (<= a (/ n (1+ n))))
           (<= (expt a (+ 1 n))
               (* k (expt a k) (/ (1+ n)))))
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
                      (:claim (equal (* (* n (/ (+ 1 n))) k (expt a k) (/ n))
                                     (* (* (/ (+ 1 n))) k (expt a k))))
                      :prove))

#|
Thm: [ a^n <= f_n(a, n) and ceil(a/(1-a)) <= n ] -> a^{1+n} <= f_n(a, 1+n)
|#
(defthm inductive-step-kens-proof
        (implies (and (pos-rationalp a)
                      (< a 1)
                      (equal k (ceiling (/ a (- 1 a)) 1))
                      (natp n)
                      (<= k n)
                      (equal fnk (fn a n))
                      (<= (expt a n) fnk))
                 (<= (expt a (1+ n)) (fn a (1+ n))))
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
              (:claim (equal (* (expt a n) a)
                             (expt a (1+ n))))
              (:use (:instance fn-definition-rule (a a)
                               (n n)))
              :pro
              (:claim (equal (fn a n)
                             (let ((k (ceiling (* a (/ (+ 1 (- a)))) 1)))
                                  (* (* k (expt a k)) (/ n)))))
              (:drop 1)
              (:claim (equal (* fnk a)
                             (* (* k (expt a k)) (/ n) a)))
              (:claim (<= (expt a (+ 1 n))
                          (* (* k (expt a k)) (/ n) a)))
              (:use (:instance incr-denom-lemma (a a)
                               (k k)
                               (n n)))
              :pro
              (:claim (and (posp k)
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
              (:claim (equal (fn a (+ 1 n))
                             (let ((k (ceiling (* a (/ (+ 1 (- a)))) 1))
                                   (n (+ 1 n)))
                                  (* (* k (expt a k)) (/ n)))))
              (:drop 1)
              (:claim (equal (let ((k (ceiling (* a (/ (+ 1 (- a)))) 1))
                                   (n (+ 1 n)))
                                  (* (* k (expt a k)) (/ n)))
                             (* (* k (expt a k)) (/ (1+ n)))))
              (:claim (<= (expt a (1+ n)) (fn a (1+ n))))
              :prove))


#|
This is the inductive scheme we will use to prove the inductive case for Ken's
argument.
|#
(defun induct-ken (a n)
  (if (and (pos-rationalp a)
	   (< a 1)
	   (natp n))
      (if (> (ceiling (/ a (- 1 a)) 1) n) 0
	(1+ (induct-ken a (- n 1))))
    0))

#|
Now, we induct using induct-ken on the argument laid out in inductive-step-kens-proof.
|#
(defthm n>=k->a^n<=fn
        (implies (and (pos-rationalp a)
                      (< a 1)
                      (natp n)
                      (<= (ceiling (/ a (- 1 a)) 1) n))
                 (<= (expt a n) (fn a n)))
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
              (:claim (equal (ceiling (* a (/ (+ 1 (- a)))) 1)
                             n))
              (:use (:instance base-case-kens-proof (a a)))
              :pro
              (:claim (equal (fn a (ceiling (* a (/ (+ 1 (- a)))) 1))
                             (expt a (ceiling (* a (/ (+ 1 (- a)))) 1))))
              :prove))

#|
Thm: 0 < b0 <= b1 -> a/b0 <= a/b1
(This is just a helper Lemma, because otherwise prover gets stuck in next proof.)
|#
(defthm div-<=-prop
  (implies (and (pos-rationalp a)
		(pos-rationalp b0)
		(pos-rationalp b1)
		(<= b0 b1))
	   (<= (/ a b1) (/ a b0))))

#|
Thm: The ceiling's codomain are the positive rationals.
(This is another helper Lemma for where otherwise the prover would get stuck.)
|#
(defthm pos-rationalp-ceil
  (implies (pos-rationalp x)
	   (pos-rationalp (ceiling x 1))))

#|
Thm: x/ceiling(x/y) <= y.
This is a very important helper lemma that explains essentially how we can pull
the y out of the ceiling-wrapped denominator ...
|#
(defthm inequality-over-ceil-frac
  (implies (and (pos-rationalp x)
		(pos-rationalp y))
	   (<= (/ x (ceiling (/ x y) 1)) y))
  :INSTRUCTIONS (:PRO (:CLAIM (<= (/ X Y) (CEILING (/ X Y) 1)))
                      (:USE (:INSTANCE MULTIPLY-INEQ (X Y)
                                       (Y (* X (/ Y)))
                                       (Z (CEILING (* X (/ Y)) 1))))
                      :PRO
                      (:CLAIM (<= (* (* X (/ Y)) Y)
                                  (* (CEILING (* X (/ Y)) 1) Y)))
                      (:DROP 1)
                      (:CLAIM (<= X (* (CEILING (* X (/ Y)) 1) Y)))
                      (:USE (:INSTANCE DIVIDE-INEQ (Y X)
                                       (Z (* (CEILING (* X (/ Y)) 1) Y))
                                       (X (CEILING (* X (/ Y)) 1))))
                      :PRO
                      (:CLAIM (<= (* X (/ (CEILING (* X (/ Y)) 1)))
                                  (* (* (CEILING (* X (/ Y)) 1) Y)
                                     (/ (CEILING (* X (/ Y)) 1)))))
                      (:DROP 1)
                      :PROVE))

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
(defthm a^n->0
        (implies (and (pos-rationalp e)
                      (pos-rationalp a)
                      (< a 1)
                      (equal k (ceiling (/ a (- 1 a)) 1))
                      (equal d (ceiling (/ (* k (expt a k)) e) 1))
                      (natp n)
                      (<= d n)
                      (<= k n))
                 (<= (expt a n) e))
        :instructions
        (:pro (:use (:instance div-<=-prop (a (* k (expt a k)))
                               (b0 d)
                               (b1 n)))
              :pro
              (:claim (pos-rationalp (* k (expt a k))))
              (:use (:instance pos-rationalp-ceil
                               (x (* (* k (expt a k)) (/ e)))))
              :pro
              (:claim (<= (* (* k (expt a k)) (/ n))
                          (* (* k (expt a k)) (/ d))))
              (:drop 1 2)
              (:claim (<= (* (* k (expt a k)) (/ n))
                          (* (* k (expt a k))
                             (/ (ceiling (* (* k (expt a k)) (/ e))
                                         1)))))
              (:drop 10)
              (:use (:instance inequality-over-ceil-frac
                               (x (* k (expt a k)))
                               (y e)))
              :pro
              (:claim (<= (* (* k (expt a k))
                             (/ (ceiling (* (* k (expt a k)) (/ e)) 1)))
                          e))
              (:drop 1)
              (:use (:instance n>=k->a^n<=fn (a a) (n n)))
              :pro (:claim (<= (expt a n) (fn a n)))
              (:drop 1)
              (:use (:instance fn-definition-rule (a a)
                               (n n)))
              :pro
              (:claim (equal (fn a n)
                             (let ((k (ceiling (* a (/ (+ 1 (- a)))) 1)))
                                  (* (* k (expt a k)) (/ n)))))
              (:drop 1)
              (:claim (equal (fn a n)
                             (* (* k (expt a k)) (/ n))))
              :prove))

(defun delta (a e)
  (max (ceiling (/ a (- 1 a)) 1)
       (ceiling (/ (* (ceiling (/ a (- 1 a)) 1)
		      (expt a (ceiling (/ a (- 1 a)) 1)))
		   e)
		1)))

;; Rephrase the theorem using defun-sk.  Note: a, e, and n are all implicitly
;; universally quantified.
(defun-sk lim-0 (a e n)
  (exists (d)
    (implies (and (pos-rationalp e)
		  (<= d n))
	     (<= (expt a n) e))))
				      
(defthm lim-a^n->0-helper
  (implies (and (pos-rationalp a)
		(< a 1)
		(pos-rationalp e)
		(natp n)
		(<= (delta a e) n))
	   (<= (expt a n) e))
  :hints (("Goal" :INSTRUCTIONS
	   (:PRO
	    (:CLAIM (<= (MAX (CEILING (/ A (- 1 A)) 1)
			     (CEILING (/ (* (CEILING (/ A (- 1 A)) 1)
					    (EXPT A (CEILING (/ A (- 1 A)) 1)))
					 E)
				      1))
			N))
	    (:CLAIM (<= (CEILING (* A (/ (+ 1 (- A)))) 1)
			(MAX (CEILING (* A (/ (+ 1 (- A)))) 1)
			     (CEILING (* (* (CEILING (* A (/ (+ 1 (- A)))) 1)
					    (EXPT A (CEILING (* A (/ (+ 1 (- A)))) 1)))
					 (/ E))
				      1))))
	    (:CLAIM (<= (CEILING (* (* (CEILING (* A (/ (+ 1 (- A)))) 1)
				       (EXPT A (CEILING (* A (/ (+ 1 (- A)))) 1)))
				    (/ E))
				 1)
			(MAX (CEILING (* A (/ (+ 1 (- A)))) 1)
			     (CEILING (* (* (CEILING (* A (/ (+ 1 (- A)))) 1)
					    (EXPT A (CEILING (* A (/ (+ 1 (- A)))) 1)))
					 (/ E))
				      1))))
	    (:CLAIM (<= (CEILING (* A (/ (+ 1 (- A)))) 1)
			N))
	    (:CLAIM (<= (CEILING (* (* (CEILING (* A (/ (+ 1 (- A)))) 1)
				       (EXPT A (CEILING (* A (/ (+ 1 (- A)))) 1)))
				    (/ E))
				 1)
			N))
	    (:DROP 6 7 8)
	    (:USE (:INSTANCE A^N->0 (A A)
			     (E E)
			     (N N)
			     (K (CEILING (/ A (- 1 A)) 1))
			     (D (CEILING (/ (* (CEILING (/ A (- 1 A)) 1)
					       (EXPT A (CEILING (/ A (- 1 A)) 1)))
					    E)
					 1))))
	    :PRO :PROVE))))

(defthm lim-a^n->0
  (implies (and (pos-rationalp a)
		(pos-rationalp e)
		(< a 1)
		(natp n))
	   (lim-0 a e n))
  :hints (("Goal"   :INSTRUCTIONS (:PRO (:USE (:INSTANCE LIM-0-SUFF (D (DELTA A E))))
					:PRO (:USE (:INSTANCE LIM-A^N->0-HELPER (A A)
							      (E E)
							      (N N)))))))
