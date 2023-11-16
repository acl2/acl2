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

#|
; Pete
; Note that this defthm can be turned into a property as shown below.
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
|#

(property cx<cy->cx<y (x y :pos-rational)
  (=> (< (ceiling x 1) (ceiling y 1))
      (and (<= x (ceiling x 1))
           (< (ceiling x 1) y)))
  :instructions (:pro (:claim (<= x (ceiling x 1)))
                      (:casesplit (<= y x))
                      (:claim (equal x y))
                      :prove
                      (:claim (implies (<= y (ceiling x 1))
                                       (equal (ceiling y 1) (ceiling x 1))))
                      :prove)
  :rule-classes :linear)


#|
Next we prove another important property of the ceiling function, showing how repeated
division inside a ceiling can be unfolded to repeated applications of ceiling-division.
This proof was adapted from: 
https://math.stackexchange.com/questions/233670/nested-division-in-the-ceiling-function

Thm: ceil(x/mn) = ceil(ceil(x/m)/n)
|#

#|
; Pete: I rewrote this rule to avoid any looping. ;

(defthm ceiling-division-lemma
        (implies (and (posp m)
                      (posp n)
                      (pos-rationalp x))
                 (equal (ceiling (/ x (* m n)) 1)
                        (ceiling (/ (ceiling (/ x m) 1) n) 1)))
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
              (:claim (and (<= (* x (/ (* m n)))
                               (ceiling (* x (/ (* m n))) 1))
                           (< (ceiling (* x (/ (* m n))) 1)
                              (* (ceiling (* x (/ m)) 1) (/ n)))))
              (:drop 1)
              (:claim (<= (/ x m)
                          (* n (ceiling (* x (/ (* m n))) 1))))
              (:claim (< (* n (ceiling (* x (/ (* m n))) 1))
                         (ceiling (/ x m) 1)))
              :prove :prove))
|#

(defthm ceiling-division-lemma
        (implies (and (posp m)
                      (posp n)
                      (pos-rationalp x))
                 (equal (ceiling (/ (ceiling (/ x m) 1) n) 1)
                        (ceiling (/ x (* m n)) 1)))
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
              (:claim (and (<= (* x (/ (* m n)))
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
  (implies (and (< 0 x) (<= y z))
           (<= (/ y x) (/ z x))))

(property multiply-ineq (x y z :pos-rational)
  (implies (and (< 0 x) (<= y z))
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
                      (:claim (<= a (* k (- 1 a))))
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

(definecd fn (a n :pos-rational) :pos-rational
  :ic (< a 1)
  (let ((k (ceiling (/ a (- 1 a)) 1)))
    (/ (* k (expt a k)) n)))

;; Claim: k a^k / k = a^k.
(property k*a^k/k=a^k (k :pos a :pos-rational)
  (equal (/ (* k (expt a k)) k)
         (expt a k)))

(defthm base-case-kens-proof
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

(property div-lem-ind-step (k n :nat)
  (implies (<= k n)
           (<= (/ k (1+ k))
               (/ n (1+ n)))))

(property repl-mul-<=
  (a b x z :pos-rational)
  (implies (and (<= a b)
                (<= x (* a z)))
           (<= x (* b z))))

#|
Thm: a^{n+1} <= a * (k a^k / n) -> a^{n+1} <= k a^k / (1+n)
|#
(defthm incr-denom-lemma
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
(definec induct-ken (a :pos-rational n :nat) :nat
  :ic (< a 1)
  (if (> (ceiling (/ a (- 1 a)) 1) n) 0
    (1+ (induct-ken a (- n 1)))))

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
(property div-<=-prop (a b0 b1 :pos-rational)
  (implies (<= b0 b1)
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
(defthm inequality-over-ceil-frac
  (implies (and (pos-rationalp x)
                (pos-rationalp y))
           (<= (/ x (ceiling (/ x y) 1)) y))
  :instructions (:pro (:claim (<= (/ x y) (ceiling (/ x y) 1)))
                      (:claim (<= (/ (ceiling (/ x y) 1))
                                  (/ (/ x y))))
                      (:claim (<= (/ x (ceiling (/ x y) 1))
                                  (/ x (/ x y))))
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

(definec delta (a e :pos-rational) :nat
  :ic (< a 1)
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
				      
(property lim-a^n->0-helper (a e :pos-rational n :nat)
  (implies (and (< a 1)
		(<= (delta a e) n))
	   (<= (expt a n) e))
  :instructions
  (:pro
   (:claim (<= (max (ceiling (/ a (- 1 a)) 1)
		    (ceiling (/ (* (ceiling (/ a (- 1 a)) 1)
				   (expt a (ceiling (/ a (- 1 a)) 1)))
				e)
			     1))
	       n))
   (:claim (<= (ceiling (* a (/ (+ 1 (- a)))) 1)
	       (max (ceiling (* a (/ (+ 1 (- a)))) 1)
		    (ceiling (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
				   (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
				(/ e))
			     1))))
   (:claim (<= (ceiling (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
			      (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
			   (/ e))
			1)
	       (max (ceiling (* a (/ (+ 1 (- a)))) 1)
		    (ceiling (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
				   (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
				(/ e))
			     1))))
   (:claim (<= (ceiling (* a (/ (+ 1 (- a)))) 1)
	       n))
   (:claim (<= (ceiling (* (* (ceiling (* a (/ (+ 1 (- a)))) 1)
			      (expt a (ceiling (* a (/ (+ 1 (- a)))) 1)))
			   (/ e))
			1)
	       n))
   (:drop 6 7 8)
   (:use (:instance a^n->0 (a a)
		    (e e)
		    (n n)
		    (k (ceiling (/ a (- 1 a)) 1))
		    (d (ceiling (/ (* (ceiling (/ a (- 1 a)) 1)
				      (expt a (ceiling (/ a (- 1 a)) 1)))
				   e)
				1))))
   :pro :prove))

#| Why doesn't this work?
(property lim-a^n->0 (a e :pos-rational n :nat)
  :hyps (< a 1)
  (lim-0 a e n)
  :hints (("Goal" :instructions (:pro (:use (:instance lim-0-suff (d (delta a e))))
                      :pro (:use (:instance lim-a^n->0-helper (a a)
                                            (e e)
                                            (n n)))))))
|#

(defthm lim-a^n->0
  (implies (and (< a 1)
                (pos-rationalp a)
                (pos-rationalp e)
                (natp n))
           (lim-0 a e n))
  :instructions (:pro (:use (:instance lim-0-suff (d (delta a e))))
                      :pro (:use (:instance lim-a^n->0-helper (a a)
                                            (e e)
                                            (n n)))))
