(in-package "ACL2S")

;; The first SRTT is the first sample.
;; Each subsequent srtt = (1-alpha)(prior srtt) + (alpha)(cur sample).
(definec paramaterized-new-srtt (alpha srtt s :pos-rational) :pos-rational
  :ic (< alpha 1)
  (+ (* (- 1 alpha) srtt) (* alpha s)))

(defdata prs (listof pos-rational))

;; R(a,sr,[s0]) = P(a,sr,s0)
;; R(a,sr,[s0,s1,...,sN]) = R(a,P(a,sr,s0),[s1,...,sN])
(definec recurse-srtt (alpha srtt :pos-rational ss :prs) :pos-rational
  :ic (^ (< alpha 1) (< 0 (len ss)))
  (let ((srtt0 (paramaterized-new-srtt alpha srtt (car ss))))
    (if (= (len ss) 1) srtt0 (recurse-srtt alpha srtt0 (cdr ss)))))

;; Next, define the recursive srtt for the case with N consecutive samples.
(definec recurse-srtt-N-cons (alpha srtt s :pos-rational N :nat) :pos-rational
  :ic (< alpha 1)
  (if (= N 0) (paramaterized-new-srtt alpha srtt s)
    (recurse-srtt-N-cons
     alpha
     (paramaterized-new-srtt alpha srtt s)
     s
     (1- N))))

(definec all-eq (ss :prs) :bool
  (if (< (len ss) 2) t (^ (= (car ss) (cadr ss)) (all-eq (cdr ss)))))

(property all-eq-works (ss :prs x y :pos-rational)
  (=> (^ (all-eq ss) (!= x y))
	   (! (^ (in x ss) (in y ss)))))

;; Prove equivalence.
(property recurse-srtt-when-N-cons (alpha srtt :pos-rational ss :prs)
  :h (^ (< alpha 1) (< 0 (len ss)) (all-eq ss))
  (= (recurse-srtt alpha srtt ss)
     (recurse-srtt-N-cons alpha srtt (car ss) (1- (len ss)))))

;; Next we will prove that recurse-srtt-N-cons can be re-written as an alpha summation.
;; To do this we first need to define alpha summations.

;; Define the alpha summation we will use to rewrite the case where there are N
;; identical consecutive samples.
;;     alpha-summation(N, a) = sum_{i=0}^N (1-a)^i (a)
(definec alpha-summation (N :nat alpha :pos-rational) :pos-rational
  :ic (< alpha 1)
  (if (= N 0) alpha
    (+ (* (expt (- 1 alpha) N) alpha)
       (alpha-summation (1- N) alpha))))

;; Prove critical shifting property of the alpha summation:
;;     (1-a)alpha-summation(N, a) + (a) = alpha-summation(N+1, a)
(property shift-alpha-summation (N :nat alpha :pos-rational)
  :h (< alpha 1)
  (= (+ (* (- 1 alpha) (alpha-summation N alpha)) alpha)
     (alpha-summation (1+ N) alpha)))

;; Observe: srttK+1 = (1-a)srtt + (a)s
;;          srttK+2 = (1-a)^2(srtt) + (1-a)(a)s + (a)s
;;          srttK+3 = (1-a)^3(srtt) + (1-a)^2(a)s + (1-a)(a)s + (a)s
;;          ...
;;          srttK+N = (1-a)^N(srtt) + ( sum_{i=0}^{N-1} (1-a)^i (a) ) s

;; Begin with the base case.
(property base-case-unfold-recurse-srtt (alpha srtt s :pos-rational)
  :h (< alpha 1)
  (= (recurse-srtt-N-cons alpha srtt s 0)
     (+ (* (expt (- 1 alpha) 1) srtt) (* (alpha-summation 0 alpha) s))))

;; Now for the general case (N arbitrary).
(property unfold-recurse-srtt (alpha srtt s :pos-rational N :nat)
  :h (< alpha 1)
  (= (recurse-srtt-N-cons alpha srtt s N)
     (+ (* (expt (- 1 alpha) (1+ N)) srtt) (* (alpha-summation N alpha) s))))

;; We can further simplify the alpha summation to a closed form (which I discovered
;; using Wolfram Alpha).
(property simplify-alpha-sum (N :nat alpha :pos-rational)
  :h (< alpha 1)
  (= (alpha-summation N alpha)
     (+ (* alpha (expt (- 1 alpha) N))
	(* -1 (expt (- 1 alpha) N))
	1))
  :hints (("Goal" :use (:instance shift-alpha-summation (N (- N 1)) (alpha alpha)))))

;; Now we can use this closed form to rewrite the recurse srtt (when samples are identical).
;; This is the Observation we report in the paper.  From this Observation, the limit is
;; immediately obvious.
(property further-unfold-recurse-srtt (alpha srtt s :pos-rational N :nat)
  :h (< alpha 1)
  (= (recurse-srtt-N-cons alpha srtt s N)
     (+ (* (expt (- 1 alpha) (1+ N)) srtt)
	(* (+ (* alpha (expt (- 1 alpha) N))
	      (* -1 (expt (- 1 alpha) N))
	      1)
	   s))))

;; Now that we proved something sufficient to get the limit for identical samples
;; [s0 = s1 = ... = sN], let's consider the more general case where all the si fall
;; in some range (a, b) = Br_e(c) = (e - c, e + c).  To handle this case we first
;; need to prove srtt is monotone in the sense that increasing input increases output.
;; Once we've proven this, then we need to show it also holds for the recursive case.

;; Prove that s0 <= s1 and srtt0 <= srtt1 -> srtt(srtt0,s0) <= srtt(srtt1,s1)
(property srtt-is-monotone (srtt0 srtt1 s0 s1 alpha :pos-rational)
  :h (^ (< alpha 1) (<= s0 s1) (<= srtt0 srtt1))
  (<= (paramaterized-new-srtt alpha srtt0 s0)
      (paramaterized-new-srtt alpha srtt1 s1)))

;; Need a way to show that every element of one list is <= each corresponding
;; element of the other (index-wise comparison ...)
(definec all-<= (ss0 ss1 :prs) :bool
  :ic (= (len ss0) (len ss1))
  (if (= (len ss0) 0) t
    (^ (<= (car ss0) (car ss1))
       (all-<= (cdr ss0) (cdr ss1)))))

;; Prove a sanity thm about this.
(property all-<=-works (ss0 ss1 :prs)
  :h (^ (= (len ss0) (len ss1)) (< 0 (len ss0)) (all-<= ss0 ss1))
  (<= (car ss0) (car ss1)))

;; Lemma that nth samples is rational.
(property nth-ss-is-s (ss :prs n :nat)
  :h (< n (len ss))
  (pos-rationalp (nth n ss)))

;; Prove another sanity thm about this.
(property all-<=-works-inside (ss0 ss1 :prs n :nat)
  :h (^ (= (len ss0) (len ss1)) (all-<= ss0 ss1) (< n (len ss0)))
  (<= (nth n ss0) (nth n ss1)))

;; Now we need to prove as much for the recursive case.
;; Let's begin by sketching out a proof.
;; Start with the base case.
(property srtt-rec-is-monotone-bc
  (alpha srtt :pos-rational ss0 ss1 :prs)
  :h (^ (< alpha 1) (= 1 (len ss0)) (= (len ss0) (len ss1)) (all-<= ss0 ss1))
  (<= (recurse-srtt alpha srtt ss0)
      (recurse-srtt alpha srtt ss1)))

;; Now let's think a bit about the inductive step.  Recall:
;; R(a,sr,[s0]) = P(a,sr,s0)
;; R(a,sr,[s0,s1,...,sN]) = R(a,P(a,sr,s0),[s1,...,sN])
;; 
;; Let ss0 = [s0,...,sN] and ss1 = [s0',...,sN'] s.t. for each 0 <= i <= N,
;; si <= si'.  And assume N >= 1.
;;
;; Then R(a,sr,[s0,...,sN]) <= R(a,sr,[s0',...,sN'])
;; <-> R(a,P(a,sr,s0),[s1,...,sN]) <= R(a,P(a,sr,s0'),[s1',...,sN']).
;; So we need an inductor for this.
(property srtt-rec-proof-inductor-contracts
  (alpha srtt0 srtt1 :pos-rational ss0 ss1 :prs)
  :h (^ (< alpha 1) (< 0 (len ss0)) (= (len ss0) (len ss1)))
  (if (= (len ss0) 1) (natp 1)
    (^ (pos-rationalp alpha)
       (pos-rationalp (paramaterized-new-srtt alpha srtt0 (car ss0)))
       (pos-rationalp (paramaterized-new-srtt alpha srtt1 (car ss1)))
       (prsp (cdr ss0))
       (prsp (cdr ss1)))))

(definec srtt-rec-proof-inductor
  (alpha srtt0 srtt1 :pos-rational ss0 ss1 :prs) :nat
  :ic (^ (< alpha 1) (< 0 (len ss0)) (= (len ss0) (len ss1)))
  (if (= (len ss0) 1) 1
    (1+ (srtt-rec-proof-inductor
	 alpha
	 (paramaterized-new-srtt alpha srtt0 (car ss0))
	 (paramaterized-new-srtt alpha srtt1 (car ss1))
	 (cdr ss0)
	 (cdr ss1)))))

(property srtt-rec-is-monotone (alpha srtt0 srtt1 :pos-rational ss0 ss1 :prs)
  :h (^ (< alpha 1) (< 0 (len ss0)) (= (len ss0) (len ss1)) (<= srtt0 srtt1) (all-<= ss0 ss1))
  (<= (recurse-srtt alpha srtt0 ss0)
      (recurse-srtt alpha srtt1 ss1))
  :hints (("Goal" :induct (srtt-rec-proof-inductor alpha srtt0 srtt1 ss0 ss1))))

;; Next, I want to argue for a bounded closed form, which gives me the bounded
;; convergence result.
(property srtt-bounded-thm (alpha srtt :pos-rational ss-bot ss-top ss :prs)
  :h (^ (< alpha 1)
	(= (len ss-bot) (len ss)) (= (len ss) (len ss-top))
	(all-eq ss-bot) (all-eq ss-top)
	(all-<= ss-bot ss) (all-<= ss ss-top)
	(< 0 (len ss)))
  (^ (<= (recurse-srtt-N-cons alpha srtt (car ss-bot) (1- (len ss-bot)))
	 (recurse-srtt alpha srtt ss))
     (<= (recurse-srtt alpha srtt ss)
	 (recurse-srtt-N-cons alpha srtt (car ss-top) (1- (len ss-bot)))))
  :hints (("Goal" :use ((:instance srtt-rec-is-monotone (alpha alpha)
                               (srtt0 srtt)
                               (srtt1 srtt)
                               (ss0 ss-bot)
                               (ss1 ss))
			(:instance srtt-rec-is-monotone (alpha alpha)
                               (srtt0 srtt)
                               (srtt1 srtt)
                               (ss0 ss)
                               (ss1 ss-top))))))

;; Now, let's take a look at RTTVar.
(definec paramaterized-new-rttvar (beta srtt rttvar s :pos-rational) :pos-rational
  :ic (^ (< 0 beta) (< beta 1))
  (+ (* (- 1 beta) rttvar)
     (* beta (abs (- srtt s)))))

;; NOTE: The rttvar IS NOT monotone in srtt and/or s.

;; Step 1: Show how RTTVar collapses when d(SRTT, S) is upper-bounded.
(property rttvar-collapses-when-d-srtt-s-bounded (beta srtt rttvar s bnd :pos-rational)
  :h (^ (< beta 1) (<= (abs (- srtt s)) bnd))
  (<= (paramaterized-new-rttvar beta srtt rttvar s)
      (+ (* (- 1 beta) rttvar)
	 (* beta bnd))))

#|
R(1) = (1-b)R(0) + (b)2r
R(2) = (1-b)^2 R(0) + (1-b)(b)2r + (b)2r
R(3) = (1-b)^3 R(0) + (1-b)^2(b)2r + (1-b)(b)2r + (b)2r
R(N) = (1-b)^N R(0) + sum_{i=0}^{N-1} (1-b)^i (b)2r = (1-b)^N R(0) + (1 - (1-b)^n)2r
Lim N->inf R(N) = 0 + 2r
|#
(definec rttvar-right-sum (r beta :pos-rational N :pos) :rational
  (let ((term (* (expt (- 1 beta) (- N 1)) beta 2 r)))
	(if (= N 1) term
	  (+ term (rttvar-right-sum r beta (- N 1))))))

(definec rttvar-right-sum-cf (r beta :pos-rational N :nat) :rational
  (* (- 1 (expt (- 1 beta) N)) 2 r))

;; Simplification for final observation for rttvar pre-limit.
(property rttvar-right-sum-to-cf (r beta :pos-rational N :pos)
  (= (rttvar-right-sum r beta N) (rttvar-right-sum-cf r beta N)))

(definec d[srtt-s]<=Del-always (ss srtts :prs beta del :pos-rational) :boolean
  :ic (^ (= (len ss) (len srtts)) (< beta 1))
  (if (consp ss) (^ (<= (abs (- (car srtts) (car ss))) del)
		    (d[srtt-s]<=Del-always (cdr ss) (cdr srtts) beta del))
    t))

;; Refine recurse-rttvars to return a LIST of the consecutive RTTVars.
(definec recurse-rttvars (beta rttvar0 :pos-rational srtts ss :prs) :prs
  :ic (^ (< beta 1) (< 0 (len ss)) (= (len ss) (len srtts)))
  (let ((rttvar1 (paramaterized-new-rttvar beta (car srtts) rttvar0 (car ss))))
    (if (= (len ss) 1) (list rttvar1)
      (cons rttvar1 (recurse-rttvars beta rttvar1 (cdr srtts) (cdr ss))))))

(property unwrap-recurse-rttvars (beta rttvar0 :pos-rational srtts ss :prs)
  :hyps (^ (< beta 1) (< 1 (len ss)) (= (len ss) (len srtts)))
  (equal (recurse-rttvars beta rttvar0 srtts ss)
	 (cons (paramaterized-new-rttvar beta (car srtts) rttvar0 (car ss))
	       (recurse-rttvars
		beta
		(paramaterized-new-rttvar beta (car srtts) rttvar0 (car ss))
		(cdr srtts)
		(cdr ss))))
  :hints (("Goal" :use (:instance recurse-rttvars-definition-rule
				  (beta beta)
				  (rttvar0 rttvar0)
				  (srtts srtts)
				  (ss ss)))))

(property d[srtt-s]<=Del-always-shifts (ss srtts :prs beta del :pos-rational)
  :h (^ (= (len ss) (len srtts))
	(< beta 1)
	(d[srtt-s]<=Del-always ss srtts beta del)
	(consp ss))
  (^ (<= (abs (- (car srtts) (car ss))) del)
     (d[srtt-s]<=Del-always (cdr ss) (cdr srtts) beta del)))

(definec rttvar-bnd-inductor (ss srtts :prs rttvar0 beta :pos-rational) :nat
  :ic (and (= (len ss) (len srtts)) (< beta 1))
  (if (consp ss)
      (1+ (rttvar-bnd-inductor
	   (cdr ss)
	   (cdr srtts)
	   (paramaterized-new-rttvar beta (car srtts) rttvar0 (car ss))
	   beta))
    0))

(property car-last-ss=car-last-cdr-ss (ss :prs)
  :hyps (< 1 (len ss))
  (= (car (last ss)) (car (last (cdr ss)))))

(property len-rec-rttvars=len-ss (beta rttvar0 :pos-rational srtts ss :prs)
  :hyps (^ (< beta 1) (consp ss) (= (len ss) (len srtts)))
  (= (len (recurse-rttvars beta rttvar0 srtts ss))
     (len ss)))

(property posrp-car-last-rec-rttvars (beta rttvar0 :pos-rational srtts ss :prs)
  :hyps (^ (< beta 1) (consp ss) (= (len ss) (len srtts)))
  (pos-rationalp (car (last (recurse-rttvars beta rttvar0 srtts ss)))))

(definec relate-lasts-rttvars-func (beta rttvar0 :pos-rational srtts ss :prs) :bool
  :ic (^ (< beta 1) (< 1 (len ss)) (= (len ss) (len srtts)))
  :function-contract-hints (("Goal" :use (:instance posrp-car-last-rec-rttvars
						    (beta beta)
						    (rttvar0 rttvar0)
						    (srtts srtts)
						    (ss ss))))
  :body-contracts-hints (("Goal" :use ((:instance posrp-car-last-rec-rttvars
						    (beta beta)
						    (rttvar0 rttvar0)
						    (srtts srtts)
						    (ss ss))
				       (:instance posrp-car-last-rec-rttvars
						    (beta beta)
						    (rttvar0 (paramaterized-new-rttvar
							      beta
							      (car srtts)
							      rttvar0
							      (car ss)))
						    (srtts (cdr srtts))
						    (ss (cdr ss))))))
  (= (car (last (recurse-rttvars
		 beta
		 (paramaterized-new-rttvar beta (car srtts) rttvar0 (car ss))
		 (cdr srtts)
		 (cdr ss))))
     (car (last (recurse-rttvars beta rttvar0 srtts ss)))))

(property relate-lasts-rttvars (beta rttvar0 :pos-rational srtts ss :prs)
  :hyps (^ (< beta 1) (< 1 (len ss)) (= (len ss) (len srtts)))
  (relate-lasts-rttvars-func beta rttvar0 srtts ss)
  :hints (("Goal" :use ((:instance relate-lasts-rttvars-func-definition-rule
				   (beta beta)
				   (rttvar0 rttvar0)
				   (srtts srtts)
				   (ss ss))
			(:instance unwrap-recurse-rttvars (beta beta)
				   (rttvar0 rttvar0)
				   (srtts srtts)
				   (ss ss))
			(:instance car-last-ss=car-last-cdr-ss
				   (ss (recurse-rttvars beta rttvar0 srtts ss)))
			(:instance len-rec-rttvars=len-ss (beta beta)
				   (rttvar0 rttvar0)
				   (srtts srtts)
				   (ss ss))))))

;; Precondition for the functional representation of the lemma I'll need for the next step
(definec precondition-inner-bnd-lemma
  (beta rttvar0 del blarg :pos-rational srtts ss :prs) :boolean
  :body-contracts-hints (("Goal" :use (:instance posrp-car-last-rec-rttvars
					    (beta beta)
					    (rttvar0 rttvar0)
					    (srtts srtts)
					    (ss ss))))
  (^ (< beta 1)
     (< 1 (len ss))
     (= (len ss) (len srtts))
     (<= (car (last (recurse-rttvars beta rttvar0 srtts ss)))
	 (+ (* (expt (+ 1 (- beta)) (len (cdr ss)))
	       (paramaterized-new-rttvar beta (car srtts)
					 rttvar0 (car ss)))
	    (* (+ 1
		  (- (expt (+ 1 (- beta)) (len (cdr ss)))))
	       del)))
     (<= (paramaterized-new-rttvar beta (car srtts)
				   rttvar0 (car ss))
	 blarg)))
  
;; Functional representation of a lemma I'll need in the next step ... 
(definec inner-bnd-lemma-func (beta rttvar0 del blarg :pos-rational srtts ss :prs) :boolean
  :ic (precondition-inner-bnd-lemma beta rttvar0 del blarg srtts ss)
  :body-contracts-hints (("Goal" :use (:instance posrp-car-last-rec-rttvars
					    (beta beta)
					    (rttvar0 rttvar0)
					    (srtts srtts)
					    (ss ss))))
  (<= (car (last (recurse-rttvars beta rttvar0 srtts ss)))
      (+ (* (expt (+ 1 (- beta)) (len (cdr ss))) blarg)
           (* (+ 1 (- (expt (+ 1 (- beta)) (len (cdr ss)))))
              del))))

#|
Now, the actual lemma I'll need for the next step ...

   (1-b)^(n-1) rttvar1 + (1-(1-b)^(n-1)) del
 = (1-b)^(n-1) PR(b, srtt0, rttvar0, ss0) + (1-(1-b)^(n-1)) del
 = (1-b)^(n-1) [ (1-b) rttvar0 + b|srtt0 - ss0| ] + (1-(1-b)^(n-1)) del
<= (1-b)^(n-1) [ (1-b) rttvar0 + b del ] + (1-(1-b)^(n-1)) del
 = (1-b)^n rttvar0 + [ (1-b)^(n-1) ](b)(del) + (1-(1-b)^(n-1)) del
 = (1-b)^n rttvar0 + (1-(1-b)^n) del
   QED.
|#
(property inner-bnd-lemma (beta rttvar0 del blarg :pos-rational srtts ss :prs)
  :hyps (precondition-inner-bnd-lemma beta rttvar0 del blarg srtts ss)
  (inner-bnd-lemma-func beta rttvar0 del blarg srtts ss)
  :instructions
  ((:use (:instance inner-bnd-lemma-func-definition-rule
                    (beta beta)
                    (rttvar0 rttvar0)
                    (del del)
                    (blarg blarg)
                    (srtts srtts)
                    (ss ss)))
   (:use (:instance precondition-inner-bnd-lemma-definition-rule
                    (beta beta)
                    (rttvar0 rttvar0)
                    (del del)
                    (blarg blarg)
                    (srtts srtts)
                    (ss ss)))
   :pro
   (:claim (= (inner-bnd-lemma-func beta rttvar0 del blarg srtts ss)
                  (<= (car (last (recurse-rttvars beta rttvar0 srtts ss)))
                      (+ (* (expt (+ 1 (- beta)) (len (cdr ss)))
                            blarg)
                         (* (+ 1
                               (- (expt (+ 1 (- beta)) (len (cdr ss)))))
                            del)))))
   (:claim (<= (+ (* (expt (+ 1 (- beta)) (len (cdr ss)))
                     (paramaterized-new-rttvar beta (car srtts)
                                               rttvar0 (car ss)))
                  (* (+ 1
                        (- (expt (+ 1 (- beta)) (len (cdr ss)))))
                     del))
               (+ (* (expt (+ 1 (- beta)) (len (cdr ss)))
                     blarg)
                  (* (+ 1
                        (- (expt (+ 1 (- beta)) (len (cdr ss)))))
                     del))))
   :prove))

#|
The "Next Step": under the assumption that d(SRTT, S) < Delta for all the SS,
       it follows that the final RTTVar in the list is <= (1 - (1-b)^n)Delta.
|#
(property |d(srtt, s)<=del -> rttvar<=bnd| (beta del rttvar0 :pos-rational ss srtts :prs)
  :h (^ (< beta 1)
	(consp ss)
	(= (len ss) (len srtts))
	(d[srtt-s]<=Del-always ss srtts beta del))
  (<= (car (last (recurse-rttvars beta rttvar0 srtts ss)))
      (+ (* (expt (- 1 beta) (len ss)) rttvar0)
	 (* (- 1 (expt (- 1 beta) (len ss))) del)))
  :instructions
  (:pro
   (:induct (rttvar-bnd-inductor ss srtts rttvar0 beta))
   :pro
   (:use (:instance rttvar-collapses-when-d-srtt-s-bounded
		    (bnd del) (srtt (car srtts)) (rttvar rttvar0) (s (car ss))))
   (:use (:instance relate-lasts-rttvars-func-definition-rule))
   (:use (:instance relate-lasts-rttvars (beta beta)))
   :pro (:casesplit (< 1 (len ss)))
   (:claim (relate-lasts-rttvars-func beta rttvar0 srtts ss))
   (:claim
    (= (car (last (recurse-rttvars beta
				   (paramaterized-new-rttvar beta (car srtts)
							     rttvar0 (car ss))
				   (cdr srtts)
				   (cdr ss))))
       (car (last (recurse-rttvars beta rttvar0 srtts ss)))))
   (:claim (<= (paramaterized-new-rttvar beta (car srtts) rttvar0 (car ss))
	       (+ (* (+ 1 (- beta)) rttvar0) (* beta del))))
   (:claim
    (<=
     (car (last (recurse-rttvars beta
				 (paramaterized-new-rttvar beta (car srtts)
							   rttvar0 (car ss))
				 (cdr srtts)
				 (cdr ss))))
     (+ (* (expt (+ 1 (- beta)) (len (cdr ss)))
	   (paramaterized-new-rttvar beta (car srtts) rttvar0 (car ss)))
	(* (+ 1 (- (expt (+ 1 (- beta)) (len (cdr ss))))) del))))
   (:claim (<= (car (last (recurse-rttvars beta rttvar0 srtts ss)))
	       (+ (* (expt (+ 1 (- beta)) (len (cdr ss)))
		     (paramaterized-new-rttvar beta (car srtts)
					       rttvar0 (car ss)))
		  (* (+ 1
			(- (expt (+ 1 (- beta)) (len (cdr ss)))))
		     del))))
   (:use (:instance paramaterized-new-rttvar-definition-rule
		    (srtt (car srtts)) (rttvar rttvar0) (s (car ss))))
   :pro
   (:claim (equal (paramaterized-new-rttvar beta (car srtts) rttvar0 (car ss))
		  (+ (* (+ 1 (- beta)) rttvar0)
		     (* beta (abs (+ (car srtts) (- (car ss))))))))
   (:use (:instance rttvar-collapses-when-d-srtt-s-bounded
		    (srtt (car srtts)) (rttvar rttvar0) (s (car ss)) (bnd del)))
   :pro
   (:claim (<= (paramaterized-new-rttvar beta (car srtts) rttvar0 (car ss))
	       (+ (* (+ 1 (- beta)) rttvar0) (* beta del))))
   (:use (:instance precondition-inner-bnd-lemma-definition-rule
		    (blarg (+ (* (+ 1 (- beta)) rttvar0) (* beta del)))))
   (:use (:instance inner-bnd-lemma-func-definition-rule
		    (blarg (+ (* (+ 1 (- beta)) rttvar0) (* beta del)))))
   (:use (:instance inner-bnd-lemma (blarg (+ (* (+ 1 (- beta)) rttvar0) (* beta del)))))
   :pro
   (:claim
    (= (precondition-inner-bnd-lemma beta rttvar0 del
				     (+ (* (+ 1 (- beta)) rttvar0) (* beta del))
				     srtts ss)
       (^ (< beta 1)
	  (< 1 (len ss))
	  (= (len ss) (len srtts))
	  (<= (car (last (recurse-rttvars beta rttvar0 srtts ss)))
	      (+ (* (expt (+ 1 (- beta)) (len (cdr ss)))
		    (paramaterized-new-rttvar beta (car srtts) rttvar0 (car ss)))
		 (* (+ 1 (- (expt (+ 1 (- beta)) (len (cdr ss))))) del)))
	  (<= (paramaterized-new-rttvar beta (car srtts) rttvar0 (car ss))
	      (+ (* (+ 1 (- beta)) rttvar0) (* beta del))))))
   (:claim (inner-bnd-lemma-func beta rttvar0 del
				 (+ (* (+ 1 (- beta)) rttvar0) (* beta del))
				 srtts ss))
   (:claim (<= (car (last (recurse-rttvars beta rttvar0 srtts ss)))
	       (+ (* (expt (+ 1 (- beta)) (len (cdr ss)))
		     (+ (* (+ 1 (- beta)) rttvar0) (* beta del)))
		  (* (+ 1 (- (expt (+ 1 (- beta)) (len (cdr ss))))) del))))
   :prove :prove))


;; Now let's quickly make this point about how rttvar isn't actually a variance
;; in the statistical sense.

;; (recurse-rttvars 1/8 5 '(12 33 8) '(2 3 4))

(definec sum-square-dels (ss :prs mu :pos-rational) :rational
  :ic (< 0 (len ss))
  (let ((del (expt (- (car ss) mu) 2)))
    (if (= (len ss) 1) del
      (+ del (sum-square-dels (cdr ss) mu)))))

(definec sum (ss :prs) :pos-rational
  :ic (< 0 (len ss))
  (if (equal (len ss) 1) (car ss)
    (+ (car ss) (sum (cdr ss)))))

(definec mean (ss :prs) :pos-rational
  :ic (< 0 (len ss))
  (/ (sum ss) (len ss)))

(definec sample-variance-squared (ss :prs) :rational
  :ic (< 1 (len ss))
  (/ (sum-square-dels ss (mean ss)) (- (len ss) 1)))

;; Observation: RTTVar is NOT the statistical variance.
#|
(let* ((ss '(1 44 13))
       (beta 1/4)
       (alpha 1/8)
       (srtt0 1)
       (srtt1 (paramaterized-new-srtt alpha srtt0 (cadr ss)))
       (srtt2 (paramaterized-new-srtt alpha srtt1 (caddr ss)))
       (srtts (list srtt0 srtt1 srtt2))
       (rttvar0 1/2))
  (list (expt (car (last (recurse-rttvars beta rttvar0 srtts ss))) 2)
	(sample-variance-squared ss)))
|#

;; I'll need this later ...
(property arithmetic-lower-bnd-step-srtt-inner (ss0 rs eps :pos-rational)
   (=> (^ (>= (+ ss0 (- (* eps 1/2))) rs) (< (/ eps 2) ss0))
       (<= (- (/ eps 2)) (+ ss0 (- rs)))))

(defun-sk lim-const-srtt (alpha srtt eps ss lim)
  (declare (xargs :guard (^ (pos-rationalp alpha)
			    (pos-rationalp srtt)
			    (pos-rationalp eps)
			    (rationalp lim)
			    (prsp ss)
			    (all-eq ss)
			    (< alpha 1)
			    (< 0 (len ss)))))
  (exists (d)
    (and (natp d)
	 (=> (< d (len ss))
	     (< (abs (- lim (recurse-srtt alpha srtt ss))) eps)))))

(property max-works (a b :pos-rational)
  (^ (<= a (max a b))
     (<= b (max a b))))

(property consolidate-deltas (alpha srtt eps :pos-rational ss :prs)
  :h (^ (consp ss)
	(all-eq ss)
	(!= srtt (car ss))
	(< alpha 1)
	(< (+ 1
	      (max (* (numerator (+ 1 (- alpha)))
		      (denominator (* eps (/ (* 2 (car ss))))))
		   (* (numerator (+ 1 (- alpha)))
		      (denominator (* eps (/ (* 2 srtt)))))))
	   (len ss))
	(=> (< (* (numerator (+ 1 (- alpha)))
		  (denominator (* eps (/ (* 2 (car ss))))))
	       (+ -1 (len ss)))
	    (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
	       (* eps (/ (* 2 (car ss))))))
	(=> (< (* (numerator (+ 1 (- alpha)))
		  (denominator (* eps (/ (* 2 srtt)))))
	       (+ -1 (len ss)))
	    (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
	       (* eps (/ (* 2 srtt))))))
  (=> (< (+ 1
	    (max (* (numerator (+ 1 (- alpha)))
		    (denominator (* eps (/ (* 2 (car ss))))))
		 (* (numerator (+ 1 (- alpha)))
		    (denominator (* eps (/ (* 2 srtt)))))))
	 (len ss))
      (^ (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
	    (* eps (/ (* 2 (car ss)))))
	 (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
	    (* eps (/ (* 2 srtt))))))
  :instructions
  ((:use (:instance max-works
                    (a (* (numerator (+ 1 (- alpha)))
                          (denominator (* eps (/ (* 2 (car ss)))))))
                    (b (* (numerator (+ 1 (- alpha)))
                          (denominator (* eps (/ (* 2 srtt))))))))
   :pro
   (:claim (and (<= (* (numerator (+ 1 (- alpha)))
                       (denominator (* eps (/ (* 2 (car ss))))))
                    (max (* (numerator (+ 1 (- alpha)))
                            (denominator (* eps (/ (* 2 (car ss))))))
                         (* (numerator (+ 1 (- alpha)))
                            (denominator (* eps (/ (* 2 srtt)))))))
                (<= (* (numerator (+ 1 (- alpha)))
                       (denominator (* eps (/ (* 2 srtt)))))
                    (max (* (numerator (+ 1 (- alpha)))
                            (denominator (* eps (/ (* 2 (car ss))))))
                         (* (numerator (+ 1 (- alpha)))
                            (denominator (* eps (/ (* 2 srtt)))))))))
   (:drop 1)
   (:claim (< (* (numerator (+ 1 (- alpha)))
                 (denominator (* eps (/ (* 2 srtt)))))
              (+ -1 (len ss))))
   (:claim (< (* (numerator (+ 1 (- alpha)))
                 (denominator (* eps (/ (* 2 (car ss))))))
              (+ -1 (len ss))))
   :prove))

(property alpha-reduces (a :pos-rational n :nat)
  :h (< a 1)
  (<= (expt a (1+ n))
      (expt a n))
  :instructions (:pro (:claim (equal (expt a (1+ n))
                                     (* a (expt a n))))
                      (:claim (< 0 (expt a n)))
                      :prove))

(property simplify-before-second-eps (eps alpha :pos-rational ss :prs)
  :h (consp ss)
  (= (+ (* eps 1/2)
        (* (+ (* alpha (expt (+ 1 (- alpha)) (+ -1 (len ss))))
              (* -1 (expt (+ 1 (- alpha)) (+ -1 (len ss))))
	      1)
	   (car ss))) 
     (+ (/ eps 2)
	(car ss)
	(* (car ss) (- alpha 1) (expt (+ 1 (- alpha)) (+ -1 (len ss)))))))

(property alpha-leq-1 (a :pos-rational n :nat)
  :h (< a 1)
  (<= (expt a n) 1))

(property simplify-negation-alpha (alpha ss0 :pos-rational L :pos)
   (= (+ ss0
	 (* ss0
	    (* -1 (+ 1 (- alpha)))
	    (expt (+ 1 (- alpha))
		  (+ -1 L))))
      (- ss0
	 (* ss0
	    (+ 1 (- alpha))
	    (expt (+ 1 (- alpha))
		  (+ -1 L))))))

(property lower-srtt-thm (alpha srtt eps :pos-rational ss :prs)
  :check-contracts? nil ;; Would be nice if we could do contracts too here,
  ;; but it's turning into quite a pain and I'm not sure how best to resolve it.
  :h (^ (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
	   (* eps (/ (* 2 (car ss)))))
	(consp ss)
	(< alpha 1)
	(!= srtt (car ss)))
  (<= (- (car ss) (/ eps 2))
      (+ (* (expt (+ 1 (- alpha)) (+ 1 -1 (len ss)))
	    srtt)
	 (* (+ (* alpha
		  (expt (+ 1 (- alpha)) (+ -1 (len ss))))
	       (* -1
		  (expt (+ 1 (- alpha)) (+ -1 (len ss))))
	       1)
	    (car ss))))
  :instructions
  (:pro (:claim (equal (+ (* (expt (+ 1 (- alpha)) (+ 1 -1 (len ss)))
                             srtt)
                          (* (+ (* alpha
                                   (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                                (* -1
                                   (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                                1)
                             (car ss)))
                       (+ (* (expt (- 1 alpha) (len ss)) srtt)
                          (* (1+ (* (- alpha 1)
                                    (expt (- 1 alpha) (- (len ss) 1))))
                             (car ss)))))
        (:claim (< (- alpha 1) 0))
        (:claim (pos-rationalp (* (expt (+ 1 (- alpha)) (+ 1 -1 (len ss)))
                                  srtt)))
        (:claim (<= (* (+ 1
                          (* (+ -1 alpha)
                             (expt (+ 1 (- alpha)) (+ -1 (len ss)))))
                       (car ss))
                    (+ (* (expt (+ 1 (- alpha)) (len ss)) srtt)
                       (* (+ 1
                             (* (+ -1 alpha)
                                (expt (+ 1 (- alpha)) (+ -1 (len ss)))))
                          (car ss)))))
        (:claim (= (* (+ 1
                         (* (+ -1 alpha)
                            (expt (+ 1 (- alpha)) (+ -1 (len ss)))))
                      (car ss))
                   (+ (car ss)
                      (* (car ss)
                         (* (+ -1 alpha)
                            (expt (+ 1 (- alpha))
                                  (+ -1 (len ss))))))))
        (:claim (= (+ -1 alpha) (* -1 (- 1 alpha))))
        (:claim (= (+ (car ss)
                      (* (car ss)
                         (+ -1 alpha)
                         (expt (+ 1 (- alpha)) (+ -1 (len ss)))))
                   (+ (car ss)
                      (* (car ss)
                         (* -1 (+ 1 (- alpha)))
                         (expt (+ 1 (- alpha))
                               (+ -1 (len ss)))))))
        (:use (:instance simplify-negation-alpha (alpha alpha)
                         (ss0 (car ss))
                         (l (len ss))))
        :pro
        (:claim (= (+ (car ss)
                      (* (car ss)
                         (* -1 (+ 1 (- alpha)))
                         (expt (+ 1 (- alpha)) (+ -1 (len ss)))))
                   (+ (car ss)
                      (- (* (car ss)
                            (+ 1 (- alpha))
                            (expt (+ 1 (- alpha))
                                  (+ -1 (len ss))))))))
        (:drop 1)
        (:claim (= (+ (car ss)
                      (* (car ss)
                         (+ -1 alpha)
                         (expt (+ 1 (- alpha)) (+ -1 (len ss)))))
                   (+ (car ss)
                      (- (* (car ss)
                            (+ 1 (- alpha))
                            (expt (+ 1 (- alpha))
                                  (+ -1 (len ss))))))))
        (:drop 15 16)
        (:claim (= (* (+ 1 (- alpha))
                      (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                   (expt (+ 1 (- alpha)) (len ss))))
        (:claim (= (- (* (car ss)
                         (+ 1 (- alpha))
                         (expt (+ 1 (- alpha)) (+ -1 (len ss)))))
                   (- (* (car ss)
                         (expt (+ 1 (- alpha)) (len ss))))))
        (:claim (<= (- (* (car ss)
                          (expt (+ 1 (- alpha)) (len ss))))
                    (/ eps 2)))
        :prove))

;; Finally we need to do the actual asymptotic proofs.
(include-book "pete-proof")

(property abs[a-b]<=max[a-or-b] (a :pos-rational b :rational)
  :h (< b 0)
  (<= (abs (+ a b)) (max a (abs b))))

;; The following implies the following 2 results:
;; Theorem: Upper bound H on SRTT -> c + r
;;          Lower bound L on SRTT -> c - r
;; By instantiating w/ ss = [c+r, c+r, ...] or ss = [c-r, c-r, ...] resp.
(property srtt-bounds-convergence-thm (alpha srtt eps :pos-rational ss :prs)
  :h (^ (consp ss)
	(all-eq ss)
	(< (car ss) srtt) ;; WLOG
	(< alpha 1))
  (lim-const-srtt alpha srtt eps ss (car ss))
  :proof-timeout 6000
  :instructions
  ((:use (:instance further-unfold-recurse-srtt
                    (alpha alpha)
                    (srtt srtt)
                    (s (car ss))
                    (n (1- (len ss)))))
   :pro
   (:claim (= (recurse-srtt-n-cons alpha srtt (car ss)
                                   (+ -1 (len ss)))
              (+ (* (expt (+ 1 (- alpha)) (+ 1 -1 (len ss)))
                    srtt)
                 (* (+ (* alpha
                          (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                       (* -1
                          (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                       1)
                    (car ss)))))
   (:drop 1)
   (:use (:instance recurse-srtt-when-n-cons (alpha alpha)
                    (srtt srtt)
                    (ss ss)))
   :pro
   (:claim (= (recurse-srtt alpha srtt ss)
              (recurse-srtt-n-cons alpha srtt (car ss)
                                   (+ -1 (len ss)))))
   (:drop 1)
   (:claim (= (recurse-srtt alpha srtt ss)
              (+ (* (expt (+ 1 (- alpha)) (+ 1 -1 (len ss)))
                    srtt)
                 (* (+ (* alpha
                          (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                       (* -1
                          (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                       1)
                    (car ss)))))
   (:drop 9 10)
   (:use (:instance a^n->0-helper (a (+ 1 (- alpha)))
                    (n (+ -1 (len ss)))
                    (e (/ eps (* 2 srtt)))))
   :pro
   (:claim (=> (< (* (numerator (+ 1 (- alpha)))
                     (denominator (* eps (/ (* 2 srtt)))))
                  (+ -1 (len ss)))
               (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                  (* eps (/ (* 2 srtt))))))
   (:drop 1)
   (:use (:instance a^n->0-helper (a (+ 1 (- alpha)))
                    (n (+ -1 (len ss)))
                    (e (/ eps (* 2 (car ss))))))
   :pro
   (:claim (=> (< (* (numerator (+ 1 (- alpha)))
                     (denominator (* eps (/ (* 2 (car ss))))))
                  (+ -1 (len ss)))
               (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                  (* eps (/ (* 2 (car ss)))))))
   (:drop 1)
   (:use (:instance lim-const-srtt-suff
                    (d (1+ (max (* (numerator (+ 1 (- alpha)))
                                   (denominator (* eps (/ (* 2 (car ss))))))
                                (* (numerator (+ 1 (- alpha)))
                                   (denominator (* eps (/ (* 2 srtt))))))))
                    (lim (car ss))))
   :pro
   (:claim (=> (=> (< (+ 1
                         (max (* (numerator (+ 1 (- alpha)))
                                 (denominator (* eps (/ (* 2 (car ss))))))
                              (* (numerator (+ 1 (- alpha)))
                                 (denominator (* eps (/ (* 2 srtt)))))))
                      (len ss))
                   (< (abs (+ (car ss)
                              (- (recurse-srtt alpha srtt ss))))
                      eps))
               (lim-const-srtt alpha srtt eps ss (car ss))))
   (:drop 1)
   (:use (:instance consolidate-deltas (alpha alpha)
                    (srtt srtt)
                    (eps eps)
                    (ss ss)))
   :pro
   (:claim (implies (< (+ 1
                          (max (* (numerator (+ 1 (- alpha)))
                                  (denominator (* eps (/ (* 2 (car ss))))))
                               (* (numerator (+ 1 (- alpha)))
                                  (denominator (* eps (/ (* 2 srtt)))))))
                       (len ss))
                    (and (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                            (* eps (/ (* 2 (car ss)))))
                         (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                            (* eps (/ (* 2 srtt)))))))
   (:drop 11 12)
   (:drop 1)
   (:claim (= (abs (+ (car ss)
                      (- (recurse-srtt alpha srtt ss))))
              (abs (- (car ss)
                      (+ (* (expt (+ 1 (- alpha)) (+ 1 -1 (len ss)))
                            srtt)
                         (* (+ (* alpha
                                  (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                               (* -1
                                  (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                               1)
                            (car ss)))))))
   (:claim (= (abs (+ (car ss)
                      (- (+ (* (expt (+ 1 (- alpha)) (+ 1 -1 (len ss)))
                               srtt)
                            (* (+ (* alpha
                                     (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                                  (* -1
                                     (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                                  1)
                               (car ss))))))
              (abs (+ (- (+ (* (expt (+ 1 (- alpha)) (+ 1 -1 (len ss)))
                               srtt)
                            (* (+ (* alpha
                                     (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                                  (* -1
                                     (expt (+ 1 (- alpha)) (+ -1 (len ss)))))
                               (car ss))))))))
   (:claim (= (abs (+ (car ss)
                      (- (recurse-srtt alpha srtt ss))))
              (abs (+ (* (expt (+ 1 (- alpha)) (+ 1 -1 (len ss)))
                         srtt)
                      (* (+ (* alpha
                               (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                            (* -1
                               (expt (+ 1 (- alpha)) (+ -1 (len ss)))))
                         (car ss))))))
   (:drop 12 13)
   (:claim (= (abs (+ (* (expt (+ 1 (- alpha)) (+ 1 -1 (len ss)))
                         srtt)
                      (* (+ (* alpha
                               (expt (+ 1 (- alpha)) (+ -1 (len ss))))
                            (* -1
                               (expt (+ 1 (- alpha)) (+ -1 (len ss)))))
                         (car ss))))
              (abs (+ (* (expt (+ 1 (- alpha)) (len ss)) srtt)
                      (* (- alpha 1)
                         (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                         (car ss))))))
   (:claim (= (abs (+ (car ss)
                      (- (recurse-srtt alpha srtt ss))))
              (abs (+ (* (expt (+ 1 (- alpha)) (len ss)) srtt)
                      (* (+ -1 alpha)
                         (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                         (car ss))))))
   (:drop 12 13)
   (:claim (<= (* (+ -1 alpha)
                  (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                  (car ss))
               0))
   (:use (:instance abs[a-b]<=max[a-or-b]
                    (a (* (expt (+ 1 (- alpha)) (len ss))
                          srtt))
                    (b (* (+ -1 alpha)
                          (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                          (car ss)))))
   :pro
   (:claim (<= (abs (+ (* (expt (+ 1 (- alpha)) (len ss)) srtt)
                       (* (+ -1 alpha)
                          (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                          (car ss))))
               (max (* (expt (+ 1 (- alpha)) (len ss)) srtt)
                    (abs (* (+ -1 alpha)
                            (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                            (car ss))))))
   (:drop 1)
   (:use (:instance alpha-reduces (a (+ 1 (- alpha)))
                    (n (+ -1 (len ss)))))
   :pro
   (:claim (<= (expt (+ 1 (- alpha)) (+ 1 -1 (len ss)))
               (expt (+ 1 (- alpha)) (+ -1 (len ss)))))
   (:claim (<= (* (expt (+ 1 (- alpha)) (len ss)) srtt)
               (* (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                  srtt)))
   (:drop 16)
   (:claim (=> (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                  (* eps (/ (* 2 srtt))))
               (<= (* (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                      srtt)
                   (/ eps 2))))
   (:claim (implies (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                       (* eps (/ (* 2 srtt))))
                    (<= (* (expt (+ 1 (- alpha)) (len ss)) srtt)
                        (* eps 1/2))))
   (:drop 16 17)
   (:claim (=> (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                  (* eps (/ (* 2 (car ss)))))
               (<= (abs (* (+ -1 alpha)
                           (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                           (car ss)))
                   (abs (* (+ -1 alpha) (/ eps 2))))))
   (:claim (implies (^ (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                          (* eps (/ (* 2 srtt))))
                       (< (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                          (* eps (/ (* 2 srtt)))))
                    (<= (abs (+ (* (expt (+ 1 (- alpha)) (len ss)) srtt)
                                (* (+ -1 alpha)
                                   (expt (+ 1 (- alpha)) (+ -1 (len ss)))
                                   (car ss))))
                        (max (/ eps 2)
                             (abs (* (+ -1 alpha) eps 1/2))))))
   (:claim (=> (< (+ 1
                     (max (* (numerator (+ 1 (- alpha)))
                             (denominator (* eps (/ (* 2 (car ss))))))
                          (* (numerator (+ 1 (- alpha)))
                             (denominator (* eps (/ (* 2 srtt)))))))
                  (len ss))
               (<= (abs (+ (car ss)
                           (- (recurse-srtt alpha srtt ss))))
                   (/ eps 2))))
   :prove))

;; Now we move on to RTTVar.
(property abs-rat-rat (r :rational)
  (^ (<= 0 (abs r)) (rationalp (abs r))))

(property lim-Delta-gc (r beta eps :pos-rational n :pos)
  :h (< beta 1)
  (rationalp (abs (- (* 2 r) (rttvar-right-sum-cf r beta n))))
  :hints (("Goal" :use (:instance
			abs-rat-rat (r (- (* 2 r) (rttvar-right-sum-cf r beta n)))))))

(defun-sk lim-Delta (r beta eps n)
  (declare (xargs :guard (^ (pos-rationalp r)
			    (pos-rationalp beta)
			    (< beta 1)
			    (posp n)
			    (pos-rationalp eps))))
  (exists (d)
    (and (natp d)
	 (=> (< d n)
	     (< (abs (- (* 2 r) (rttvar-right-sum-cf r beta N))) eps)))))

;; Theorem: Delta -> 2r
;; | 2r - (1 - (1-b)^n)2r |
;; = | (1-b)^n 2r |
(property Delta->2r (r beta eps :pos-rational n :pos)
  :h (< beta 1)
  (lim-Delta r beta eps n)
  :hints (("Goal" :use (:instance a^n->0-helper
				  (a (- 1 beta))
				  (e (/ eps (* 2 r)))
				  (n n)))))

(defun-sk lim-upper-bnd-RTTVar (beta del rttvar0 eps ss srtts)
  (exists (d)
    (and (natp d)
	 (=> (< d (len ss))
	     (< (abs (- del (+ (* (expt (- 1 beta) (len ss)) rttvar0)
			       (* (- 1 (expt (- 1 beta) (len ss))) del))))
		eps)))))
	   
#|
(del - [ (1-b)^|ss| rttvar0 + (1-(1-b)^|ss|) del ])
=
(del - del + (1-b)^|ss| del - (1-b)^|ss| rttvar0)
=
(1-b)^|ss|[del - rttvar0]
|#

;; Theorem Upper bound on RTTVar -> Delta
(property upper-bnd-RTTVar-conv (beta del rttvar0 eps :pos-rational ss srtts :prs)
  :h (^ (< beta 1)
	(consp ss)
	(= (len ss) (len srtts))
	(d[srtt-s]<=Del-always ss srtts beta del))
  :check-contracts? nil
  :proof-timeout 6000
  (lim-upper-bnd-RTTVar beta del rttvar0 eps ss srtts)
  :instructions
 ((:use (:instance a^n->0-helper (a (- 1 beta))
                   (e (/ eps (* 2 (+ rttvar0 del))))
                   (n (len ss))))
  (:use (:instance lim-upper-bnd-rttvar-suff
                   (d (* (numerator (+ 1 (- beta)))
                         (denominator (* eps (/ (* 2 (+ rttvar0 del)))))))))
  :pro
  (:claim
    (=> (implies (< (* (numerator (+ 1 (- beta)))
                       (denominator (* eps (/ (* 2 (+ rttvar0 del))))))
                    (len ss))
                 (< (abs (+ del
                            (- (+ (* (expt (+ 1 (- beta)) (len ss))
                                     rttvar0)
                                  (* (+ 1 (- (expt (+ 1 (- beta)) (len ss))))
                                     del)))))
                    eps))
        (lim-upper-bnd-rttvar beta del rttvar0 eps ss srtts)))
  (:drop 1)
  (:claim (=> (< (* (numerator (+ 1 (- beta)))
                    (denominator (* eps (/ (* 2 (+ rttvar0 del))))))
                 (len ss))
              (< (expt (+ 1 (- beta)) (len ss))
                 (* eps (/ (* 2 (+ rttvar0 del)))))))
  (:drop 1)
  (:claim (= (+ del
                (- (+ (* (expt (+ 1 (- beta)) (len ss))
                         rttvar0)
                      (* (+ 1 (- (expt (+ 1 (- beta)) (len ss))))
                         del))))
             (+ del (- del)
                (* (expt (- 1 beta) (len ss)) del)
                (- (* (expt (- 1 beta) (len ss))
                      rttvar0)))))
  (:claim (= (+ del (- del)
                (* (expt (+ 1 (- beta)) (len ss)) del)
                (- (* (expt (+ 1 (- beta)) (len ss))
                      rttvar0)))
             (* (expt (- 1 beta) (len ss))
                (- del rttvar0))))
  (:claim (= (abs (+ del
                     (- (+ (* (expt (+ 1 (- beta)) (len ss))
                              rttvar0)
                           (* (+ 1 (- (expt (+ 1 (- beta)) (len ss))))
                              del)))))
             (abs (* (expt (+ 1 (- beta)) (len ss))
                     (+ del (- rttvar0))))))
  (:claim (pos-rationalp (expt (+ 1 (- beta)) (len ss))))
  (:claim (= (abs (* (expt (+ 1 (- beta)) (len ss))
                     (+ del (- rttvar0))))
             (* (expt (+ 1 (- beta)) (len ss))
                (abs (+ del (- rttvar0))))))
  (:claim (= (abs (+ del
                     (- (+ (* (expt (+ 1 (- beta)) (len ss))
                              rttvar0)
                           (* (+ 1 (- (expt (+ 1 (- beta)) (len ss))))
                              del)))))
             (* (expt (+ 1 (- beta)) (len ss))
                (abs (+ del (- rttvar0))))))
  (:drop 13 14 15 16 17)
  (:claim (=> (< (* (numerator (+ 1 (- beta)))
                    (denominator (* eps (/ (* 2 (+ rttvar0 del))))))
                 (len ss))
              (<= (* (expt (+ 1 (- beta)) (len ss))
                     (abs (+ del (- rttvar0))))
                  (* (* eps (/ (* 2 (+ rttvar0 del))))
                     (abs (+ del (- rttvar0)))))))
  (:claim (<= (abs (+ del (- rttvar0)))
              (* 2 (+ rttvar0 del))))
  :prove))

(property rttvar-bnd-helper (A B :pos-rational C :rational)
  :h (^ (<= 0 C) (< A B))
  (<= (* A C) (* B C)))

(property A<B->A/B<1 (A :rational B :pos-rational)
  :h (^ (<= 0 A) (< A B))
  (< (/ A B) 1))

(property rttvar-bnd-helper-2 (eps :pos-rational abs-bnd :rational)
  :h (<= 0 abs-bnd)
  (< (* (* eps (/ (* 2 (+ 1 abs-bnd))))
	abs-bnd)
     eps)
  :hints (("Goal" :use (:instance A<B->A/B<1
				  (A abs-bnd)
				  (B (* 2 (+ 1 abs-bnd)))))))

(property rttvar-convergence-thm
  (beta del rttvar0 eps :pos-rational ss srtts :prs)
  :h (^ (< beta 1)
	(consp ss)
	(= (len ss) (len srtts))
	(d[srtt-s]<=del-always ss srtts beta del))
  (lim-upper-bnd-rttvar beta del rttvar0 eps ss srtts)
  :proof-timeout 6000
  :check-contracts? nil
  :instructions
  (:pro
   (:use (:instance a^n->0-helper (a (- 1 beta))
		    (e (/ eps (* 2 (1+ (abs (- rttvar0 del))))))
		    (n (len ss))))
   (:use (:instance
	  lim-upper-bnd-rttvar-suff
	  (d (* (numerator (+ 1 (- beta)))
		(denominator (* eps
				(/ (* 2 (1+ (abs (- rttvar0 del)))))))))))
   :pro
   (:claim
    (natp (* (numerator (+ 1 (- beta)))
	     (denominator (* eps
			     (/ (* 2 (+ 1 (abs (+ rttvar0 (- del)))))))))))
   (:claim
    (=> (=> (< (* (numerator (+ 1 (- beta)))
		  (denominator (* eps
				  (/ (* 2 (+ 1 (abs (+ rttvar0 (- del)))))))))
	       (len ss))
	    (< (abs (+ del
		       (- (+ (* (expt (+ 1 (- beta)) (len ss))
				rttvar0)
			     (* (+ 1 (- (expt (+ 1 (- beta)) (len ss))))
				del)))))
	       eps))
	(lim-upper-bnd-rttvar beta del rttvar0 eps ss srtts)))
   (:drop 1 13)
   (:claim (pos-rationalp (* eps
			     (/ (* 2 (+ 1 (abs (+ rttvar0 (- del)))))))))
   (:claim
    (=> (< (* (numerator (+ 1 (- beta)))
	      (denominator (* eps
			      (/ (* 2 (+ 1 (abs (+ rttvar0 (- del)))))))))
	   (len ss))
	(< (expt (+ 1 (- beta)) (len ss))
	   (* eps
	      (/ (* 2 (+ 1 (abs (+ rttvar0 (- del))))))))))
   (:drop 1 13)
   (:claim (= (abs (+ del
		      (- (+ (* (expt (+ 1 (- beta)) (len ss))
			       rttvar0)
			    (* (+ 1 (- (expt (+ 1 (- beta)) (len ss))))
			       del)))))
	      (abs (+ (* (expt (+ 1 (- beta)) (len ss))
			 rttvar0)
		      (* (+ 1 (- (expt (+ 1 (- beta)) (len ss))))
			 del)
		      (- del)))))
   (:claim (= (* (+ 1 (- (expt (+ 1 (- beta)) (len ss))))
		 del)
	      (- del
		 (* (expt (+ 1 (- beta)) (len ss))
		    del))))
   (:claim (= (* (+ 1 (- (expt (+ 1 (- beta)) (len ss))))
		 del)
	      (- del
		 (* (expt (+ 1 (- beta)) (len ss))
		    del))))
   (:claim (= (abs (+ (* (expt (+ 1 (- beta)) (len ss))
			 rttvar0)
		      (* (+ 1 (- (expt (+ 1 (- beta)) (len ss))))
			 del)
		      (- del)))
	      (abs (+ (* (expt (+ 1 (- beta)) (len ss))
			 rttvar0)
		      (+ del
			 (- (* (expt (+ 1 (- beta)) (len ss)) del)))
		      (- del)))))
   (:claim (= (abs (+ (* (expt (+ 1 (- beta)) (len ss))
			 rttvar0)
		      (+ del
			 (- (* (expt (+ 1 (- beta)) (len ss)) del)))
		      (- del)))
	      (abs (- (* (expt (+ 1 (- beta)) (len ss))
			 rttvar0)
		      (* (expt (+ 1 (- beta)) (len ss))
			 del)))))
   (:claim (= (abs (+ del
		      (- (+ (* (expt (+ 1 (- beta)) (len ss))
			       rttvar0)
			    (* (+ 1 (- (expt (+ 1 (- beta)) (len ss))))
			       del)))))
	      (abs (+ (* (expt (+ 1 (- beta)) (len ss))
			 rttvar0)
		      (- (* (expt (+ 1 (- beta)) (len ss))
			    del))))))
   (:claim (= (+ (* (expt (+ 1 (- beta)) (len ss))
		    rttvar0)
		 (- (* (expt (+ 1 (- beta)) (len ss)) del)))
	      (* (expt (+ 1 (- beta)) (len ss))
		 (- rttvar0 del))))
   (:claim (= (abs (+ del
		      (- (+ (* (expt (+ 1 (- beta)) (len ss))
			       rttvar0)
			    (* (+ 1 (- (expt (+ 1 (- beta)) (len ss))))
			       del)))))
	      (abs (* (expt (+ 1 (- beta)) (len ss))
		      (+ rttvar0 (- del))))))
   (:claim (pos-rationalp (expt (+ 1 (- beta)) (len ss))))
   (:claim (= (abs (* (expt (+ 1 (- beta)) (len ss))
		      (+ rttvar0 (- del))))
	      (* (expt (+ 1 (- beta)) (len ss))
		 (abs (- rttvar0 del)))))
   (:claim (= (abs (+ del
		      (- (+ (* (expt (+ 1 (- beta)) (len ss))
			       rttvar0)
			    (* (+ 1 (- (expt (+ 1 (- beta)) (len ss))))
			       del)))))
	      (* (expt (+ 1 (- beta)) (len ss))
		 (abs (+ rttvar0 (- del))))))
   (:drop 13 14 15 16 17 18 19 20 21 22)
   (:claim (<= 0 (abs (+ rttvar0 (- del)))))
   (:use (:instance rttvar-bnd-helper
		    (a (expt (+ 1 (- beta)) (len ss)))
		    (b (* eps
			  (/ (* 2 (+ 1 (abs (+ rttvar0 (- del))))))))
		    (c (abs (+ rttvar0 (- del))))))
   :pro
   (:claim
    (=> (< (* (numerator (+ 1 (- beta)))
	      (denominator (* eps
			      (/ (* 2 (+ 1 (abs (+ rttvar0 (- del)))))))))
	   (len ss))
	(<= (* (expt (+ 1 (- beta)) (len ss))
	       (abs (+ rttvar0 (- del))))
	    (* (* eps
		  (/ (* 2 (+ 1 (abs (+ rttvar0 (- del)))))))
	       (abs (+ rttvar0 (- del)))))))
   (:drop 1)
   (:use (:instance rttvar-bnd-helper-2 (eps eps)
		    (abs-bnd (abs (+ rttvar0 (- del))))))
   :pro
   (:claim (< (* (* eps
		    (/ (* 2 (+ 1 (abs (+ rttvar0 (- del)))))))
		 (abs (+ rttvar0 (- del))))
	      eps))
   (:drop 1)
   (:claim
    (implies
     (< (* (numerator (+ 1 (- beta)))
	   (denominator (* eps
			   (/ (* 2 (+ 1 (abs (+ rttvar0 (- del)))))))))
	(len ss))
     (< (* (expt (+ 1 (- beta)) (len ss))
	   (abs (+ rttvar0 (- del))))
	eps)))
   :prove))
