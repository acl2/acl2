;  Book           fibonacci
;  Contributed by Matyas Sustik
;  Date created   2000-05-08
;  $Id: fibonacci.lisp,v 1.3 2001/09/05 19:12:21 matyas Exp $
;
;  Matt Kaufmann has simplified and rearranged several proofs.  Thank
;  you!  See his comments inserted before the theorems.


(in-package "ACL2")
(include-book "int-division")
(include-book "grcd")

(defmacro np (x)
  (list 'and (list 'integerp x) (list '<= 0 x)))

(defmacro pintp (x)
  (list 'and (list 'integerp x) (list '< 0 x)))

; This is the efficient definition.
(defun fib-general (x y n)
  (cond ((zp n) 0)
	((equal n 0) 0)
	((equal n 1) x)
	((equal n 2) y)
	((< 2 n) (fib-general y (+ x y) (+ -1 n)))
	(t nil)))

; This is better for proofs.
(defun fib (n)
  (cond ((zp n) 0)
	((equal n 0) 0)
	((equal n 1) 1)
	(t (+ (fib (- n 1)) (fib (- n 2))))))

(defthm fib-general-at-3
  (equal (fib-general x y 3) (+ x y))
  :hints (("Goal" :expand (fib-general x y 3))))

(defthm fib-general-recursive-equation ; requires top-with-meta
  (implies (and (integerp n)
		(< 2 n))
	   (equal (+ (fib-general x y (+ -1 n))
		     (fib-general x y (+ -2 n)))
		  (fib-general x y n))))

; The function fib is really a special case of fib-general:

(defthm fib-is-special-case-of-fib-general
  (equal (fib n)
	 (fib-general 1 1 n))
  :hints (("Goal" :induct (fib n)))
  :rule-classes nil)

; The fib-general is more efficient but proofs are easier on fib.
; We use fib from now on.

(defthm fib-identity-base-case ; This is needed for the next theorem.
  (implies (and (integerp n) (< 1 n))
	   (equal (fib n)
		  (+ (fib (- n 1))
		     (fib (- n 2))))))

(defthm fib-identity
  (implies (and (pintp n)
		(pintp k)
		(< k n))
	   (equal (fib n)
		  (+ (* (fib k)
			(fib (+ n (- k) 1)))
		     (* (fib (+ k -1))
			(fib (+ n (- k)))))))
  :rule-classes nil)

; MattK: Moved fib-identity-base-case below the proof of fib-neighbours-lemma
; in order to avoid the need for one of the :use hints.
(in-theory (disable fib))

(defthm fib-neighbours-lemma
  (implies (and (integerp k)
		(< 1 k))
	   (equal (grcd (fib k)
			(fib (+ -1 k)))
		  (grcd (fib (+ -1 k))
			(fib (+ -2 k)))))
  :hints (("Goal"
	   :use ((:instance grcd-addition-lemma
			    (a (fib (+ -1 k)))
			    (b (fib (+ -2 k)))
			    (c 1))))))

(in-theory (disable fib-identity-base-case))

; MattK: Trivial mod, probably unnecessary, but result is simpler.
(local
 (defun ind-int->=-2 (n)
   (if (and (integerp n)
	    (<= 2 n))
       (ind-int->=-2 (+ -1 n))
     t)))

(defthm fib-neighbours-are-relative-primes
  (implies (pintp k)
	   (equal (grcd (fib k)
			(fib (+ -1 k)))
		  1))
  :hints (("Goal"
	   :induct (ind-int->=-2 k))))

; (F(k); F(n-k)*F(k-1)) = (F(k); F(n-k))
; MattK: I rearranged the terms of the following in order to make it a better
; rewrite rule.  In order for the left side to match, we need to be sure it's
; in a form that is likely to be matched during the proof of the next lemma.
; The documentation for loop-stopper hints that (- x) and x are ordered the
; same when directly under a call of +, and that variables closer to the start
; of the alphabet are ordered before those later in the alphabet.  Those facts
; are relevant below since there are rewrite rules for commutativity of + and *
; that have loop stoppers.  This is all pretty subtle, and of course there is
; nothing really wrong with just giving a :use hint, as was done originally.
(defthm grcd-fib-recursion-lemma-1
  (implies (and (pintp n)
		(pintp k)
		(<= k n))
	   (equal (grcd (fib k)
			(* (fib (+ -1 k))
			   (fib (+ (- k) n))))
		  (grcd (fib k)
			(fib (- n k)))))
  :hints (("Goal"
	   :use ((:instance grcd-multiplication-with-relative-prime
			    (a (fib k))
			    (b (fib (- n k)))
			    (c (fib (+ -1 k))))))))

; (F(k); F(n-k)*F(k-1)+F(n-k+1)*F(k)) = (F(k); F(n-k))
; MattK: Just for fun, I restated this lemma in a form that would apply in the
; proof of grcd-fib-recursion.  I came up with this restatement by looking at
; the failed proof of grcd-fib-recursion. when this lemma was not supplied ina
; :use hint.
(defthm grcd-fib-recursion-lemma-2
  (implies (and (pintp n)
		(pintp k)
		(<= k n)
                (equal (fib n)
                       (+ (* (fib k)
                             (fib (+ 1 (- k) n)))
                          (* (fib (+ -1 k))
                             (fib (+ (- k) n))))))
	   (equal (grcd (fib k)
			(fib n))
		  (grcd (fib k)
			(fib (- n k)))))
  :hints (("Goal"
	   :use ((:instance grcd-addition-lemma
			    (a (fib k))
			    (b (* (fib (- n k))
				  (fib (+ -1 k))))
			    (c (fib (+ 1 n (- k)))))))))

; MattK: The following is used automatically in grcd-fib-recursion and
; main-grcd-fib, thus saving two :use hints.  Except, we also need grcd-0 for
; the proof of grcd-fib-recursion, which is OK since we will need it in
; main-grcd-fib, anyhow.
(defthm grcd-subtract
  (implies (and (integerp k) (integerp n))
           (equal (grcd k (+ (- k) n))
                  (grcd k n)))
  :hints (("Goal"
	   :use ((:instance grcd-addition-lemma
			    (a k)
			    (b n)
			    (c (- 1)))))))

; We already have a similar grcd-with-0 but that has (grcd a 0) in it.
; ACL2 does not seem to use commutativity with constants in this case.
(defthm grcd-0
  (implies (np a)
	   (equal (grcd 0 a) a))
  :hints (("Goal" :in-theory (enable grcd euclid-alg-nat))))

; This says that the Euclidean algorithm for Fibonacci numbers can be
; thought of as operating on the indices.
(defthm grcd-fib-recursion
  (implies (and (pintp n)
		(pintp k)
		(<= k n))
	   (equal (grcd (fib k)
			(fib n))
		  (grcd (fib k)
			(fib (- n k)))))
  :hints (("Goal" :use fib-identity)))

(in-theory (enable Euclid-alg-nat))

(defthm main-grcd-fib
  (implies (and (pintp n)
		(pintp k))
	   (equal (grcd (fib k)
			(fib n))
		  (fib (grcd k n))))
  :hints (("Goal"
	   :induct (Euclid-alg-nat k n))
	  ("Subgoal *1/4"
	   :in-theory (disable grcd-fib-recursion))))
