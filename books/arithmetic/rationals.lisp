; ACL2 Arithmetic Rationals-with-axioms-PROVED book.
; Copyright (C) 1998  John R. Cowles, University of Wyoming
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:
; John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071-3682 U.S.A.

#| Summer 1997
     Last modified 30 June 1998

     Depends on the Arithmetic Inequalities book and the
         Arithmetic Nonnegative Integer Mod and Gcd book.

Modified by Jared Davis in January 2014 to add xdoc section.

This book proves all the axioms in the
     Arithmetic Rationals-with-axioms book

   To certify in Arithmetic Book directory:

      (certify-book "rationals-with-axioms-proved" 0 nil)
|#


#| This following is copied from the Arithmetic Rationals-with-axioms book:

; Written by:
; Matt Kaufmann, Bishop Brock, and John Cowles, with help from Art Flatau
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")

(include-book "inequalities")

; The following three axioms seemed crucial for some of Matt
; Kaufmann's work, both in non-standard analysis and in a termination
; and guard verification exercise for axioms.lisp.  After these three
; axioms is an informal argument that justifies them.  Perhaps some
; day, someone will translate this informal proof to an Acl2 proof.

(defaxiom denominator-unary-minus
  (implies (rationalp x)
	   (equal (denominator (- x))
		  (denominator x))))

(defaxiom numerator-goes-down-by-integer-division
  (implies (and (integerp x)
		(< 0 x)
		(rationalp r)
		(<= 0 r))
	   (<= (numerator (* (/ x) r))
	       (numerator r)))
  :rule-classes :linear)

(defaxiom denominator-plus
  (implies (and (rationalp r)
		(integerp i))
           (equal (denominator (+ r i))
                  (denominator r)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (implies (and (rationalp r)
                           (integerp i))
                      (equal (denominator (+ i r))
                             (denominator r))))))

#|

Here are proofs of the three axioms above, using heavily some standard
facts about gcd.

Basic Fact:
If r = p/q where all are rational, p and q are integers, and q is
positive, then if g = gcd(|p|,q), we have (numerator r) = p/g,
(denominator r) = q/g.

Proof of Basic Fact.  Let n1 = p/g, d1 = q/g, n = (numerator r), d =
(denominator r).  Thus we have n1/d1 = n/d, and we know that n1 and d1
are relatively prime.  Let d2 = gcd(d1,d).  We will show d2 = d.  Let
us write d = k*d2 (all positive integers) where k and d1 are
relatively prime.  Now n1*d=n*d1, so since k divides d, k divides
n*d1, and hence since k and d1 are relatively prime, therefore k
divides n.  But then since k divides both n and d, we have a
contradiction of lowest terms.  Therefore k=1, and hence d = d2 =
gcd(d1,d).  Thus we may write d1 = i*d for some positive integer i.
Now n1*d=n*d1, so n1*d=n*i*d, and hence n1 = n*i.  So i divides both
n1 and d1, which implies i = 1, and hence we're done.

Corollary:  gcd(|(numerator r)|,(denominator r)) = 1 for all rationals r.

Proof.  Setting p = (numerator r) and q = (denominator r) above, we
obtain p = p/gcd(|p|,q) and hence p = 0 or else gcd(|p|,q) = 1.  But
if p = 0 then (denominator r) = 1 and hence gcd(|p|,q) = 1 in that
case too.

Lemma about gcd (stated without proof).
gcd(|i+k*j|,j) = gcd(i,j) for integers i,j,k.

(defaxiom denominator-unary-minus
  (implies (rationalp x)
	   (equal (denominator (- x))
		  (denominator x))))

Proof.  Let x = p/q, where p and q are the numerator and denominator
of x.  Then -x = (-p)/q, so (denominator -x) = q/gcd(|-p|,q) =
q/gcd(p,q) = q/1 = q.

(defaxiom denominator-plus
  (implies (and (rationalp r)
		(integerp i))
	   (equal (denominator (+ r i))
                  (denominator r))))

Proof.  (+ r i) = (/ (+ n (* i d)) d), where n and d are the numerator
and denominator of r.  Now we have (denominator (+ r i)) = d/gcd(|+ n
(* i d)|,d) by the Basic Fact.  But using the lemma about gcd stated
above, we have gcd(|+ n (* i d)|,d) = gcd(|n|,d) = 1, and hence we're
done.

(defaxiom numerator-goes-down-by-integer-division
  (implies (and (integerp x)
		(< 0 x)
		(rationalp r)
		(<= 0 r))
	   (<= (numerator (* (/ x) r))
	       (numerator r)))
  :rule-classes :linear)

Let r = n/d, where n and d are its numerator and denominator.
Then (* (/ x) r) = n/(x*d), so by the Basic Fact,
(numerator (* (/ x) r)) = n/gcd(|n|,(x*d)) <= n.

|#

; Here are some axioms that Bishop wanted.

(encapsulate
 ()

 (local
  (defthm /-cancellation-on-right-temp
    (implies (and (equal z (* x (/ y)))
                  (rationalp x)
                  (rationalp y)
                  (not (equal y 0)))
             (equal (* y z) x))))

 (defthm numerator-minus
   (equal (numerator (- i))
          (- (numerator i)))
   :hints (("Goal" :use
            ((:instance rational-implies2
                        (x i))
             (:instance rational-implies2
                        (x (- i)))
             (:instance denominator-unary-minus
                        (x i)))
            :in-theory (disable rational-implies2
                                denominator-unary-minus))))
 )

(encapsulate
 ()

 (local
  (defthm numerator-/x-positive-case
    (implies
     (and (integerp x)
          (< 0 x))
     (equal (numerator (/ x)) 1))
    :rule-classes nil
    :hints
    (("Goal" :use
      ((:instance rational-implies2 (x (/ x)))
       (:instance lowest-terms (n (numerator (/ x)))
                  (r 1)
                  (q x)
                  (x (/ x))))
      :in-theory (disable rational-implies2
                          *-r-denominator-r)))))

 (defthm numerator-/x
   (implies
    (and (integerp x)
         (not (equal x 0)))
    (equal (numerator (/ x)) (signum x)))
   :hints
   (("Goal"
     :use
     (numerator-/x-positive-case
      (:instance numerator-/x-positive-case
                 (x (- x)))))))
 )

|#

(in-package "ACL2")

(include-book "inequalities")

(local (include-book "mod-gcd"))

(defsection more-rational-identities
  :parents (arithmetic-1 numerator denominator)
  :short "Rules about @(see numerator) and @(see denominator) in the
@('arithmetic/rationals') book."

(defthm Denominator-unary-minus
  (implies (rationalp x)
	   (equal (denominator (- x))
		  (denominator x)))
 :hints (("Goal" :use (:instance Unique-rationalp
                                 (d (denominator x))
                                 (n (- (numerator x)))))))

(defthm Numerator-goes-down-by-integer-division
  (implies (and (integerp x)
		(< 0 x)
		(rationalp r))
	   (<= (abs (numerator (* (/ x) r)))
	       (abs (numerator r))))
  :rule-classes ((:linear :corollary
                          (implies (and (integerp x)
                                        (< 0 x)
                                        (rationalp r)
                                        (>= r 0))
                                   (<= (numerator (* (/ x) r))
                                       (numerator r))))
		 (:linear :corollary
                          (implies (and (integerp x)
                                        (< 0 x)
                                        (rationalp r)
                                        (<= r 0))
                                   (<= (numerator r)
                                       (numerator (* (/ x) r))))))
  :hints (("Goal" :use (:instance LEAST-numerator-denominator-<=
                                  (n (numerator r))
                                  (d (* x (denominator r)))))))

(defthm Denominator-plus
  (implies (and (rationalp r)
		(integerp i))
           (equal (denominator (+ i r))
                  (denominator r)))
  :hints (("Goal" :use ((:instance Unique-rationalp
                                   (d (denominator r))
                                   (n (+ (numerator r)(* i (denominator r)))))
                        (:instance Nonneg-int-gcd-abs
                                   (x (numerator r))
                                   (j i)
                                   (n (denominator r)))))))

; Here are some axioms that Bishop wanted.

(defthm Numerator-minus
  (equal (numerator (- i))
	 (- (numerator i)))
  :hints (("Goal" :cases ((rationalp i)))
	  ("Subgoal 1" :use (:instance Unique-rationalp
                                       (d (denominator i))
                                       (n (- (numerator i)))))))

(defthm Numerator-/x
  (implies (and (integerp x)
		(not (equal x 0)))
	   (equal (numerator (/ x))
		  (signum x)))
  :hints (("Goal" :use (:instance Unique-rationalp
                                  (n (signum x))
                                  (d (abs x))))))

)
