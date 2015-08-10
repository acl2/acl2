#|

This is in an ACL2 "book" with definitions and theorems about an abstract
correctness proof of the Fast Fourier Transform.  The proof verified here comes
from Misra's 1994 paper on powerlists.

To certify this book, first define the POWERLISTS package, then execute an
appropriate certify-book command.  Something like the following will work:

|#

#|;

    (defpkg "POWERLISTS"
      (union-eq *common-lisp-symbols-from-main-lisp-package*
		*acl2-exports*))

    (certify-book "eval-poly" 1)

|#

(in-package "POWERLISTS")

(include-book "eval-poly")

;; This first theorem shows how to evaluate a polynomial at a vector with the
;; special property v = < u | -u >.  This special property is the heart of the
;; proof as given in Misra's 1994 powerlists paper.

(defthm eval-poly-u-unary---u
  (implies (powerlist-p x)
	   (equal (eval-poly x (p-tie u (p-unary-- u)))
		  (p-tie (p-+ (eval-poly (p-unzip-l x)
					 (p-* u u))
			      (p-* u
				   (eval-poly
				    (p-unzip-r x)
				    (p-* u u))))
			 (p-- (eval-poly (p-unzip-l x)
					 (p-* u u))
			      (p-* u
				   (eval-poly
				    (p-unzip-r x)
				    (p-* u u)))))))
  :hints (;;("Goal" :expand (eval-poly x (p-tie u (p-unary-- u))))
	  ("Goal'4'"
	   :use (:instance p-+-p-unary--
			   (x (eval-poly pul (p-* u u)))
			   (y (p-* u (eval-poly pur (p-* u u)))))
	   :in-theory (disable p-+-p-unary--))))

;; The most important step is to introduce the constrained function p-omega
;; which will have the property (p-omega n) = < u | -u > used in the previous
;; lemma.  P-omega is actually a family of vectors.  In particular, (p-omega n)
;; is a numeric vector of length 2^n.  Because we do not have a square root
;; function, we constrain two functions, p-omega and p-omega-sqrt, with the
;; needed properties.

(encapsulate
 ((p-omega (n) t)
  (p-omega-sqrt (n) t))

 ;; This definition of p-omega is needed only to provide a witness function to
 ;; the constrains about p-omega.  It simply defines p-omega as the function
 ;; that generates 2^n zeros.

 (local
  (defun p-omega (n)
    (if (zp n)
	0
      (p-tie (p-omega (1- n)) (p-omega (1- n))))))
 (local (in-theory (disable (p-omega))))

 ;; Since p-omega has only zeros, its square root is simply p-omega itself.

 (local
  (defun p-omega-sqrt (n)
    (p-omega n)))
 (local (in-theory (disable (p-omega-sqrt))))

 ;; The following theorem trivializes the constrains of p-omega, namely that
 ;; the witness for p-omega satisfies p-omega = -p-omega.  This is trivially
 ;; true, since the witness p-omega is the zero vector.  This is clearly a
 ;; _local_ theorem, i.e., one which is not expected to be true of the
 ;; constrained p_omega.

 (local
  (defthm p-unary---omega
    (equal (p-unary-- (p-omega n))
	   (p-omega n))))

 ;; The first constraint on p-omega is that the base case returns a number.

 (defthm numberp-omega-0
   (acl2-numberp (p-omega 0))
   :rule-classes (:type-prescription :rewrite))

 ;; Another constraint on p-omega is that for n positive, (p-omega n) equals
 ;; < (p-omega-sqrt n) | -(p-omega-sqrt n) >.

 (defthm p-omega->tie-minus
   (implies (not (zp n))
	    (equal (p-omega n)
		   (p-tie (p-omega-sqrt (1- n))
			  (p-unary--
			   (p-omega-sqrt (1- n))))))
   :rule-classes nil)

 ;; The last constraint merely asserts that p-omega-sqrt is indeed the square
 ;; root of p-omega.

 (defthm p-omega-sqrt**2
       (equal (p-* (p-omega-sqrt n)
                   (p-omega-sqrt n))
              (p-omega n)))
 )

;; We have already shown how to expand (eval-poly x v) for a vector v with the
;; form v = < u | -u >.  Also, we know (p-omega n) = < u | -u > for some u,
;; specifically for u = (p-omega-sqrt (1- n)).  We combine these two theorems
;; to give the expansion of (eval-poly x (p-omega n)).

;; First, we prove a useful lemma that simply instantiates the u in the theorem
;; about < u | -u > with (p-omega-sqrt (1- n)).

(defthm eval-poly-omega-n-aux
  (implies (powerlist-p x)
	   (equal (eval-poly x
			     (p-tie (p-omega-sqrt (1- n))
				    (p-unary-- (p-omega-sqrt (1- n)))))
		  (p-tie (p-+ (eval-poly (p-unzip-l x) (p-omega (1- n)))
			      (p-* (p-omega-sqrt (1- n))
				   (eval-poly (p-unzip-r x) (p-omega (1- n)))))
			 (p-- (eval-poly (p-unzip-l x) (p-omega (1- n)))
			      (p-* (p-omega-sqrt (1- n))
				   (eval-poly (p-unzip-r x)
					      (p-omega (1- n))))))))
  :rule-classes nil)

;; Now, we can prove the actual theorem about (eval-poly x (p-omega n)).

(defthm eval-poly-omega-n
  (implies (and (powerlist-p x)
		(not (zp n)))
	   (let ((n1 (1- n)))
	     (equal (eval-poly x (p-omega n))
		    (p-tie (p-+ (eval-poly (p-unzip-l x)
					   (p-omega n1))
				(p-* (p-omega-sqrt n1)
				     (eval-poly
				      (p-unzip-r x)
				      (p-omega n1))))
			   (p-- (eval-poly (p-unzip-l x)
					   (p-omega n1))
				(p-* (p-omega-sqrt n1)
				     (eval-poly
				      (p-unzip-r x)
				      (p-omega n1))))))))
  :hints (("Goal"
	   :use (eval-poly-omega-n-aux p-omega->tie-minus)
	   :hands-off (eval-poly p-omega p-omega-sqrt)))
  :rule-classes nil)

(defun p-depth (x)
  "The depth of a powerlist is the number of ties in its left branch."
  (if (powerlist-p x)
      (1+ (p-depth (p-untie-l x)))
    0))
(in-theory (disable (p-depth)))

;; We have to prove a silly theorem about depth.  Namely, if a powerlist is non
;; scalar, then its depth is non-zero.

(defthm powerlist->non-zero-depth
  (implies (powerlist-p x)
	   (not (zp (p-depth x)))))

;; Now that we know that for a powerlist-p x its p-depth is non-zero, we can
;; remove the hypothesis that n > 0 in (p-omega n) since we are interested only
;; in (p-omega (p-depth x)) anyway.

(defthm eval-poly-omega-depth
  (let* ((n (p-depth x))
	 (n1 (1- n)))
    (implies (powerlist-p x)
	     (equal (eval-poly x (p-omega n))
		    (p-tie (p-+ (eval-poly (p-unzip-l x)
					   (p-omega n1))
				(p-* (p-omega-sqrt n1)
				     (eval-poly
				      (p-unzip-r x)
				      (p-omega n1))))
			   (p-- (eval-poly (p-unzip-l x)
					   (p-omega n1))
				(p-* (p-omega-sqrt n1)
				     (eval-poly
				      (p-unzip-r x)
				      (p-omega n1))))))))
  :hints (("Goal"
	   :use (:instance eval-poly-omega-n (n (p-depth x)))))
  :rule-classes nil)

(defun p-ft-omega (x)
  "The Fourier Transform of a vector x is defined as the value of evaluating
  the vector x as a polynomial on the vector w = (p-omega (p-depth x)).  The
  vector w will have as many elements as x.  Moreover, it is constrained to
  have special properties.  See the documentation for p-omega."
  (eval-poly x (p-omega (p-depth x))))
(in-theory (disable (p-ft-omega)))

;; We defined p-depth in terms of tie, but we are also interested in recursing
;; in terms of zip.  Thus, we have to prove a theorem about the depth of
;; unzipped powerlists.

(defthm p-depth-unzip
      (implies (and (powerlist-p x)
                    (p-regular-p x))
               (and (equal (p-depth (p-unzip-l x))
                           (1- (p-depth x)))
                    (equal (p-depth (p-unzip-r x))
                           (1- (p-depth x))))))

;; The theorem eval-poly-omega-depth gives us a good characterization of
;; (eval-poly x (p-omega (p-depth x))).  As it turns out, this is precisely the
;; definition of (p-ft-omega x), so we can rewrite eval-poly-omega-depth in
;; terms of p-ft-omega.  This gives the following useful lemma.

(defthm ft-omega-lemma
  (implies (and (powerlist-p x)
		(p-regular-p x))
	   (equal (p-ft-omega x)
		  (p-tie (p-+ (p-ft-omega (p-unzip-l x))
			      (p-* (p-omega-sqrt
				    (1- (p-depth x)))
				   (p-ft-omega
				    (p-unzip-r x))))
			 (p-- (p-ft-omega (p-unzip-l x))
			      (p-* (p-omega-sqrt
				    (1- (p-depth x)))
				   (p-ft-omega
				    (p-unzip-r x)))))))
  :hints (("Goal" :in-theory (disable eval-poly-lemma))
; Matt K. v7-1 mod for avoiding "Goal'", 2/13/2015: "Goal''" changed to "Goal'".
	  ("Goal'" :use eval-poly-omega-depth))
  :rule-classes nil)

(defun p-fft-omega (x)
  "The Fast Fourier Transform is a fast way of computing the Fourier Transform."
  (if (powerlist-p  x)
      (p-tie (p-+ (p-fft-omega (p-unzip-l x))
		  (p-* (p-omega-sqrt (1- (p-depth x)))
		       (p-fft-omega (p-unzip-r x))))
	     (p-- (p-fft-omega (p-unzip-l x))
		  (p-* (p-omega-sqrt (1- (p-depth x)))
		       (p-fft-omega (p-unzip-r x)))))
    (fix x)))
(in-theory (disable (p-fft-omega)))

;; We can now prove the main theorem, namely that the Fast Fourier Transform
;; returns the same result as the Fourier Transform.  This theorem is a simple
;; corollary of ft-omega-lemma.

(defthm fft-omega->ft-omega
  (implies (p-regular-p x)
	   (equal (p-fft-omega x)
		  (p-ft-omega x)))
  :hints (("Subgoal *1/4"
	   :use ft-omega-lemma
	   :hands-off (eval-poly p-omega p-omega-sqrt p-+ p--))))

