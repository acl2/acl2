#|

This is in an ACL2 "book" with definitions and theorems about a concrete
correctness proof of the Fast Fourier Transform.  The proof uses the abstract
proof in fft-omega.lisp.  In that ACL2 book, it is shown that the FFT algorithm
works correctly, provided the vector of omegas has the property w = < u || -u >
for some u.  In this book, we prove that the vector formed by taking the powers
of the principla roots of 1 can be written in this form.  I.e., by taking the
vector omega as normally defined for the Fourier Transform.

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

; cert_param: (uses-acl2r)

(include-book "fft-omega")

;; We begin by axiomatizing the functions sine and cosine, as well as the
;; constant pi.  We don't need too many axioms about these; however, it is hard
;; to come up with a witness function, so it is easier to introduce these
;; functions axiomatically.

(acl2::defstub acl2-pi () t)
(acl2::defstub acl2-sine (x) t)
(acl2::defstub acl2-cosine (x) t)

;; The first axiom is simply that all the functions are real-valued, and that
;; pi is a positive real.

(defaxiom type-prescriptions
  (and (realp (acl2-sine x))
       (realp (acl2-cosine x))
       (realp (acl2-pi))
       (< 0 (acl2-pi))))

;; The next axiom defines sine(pi) = 0 and cosine(pi) = -1.

(defaxiom values-at-pi
  (and (equal (acl2-sine (acl2-pi)) 0)
       (equal (acl2-cosine (acl2-pi)) -1)))

;; We also assume the sine of sums law:
;; sine(x+y) = sine(x)*cosine(y) + cosine(x)*sine(y)

(defaxiom sine-of-sums
  (equal (acl2-sine (+ x y))
	 (+ (* (acl2-sine x) (acl2-cosine y))
	    (* (acl2-cosine x) (acl2-sine y)))))

;; The last assumption is the cosine of sums law:
;; cosine(x+y) = cosine(x)*cosine(y) - sine(x)*sine(y)

(defaxiom cosine-of-sums
  (equal (acl2-cosine (+ x y))
	 (- (* (acl2-cosine x) (acl2-cosine y))
	    (* (acl2-sine x) (acl2-sine y)))))

;; We are now finished with the trigonometric axioms.  Next, we will define the
;; basic functions needed to generate the standard omega vector in the Fourier
;; Transform.

(defun p-halve (x)
  "P-halve halves all the elements of a powerlist."
  (if (powerlist-p x)
      (p-tie (p-halve (p-untie-l x)) (p-halve (p-untie-r x)))
    (/ x 2)))
(in-theory (disable (p-halve)))

(defun p-offset (x p)
  "P-offset adds a constant x to all elements of a powerlist p."
  (if (powerlist-p p)
      (p-tie (p-offset x (p-untie-l p)) (p-offset x (p-untie-r p)))
    (+ x p)))
(in-theory (disable (p-offset)))

(defun p-exponents (n)
  "P-exponents returns 2^n evenly spaced points between 0 and 2*pi.k
  For example,
  (p-exponents 1) = < pi, 2*pi >
  (p-exponents 2) = < pi/2, pi, 3*pi/2, 2*pi >"
  (if (acl2::zp n)
      (* 2 (acl2-pi))
    (let ((sqrt-expnts (p-halve (p-exponents (1- n)))))
      (p-tie sqrt-expnts
	     (p-offset (acl2-pi) sqrt-expnts)))))
(in-theory (disable (p-exponents)))

(defun complex-expt (x)
  "Complex-expt returns e^{i*x} for a real number x.  It uses the formula
  e^{i*x} = cosine(x) + i*sine(x)"
  (complex (acl2-cosine x) (acl2-sine x)))
(in-theory (disable (complex-expt)))

(defun p-complex-expt (x)
  "Returns the complex-expt of all elements of a powerlist."
  (if (powerlist-p x)
      (p-tie (p-complex-expt (p-untie-l x)) (p-complex-expt (p-untie-r x)))
    (complex-expt x)))
(in-theory (disable (p-complex-expt)))

(defun p-expt-omega (n)
  "The standard definition of omega in the Fourier Transform.  It is given by
  repeated powers of the 2^nth principal root of 1.  For example,
  (p-expt-omega 1) = < e^i*pi, e^i*2*pi >
  (p-expt-omega 2) = < e^i*pi/2, e^i*pi, e^i*3*pi/2, e^i*2*pi >"
  (p-complex-expt (p-exponents n)))
(in-theory (disable (p-expt-omega)))

(defun p-expt-omega-sqrt (n)
  "The pointwise square root of p-expt-omega."
  (p-complex-expt (p-halve (p-exponents n))))
(in-theory (disable (p-expt-omega-sqrt)))

;; We will have to do a little bit of complex arithmetic, something which ACL2
;; is remarkably ignorant of.  So, we will give it a little help.  An important
;; lemma reduces the complex square (x+i*y)^2 into (x^2-y^2)+i*(2xy).  We will
;; prove that first.

(encapsulate
 ()

 ;; To prove the rewrite rule for complex squares, we start with the algebraic
 ;; rewriting using the constant \#c(0 1), better known in complex arithmetic as
 ;; i=sqrt(-1).  In fact, the key part of the proof, which ACL2 finds by
 ;; itself, is that \#c(0 1) * \#c(0 1) = i * i = -1.

 (local
  (defthm complex-square-definition-1
    (equal (* (+ x (* #c(0 1) y))
	      (+ x (* #c(0 1) y)))
	   (+ (- (* x x) (* y y))
	      (* #c(0 1) (+ (* x y) (* x y)))))
    :rule-classes nil))

 ;; Now that we have the basic result using the constant i, we convert the
 ;; conclusion of the theorem into the more natural (complex x y) notation.

 (local
  (defthm complex-square-definition-2
    (implies (and (realp x)
		  (realp y))
	     (equal (* (+ x (* #c(0 1) y))
		       (+ x (* #c(0 1) y)))
		    (complex (- (* x x) (* y y))
			     (+ (* x y) (* x y)))))
    :hints (("Goal"
	     :use ((:instance complex-square-definition-1)
		   (:instance acl2::complex-definition
			      (acl2::x (- (* x x) (* y y)))
			      (acl2::y (+ (* x y) (* x y)))))))
    :rule-classes nil))

 ;; Finally, we can prove our intended theorem, with both the conclusion and
 ;; hypothesis using the function (complex x y) instead of the constant i.

 (defthm complex-square-definition
   (implies (and (realp x)
		 (realp y))
	    (equal (* (complex x y) (complex x y))
		   (complex (- (* x x) (* y y))
			    (+ (* x y) (* x y)))))
   :hints (("Goal"
	    :use ((:instance acl2::complex-definition
			     (acl2::x x)
			     (acl2::y y))
		  (:instance complex-square-definition-2))))))

;; It seems shameful to those who haven't written a theorem prover that the
;; term x/2 + x/2 is not immediately reduced to x.  Sadly, ACL2 doesn't, so we
;; prove the following rewrite rule to help.

(defthm sum-of-halves
  (implies (acl2::acl2-numberp x)
	   (equal (+ (* 1/2 x) (* 1/2 x)) x)))

;; Using our rewrite rule about x/2 + x/2 = x, we prove that e^{x/2}*e^{x/2} is
;; equal to e^x.

(defthm complex-expt-/-2
  (implies (acl2::acl2-numberp x)
	   (equal (* (complex-expt (* 1/2 x)) (complex-expt (* 1/2 x)))
		  (complex-expt x)))
  :hints (("Goal"
	   :use ((:instance sine-of-sums (x (* 1/2 X)) (y (* 1/2 X)))
		 (:instance cosine-of-sums (x (* 1/2 X)) (y (* 1/2 X))))
	   :in-theory (disable sine-of-sums cosine-of-sums))))

;; We are preparing to prove theorems about the powerlist p-expt-omega.
;; Unfortunately, the key lemmas we need are true only for numeric arguments,
;; so we need to extend this property to powerlists.

(defun p-acl2-number-list (x)
  "P-acl2-number-list is true of a powerlist x iff all its members are numeric."
  (if (powerlist-p x)
      (and (p-acl2-number-list (p-untie-l x))
	   (p-acl2-number-list (p-untie-r x)))
    (acl2::acl2-numberp x)))
(in-theory (disable (p-acl2-number-list)))

;; Now, we can generalize the theorem that e^{x/2}*e{x/2} = e^x into
;; powerlists.  The "x/2" is replaced by the powerlist function p-halve, e^x by
;; the powerlist exponentiation function p-complex-expt, and the multiplication
;; by the powerlist pointwise multiplication p-*.

(defthm p-complex-expt-halve
  (implies (p-acl2-number-list x)
	   (equal (p-* (p-complex-expt (p-halve x))
		       (p-complex-expt (p-halve x)))
		  (p-complex-expt x)))
  :hints (("Goal" :in-theory (disable complex-expt))))

;; Next on the agenda will be to prove that p-expt-omega-sqrt is in fact the
;; square root of p-expt-omega, as required.  The previous theorem is the key
;; lemma in that proof, but first we must establish the hypothesis that
;; p-exponents returns a numeric powerlists.  We do so here.

(defthm number-list-exponents-n
  (p-acl2-number-list (p-exponents n)))

;; Now, we can prove one of the encapsulation obligations, namely that
;; p-expt-omega-sqrt is the square root of p-expt-omega.

(defthm p-expt-omega-sqrt**2
  (equal (p-* (p-expt-omega-sqrt n)
	      (p-expt-omega-sqrt n))
	 (p-expt-omega n))
  :hints (("Goal"
	   :use (:instance p-complex-expt-halve (x (p-exponents n)))
	   :in-theory (disable p-complex-expt-halve))))

;; We are done with p-expt-omega and p-exponents, so we disable those
;; definitions.

(in-theory (disable (p-expt-omega)))
(in-theory (disable (p-exponents)))

;; Since p-expt-omega is disabled, the following theorem, that (p-expt-omega 0)
;; is numeric, is no longer trivial.

(defthm numberp-expt-omega-0
  (acl2::acl2-numberp (p-expt-omega 0))
  :rule-classes (:type-prescription :rewrite))

;; We are trying to prove that p-expt-omega can be written as < u || -u >.
;; First, we require a simple fact about unary minus in complex arithmetic.

(defthm complex-unary
  (implies (and (realp ace)
		(realp ase))
	   (equal (complex (- ace) (- ase))
		  (- (complex ace ase))))
  :hints (("Goal"
	   :use ((:instance acl2::complex-definition
			    (acl2::x ace)
			    (acl2::y ase))
		 (:instance acl2::complex-definition
			    (acl2::x (- ace))
			    (acl2::y (- ase)))))))


;; The following sad lemma is needed because the type-system can't establish
;; (realp x) in some cases.  This can only be established by the rewriter, but
;; the built-in inference rule allowing us to deduce "number" from "real" is
;; not a rewrite rule, only a type-prescription, so it's not available to the
;; rewriter!

(defthm realp-implies-acl2-numberp
  (implies (realp x)
	   (acl2::acl2-numberp x)))

;; Here is an important lemma.  In order to establish that p-expt-omega can be
;; written as < u | -u >, we first show that e^{pi+x} = -e^x.  We can do so for
;; all the elements of a powerlist at once.  So now, if we have u = e^v for
;; some powerlist v, then u^{pi+v} = -u.  The needed "v" will be the result of
;; p-exponents.

(defthm complex-expt-offset-pi
  (equal (p-complex-expt (p-offset (acl2-pi) expnts))
	 (p-unary-- (p-complex-expt expnts))))


;; Finally, we cna prove the fact that p-expt-omega is equal to < u | -u > for
;; u equal to p-expt-sqrt-omega.  This is the last constrain on p-omega and
;; p-sqrt-omega that we will need to invoke the results from the fft-omega ACL2
;; book.

(defthm p-expt-omega->tie-minus
  (implies (not (acl2::zp n))
	   (equal (p-expt-omega n)
		  (p-tie (p-expt-omega-sqrt (1- n))
			 (p-unary-- (p-expt-omega-sqrt (1- n))))))
  :rule-classes nil)

(defun p-ft-expt-omega (x)
  "The Fourier Transform of a powerlist x, using the powers of the principal
  roots of 1 as the vector omega."
  (eval-poly x (p-expt-omega (p-depth x))))
(in-theory (disable (p-ft-expt-omega)))

(defun p-fft-expt-omega (x)
  "The Fast Fourier Transform of a powerlist x, using the powers of the
  principal roots of 1 as the vector omega."
  (if (powerlist-p x)
      (p-tie (p-+ (p-fft-expt-omega (p-unzip-l x))
		  (p-* (p-expt-omega-sqrt (1- (p-depth x)))
		       (p-fft-expt-omega (p-unzip-r x))))
	     (p-- (p-fft-expt-omega (p-unzip-l x))
		  (p-* (p-expt-omega-sqrt (1- (p-depth x)))
		       (p-fft-expt-omega (p-unzip-r x)))))
    (acl2::fix x)))
(in-theory (disable (p-fft-expt-omega)))

;; Using the abstract correctness proof of FFT in fft-omega.lisp, we can now
;; show that the FFT based on powers of the roots of 1 correctly computes the
;; Fourier Transform.

(defthm fft-expt-omega->ft-expt-omega
  (implies (p-regular-p x)
	   (equal (p-fft-expt-omega x)
		  (p-ft-expt-omega x)))
  :hints (("Goal"
	   :by (:functional-instance fft-omega->ft-omega
				     (p-fft-omega p-fft-expt-omega)
				     (p-ft-omega p-ft-expt-omega)
				     (p-omega p-expt-omega)
				     (p-omega-sqrt p-expt-omega-sqrt)))))
