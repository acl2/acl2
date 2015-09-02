; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

(set-enforce-redundancy t)

(local (include-book "../support/top/top"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

;; From bits.lisp:

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defund bits (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defund binary-cat (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

;; We define a macro, CAT, that takes a list of a list X of alternating data values
;; and sizes.  CAT-SIZE returns the formal sum of the sizes.  X must contain at
;; least 1 data/size pair, but we do not need to specify this in the guard, and
;; leaving it out of the guard simplifies the guard proof.

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defun cat-size (x)
  (declare (xargs :guard (and (true-listp x) (evenp (length x)))))
  (if (endp (cddr x))
      (cadr x)
    (formal-+ (cadr x)
	      (cat-size (cddr x)))))

(defmacro cat (&rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(bits ,(car x) ,(formal-+ -1 (cadr x)) 0))
        ((endp (cddddr x))
         `(binary-cat ,@x))
        (t
         `(binary-cat ,(car x)
                      ,(cadr x)
                      (cat ,@(cddr x))
                      ,(cat-size (cddr x))))))

(defund mulcat (l n x)
  (declare (xargs :guard (and (integerp l) (< 0 l) (acl2-numberp n) (natp x))))
  (mbe :logic (if (and (integerp n) (> n 0))
                  (cat (mulcat l (1- n) x)
                       (* l (1- n))
                       x
                       l)
                0)
       :exec  (cond ((eql n 1)
                     (bits x (1- l) 0))
                    ((and (integerp n) (> n 0))
                     (cat (mulcat l (1- n) x)
                          (* l (1- n))
                          x
                          l))
                    (t 0))))

;; From float.lisp:

(defund sgn (x)
  (declare (xargs :guard t))
  (if (or (not (rationalp x)) (equal x 0))
      0
    (if (< x 0) -1 +1)))

(defund expo (x)
  (declare (xargs :guard t
                  :measure (:? x)))
  (cond ((or (not (rationalp x)) (equal x 0)) 0)
	((< x 0) (expo (- x)))
	((< x 1) (1- (expo (* 2 x))))
	((< x 2) 0)
	(t (1+ (expo (/ x 2))))))

(defund sig (x)
  (declare (xargs :guard t))
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

(defund exactp (x n)
  (integerp (* (sig x) (expt 2 (1- n)))))


;;;***************************************************************
;;;          REPRESENTATIONS WITH EXPLICIT MSB
;;;***************************************************************

(defund bias (q) (- (expt 2 (- q 1)) 1) )

(defthm bias-non-negative-integerp-type-prescription
  (implies (and (case-split (integerp q))
                (case-split (< 0 q)))
           (and (integerp (bias q))
                (>= (bias q) 0)))
  :rule-classes :type-prescription)

;; Should these be disabled?
(defun esgnf  (x p q) (bitn x (+ p q)))
(defun eexpof (x p q) (bits x (1- (+ p q)) p))
(defun esigf  (x p)   (bits x (1- p) 0))

(defund erepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (bvecp (+ (expo x) (bias q)) q)
       (exactp x p)))

(defund eencodingp (x p q)
  (and (bvecp x (+ p q 1))
       (= (bitn x (- p 1)) 1)))

(defund eencode (x p q)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    1
	    (+ (expo x) (bias q))
	    q)
       (1+ q)
       (* (sig x) (expt 2 (- p 1)))
       p) )

(defund edecode (x p q)
  (* (if (= (esgnf x p q) 0) 1 -1)
     (esigf x p)
     (expt 2 (+ 1 (- p) (eexpof x p q) (- (bias q))))))

(defthm eencodingp-not-zero
    (implies (and (eencodingp x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (not (equal (edecode x p q) 0))))

(defthm erepp-edecode
    (implies (and (eencodingp x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (erepp (edecode x p q) p q)))

(defthm eencodingp-eencode
    (implies (and (erepp x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (eencodingp (eencode x p q) p q) ))

(defthm edecode-eencode
    (implies (and (erepp x p q)
		  (integerp p)
;		  (> p 0)
		  (integerp q)
	;	  (> q 0)
                  )
	     (equal (edecode (eencode x p q) p q)
		    x)))

(defthm eencode-edecode
    (implies (and (eencodingp x p q)
		  (integerp p)
		  (>= p 0)
		  (integerp q)
		  (> q 0))
	     (equal (eencode (edecode x p q) p q)
		    x)))

(defthm expo-edecode
    (implies (and (eencodingp x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (equal (expo (edecode x p q))
		    (- (eexpof x p q) (bias q)))))

(defthm sgn-edecode
    (implies (and (eencodingp x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (equal (sgn (edecode  x p q))
		    (if (= (esgnf x p q) 0) 1 -1))))

(defthm sig-edecode
    (implies (and (eencodingp  x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (equal (sig (edecode  x p q))
		    (/ (esigf x p) (expt 2 (- p 1))))))

(defund rebias-expo (expo old new)
  (+ expo (- (bias new) (bias old))))

(defthm natp-rebias-up
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (natp (rebias-expo x m n))))

(defthm natp-rebias-down
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (natp (rebias-expo x n m))))

(defthm bvecp-rebias-up
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (bvecp (rebias-expo x m n) n)))

(defthm bvecp-rebias-down
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (bvecp (rebias-expo x n m) m)))

(defthmd rebias-lower
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (equal (rebias-expo x n m)
		    (cat (bitn x (1- n))
			 1
			 (bits x (- m 2) 0)
			 (1- m)))))

(defthmd rebias-higher
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x m))
	     (equal (rebias-expo x m n)
		    (cat (cat (bitn x (1- m))
			      1
			      (mulcat 1 (- n m) (bitn (lognot x) (1- m)))
			      (- n m))
			 (1+ (- n m))
			 (bits x (- m 2) 0)
			 (1- m)))))


;;;***************************************************************
;;;          REPRESENTATIONS WITH IMPLICIT MSB
;;;***************************************************************

;;Bit vectors of length p+q, consisting of 1-bit sign field, q-bit
;;exponent field (bias = 2**(q-1)-1), and (p-1)-bit significand field,
;;where p > 1.

;;Field extractors:

(defun isgnf (x p q) (bitn x (1- (+ p q))))
(defun iexpof (x p q) (bits x (- (+ p q) 2) (1- p)))
(defun isigf (x p) (bits x (- p 2) 0))


;Representable numbers (normals and denormal):

(defund nrepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (< 0 (+ (expo x) (bias q)))
       (< (+ (expo x) (bias q)) (- (expt 2 q) 1))
       (exactp x p)))

(defund drepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (<= (- 2 p) (+ (expo x) (bias q)))
       (<= (+ (expo x) (bias q)) 0)
       ;number of bits available in the sig field = p - 1 - ( - bias - expo(x))
       (exactp x (+ -2 p (expt 2 (- q 1)) (expo x)))))

(defund irepp (x p q)
  (or (nrepp x p q)
      (drepp x p q)))


;;Valid encodings:

(defund nencodingp (x p q)
  (and (bvecp x (+ p q))
       (< 0 (iexpof x p q))
       (< (iexpof x p q) (- (expt 2 q) 1))))

(defund dencodingp (x p q)
  (and (bvecp x (+ p q))
       (= (iexpof x p q) 0)
       (not (= (isigf x p) 0))))

(defund iencodingp (x p q)
  (or (nencodingp x p q)
      (dencodingp x p q)))

(defthm not-both-nrepp-and-drepp
    (implies (irepp x p q)
	     (iff (nrepp x p q) (not (drepp x p q))))
  :rule-classes ())

(defthm not-both-nencodingp-and-dencodingp
    (implies (iencodingp x p q)
	     (iff (nencodingp x p q) (not (dencodingp x p q))))
  :rule-classes ())


;;Encoding functions:

(defund nencode (x p q)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    1
            (+ (expo x) (bias q))
            q)
       (1+ q)
       (* (- (sig x) 1) (expt 2 (- p 1)))
       (- p 1)))

(defund dencode (x p q)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    1
            0
            q)
       (1+ q)
       (* (sig x) (expt 2 (+ -2 p (expo x) (bias q))))
       (- p 1)))

(defund iencode (x p q)
  (cond ((nrepp x p q)
	 (nencode x p q))
	((drepp x p q)
	 (dencode x p q))))


;;Decoding functions:

(defund ndecode (x p q)
  (* (if (= (isgnf x p q) 0) 1 -1)
     (+ (expt 2 (- (iexpof x p q) (bias q)))
        (* (isigf x p)
           (expt 2 (+ 1 (iexpof x p q) (- (bias q)) (- p)))))))

(defund ddecode (x p q)
  (* (if (= (isgnf x p q) 0) 1 -1)
     (isigf x p)
     (expt 2 (+ 2 (- (bias q)) (- p)))))

(defund idecode (x p q)
  (cond ((nencodingp x p q)
	 (ndecode x p q))
	((dencodingp x p q)
	 (ddecode x p q))))


;;Field extraction:

(defthm sgn-ndecode
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sgn (ndecode x p q))
		    (if (= (isgnf x p q) 0) 1 -1))))

(defthm expo-ndecode
    (implies (and (nencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (expo (ndecode x p q))
		    (- (iexpof x p q) (bias q)))))

(defthm sig-ndecode
    (implies (and (nencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sig (ndecode x p q))
		    (+ 1 (/ (isigf x p) (expt 2 (- p 1)))))))

(defthm sgn-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sgn (ddecode x p q))
		    (if (= (isgnf x p q) 0) 1 -1))))

(defthm expo-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (expo (ddecode x p q))
		    (+ 2 (- p) (- (bias q)) (expo (isigf x p))))))

(defthm sig-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sig (ddecode x p q))
		    (sig (isigf x p)))))

(defthm sgn-idecode
    (implies (and (iencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal
	      (sgn (idecode x p q))
	      (if (= (isgnf x p q) 0) 1 -1))))

(defthm expo-idecode
    (implies (and (iencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal
	      (expo (idecode x p q))
	      (cond ((nencodingp x p q)
		     (- (iexpof x p q) (bias q)))
		    ((dencodingp x p q)
		     (+ 2 (- p) (- (bias q)) (expo (isigf x p))))))))

(defthm sig-idecode
    (implies (and (iencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sig (idecode x p q))
		    (cond ((nencodingp x p q)
			   (+ 1 (/ (isigf x p) (expt 2 (- p 1)))))
			  ((dencodingp x p q)
			   (sig (isigf x p)))))))

;;Inversions:

(defthm dencodingp-dencode
    (implies (and (drepp x p q)
		  (integerp p)
		  (integerp q)
		  (> q 0))
	     (dencodingp (dencode x p q) p q)))

(defthm iencodingp-iencode
    (implies (and (irepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (iencodingp (iencode x p q) p q)))

(defthm nrepp-ndecode
    (implies (and (nencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (nrepp (ndecode x p q) p q)))

(defthm drepp-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (drepp (ddecode x p q) p q)))

(defthm irepp-idecode
    (implies (and (iencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (irepp (idecode x p q) p q)))

(defthm nencodingp-nencode
    (implies (and (nrepp x p q)
                  (integerp p)
                  (> p 1)
                  (integerp q)
                  (> q 0))
             (nencodingp (nencode x p q) p q)))

(defthm ndecode-nencode
    (implies (and (nrepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (ndecode (nencode x p q) p q)
		    x)))

(defthm ddecode-dencode
    (implies (and (drepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (ddecode (dencode x p q) p q)
		    x)))

(defthm idecode-iencode
    (implies (and (irepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (idecode (iencode x p q) p q)
		    x)))

(defthm nencode-ndecode
    (implies (and (nencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (nencode (ndecode x p q) p q)
		    x)))

(defthm dencode-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (dencode (ddecode x p q) p q)
		    x)))

(defthm iencode-idecode
    (implies (and (iencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (iencode (idecode x p q) p q)
		    x)))

;; Smallest positive normal:

(defund spn (q)
  (expt 2 (- 1 (bias q))))

(defthmd positive-spn
  (> (spn q) 0)
  :rule-classes ( :linear))

(defthmd nrepp-spn
  (implies (and (integerp p)
                (> p 0)
                (integerp q)
                (> q 1))
           (nrepp (spn q) p q)))

(defthmd smallest-spn
  (implies (and (nrepp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 1))
           (>= (abs x) (spn q)))
  :rule-classes
  ((:rewrite :match-free :once)))

;; Smallest positive denormal:

(defund spd (p q)
     (expt 2 (+ 2 (- (bias q)) (- p))))

(defthm positive-spd
  (implies (and (integerp p)
                (> p 1)
                (> q 0))
           (> (spd p q) 0))
  :rule-classes :linear)

(defthmd drepp-spd
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (drepp (spd p q) p q)))

(defthmd smallest-spd
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (drepp r p q))
           (>= (abs r) (spd p q))))

(defthmd spd-mult
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (> r 0)
		(rationalp r)
		(= m (/ r (spd p q))))
	   (iff (drepp r p q)
		(and (natp m)
		     (<= 1 m)
		     (< m (expt 2 (1- p)))))))
