(in-package "ACL2")

; Eric Smith, David Russinoff, with contributions and suggestions by Matt Kaufmann
; AMD, June 2001
;this file was previously called repsproofs.lisp

(include-book "rtl")
(include-book "float") ;to get the defns...

(local (include-book "ereps-proofs"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))
;(set-inhibit-warnings) ; restore theory warnings (optional)


; bias of a q bit exponent field is 2^(q-1)-1
(defund bias (q) (- (expt 2 (- q 1)) 1) )

;;Encoding of floating-point numbers with explicit leading one:
;;bit vectors of length p+q+1, consisting of 1-bit sign field,
;;q-bit exponent field (bias = 2**(q-1)-1), and p-bit significand field.

(defund esgnf  (x p q) (bitn x (+ p q)))
(defund eexpof (x p q) (bits x (1- (+ p q)) p))
(defund esigf  (x p)   (bits x (1- p) 0))

;;;**********************************************************************
;;;                       REPRESENTABLE NUMBERS
;;;**********************************************************************

(defund erepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (bvecp (+ (expo x) (bias q)) q)
       (exactp x p)))


;;;**********************************************************************
;;;                      VALID ENCODINGS
;;;**********************************************************************

(defund eencodingp (x p q)
  (and (bvecp x (+ p q 1))
       (= (bitn x (- p 1)) 1)))


;;;**********************************************************************
;;;                       EENCODE
;;;**********************************************************************



; sig, expo, and sgn are defined in float.lisp


;bozo disable!
(defund eencode (x p q)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    1
	    (+ (expo x) (bias q))
	    q)
       (1+ q)
       (* (sig x) (expt 2 (- p 1)))
       p) )




;;;**********************************************************************
;;;                       EDECODE
;;;**********************************************************************


(defund edecode (x p q)
  (* (if (= (esgnf x p q) 0) 1 -1)
     (esigf x p)
     (expt 2 (+ 1 (- p) (eexpof x p q) (- (bias q))))))



;;;**********************************************************************
;;;                      Encoding and Decoding are Inverses
;;;**********************************************************************

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
;                (> p 0)
                (integerp q)
 ;               (> q 0)
                )
           (equal (edecode (eencode x p q) p q)
                  x )))

(defthm eencode-edecode
  (implies (and (eencodingp x p q)
                (integerp p)
                (>= p 0)
                (integerp q)
                (> q 0))
           (equal (eencode (edecode x p q) p q)
                  x )))

(defthm expo-edecode
  (implies (and (eencodingp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (equal (expo (edecode x p q))
                  (- (eexpof x p q) (bias q))
                  )))

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

(defthm eencodingp-not-zero
  (implies (and (eencodingp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (not (equal (edecode x p q) 0))))

(defund rebias-expo (expo old new)
  (+ expo (- (bias new) (bias old))))

;;I actually needed all four of the following lemmas, although I would have thought
;;that the two bvecp lemmas would be enough.

(defthm natp-rebias-up
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (natp (rebias-expo x m n)))
    :hints (("goal" :in-theory (e/d ( expt-split rebias-expo bvecp natp bias
                                                  ) (expt-compare))
		  :use (:instance expt-weak-monotone (n m) (m n)))))

(defthm natp-rebias-down
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (natp (rebias-expo x n m)))
    :hints (("goal" :in-theory (enable rebias-expo bvecp natp bias))))

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

(defthm rebias-up
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x m))
	     (equal (rebias-expo x m n)
		    (cat (cat (bitn x (1- m))
			      1
			      (mulcat 1 (- n m) (lnot (bitn x (1- m)) 1))
			      (- n m))
			 (1+ (- n m))
			 (bits x (- m 2) 0)
			 (1- m))))
  :rule-classes ())

(defthm rebias-down
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
			 (1- m))))
  :rule-classes ())

