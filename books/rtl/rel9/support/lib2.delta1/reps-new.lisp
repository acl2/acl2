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

(include-book "log-new")
(include-book "float-new")

(local (include-book "reps-new-proofs"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))


;;;***************************************************************
;;;          REPRESENTATIONS WITH EXPLICIT MSB
;;;***************************************************************

(defund bias (q) (- (expt 2 (- q 1)) 1) )

;BOZO add rewrite rule?
(defthm bias-non-negative-integerp-type-prescription
  (implies (and (case-split (integerp q))
                (case-split (< 0 q)))
           (and (integerp (bias q))
                (>= (bias q) 0)))
  :rule-classes :type-prescription)

;BOZO disable?
(defun esgnf_alt  (x p q) (bitn_alt x (+ p q)))


(defun eexpof_alt (x p q) (bits_alt x (1- (+ p q)) p))


(defun esigf_alt  (x p)   (bits_alt x (1- p) 0))

(defund erepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (bvecp (+ (expo x) (bias q)) q)
       (exactp x p)))

(defund eencodingp_alt (x p q)
  (and (bvecp x (+ p q 1))
       (= (bitn_alt x (- p 1)) 1)))


(defund eencode_alt (x p q)
  (cat_alt (cat_alt (if (= (sgn x) 1) 0 1)
	    1
	    (+ (expo x) (bias q))
	    q)
       (1+ q)
       (* (sig x) (expt 2 (- p 1)))
       p) )


(defund edecode_alt (x p q)
  (* (if (= (esgnf_alt x p q) 0) 1 -1)
     (esigf_alt x p)
     (expt 2 (+ 1 (- p) (eexpof_alt x p q) (- (bias q))))))



(defthm eencodingp_alt-not-zero
    (implies (and (eencodingp_alt x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (not (equal (edecode_alt x p q) 0)))
    :hints (("Goal" :use ((:instance eencodingp-not-zero)))))


(defthm erepp-edecode_alt
    (implies (and (eencodingp_alt x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (erepp (edecode_alt x p q) p q))
    :hints (("Goal" :use ((:instance erepp-edecode)))))

(defthm eencodingp_alt-eencode_alt
    (implies (and (erepp x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (eencodingp_alt (eencode_alt x p q) p q) )
    :hints (("Goal" :use ((:instance eencodingp-eencode)))))

(defthm edecode_alt-eencode_alt
    (implies (and (erepp x p q)
		  (integerp p)
;		  (> p 0)
		  (integerp q)
	;	  (> q 0)
                  )
	     (equal (edecode_alt (eencode_alt x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance edecode-eencode)))))

(defthm eencode_alt-edecode_alt
    (implies (and (eencodingp_alt x p q)
		  (integerp p)
		  (>= p 0)
		  (integerp q)
		  (> q 0))
	     (equal (eencode_alt (edecode_alt x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance eencode-edecode)))))

(defthm expo-edecode_alt
    (implies (and (eencodingp_alt x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (equal (expo (edecode_alt x p q))
		    (- (eexpof_alt x p q) (bias q))))
    :hints (("Goal" :use ((:instance expo-edecode)))))

(defthm sgn-edecode_alt
    (implies (and (eencodingp_alt x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (equal (sgn (edecode_alt  x p q))
		    (if (= (esgnf_alt x p q) 0) 1 -1)))
    :hints (("Goal" :use ((:instance sgn-edecode)))))

(defthm sig-edecode_alt
    (implies (and (eencodingp_alt  x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (equal (sig (edecode_alt  x p q))
		    (/ (esigf_alt x p) (expt 2 (- p 1)))))
    :hints (("Goal" :use ((:instance sig-edecode)))))

;BOZO disable?
(defun rebias-expo (expo old new)
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

(defthm rebias-down_alt
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (equal (rebias-expo x n m)
		    (cat_alt (bitn_alt x (1- n))
			 1
			 (bits_alt x (- m 2) 0)
			 (1- m))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rebias-down)))))





(defthm rebias-up_alt
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x m))
	     (equal (rebias-expo x m n)
		    (cat_alt (cat_alt (bitn_alt x (1- m))
			      1
			      (mulcat_alt 1 (- n m) (bitn_alt (lognot x) (1- m)))
			      (- n m))
			 (1+ (- n m))
			 (bits_alt x (- m 2) 0)
			 (1- m))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rebias-UP)
                        (:instance bitn-lognot-g
                                   (x (bitn x (+ -1 m)))
                                   (n 0))
                        (:instance bitn-lognot-g
                                   (x x)
                                   (n (+ -1 m)))
                        (:instance bitn-0-1
                                   (x x)
                                   (n (+ -1 m))))
           :in-theory (e/d (lnot-lognot
                            bitn-lnot)
                           (cat-0)))))



;;;***************************************************************
;;;          REPRESENTATIONS WITH IMPLICIT MSB
;;;***************************************************************

;;Bit vectors of length p+q, consisting of 1-bit sign field, q-bit
;;exponent field (bias = 2**(q-1)-1), and (p-1)-bit significand field,
;;where p > 1.

;;Field extractors:

(defun isgnf_alt (x p q) (bitn_alt x (1- (+ p q))))




(defun iexpof_alt (x p q) (bits_alt x (- (+ p q) 2) (1- p)))



(defun isigf_alt (x p) (bits_alt x (- p 2) 0))


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
       ;number of bits_alt available in the sig field = p - 1 - ( - bias - expo(x))
       (exactp x (+ -2 p (expt 2 (- q 1)) (expo x)))))

(defund irepp (x p q)
  (or (nrepp x p q)
      (drepp x p q)))


;;Valid encodings:

(defund nencodingp_alt (x p q)
  (and (bvecp x (+ p q))
       (< 0 (iexpof_alt x p q))
       (< (iexpof_alt x p q) (- (expt 2 q) 1))))




(defund dencodingp_alt (x p q)
  (and (bvecp x (+ p q))
       (= (iexpof_alt x p q) 0)
       (not (= (isigf_alt x p) 0))))



(defund iencodingp_alt (x p q)
  (or (nencodingp_alt x p q)
      (dencodingp_alt x p q)))





(defthm not-both-nrepp-and-drepp
    (implies (irepp x p q)
	     (iff (nrepp x p q) (not (drepp x p q))))
  :rule-classes ())

(defthm not-both-nencodingp_alt-and-dencodingp_alt
    (implies (iencodingp_alt x p q)
	     (iff (nencodingp_alt x p q) (not (dencodingp_alt x p q))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance not-both-nencodingp-and-dencodingp)))))



;;Encoding functions:

(defund nencode_alt (x p q)
  (cat_alt (cat_alt (if (= (sgn x) 1) 0 1)
	    1
            (+ (expo x) (bias q))
            q)
       (1+ q)
       (* (- (sig x) 1) (expt 2 (- p 1)))
       (- p 1)))




(defund dencode_alt (x p q)
  (cat_alt (cat_alt (if (= (sgn x) 1) 0 1)
	    1
            0
            q)
       (1+ q)
       (* (sig x) (expt 2 (+ -2 p (expo x) (bias q))))
       (- p 1)))




(defund iencode_alt (x p q)
  (cond ((nrepp x p q)
	 (nencode_alt x p q))
	((drepp x p q)
	 (dencode_alt x p q))))





;;Decoding functions:

(defund ndecode_alt (x p q)
  (* (if (= (isgnf_alt x p q) 0) 1 -1)
     (+ (expt 2 (- (iexpof_alt x p q) (bias q)))
        (* (isigf_alt x p)
           (expt 2 (+ 1 (iexpof_alt x p q) (- (bias q)) (- p)))))))






(defund ddecode_alt (x p q)
  (* (if (= (isgnf_alt x p q) 0) 1 -1)
     (isigf_alt x p)
     (expt 2 (+ 2 (- (bias q)) (- p)))))





(defund idecode_alt (x p q)
  (cond ((nencodingp_alt x p q)
	 (ndecode_alt x p q))
	((dencodingp_alt x p q)
	 (ddecode_alt x p q))))





;;Field extraction:

(defthm sgn-ndecode_alt
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sgn (ndecode_alt x p q))
		    (if (= (isgnf_alt x p q) 0) 1 -1)))
    :hints (("Goal" :use ((:instance sgn-ndecode)))))

(defthm expo-ndecode_alt
    (implies (and (nencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (expo (ndecode_alt x p q))
		    (- (iexpof_alt x p q) (bias q))))
    :hints (("Goal" :use ((:instance expo-ndecode)))))

(defthm sig-ndecode_alt
    (implies (and (nencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sig (ndecode_alt x p q))
		    (+ 1 (/ (isigf_alt x p) (expt 2 (- p 1))))))
    :hints (("Goal" :use ((:instance sig-ndecode)))))

(defthm sgn-ddecode_alt
    (implies (and (dencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sgn (ddecode_alt x p q))
		    (if (= (isgnf_alt x p q) 0) 1 -1)))
    :hints (("Goal" :use ((:instance sgn-ddecode)))))

(defthm expo-ddecode_alt
    (implies (and (dencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (expo (ddecode_alt x p q))
		    (+ 2 (- p) (- (bias q)) (expo (isigf_alt x p)))))
    :hints (("Goal" :use ((:instance expo-ddecode)))))

(defthm sig-ddecode_alt
    (implies (and (dencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sig (ddecode_alt x p q))
		    (sig (isigf_alt x p))))
    :hints (("Goal" :use ((:instance sig-ddecode)))))

(defthm sgn-idecode_alt
    (implies (and (iencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal
	      (sgn (idecode_alt x p q))
	      (if (= (isgnf_alt x p q) 0) 1 -1)))
    :hints (("Goal" :use ((:instance sgn-idecode)))))

(defthm expo-idecode_alt
    (implies (and (iencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal
	      (expo (idecode_alt x p q))
	      (cond ((nencodingp_alt x p q)
		     (- (iexpof_alt x p q) (bias q)))
		    ((dencodingp_alt x p q)
		     (+ 2 (- p) (- (bias q)) (expo (isigf_alt x p)))))))
    :hints (("Goal" :use ((:instance expo-idecode)))))

(defthm sig-idecode_alt
    (implies (and (iencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sig (idecode_alt x p q))
		    (cond ((nencodingp_alt x p q)
			   (+ 1 (/ (isigf_alt x p) (expt 2 (- p 1)))))
			  ((dencodingp_alt x p q)
			   (sig (isigf_alt x p))))))
    :hints (("Goal" :use ((:instance sig-idecode)))))


;;Inversions:

(defthm dencodingp_alt-dencode_alt
    (implies (and (drepp x p q)
		  (integerp p)
		  (integerp q)
		  (> q 0))
	     (dencodingp_alt (dencode_alt x p q) p q))
    :hints (("Goal" :use ((:instance dencodingp-dencode)))))

(defthm iencodingp_alt-iencode_alt
    (implies (and (irepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (iencodingp_alt (iencode_alt x p q) p q))
    :hints (("Goal" :use ((:instance iencodingp-iencode)))))

(defthm nrepp-ndecode_alt
    (implies (and (nencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (nrepp (ndecode_alt x p q) p q))
    :hints (("Goal" :use ((:instance nrepp-ndecode)))))

(defthm drepp-ddecode_alt
    (implies (and (dencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (drepp (ddecode_alt x p q) p q))
    :hints (("Goal" :use ((:instance drepp-ddecode)))))

(defthm irepp-idecode_alt
    (implies (and (iencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (irepp (idecode_alt x p q) p q))
    :hints (("Goal" :use ((:instance irepp-idecode)))))

(defthm nencodingp_alt-nencode_alt
    (implies (and (nrepp x p q)
                  (integerp p)
                  (> p 1)
                  (integerp q)
                  (> q 0))
             (nencodingp_alt (nencode_alt x p q) p q))
    :hints (("Goal" :use ((:instance nencodingp-nencode)))))

(defthm ndecode_alt-nencode_alt
    (implies (and (nrepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (ndecode_alt (nencode_alt x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance ndecode-nencode)))))

(defthm ddecode_alt-dencode_alt
    (implies (and (drepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (ddecode_alt (dencode_alt x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance ddecode-dencode)))))

(defthm idecode_alt-iencode_alt
    (implies (and (irepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (idecode_alt (iencode_alt x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance idecode-iencode)))))

(defthm nencode_alt-ndecode_alt
    (implies (and (nencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (nencode_alt (ndecode_alt x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance nencode-ndecode)))))

(defthm dencode_alt-ddecode_alt
    (implies (and (dencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (dencode_alt (ddecode_alt x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance dencode-ddecode)))))

(defthm iencode_alt-idecode_alt
    (implies (and (iencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (iencode_alt (idecode_alt x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance iencode-idecode)))))







