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

(local (include-book "../lib2/top"))

(include-book "log-new")
(include-book "float-new")


(local (include-book "log-support"))

(local
 (encapsulate ()
              (local (include-book "bits-new-proofs"))

             (defthm bits_alt-is-bits
               (equal (bits_alt x i j)
                      (bits x i j)))


             (defthm bitn_alt-is-bitn
               (equal (bitn_alt x n)
                      (bitn x n)))


             (defthm binary-cat_alt-is-binary-cat
               (equal (binary-cat_alt x m y n)
                      (binary-cat x m y n)))


             (defthm mulcat_alt-is-mul-cat
               (equal (mulcat_alt l n x)
                      (mulcat l n x)))


             ))



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

(local
 (defthm esgnf_alt-is-esgnf
   (equal (esgnf_alt x p q)
          (esgnf x p q))
   :hints (("Goal" :in-theory (e/d (esgnf_alt esgnf) ())))))


(defun eexpof_alt (x p q) (bits_alt x (1- (+ p q)) p))

(local
 (defthm eexpof_alt-is-esgnf
   (equal (eexpof_alt x p q)
          (eexpof x p q))
   :hints (("Goal" :in-theory (e/d (eexpof_alt eexpof) ())))))

(defun esigf_alt  (x p)   (bits_alt x (1- p) 0))

(local
 (defthm esigf_alt-is-esigf
   (equal (esigf_alt x p)
          (esigf x p))
   :hints (("Goal" :in-theory (e/d (esigf_alt esigf) ())))))



(defund erepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (bvecp (+ (expo x) (bias q)) q)
       (exactp x p)))

(defund eencodingp_alt (x p q)
  (and (bvecp x (+ p q 1))
       (= (bitn_alt x (- p 1)) 1)))

(local
 (defthm eencodingp_alt-is-eencodingp
   (equal (eencodingp_alt x p q)
          (eencodingp x p q))
   :hints (("Goal" :in-theory (e/d (eencodingp
                                    eencodingp_alt) ())))))

(defund eencode_alt (x p q)
  (cat_alt (cat_alt (if (= (sgn x) 1) 0 1)
	    1
	    (+ (expo x) (bias q))
	    q)
       (1+ q)
       (* (sig x) (expt 2 (- p 1)))
       p) )

(local
 (defthm eencode_alt-is-eencode
   (equal (eencode_alt x p q)
          (eencode x p q))
   :hints (("Goal" :in-theory (e/d (eencode_alt
                                    eencode) ())))))


(defund edecode_alt (x p q)
  (* (if (= (esgnf_alt x p q) 0) 1 -1)
     (esigf_alt x p)
     (expt 2 (+ 1 (- p) (eexpof_alt x p q) (- (bias q))))))


(local
 (defthm edecode_alt-is-edecode
   (equal (edecode_alt x p q)
          (edecode x p q))
   :hints (("Goal" :in-theory (e/d (edecode_alt
                                    edecode) ())))))


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


(local (include-book "../../arithmetic/top"))

(local
 (defthmd bitn-lognot-g
   (implies (and (integerp x)
                 (integerp n)
                 (>= n 0))
            (not (equal (bitn (lognot x) n)
                        (bitn x n))))
   :hints (("Goal" :cases ((equal n 0)))
           ("Subgoal 2" :use ((:instance bitn_alt-lognot)))
           ("Subgoal 1" :in-theory (e/d (lognot bitn-def mod)
                                        ())))))


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

(local
 (defthm isgnf_alt-is-isgnf
   (equal (isgnf_alt x p q)
          (isgnf x p q))))


(defun iexpof_alt (x p q) (bits_alt x (- (+ p q) 2) (1- p)))

(local
 (defthm iexpof_alt-is-iexpof
   (equal (iexpof_alt x p q)
          (iexpof x p q))))

(defun isigf_alt (x p) (bits_alt x (- p 2) 0))

(local
 (defthm isigf_alt-is-isigf
   (equal (isigf_alt x p)
          (isigf x p))))


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

(local
 (defthm nencodingp_alt-is-nencoding
   (equal (nencodingp_alt x p q)
          (nencodingp x p q))
   :hints (("Goal" :in-theory (e/d (nencodingp_alt
                                    nencodingp) ())))))


(defund dencodingp_alt (x p q)
  (and (bvecp x (+ p q))
       (= (iexpof_alt x p q) 0)
       (not (= (isigf_alt x p) 0))))

(local
 (defthm dencodingp_alt-is-dencoding
   (equal (dencodingp_alt x p q)
          (dencodingp x p q))
   :hints (("Goal" :in-theory (e/d (dencodingp_alt
                                    dencodingp) ())))))

(defund iencodingp_alt (x p q)
  (or (nencodingp_alt x p q)
      (dencodingp_alt x p q)))


(local
 (defthm iencodingp_alt-is-iencoding
   (equal (iencodingp_alt x p q)
          (iencodingp x p q))
   :hints (("Goal" :in-theory (e/d (iencodingp_alt
                                    iencodingp) ())))))


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

(local
 (defthm nencode_alt-is-nencode
   (equal (nencode_alt x p q)
          (nencode x p q))
   :hints (("Goal" :in-theory (e/d (nencode_alt
                                    nencode) ())))))



(defund dencode_alt (x p q)
  (cat_alt (cat_alt (if (= (sgn x) 1) 0 1)
	    1
            0
            q)
       (1+ q)
       (* (sig x) (expt 2 (+ -2 p (expo x) (bias q))))
       (- p 1)))

(local
 (defthm dencode_alt-is-dencode
   (equal (dencode_alt x p q)
          (dencode x p q))
   :hints (("Goal" :in-theory (e/d (dencode_alt
                                    dencode) ())))))


(defund iencode_alt (x p q)
  (cond ((nrepp x p q)
	 (nencode_alt x p q))
	((drepp x p q)
	 (dencode_alt x p q))))


(local
 (defthm iencode_alt-is-iencode
   (equal (iencode_alt x p q)
          (iencode x p q))
   :hints (("Goal" :in-theory (e/d (iencode_alt
                                    iencode))))))


;;Decoding functions:

(defund ndecode_alt (x p q)
  (* (if (= (isgnf_alt x p q) 0) 1 -1)
     (+ (expt 2 (- (iexpof_alt x p q) (bias q)))
        (* (isigf_alt x p)
           (expt 2 (+ 1 (iexpof_alt x p q) (- (bias q)) (- p)))))))



(local
 (defthm ndecode_alt-is-ndecode
   (equal (ndecode_alt x p q)
          (ndecode x p q))
   :hints (("Goal" :in-theory (e/d (ndecode_alt
                                    ndecode))))))


(defund ddecode_alt (x p q)
  (* (if (= (isgnf_alt x p q) 0) 1 -1)
     (isigf_alt x p)
     (expt 2 (+ 2 (- (bias q)) (- p)))))

(local
 (defthm ddecode_alt-is-decode
   (equal (ddecode_alt x p q)
          (ddecode x p q))
   :hints (("Goal" :in-theory (e/d (ddecode_alt
                                    ddecode))))))



(defund idecode_alt (x p q)
  (cond ((nencodingp_alt x p q)
	 (ndecode_alt x p q))
	((dencodingp_alt x p q)
	 (ddecode_alt x p q))))


(local
 (defthm idecode_alt-is-idecode
   (equal (idecode_alt x p q)
          (idecode x p q))
   :hints (("Goal" :in-theory (e/d (idecode_alt
                                    idecode))))))


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







