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

(include-book "log")

(include-book "float")


(local (include-book "reps-new"))


(local
 (defthm bits-is-bits_alt
   (equal (bits x i j)
          (bits_alt x i j))
   :hints (("Goal" :in-theory (e/d (bits_alt bits) ())))))

(local
 (defthm bitn-is-bitn_alt
   (equal (bitn x n)
          (bitn_alt x n))
   :hints (("Goal" :in-theory (e/d (bitn_alt bitn) ())))))

(local
 (defthm binary-cat_alt-is-binary-cat
   (equal (binary-cat x m y n)
          (binary-cat_alt x m y n))
   :hints (("Goal" :in-theory (e/d (binary-cat_alt binary-cat) ())))))

(local
 (defthm mulcat_alt-is-mulcat
   (equal (mulcat l n x)
          (mulcat_alt l n x))
   :hints (("Goal" :in-theory (e/d (mulcat_alt mulcat) ())))))


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
(defun esgnf  (x p q) (bitn x (+ p q)))

(local
 (defthm esgnf-is-esgnf_alt
   (equal (esgnf x p q)
          (esgnf_alt x p q))
   :hints (("Goal" :in-theory (e/d (esgnf_alt esgnf) ())))))


(defun eexpof (x p q) (bits x (1- (+ p q)) p))

(local
 (defthm eexpof-is-eexpof_alt
   (equal (eexpof x p q)
          (eexpof_alt x p q))
   :hints (("Goal" :in-theory (e/d (eexpof_alt eexpof) ())))))

(defun esigf  (x p)   (bits x (1- p) 0))

(local
 (defthm esigf-is-esigf_alt
   (equal (esigf x p)
          (esigf_alt x p))
   :hints (("Goal" :in-theory (e/d (esigf esigf_alt) ())))))


(defund erepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (bvecp (+ (expo x) (bias q)) q)
       (exactp x p)))

(defund eencodingp (x p q)
  (and (bvecp x (+ p q 1))
       (= (bitn x (- p 1)) 1)))

(local
 (defthm eencodingp-is-eencodingp_alt
   (equal (eencodingp x p q)
          (eencodingp_alt x p q))
   :hints (("Goal" :in-theory (e/d (eencodingp_alt
                                    eencodingp) ())))))

(defund eencode (x p q)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    1
	    (+ (expo x) (bias q))
	    q)
       (1+ q)
       (* (sig x) (expt 2 (- p 1)))
       p) )

(local
 (defthm eencode-is-eencode_alt
   (equal (eencode x p q)
          (eencode_alt x p q))
   :hints (("Goal" :in-theory (e/d (eencode_alt
                                    eencode) ())))))


(defund edecode (x p q)
  (* (if (= (esgnf x p q) 0) 1 -1)
     (esigf x p)
     (expt 2 (+ 1 (- p) (eexpof x p q) (- (bias q))))))


(local
 (defthm edecode-is-edecode_alt
   (equal (edecode x p q)
          (edecode_alt x p q))
   :hints (("Goal" :in-theory (e/d (edecode_alt
                                    edecode) ())))))


(defthm eencodingp-not-zero
    (implies (and (eencodingp x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (not (equal (edecode x p q) 0)))
    :hints (("Goal" :use ((:instance eencodingp_alt-not-zero)))))


(defthm erepp-edecode
    (implies (and (eencodingp x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (erepp (edecode x p q) p q))
    :hints (("Goal" :use ((:instance erepp-edecode_alt)))))

(defthm eencodingp-eencode
    (implies (and (erepp x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (eencodingp (eencode x p q) p q) )
    :hints (("Goal" :use ((:instance eencodingp_alt-eencode_alt)))))

(defthm edecode-eencode
    (implies (and (erepp x p q)
		  (integerp p)
;		  (> p 0)
		  (integerp q)
	;	  (> q 0)
                  )
	     (equal (edecode (eencode x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance edecode_alt-eencode_alt)))))

(defthm eencode-edecode
    (implies (and (eencodingp x p q)
		  (integerp p)
		  (>= p 0)
		  (integerp q)
		  (> q 0))
	     (equal (eencode (edecode x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance eencode_alt-edecode_alt)))))

(defthm expo-edecode
    (implies (and (eencodingp x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (equal (expo (edecode x p q))
		    (- (eexpof x p q) (bias q))))
    :hints (("Goal" :use ((:instance expo-edecode_alt)))))

(defthm sgn-edecode
    (implies (and (eencodingp x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (equal (sgn (edecode  x p q))
		    (if (= (esgnf x p q) 0) 1 -1)))
    :hints (("Goal" :use ((:instance sgn-edecode_alt)))))

(defthm sig-edecode
    (implies (and (eencodingp  x p q)
		  (integerp p)
		  (> p 0)
		  (integerp q)
		  (> q 0))
	     (equal (sig (edecode  x p q))
		    (/ (esigf x p) (expt 2 (- p 1)))))
    :hints (("Goal" :use ((:instance sig-edecode_alt)))))

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
  :rule-classes ()
  :hints (("Goal" :use ((:instance rebias-down_alt)))))


;; (local (include-book "../../arithmetic/top"))

;; (local
;;  (defthmd bitn-lognot-g
;;    (implies (and (integerp x)
;;                  (integerp n)
;;                  (>= n 0))
;;             (not (equal (bitn (lognot x) n)
;;                         (bitn x n))))
;;    :hints (("Goal" :cases ((equal n 0)))
;;            ("Subgoal 2" :use ((:instance bitn_alt-lognot)))
;;            ("Subgoal 1" :in-theory (e/d (lognot bitn_alt-def mod)
;;                                         ())))))


(defthm rebias-up
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
			 (1- m))))
  :rule-classes ()
  :hints (("Goal" :use rebias-up_alt)))




;;;***************************************************************
;;;          REPRESENTATIONS WITH IMPLICIT MSB
;;;***************************************************************

;;Bit vectors of length p+q, consisting of 1-bit sign field, q-bit
;;exponent field (bias = 2**(q-1)-1), and (p-1)-bit significand field,
;;where p > 1.

;;Field extractors:

(defun isgnf (x p q) (bitn x (1- (+ p q))))

(local
 (defthm isgnf-is-isgnf_alt
   (equal (isgnf x p q)
          (isgnf_alt x p q))))


(defun iexpof (x p q) (bits x (- (+ p q) 2) (1- p)))

(local
 (defthm iexpof-is-iexpof_alt
   (equal (iexpof x p q)
          (iexpof_alt x p q))))

(defun isigf (x p) (bits x (- p 2) 0))

(local
 (defthm isigf-is-isigf_alt
   (equal (isigf x p)
          (isigf_alt x p))))


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

(local
 (defthm nencodingp-is-nencoding
   (equal (nencodingp x p q)
          (nencodingp_alt x p q))
   :hints (("Goal" :in-theory (e/d (nencodingp
                                    nencodingp_alt) ())))))


(defund dencodingp (x p q)
  (and (bvecp x (+ p q))
       (= (iexpof x p q) 0)
       (not (= (isigf x p) 0))))

(local
 (defthm dencodingp-is-dencoding
   (equal (dencodingp x p q)
          (dencodingp_alt x p q))
   :hints (("Goal" :in-theory (e/d (dencodingp_alt
                                    dencodingp) ())))))

(defund iencodingp (x p q)
  (or (nencodingp x p q)
      (dencodingp x p q)))


(local
 (defthm iencodingp-is-iencoding
   (equal (iencodingp x p q)
          (iencodingp_alt x p q))
   :hints (("Goal" :in-theory (e/d (iencodingp_alt
                                    iencodingp) ())))))


(defthm not-both-nrepp-and-drepp
    (implies (irepp x p q)
	     (iff (nrepp x p q) (not (drepp x p q))))
  :rule-classes ())

(defthm not-both-nencodingp-and-dencodingp
    (implies (iencodingp x p q)
	     (iff (nencodingp x p q) (not (dencodingp x p q))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance not-both-nencodingp_alt-and-dencodingp_alt)))))



;;Encoding functions:

(defund nencode (x p q)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    1
            (+ (expo x) (bias q))
            q)
       (1+ q)
       (* (- (sig x) 1) (expt 2 (- p 1)))
       (- p 1)))

(local
 (defthm nencode-is-nencode_alt
   (equal (nencode x p q)
          (nencode_alt x p q))
   :hints (("Goal" :in-theory (e/d (nencode_alt
                                    nencode)

; Matt K. mod for assume-true-false improvement for calls of the form (integerp
; (+ k term)).

                                   ((force)))))))



(defund dencode (x p q)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    1
            0
            q)
       (1+ q)
       (* (sig x) (expt 2 (+ -2 p (expo x) (bias q))))
       (- p 1)))

(local
 (defthm dencode-is-dencode
   (equal (dencode x p q)
          (dencode_alt x p q))
   :hints (("Goal" :in-theory (e/d (dencode_alt
                                    dencode)

; Matt K. mod for assume-true-false improvement for calls of the form (integerp
; (+ k term)).

                                   ((force)))))))


(defund iencode (x p q)
  (cond ((nrepp x p q)
	 (nencode x p q))
	((drepp x p q)
	 (dencode x p q))))


(local
 (defthm iencode-is-iencode_alt
   (equal (iencode x p q)
          (iencode_alt x p q))
   :hints (("Goal" :in-theory (e/d (iencode_alt
                                    iencode))))))


;;Decoding functions:

(defund ndecode (x p q)
  (* (if (= (isgnf x p q) 0) 1 -1)
     (+ (expt 2 (- (iexpof x p q) (bias q)))
        (* (isigf x p)
           (expt 2 (+ 1 (iexpof x p q) (- (bias q)) (- p)))))))



(local
 (defthm ndecode-is-ndecode
   (equal (ndecode x p q)
          (ndecode_alt x p q))
   :hints (("Goal" :in-theory (e/d (ndecode_alt
                                    ndecode))))))


(defund ddecode (x p q)
  (* (if (= (isgnf x p q) 0) 1 -1)
     (isigf x p)
     (expt 2 (+ 2 (- (bias q)) (- p)))))

(local
 (defthm ddecode-is-decode
   (equal (ddecode x p q)
          (ddecode_alt x p q))
   :hints (("Goal" :in-theory (e/d (ddecode_alt
                                    ddecode))))))



(defund idecode (x p q)
  (cond ((nencodingp x p q)
	 (ndecode x p q))
	((dencodingp x p q)
	 (ddecode x p q))))


(local
 (defthm idecode-is-idecode
   (equal (idecode x p q)
          (idecode_alt x p q))
   :hints (("Goal" :in-theory (e/d (idecode_alt
                                    idecode))))))


;;Field extraction:

(defthm sgn-ndecode
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sgn (ndecode x p q))
		    (if (= (isgnf x p q) 0) 1 -1)))
    :hints (("Goal" :use ((:instance sgn-ndecode_alt)))))

(defthm expo-ndecode
    (implies (and (nencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (expo (ndecode x p q))
		    (- (iexpof x p q) (bias q))))
    :hints (("Goal" :use ((:instance expo-ndecode_alt)))))

(defthm sig-ndecode
    (implies (and (nencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sig (ndecode x p q))
		    (+ 1 (/ (isigf x p) (expt 2 (- p 1))))))
    :hints (("Goal" :use ((:instance sig-ndecode_alt)))))

(defthm sgn-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sgn (ddecode x p q))
		    (if (= (isgnf x p q) 0) 1 -1)))
    :hints (("Goal" :use ((:instance sgn-ddecode_alt)))))

(defthm expo-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (expo (ddecode x p q))
		    (+ 2 (- p) (- (bias q)) (expo (isigf x p)))))
    :hints (("Goal" :use ((:instance expo-ddecode_alt)))))

(defthm sig-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sig (ddecode x p q))
		    (sig (isigf x p))))
    :hints (("Goal" :use ((:instance sig-ddecode_alt)))))

(defthm sgn-idecode
    (implies (and (iencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal
	      (sgn (idecode x p q))
	      (if (= (isgnf x p q) 0) 1 -1)))
    :hints (("Goal" :use ((:instance sgn-idecode_alt)))))

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
		     (+ 2 (- p) (- (bias q)) (expo (isigf x p)))))))
    :hints (("Goal" :use ((:instance expo-idecode_alt)))))

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
			   (sig (isigf x p))))))
    :hints (("Goal" :use ((:instance sig-idecode_alt)))))


;;Inversions:

(defthm dencodingp-dencode
    (implies (and (drepp x p q)
		  (integerp p)
		  (integerp q)
		  (> q 0))
	     (dencodingp (dencode x p q) p q))
    :hints (("Goal" :use ((:instance dencodingp_alt-dencode_alt)))))

(defthm iencodingp-iencode
    (implies (and (irepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (iencodingp (iencode x p q) p q))
    :hints (("Goal" :use ((:instance iencodingp_alt-iencode_alt)))))

(defthm nrepp-ndecode
    (implies (and (nencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (nrepp (ndecode x p q) p q))
    :hints (("Goal" :use ((:instance nrepp-ndecode_alt)))))

(defthm drepp-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (drepp (ddecode x p q) p q))
    :hints (("Goal" :use ((:instance drepp-ddecode_alt)))))

(defthm irepp-idecode
    (implies (and (iencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (irepp (idecode x p q) p q))
    :hints (("Goal" :use ((:instance irepp-idecode_alt)))))

(defthm nencodingp-nencode
    (implies (and (nrepp x p q)
                  (integerp p)
                  (> p 1)
                  (integerp q)
                  (> q 0))
             (nencodingp (nencode x p q) p q))
    :hints (("Goal" :use ((:instance nencodingp_alt-nencode_alt)))))

(defthm ndecode-nencode
    (implies (and (nrepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (ndecode (nencode x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance ndecode_alt-nencode_alt)))))

(defthm ddecode-dencode
    (implies (and (drepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (ddecode (dencode x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance ddecode_alt-dencode_alt)))))

(defthm idecode-iencode
    (implies (and (irepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (idecode (iencode x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance idecode_alt-iencode_alt)))))

(defthm nencode-ndecode
    (implies (and (nencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (nencode (ndecode x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance nencode_alt-ndecode_alt)))))

(defthm dencode-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (dencode (ddecode x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance dencode_alt-ddecode_alt)))))

(defthm iencode-idecode
    (implies (and (iencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (iencode (idecode x p q) p q)
		    x))
    :hints (("Goal" :use ((:instance iencode_alt-idecode_alt)))))







