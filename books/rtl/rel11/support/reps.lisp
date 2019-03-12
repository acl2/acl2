; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel11/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))
(local (in-theory (acl2::enable-arith5)))

(local (include-book "basic"))
(local (include-book "bits"))
(local (include-book "float"))
(include-book "definitions")


;;;***************************************************************
;;;               Classification of Formats
;;;***************************************************************

;;Format parameters:

; (defnd formatp (f) ... )
; (defund explicitp (f) ... )
; (defund prec (f) ... )
; (defund expw (f) ... )
; (defund sigw (f) ... )
; (defnd encodingp (x f) ... )

(defrule encodingp-forward
  (implies (encodingp x f)
           (and (natp x)
                (formatp f)))
  :enable encodingp
  :rule-classes :forward-chaining)

;;Examples:

; (defnd hp () ... )
; (defnd sp () ... )
; (defnd dp () ... )
; (defnd ep () ... )
; (in-theory (disable (sp) (dp) (ep)))

(defthm formatp-bf
  (formatp (bf))
  :hints (("Goal" :in-theory (enable bf formatp))))

(defthm formatp-hp
  (formatp (hp))
  :hints (("Goal" :in-theory (enable hp formatp))))

(defthm formatp-sp
  (formatp (sp))
  :hints (("Goal" :in-theory (enable sp formatp))))

(defthm formatp-dp
  (formatp (dp))
  :hints (("Goal" :in-theory (enable dp formatp))))

(defthm formatp-ep
  (formatp (ep))
  :hints (("Goal" :in-theory (enable ep formatp))))

;;Field extractors:

; (defund sgnf (x f) ... )

(defrule bvecp-1-of-sgnf
  (bvecp (sgnf x f) 1)
  :enable sgnf)

; (defund expf (x f) ... )
; (defund sigf (x f) ... )
; (defund manf (x f) ... )

;;Exponent bias:

; (defund bias (f) ... )

(acl2::with-arith5-nonlinear-help
 (defrule bvecp-of-bias
   (implies (and (formatp f)
                 (integerp n)
                 (>= n (1- (expw f))))
            (bvecp (bias f) n))
   :enable (bias bvecp)))

;;;***************************************************************
;;;                    Normal Encodings
;;;***************************************************************

; (defund normp (x f) ... )
; (defund unsupp (x f) ... )

;;Decoding function:

; (defund ndecode (x f) ... )

(defthmd sgn-ndecode
    (implies (normp x f)
	     (equal (sgn (ndecode x f))
		    (if (= (sgnf x f) 0) 1 -1)))
  :hints (("Goal" :in-theory (enable sgn normp ndecode))))

(local-defthmd expo-ndecode-1
    (implies (normp x f)
             (equal (abs (ndecode x f))
                    (* (+ 1 (/ (manf x f) (expt 2 (1- (prec f)))))
                       (expt 2 (- (expf x f) (bias f))))))
  :hints (("Goal" :in-theory (enable ndecode))))

(local-defthm hack-1
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (> y 0)
                (< x y))
           (< (* x (/ y)) 1))
  :rule-classes ())

(local-defthm hack-2
  (implies (and (real/rationalp x)
                (integerp n)
                (< x (expt 2 n)))
           (< (* x (expt 2 (- n))) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance hack-1 (y (expt 2 n)))))))

(local-defthmd expo-ndecode-2
    (implies (normp x f)
             (and  (<= 0 (/ (manf x f) (expt 2 (1- (prec f)))))
                   (< (/ (manf x f) (expt 2 (1- (prec f)))) 1)))
  :hints (("Goal" :in-theory (enable normp manf)
                  :use ((:instance hack-2 (x (manf x f)) (n (1- (prec f))))
                        (:instance bits-bounds (i (- (prec f) 2)) (j 0))))))

(defthmd expo-ndecode
    (implies (normp x f)
	     (equal (expo (ndecode x f))
		    (- (expf x f) (bias f))))
  :hints (("Goal" :in-theory (e/d (normp expo-ndecode-1 bias expw formatp prec) (abs))
                  :use (expo-ndecode-2
                        (:instance fp-rep-unique (x (ndecode x f)) (e (- (expf x f) (bias f))) (m (+ 1 (/ (manf x f) (expt 2 (1- (prec f)))))))))))

(defthmd sig-ndecode
    (implies (normp x f)
	     (equal (sig (ndecode x f))
		    (+ 1 (/ (manf x f) (expt 2 (1- (prec f)))))))
  :hints (("Goal" :in-theory (e/d (normp expo-ndecode-1 bias expw formatp prec) (abs))
                  :use (expo-ndecode-2
                        (:instance fp-rep-unique (x (ndecode x f)) (e (- (expf x f) (bias f))) (m (+ 1 (/ (manf x f) (expt 2 (1- (prec f)))))))))))

;;Representable normals:

; (defnd nrepp (x f) ... )

;;Encoding function:

; (defund nencode (x f) ... )

;;Inversions:

(defthm nrepp-ndecode
  (implies (normp x f)
           (nrepp (ndecode x f) f))
  :hints (("Goal" :in-theory (enable  normp nrepp expo-ndecode sig-ndecode exactp))))


(local-defthmd nencode-ndecode-1
    (implies (normp x f)
	     (equal (bitn (nencode (ndecode x f) f) (+ (expw f) (sigw f)))
		    (bitn x (+ (expw f) (sigw f)))))
  :hints (("Goal" :in-theory (enable normp bitn-cat sgnf nencode)
                  :use (sgn-ndecode))))

(local-defthmd nencode-ndecode-2
    (implies (normp x f)
	     (equal (bits (nencode (ndecode x f) f) (1- (+ (expw f) (sigw f))) (sigw f))
		    (bits x (1- (+ (expw f) (sigw f))) (sigw f))))
  :hints (("Goal" :in-theory (enable normp bits-cat expf nencode)
                  :use (expo-ndecode))))

(local-defthmd nencode-ndecode-3
    (implies (normp x f)
	     (equal (bits (nencode (ndecode x f) f) (1- (sigw f)) 0)
		    (bits (+ (expt 2 (1- (prec f))) (manf x f)) (1- (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable normp bits-cat nencode)
                  :use (sig-ndecode))))

(local-defthmd nencode-ndecode-4
    (implies (and (explicitp f)
                  (normp x f))
	     (equal (bits x (1- (sigw f)) 0)
		    (bits (+ (expt 2 (1- (prec f))) (manf x f)) (1- (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable sigw normp manf)
                  :use ((:instance bitn-plus-bits (n (1- (prec f))) (m 0))))))

(local-defthmd nencode-ndecode-5
    (implies (and (not (explicitp f))
                  (normp x f))
	     (equal (bits x (1- (sigw f)) 0)
		    (bits (+ (expt 2 (1- (prec f))) (manf x f)) (1- (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable sigw normp manf)
                  :use ((:instance bits-plus-mult-2 (x (manf x f)) (n (- (prec f) 2)) (m 0) (k (1- (prec f))) (y 1))))))

(local-defthmd nencode-ndecode-6
    (implies (normp x f)
	     (equal (bits (nencode (ndecode x f) f) (1- (sigw f)) 0)
		    (bits x (1- (sigw f)) 0)))
  :hints (("Goal" :use (nencode-ndecode-3 nencode-ndecode-4 nencode-ndecode-5))))

(local-defthmd nencode-ndecode-7
    (implies (normp x f)
	     (equal (bits (nencode (ndecode x f) f) (+ (expw f) (sigw f)) 0)
		    (bits x (+ (expw f) (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable normp)
                  :use (nencode-ndecode-1 nencode-ndecode-2 nencode-ndecode-6
                        (:instance bitn-plus-bits (n (+ (expw f) (sigw f))) (m 0))
                        (:instance bitn-plus-bits (x (nencode (ndecode x f) f)) (n (+ (expw f) (sigw f))) (m 0))
                        (:instance bits-plus-bits (n (1- (+ (expw f) (sigw f)))) (p (sigw f)) (m 0))
                        (:instance bits-plus-bits (x (nencode (ndecode x f) f)) (n (1- (+ (expw f) (sigw f)))) (p (sigw f)) (m 0))))))

(local-defthmd nencode-ndecode-8
    (implies (normp x f)
	     (and (bvecp (nencode (ndecode x f) f) (1+ (+ (expw f) (sigw f))))
		  (bvecp x (1+ (+ (expw f) (sigw f))))))
  :hints (("Goal" :in-theory (enable normp encodingp nencode))))

(defthm nencode-ndecode
    (implies (normp x f)
	     (equal (nencode (ndecode x f) f)
		    x))
  :hints (("Goal" :use (nencode-ndecode-7 nencode-ndecode-8))))

(local-defthmd normp-nencode-1
    (implies (nrepp x f)
             (bvecp (+ (bias f) (expo x)) (expw f)))
  :hints (("Goal" :in-theory (enable bvecp encodingp formatp bias expw nrepp))))

(local-defthm normp-nencode-2
    (implies (nrepp x f)
             (encodingp (nencode x f) f))
  :hints (("Goal" :in-theory (enable encodingp formatp nencode expw sigw prec nrepp))))

(local-defthm normp-nencode-3
    (implies (nrepp x f)
             (equal (expf (nencode x f) f)
                    (+ (bias f) (expo x))))
  :hints (("Goal" :use (normp-nencode-1)
                  :in-theory (enable bits-cat expf formatp nencode expw sigw prec nrepp))))

(local-defthmd normp-nencode-4
    (implies (and (explicitp f)
                  (nrepp x f))
             (equal (bitn (nencode x f) (1- (prec f)))
                    (bitn (* (sig x) (expt 2 (1- (prec f)))) (1- (prec f)))))
  :hints (("Goal" :in-theory (enable bitn-cat expf sigf formatp nencode expw sigw prec nrepp))))

(local-defthmd normp-nencode-5
    (implies (nrepp x f)
             (>= (* (sig x) (expt 2 (1- (prec f)))) (expt 2 (1- (prec f)))))
  :hints (("Goal" :use (sig-lower-bound)
                  :in-theory (enable formatp prec nrepp))))

(local-defthmd normp-nencode-6
    (implies (nrepp x f)
             (< (* (sig x) (expt 2 (1- (prec f)))) (expt 2 (prec f))))
  :hints (("Goal" :use (sig-upper-bound)
                  :in-theory (enable formatp prec nrepp))))

(local-defthmd normp-nencode-7
    (implies (nrepp x f)
             (equal (bitn (* (sig x) (expt 2 (1- (prec f)))) (1- (prec f))) 1))
  :hints (("Goal" :use (normp-nencode-5 normp-nencode-6
                        (:instance bvecp-bitn-1 (x (* (sig x) (expt 2 (1- (prec f))))) (n (1- (prec f)))))
                  :in-theory (enable exactp bvecp formatp prec nrepp))))

(defthm normp-nencode
    (implies (nrepp x f)
             (normp (nencode x f) f))
  :hints (("Goal" :in-theory (enable nrepp normp)
                  :use (normp-nencode-2 normp-nencode-3 normp-nencode-4 normp-nencode-7))))

(local-defthmd ndecode-nencode-1
    (implies (nrepp x f)
	     (equal (sgn (ndecode (nencode x f) f))
		    (sgn x)))
  :hints (("Goal" :in-theory (enable sgn nrepp bitn-cat sgnf nencode)
                  :use (normp-nencode
                        (:instance sgn-ndecode (x (nencode x f)))))))

(local-defthmd ndecode-nencode-2
    (implies (nrepp x f)
	     (equal (expo (ndecode (nencode x f) f))
		    (expo x)))
  :hints (("Goal" :in-theory (enable nrepp bits-cat expf expo-ndecode)
                  :use (normp-nencode))))

(local-defthmd ndecode-nencode-3
    (implies (nrepp x f)
             (bvecp (* (sig x) (expt 2 (1- (prec f)))) (prec f)))
  :hints (("Goal" :in-theory (enable exactp nrepp bvecp)
                  :use (normp-nencode-5 normp-nencode-6 normp-nencode))))

(local-defthmd ndecode-nencode-4
    (implies (nrepp x f)
             (equal (bits (* (sig x) (expt 2 (+ -1 (prec f)))) (+ -2 (prec f)) 0)
                    (- (* (sig x) (expt 2 (1- (prec f))))
                       (expt 2 (1- (prec f))))))
  :hints (("Goal" :in-theory (enable nrepp)
                  :use (ndecode-nencode-3 normp-nencode-7
                        (:instance bitn-plus-bits (x (* (sig x) (expt 2 (1- (prec f))))) (n (1- (prec f))) (m 0))))))

(local-defthmd ndecode-nencode-5
    (implies (nrepp x f)
	     (equal (manf (nencode x f) f)
		    (bits (* (sig x) (expt 2 (1- (prec f)))) (- (prec f) 2) 0)))
  :hints (("Goal" :in-theory (enable formatp sigw prec nrepp bits-cat manf nencode))))

(local-defthmd ndecode-nencode-6
    (implies (nrepp x f)
	     (equal (sig (ndecode (nencode x f) f))
		    (sig x)))
  :hints (("Goal" :in-theory (enable nrepp ndecode-nencode-4 ndecode-nencode-5)
                  :use (normp-nencode
                        (:instance sig-ndecode (x (nencode x f)))))))

(defthm ndecode-nencode
    (implies (nrepp x f)
	     (equal (ndecode (nencode x f) f)
		    x))
  :hints (("Goal" :use (fp-rep (:instance fp-rep (x (ndecode (nencode x f) f))))
                  :in-theory (enable nrepp ndecode-nencode-1 ndecode-nencode-2 ndecode-nencode-6))))

;; Smallest positive normal:

; (defund spn (f) ... )

(defthmd positive-spn
  (> (spn f) 0)
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable spn))))

(defthmd nrepp-spn
  (implies (formatp f)
           (nrepp (spn f) f))
  :hints (("Goal" :in-theory (enable bias exactp-2**n formatp expw prec nrepp spn))))

(defthmd smallest-spn
  (implies (nrepp x f)
           (>= (abs x) (spn f)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal" :use ((:instance expo<= (x (abs x)) (n (- (bias f)))))
                  :in-theory (enable expo spn nrepp))))

(defruled abs<spn-as-expo
  (implies
   (and
    (rationalp x)
    (formatp f))
   (equal (< (abs x) (spn f))
          (or (= x 0)
              (<= (expo x) (- (bias f))))))
  :enable (spn)
  :use ((:instance  expo<=
          (x (abs x))
          (n (- (bias f))))
        (:instance expo>=
          (x (abs x))
          (n (- 1 (bias f))))))

;; Largest positive normal:

; (defund lpn (f) ... )

(defthmd positive-lpn
  (implies (formatp f)
           (> (lpn f) 0))
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable formatp prec lpn))))

(defthmd expo-lpn
  (implies (formatp f)
           (equal (expo (lpn f))
                  (- (expt 2 (expw f)) (+ 2 (bias f)))))
  :hints (("Goal" :in-theory (enable formatp lpn prec expw bias)
                  :use ((:instance fp-rep-unique (x (lpn f)) (m (- 2 (expt 2 (- 1 (prec f))))) (e (- (expt 2 (expw f)) (+ 2 (bias f)))))))))

(defthmd sig-lpn
  (implies (formatp f)
           (equal (sig (lpn f))
                  (- 2 (expt 2 (- 1 (prec f))))))
  :hints (("Goal" :in-theory (enable formatp lpn prec expw bias)
                  :use ((:instance fp-rep-unique (x (lpn f)) (m (- 2 (expt 2 (- 1 (prec f))))) (e (- (expt 2 (expw f)) (+ 2 (bias f)))))))))

(defthmd nrepp-lpn
  (implies (formatp f)
           (nrepp (lpn f) f))
  :hints (("Goal" :in-theory (enable nrepp expo-lpn sig-lpn exactp)
                  :use (positive-lpn))
          ("Goal'4'" :in-theory (enable formatp expw))))

(local-defthmd largest-lpn-1
  (implies (and (> x 0)
                (nrepp x f))
           (<= x (lpn f)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal" :in-theory (enable exactp-2**n lpn fp- nrepp)
                  :use (positive-lpn
                        (:instance expo>= (n (- (expt 2 (expw f)) (1+ (bias f)))))
                        (:instance fp-2 (n (prec f)) (x (expt 2 (- (expt 2 (expw f)) (1+ (bias f))))) (y x))))))

(defthmd largest-lpn
  (implies (nrepp x f)
           (<= x (lpn f)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal" :in-theory (enable nrepp) :use (largest-lpn-1 positive-lpn))))

(defruled lpn<abs-as-expo
  (implies
   (and (rationalp x)
        (exactp x (prec f))
        (formatp f))
   (equal (< (lpn f) (abs x))
          (< (bias f) (expo x))))
  :prep-lemmas (
    (defrule lemma
      (implies
        (formatp f)
        (equal (expt 2 (expw f))
               (+ 2 (* 2 (bias f)))))
      :enable bias))
  :enable (nrepp expo-lpn)
  :cases ((< (expo x) (bias f))
          (> (expo x) (bias f))
          (= (expo x) (bias f)))
  :hints (
   ("subgoal 3" :use (:instance expo-monotone
                       (x (lpn f))
                       (y x)))
   ("subgoal 2" :use (:instance expo-monotone
                       (x x)
                       (y (lpn f))))
   ("subgoal 1" :use (:instance largest-lpn
                       (x (abs x))))))

;;;***************************************************************
;;;               Denormals and Zeroes
;;;***************************************************************

; (defund zerp (x f) ... )
; (defund zencode (sgn f) ... )
; (defund denormp (x f) ... )
; (defund pseudop (x f) ... )
; (defund ddecode (x f) ... )
; (defund decode (x f) ... )

(defruled decode-0
  (implies
    (encodingp x f)
    (equal (equal (decode x f) 0)
           (zerp x f)))
  :enable (decode ddecode ndecode zerp manf))

(local-defthm sgn-ddecode-1
  (implies (pseudop x f)
           (not (= (sigf x f) 0)))
  :hints (("Goal" :in-theory (enable  sigw sigf pseudop)
                  :use (:instance bitn-bits (i (1- (prec f))) (j 0) (k (1- (prec f)))))))

(defthm sgn-ddecode
  (implies (or (denormp x f) (pseudop x f))
           (equal (sgn (ddecode x f))
                  (if (= (sgnf x f) 0) 1 -1)))
  :hints (("Goal" :in-theory (enable sgn sigw sigf denormp pseudop ddecode)
                  :use (sgn-ddecode-1))))

(defthm expo-ddecode
  (implies (or (denormp x f) (pseudop x f))
	   (equal (expo (ddecode x f))
	          (+ 2 (- (prec f)) (- (bias f)) (expo (sigf x f)))))
  :hints (("Goal" :in-theory (enable ddecode denormp pseudop)
                  :use (sgn-ddecode-1
                        (:instance expo-shift (x (sigf x f)) (n (+ 2 (- (bias f)) (- (prec f)))))))))

(defthm sig-ddecode
  (implies (or (denormp x f) (pseudop x f))
           (equal (sig (ddecode x f))
                  (sig (sigf x f))))
  :hints (("Goal" :in-theory (enable ddecode denormp)
                  :use ((:instance sig-shift (x (sigf x f)) (n (+ 2 (- (bias f)) (- (prec f)))))))))

; (defund drepp (x f) ... )
; (defund dencode (x f) ... )

(defthmd drepp-exactp
  (implies (drepp x f)
           (exactp x (prec f)))
  :hints (("Goal" :in-theory (enable drepp formatp prec bias expw)
                  :use ((:instance exactp-<= (m (+ (1- (prec f)) (bias f) (expo
                                                                           x))) (n (prec f)))))))

(local-defthmd drepp-dencode-1
  (implies (denormp x f)
           (not (zerop (ddecode x f))))
  :hints (("Goal" :in-theory (enable sgn)
                  :use (sgn-ddecode))))

(local-defthm drepp-dencode-2
  (implies (denormp x f)
           (and (< 0 (sigf x f))
                (< (sigf x f) (expt 2 (1- (prec f))))))
  :hints (("Goal" :in-theory (enable sigf denormp sigw)
                  :use ((:instance bits-bounds (i (- (prec f) 2)) (j 0))
                        (:instance bitn-plus-bits (n (1- (prec f))) (m 0))))))

(local-defthmd drepp-dencode-3
  (implies (denormp x f)
           (and (<= 0 (expo (sigf x f)))
                (< (expo (sigf x f)) (1- (prec f)))))
  :hints (("Goal" :use (drepp-dencode-2
                        (:instance expo<= (x (sigf x f)) (n (- (prec f) 2)))
                        (:instance expo>= (x (sigf x f)) (n 0))))))

(local-defthmd drepp-dencode-4
  (implies (denormp x f)
           (exactp (sigf x f) (1+ (expo (sigf x f)))))
  :hints (("Goal" :in-theory (enable exactp2))))

(local-defthmd drepp-dencode-5
  (implies (denormp x f)
           (exactp (ddecode x f) (+ (1- (prec f)) (bias f) (expo (ddecode x f)))))
  :hints (("Goal" :in-theory (enable exactp sig-ddecode expo-ddecode)
                  :use (drepp-dencode-4))))

(defthm drepp-ddecode
  (implies (denormp x f)
           (drepp (ddecode x f) f))
  :hints (("Goal" :in-theory (enable denormp drepp)
                  :use (drepp-dencode-1 drepp-dencode-3 drepp-dencode-5))))

(local-defthmd dencode-ddecode-1
    (implies (denormp x f)
	     (equal (bitn (dencode (ddecode x f) f) (+ (expw f) (sigw f)))
		    (bitn x (+ (expw f) (sigw f)))))
  :hints (("Goal" :in-theory (enable denormp bitn-cat sgnf dencode)
                  :use (sgn-ddecode))))

(local-defthmd dencode-ddecode-2
    (implies (denormp x f)
	     (equal (bits (dencode (ddecode x f) f) (1- (+ (expw f) (sigw f))) (sigw f))
		    (bits x (1- (+ (expw f) (sigw f))) (sigw f))))
  :hints (("Goal" :in-theory (enable bits-cat expf  sigw denormp dencode)
                  :use (expo-ddecode))))

(local-defthmd dencode-ddecode-3
    (implies (denormp x f)
	     (equal (bits (dencode (ddecode x f) f) (1- (sigw f)) 0)
		    (bits (* (sig (sigf x f)) (expt 2 (expo (sigf x f)))) (1- (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable denormp bits-cat dencode sig-ddecode expo-ddecode))))

(local-defthmd dencode-ddecode-4
    (implies (denormp x f)
	     (equal (bits (dencode (ddecode x f) f) (1- (sigw f)) 0)
		    (bits (sigf x f) (1- (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable sgn)
                  :use (dencode-ddecode-3 (:instance fp-rep (x (sigf x f)))))))

(local-defthmd dencode-ddecode-5
    (implies (denormp x f)
	     (equal (bits (dencode (ddecode x f) f) (1- (sigw f)) 0)
		    (bits x (1- (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable bits-bits sigf)
                  :use (dencode-ddecode-4 (:instance fp-rep (x (sigf x f)))))))

(local-defthmd dencode-ddecode-6
    (implies (denormp x f)
	     (equal (bits (dencode (ddecode x f) f) (+ (expw f) (sigw f)) 0)
		    (bits x (+ (expw f) (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable denormp)
                  :use (dencode-ddecode-1 dencode-ddecode-2 dencode-ddecode-5
                        (:instance bitn-plus-bits (n (+ (expw f) (sigw f))) (m 0))
                        (:instance bitn-plus-bits (x (dencode (ddecode x f) f)) (n (+ (expw f) (sigw f))) (m 0))
                        (:instance bits-plus-bits (n (1- (+ (expw f) (sigw f)))) (p (sigw f)) (m 0))
                        (:instance bits-plus-bits (x (dencode (ddecode x f) f)) (n (1- (+ (expw f) (sigw f)))) (p (sigw f)) (m 0))))))

(local-defthmd dencode-ddecode-7
    (implies (denormp x f)
	     (and (bvecp (dencode (ddecode x f) f) (1+ (+ (expw f) (sigw f))))
		  (bvecp x (1+ (+ (expw f) (sigw f))))))
  :hints (("Goal" :in-theory (enable denormp encodingp dencode))))

(defthm dencode-ddecode
    (implies (denormp x f)
	     (equal (dencode (ddecode x f) f)
		    x))
  :hints (("Goal" :use (dencode-ddecode-7 dencode-ddecode-6))))

(local-defthm denormp-dencode-1
    (implies (drepp x f)
             (encodingp (dencode x f) f))
  :hints (("Goal" :in-theory (enable encodingp formatp dencode expw sigw prec drepp))))

(local-defthm denormp-dencode-2
    (implies (drepp x f)
             (equal (expf (dencode x f) f) 0))
  :hints (("Goal" :in-theory (enable bits-cat expf formatp dencode expw sigw prec drepp))))

(local-defthmd denormp-dencode-3
    (implies (and (explicitp f)
                  (drepp x f))
             (equal (bitn (dencode x f) (1- (prec f)))
                    (bitn (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f)))) (1- (prec f)))))
  :hints (("Goal" :in-theory (enable bitn-cat expf sigf formatp dencode expw sigw prec drepp))))

(local-defthm hack-3
  (implies (and (real/rationalp x)
                (integerp n)
                (< x (expt 2 m))
                (integerp m)
                (<= m n))
           (< (* x (expt 2 (- n))) 1))
  :rule-classes ()
  :hints (("Goal" :use (hack-2))))

(local-defthmd denormp-dencode-4
    (implies (drepp x f)
             (< (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f)))) (expt 2 (1- (prec f)))))
  :hints (("Goal" :use (sig-upper-bound
                        (:instance hack-3 (x (sig x)) (m 1) (n (- 1 (+ (expo x) (bias f))))))
                  :in-theory (enable formatp prec drepp))))

(local-defthmd denormp-dencode-5
    (implies (drepp x f)
             (equal (bitn (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f)))) (1- (prec f))) 0))
  :hints (("Goal" :use (denormp-dencode-4
                        (:instance bvecp-bitn-0 (x (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f))))) (n (1- (prec f)))))
                   :in-theory (enable exactp bvecp formatp prec drepp))))

(local-defthmd denormp-dencode-6
    (implies (drepp x f)
             (bvecp (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f)))) (1- (prec f))))
  :hints (("Goal" :use (denormp-dencode-4)
                   :in-theory (enable exactp bvecp formatp prec drepp))))

(local-defthmd denormp-dencode-7
    (implies (drepp x f)
             (equal (manf (dencode x f) f) (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f))))))
  :hints (("Goal" :use (denormp-dencode-6)
                   :in-theory (enable drepp manf bits-bits sigw bits-cat dencode))))

(local-defthmd denormp-dencode-8
    (implies (drepp x f)
             (< 0 (manf (dencode x f) f)))
  :hints (("Goal" :use (denormp-dencode-7 sig-lower-bound)
                   :in-theory (enable drepp))))

(local-defthmd denormp-dencode-9
    (implies (drepp x f)
             (not (= (sigf (dencode x f) f) 0)))
  :hints (("Goal" :use (denormp-dencode-8
                        (:instance bitn-plus-bits (x (dencode x f)) (n (1- (prec f))) (m 0)))
                   :in-theory (enable manf sigf sigw drepp))))

(defthm denormp-dencode
  (implies (drepp x f)
           (denormp (dencode x f) f))
  :hints (("Goal" :use (denormp-dencode-1 denormp-dencode-2 denormp-dencode-3 denormp-dencode-5 denormp-dencode-9)
                  :in-theory (enable denormp))))

(local-defthmd ddecode-dencode-1
    (implies (drepp x f)
	     (equal (sgn (ddecode (dencode x f) f))
		    (sgn x)))
  :hints (("Goal" :in-theory (enable sgn drepp bitn-cat sgnf dencode)
                  :use (denormp-dencode
                        (:instance sgn-ddecode (x (dencode x f)))))))

(local-defthmd ddecode-dencode-2
  (implies (formatp f)
           (>= (sigw f) 1))
  :hints (("Goal" :in-theory (enable formatp sigw prec))))

(local-defthmd ddecode-dencode-3
    (implies (drepp x f)
             (equal (sigf (dencode x f) f) (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f))))))
  :hints (("Goal" :use (denormp-dencode-7 denormp-dencode
                        (:instance bitn-plus-bits (x (dencode x f)) (n (1- (prec f))) (m 0)))
                   :in-theory (e/d (drepp formatp prec expw sigw manf sigf denormp) (denormp-dencode)))))

(local-defthmd ddecode-dencode-4
    (implies (drepp x f)
             (equal (expo (sigf (dencode x f) f))
                    (+ -2 (prec f) (expo x) (bias f))))
  :hints (("Goal" :use (sig-lower-bound (:instance expo-shift (x (sig x)) (n (+ -2 (prec f) (expo x) (bias f)))))
                   :in-theory (enable ddecode-dencode-3 drepp))))

(local-defthmd ddecode-dencode-5
    (implies (drepp x f)
	     (equal (expo (ddecode (dencode x f) f))
		    (expo x)))
  :hints (("Goal" :in-theory (enable ddecode-dencode-4 expo-ddecode))))

(local-defthmd ddecode-dencode-6
    (implies (drepp x f)
	     (equal (sig (ddecode (dencode x f) f))
		    (sig x)))
  :hints (("Goal" :in-theory (enable ddecode-dencode-3 sig-ddecode)
                  :use (denormp-dencode
                        (:instance sig-shift (x (sig x)) (n (+ -2 (prec f) (expo x) (bias f))))))))

(defthm ddecode-dencode
  (implies (drepp x f)
           (equal (ddecode (dencode x f) f)
                  x))
  :hints (("Goal" :use (fp-rep (:instance fp-rep (x (ddecode (dencode x f) f))))
                  :in-theory (enable drepp ddecode-dencode-1 ddecode-dencode-5 ddecode-dencode-6))))


(defthmd drepp<spn
  (implies (drepp x f)
           (< (abs x) (spn f)))
  :hints (("Goal" :in-theory (enable formatp spn drepp bias expw)
           :use ((:instance expo>= (x (abs x)) (n (- 1 (bias f))))))))

;; Smallest positive denormal:

; (defund spd (f) ... )

(defthm positive-spd
  (implies (formatp f)
           (> (spd f) 0))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable spd))))

(defthmd drepp-spd
  (implies (formatp f)
           (drepp (spd f) f))
  :hints (("Goal" :in-theory (enable bias exactp-2**n formatp expw prec drepp spd))))

(defthmd smallest-spd
  (implies (drepp r f)
           (>= (abs r) (spd f)))
  :hints (("Goal" :use ((:instance expo<= (x (abs r)) (n (- 1 (+ (prec f) (bias f))))))
                  :in-theory (enable spd drepp))))

(defruled spd-mult
  (implies (and (formatp f)
                (> r 0)
		(= m (/ r (spd f))))
	   (iff (drepp r f)
		(and (natp m)
		     (<= 1 m)
		     (< m (expt 2 (1- (prec f)))))))
  :prep-lemmas (
    (defrule lemma
      (implies (and (posp p)
                    (rationalp x)
                    (> x 0))
               (iff (and
                      (<= 0 (expo x))
                      (<= (expo x) (- p 2))
                      (exactp x (1+ (expo x))))
                    (and
                      (natp x)
                      (<= 1 x)
                      (< x (expt 2 (1- p))))))
      :enable (exactp2)
      :use (
        (:instance expo>= (n (1- p)))
        (:instance expo>= (n 0))
        (:instance expo<= (n (- p 2))))
      :rule-classes ()))
  :enable (drepp spd)
  :use (
    (:instance expo-shift
      (x (/ r (spd f)))
      (n (+ 2 (- (bias f)) (- (prec f)))))
    (:instance exactp-shift
      (x (/ r (spd f)))
      (k (+ 2 (- (bias f)) (- (prec f))))
      (n (1+ (expo (/ r (spd f))))))
    (:instance lemma
      (x m)
      (p (prec f)))))


;;;***************************************************************
;;;                 Infinities and NaNs
;;;***************************************************************

; (defund infp (x f) ... )
; (defun iencode (sgn f) ... )
; (defund nanp (x f) ... )
; (defund qnanp (x f) ... )
; (defund snanp (x f) ... )
; (defund qnanize (x f) ... )
; (defund indef (f) ... )

;;Use this to induce case-splitting:

(defrule encodingp-case-splitting
  (implies (encodingp x f)
           (or (zerp x f)
               (denormp x f)
               (pseudop x f)
               (normp x f)
               (infp x f)
               (nanp x f)
               (unsupp x f)))
  :prep-lemmas (
    (defrule bvecp-0
      (bvecp 0 n)
      :enable bvecp))
  :enable (encodingp zerp denormp pseudop normp infp nanp unsupp
           sigw sigf)
  :cases ((bvecp (expf x f) (expw f)))
  :hints (("subgoal 2" :in-theory (enable expf)))
  :rule-classes ())

(defrule encodingp-disjoint-cases
  (and
    (implies (zerp x f)
             (and (encodingp x f)
                  (not (denormp x f))
                  (not (pseudop x f))
                  (not (normp x f))
                  (not (infp x f))
                  (not (nanp x f))
                  (not (unsupp x f))))
    (implies (denormp x f)
             (and (encodingp x f)
                  (not (zerp x f))
                  (not (pseudop x f))
                  (not (normp x f))
                  (not (infp x f))
                  (not (nanp x f))
                  (not (unsupp x f))))
    (implies (pseudop x f)
             (and (encodingp x f)
                  (not (zerp x f))
                  (not (denormp x f))
                  (not (normp x f))
                  (not (infp x f))
                  (not (nanp x f))
                  (not (unsupp x f))))
    (implies (normp x f)
             (and (encodingp x f)
                  (not (zerp x f))
                  (not (denormp x f))
                  (not (pseudop x f))
                  (not (infp x f))
                  (not (nanp x f))
                  (not (unsupp x f))))
    (implies (infp x f)
             (and (encodingp x f)
                  (not (zerp x f))
                  (not (denormp x f))
                  (not (pseudop x f))
                  (not (normp x f))
                  (not (nanp x f))
                  (not (unsupp x f))))
    (implies (nanp x f)
             (and (encodingp x f)
                  (not (zerp x f))
                  (not (denormp x f))
                  (not (pseudop x f))
                  (not (normp x f))
                  (not (infp x f))
                  (not (unsupp x f))))
    (implies (unsupp x f)
             (and (encodingp x f)
                  (not (zerp x f))
                  (not (denormp x f))
                  (not (pseudop x f))
                  (not (normp x f))
                  (not (infp x f))
                  (not (nanp x f)))))
  :enable (zerp denormp pseudop normp infp nanp unsupp
           sigf sigw)
  :use (:instance bitn-bits
         (i (1- (prec f)))
         (j 0)
         (k (1- (prec f)))))

;;;***************************************************************
;;;                Rebiasing Exponents
;;;***************************************************************

; (defund rebias (expo old new) ... )

(acl2::with-arith5-nonlinear-help (defrule bvecp-rebias-up
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (bvecp (rebias x m n) n))
  :enable (rebias bvecp)))

(defrule natp-rebias-up
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (natp (rebias x m n)))
  :disable bvecp-rebias-up
  :use bvecp-rebias-up)

(acl2::with-arith5-nonlinear-help (defrule bvecp-rebias-down
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (bvecp (rebias x n m) m))
  :enable (rebias bvecp)))

(defrule natp-rebias-down
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (natp (rebias x n m)))
  :disable bvecp-rebias-down
  :use bvecp-rebias-down)


(acl2::with-arith5-nonlinear-help (defruled rebias-lower
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (equal (rebias x n m)
		    (cat (bitn x (1- n))
			 1
			 (bits x (- m 2) 0)
			 (1- m))))
  :enable (rebias binary-cat bits-mod bitn-def)
  :use (
    (:instance mod-force
      (m x)
      (n (expt 2 (1- m)))
      (a (if (< x (expt 2 (1- n)))
             (1- (expt 2 (- n m)))
             (expt 2 (- n m)))))
   (:instance fl-unique
     (x (* x (expt 2 (- 1 n))))
     (n (if (< x (expt 2 (1- n))) 0 1))))))

(defruled rebias-higher
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x m))
	     (equal (rebias x m n)
		    (cat (cat (bitn x (1- m))
			      1
			      (mulcat 1 (- n m) (bitn (lognot x) (1- m)))
			      (- n m))
			 (1+ (- n m))
			 (bits x (- m 2) 0)
			 (1- m))))
  :prep-lemmas (
    (acl2::with-arith5-nonlinear-help (defrule lemma1
      (implies (and (posp m) (natp x) (< x (expt 2 (1- m))))
               (equal (bitn x (1- m)) 0))
      :enable (bitn-def fl)))
    (acl2::with-arith5-nonlinear-help (defrule lemma2
      (implies (and (posp m) (integerp x) (>= x (expt 2 (1- m))) (< x (expt 2 m)))
               (equal (bitn x (1- m)) 1))
      :enable (bitn-def fl)))
    (defrule lemma3
     (implies (and (posp m) (bvecp x m))
              (equal (bitn x (1- m))
                     (if (< x (expt 2 (1- m))) 0 1)))
      :cases ((< x (expt 2 (1- m)))))
    (defrule lemma4
     (implies (and (posp m) (bvecp x m))
              (equal (bitn (lognot x) (1- m))
                     (if (< x (expt 2 (1- m))) 1 0)))
     :enable (lognot)))
  :enable (rebias binary-cat bits-mod)
  :use (:instance mod-force
         (m x)
         (n (expt 2 (1- m)))
         (a (if (< x (expt 2 (1- m))) 0 1))))
