; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
;
; Contact:
;   David M. Russinoff
;   1106 W 9th St., Austin, TX 78703
;   david@russinoff.com
;   http://www.russinoff.com/
;
; See license file books/rtl/rel11/license.txt.
;

(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "../support/top"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

(include-book "defs")

;;;***************************************************************
;;;               Classification of Formats
;;;***************************************************************

(defsection-rtl |Classification of Formats| |Floating-Point Formats|

;;Format parameters:

(defnd formatp (f)
  (and (consp f)
       (consp (cdr f))
       (consp (cddr f))
       (natp (cadr f))
       (> (cadr f) 1)
       (natp (caddr f))
       (> (caddr f) 1)))

(defund explicitp (f) (declare (xargs :guard (formatp f))) (car f))

(defund prec (f) (declare (xargs :guard (formatp f))) (cadr f))

(defund expw (f) (declare (xargs :guard (formatp f))) (caddr f))

(defund sigw (f)
  (declare (xargs :guard (formatp f)))
  (if (explicitp f)
      (prec f)
    (1- (prec f))))

(defnd encodingp (x f)
  (and (formatp f) (bvecp x (+ 1 (expw f) (sigw f)))))

;;Examples:

(defnd hp () '(nil 11 5))

(defnd sp () '(nil 24 8))

(defnd dp () '(nil 53 11))

(defnd bf () '(nil 8 8))

(defnd ep () '(t 64 15))

(in-theory (disable (sp) (dp) (hp) (bf) (ep)))

(defthm formatp-sp
  (formatp (sp)))

(defthm formatp-dp
  (formatp (dp)))

(defthm formatp-hp
  (formatp (hp)))

(defthm formatp-ep
  (formatp (ep)))

;;Field extractors:

(defund sgnf (x f)
  (declare (xargs :guard (encodingp x f)))
  (bitn x (+ (expw f) (sigw f))))

(defund expf (x f)
  (declare (xargs :guard (encodingp x f)))
  (bits x (1- (+ (expw f) (sigw f))) (sigw f)))

(defund sigf (x f)
  (declare (xargs :guard (encodingp x f)))
  (bits x (1- (sigw f)) 0))

(defund manf (x f)
  (declare (xargs :guard (encodingp x f)))
  (bits x (- (prec f) 2) 0))

;;Exponent bias:

(defund bias (f) (declare (xargs :guard (formatp f))) (- (expt 2 (- (expw f) 1)) 1))

)
;;;***************************************************************
;;;                    Normal Encodings
;;;***************************************************************

(defsection-rtl |Normal Encodings| |Floating-Point Formats|

(defund normp (x f)
  (declare (xargs :guard (encodingp x f)))
  (and (mbt (encodingp x f))
       (< 0 (expf x f))
       (< (expf x f) (1- (expt 2 (expw f))))
       (implies (explicitp f) (= (bitn x (1- (prec f))) 1))))

(defund unsupp (x f)
  (declare (xargs :guard (encodingp x f)))
  (and (mbt (encodingp x f))
       (explicitp f)
       (< 0 (expf x f))
       (= (bitn x (1- (prec f))) 0)))

;;Decoding function:

(defund ndecode (x f)
  (declare (xargs :guard (encodingp x f)))
  (* (if (= (sgnf x f) 0) 1 -1)
     (expt 2 (- (expf x f) (bias f)))
     (1+ (* (manf x f) (expt 2 (- 1 (prec f)))))))

(defthmd sgn-ndecode
    (implies (normp x f)
	     (equal (sgn (ndecode x f))
		    (if (= (sgnf x f) 0) 1 -1))))

(defthmd expo-ndecode
    (implies (normp x f)
	     (equal (expo (ndecode x f))
		    (- (expf x f) (bias f)))))

(defthmd sig-ndecode
    (implies (normp x f)
	     (equal (sig (ndecode x f))
		    (+ 1 (/ (manf x f) (expt 2 (1- (prec f))))))))


;;Representable normals:

(defnd nrepp (x f)
  (and (rationalp x)
       (formatp f)
       (not (= x 0))
       (< 0 (+ (expo x) (bias f)))
       (< (+ (expo x) (bias f)) (1- (expt 2 (expw f))))
       (exactp x (prec f))))

;;Encoding function:

(defund nencode (x f)
  (declare (xargs :guard (nrepp x f)))
  (cat (if (= (sgn x) 1) 0 1)
       1
       (+ (expo x) (bias f))
       (expw f)
       (* (sig x) (expt 2 (1- (prec f))))
       (sigw f)))

;;Inversions:

(defthm nrepp-ndecode
    (implies (normp x f)
	     (nrepp (ndecode x f) f)))

(defthm nencode-ndecode
    (implies (normp x f)
	     (equal (nencode (ndecode x f) f)
		    x)))

(defthm normp-nencode
    (implies (nrepp x f)
             (normp (nencode x f) f)))

(defthm ndecode-nencode
    (implies (nrepp x f)
	     (equal (ndecode (nencode x f) f)
		    x)))

;; Smallest positive normal:

(defund spn (f)
  (declare (xargs :guard (formatp f)))
  (expt 2 (- 1 (bias f))))

(defthmd positive-spn
  (> (spn f) 0)
  :rule-classes ( :linear))

(defthmd nrepp-spn
  (implies (formatp f)
           (nrepp (spn f) f)))

(defthmd smallest-spn
  (implies (nrepp x f)
           (>= (abs x) (spn f)))
  :rule-classes
  ((:rewrite :match-free :once)))

;; Largest positive normal:

(defund lpn (f)
  (declare (xargs :guard (formatp f)))
  (* (expt 2 (- (expt 2 (expw f)) (+ 2 (bias f))))
     (- 2 (expt 2 (- 1 (prec f))))))

(defthmd positive-lpn
  (implies (formatp f)
           (> (lpn f) 0))
  :rule-classes ( :linear))

(defthmd expo-lpn
  (implies (formatp f)
           (equal (expo (lpn f))
                  (- (expt 2 (expw f)) (+ 2 (bias f))))))

(defthmd sig-lpn
  (implies (formatp f)
           (equal (sig (lpn f))
                  (- 2 (expt 2 (- 1 (prec f)))))))

(defthmd nrepp-lpn
  (implies (formatp f)
           (nrepp (lpn f) f)))

(defthmd largest-lpn
  (implies (nrepp x f)
           (<= x (lpn f)))
  :rule-classes
  ((:rewrite :match-free :once)))
)

;;;***************************************************************
;;;               Denormals and Zeroes
;;;***************************************************************

(defsection-rtl |Denormals and Zeroes| |Floating-Point Formats|

(defund zerp (x f)
  (declare (xargs :guard (encodingp x f)))
  (and (mbt (encodingp x f))
       (= (expf x f) 0)
       (= (sigf x f) 0)))

(defund zencode (sgn f)
  (declare (xargs :guard (and (bvecp sgn 1)
                              (formatp f))))
  (cat sgn 1 0 (+ (sigw f) (expw f))))

(defund denormp (x f)
  (declare (xargs :guard (encodingp x f)))
  (and (mbt (encodingp x f))
       (= (expf x f) 0)
       (not (= (sigf x f) 0))
       (implies (explicitp f) (= (bitn x (1- (prec f))) 0))))

(defund pseudop (x f)
  (declare (xargs :guard (encodingp x f)))
  (and (mbt (encodingp x f))
       (explicitp f)
       (= (expf x f) 0)
       (= (bitn x (1- (prec f))) 1)))

(defund ddecode (x f)
  (declare (xargs :guard (encodingp x f)))
  (* (if (= (sgnf x f) 0) 1 -1)
     (sigf x f)
     (expt 2 (+ 2 (- (bias f)) (- (prec f))))))

(defund decode (x f)
  (declare (xargs :guard (encodingp x f)))
  (if (= (expf x f) 0)
      (ddecode x f)
    (ndecode x f)))

(defthm sgn-ddecode
  (implies (or (denormp x f) (pseudop x f))
           (equal (sgn (ddecode x f))
                  (if (= (sgnf x f) 0) 1 -1))))

(defthm expo-ddecode
  (implies (or (denormp x f) (pseudop x f))
	   (equal (expo (ddecode x f))
	          (+ 2 (- (prec f)) (- (bias f)) (expo (sigf x f))))))

(defthm sig-ddecode
  (implies (or (denormp x f) (pseudop x f))
           (equal (sig (ddecode x f))
                  (sig (sigf x f)))))

(defnd drepp (x f)
  (and (rationalp x)
       (formatp f)
       (not (= x 0))
       (<= (- 2 (prec f)) (+ (expo x) (bias f)))
       (<= (+ (expo x) (bias f)) 0)
       (exactp x (+ (1- (prec f)) (bias f) (expo x)))))

(defthmd drepp-exactp
  (implies (drepp x f)
           (exactp x (prec f))))

(defund dencode (x f)
  (declare (xargs :guard (drepp x f)))
  (cat (if (= (sgn x) 1) 0 1)
       1
       0
       (expw f)
       (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f))))
       (sigw f)))

(defthm drepp-ddecode
  (implies (denormp x f)
           (drepp (ddecode x f) f)))

(defthm dencode-ddecode
  (implies (denormp x f)
           (equal (dencode (ddecode x f) f)
                  x)))

(defthm denormp-dencode
  (implies (drepp x f)
           (denormp (dencode x f) f)))

(defthm ddecode-dencode
  (implies (drepp x f)
           (equal (ddecode (dencode x f) f)
                  x)))

(defthmd drepp<spn
  (implies (drepp x f)
           (< (abs x) (spn f))))

;; Smallest positive denormal:

(defund spd (f)
     (declare (xargs :guard (formatp f)))
     (expt 2 (+ 2 (- (bias f)) (- (prec f)))))

(defthm positive-spd
  (implies (formatp f)
           (> (spd f) 0))
  :rule-classes :linear)

(defthmd drepp-spd
  (implies (formatp f)
           (drepp (spd f) f)))

(defthmd smallest-spd
  (implies (drepp r f)
           (>= (abs r) (spd f))))

(defthmd spd-mult
  (implies (and (formatp f)
                (> r 0)
		(= m (/ r (spd f))))
	   (iff (drepp r f)
		(and (natp m)
		     (<= 1 m)
		     (< m (expt 2 (1- (prec f))))))))

)
;;;***************************************************************
;;;                 Infinities and NaNs
;;;***************************************************************

(defsection-rtl |Infinities and NaNs| |Floating-Point Formats|

(defund infp (x f)
  (declare (xargs :guard (encodingp x f)))
  (and (mbt (encodingp x f))
       (= (expf x f) (1- (expt 2 (expw f))))
       (not (unsupp x f))
       (= (manf x f) 0)))

(defun iencode (sgn f)
  (declare (xargs :guard (and (bvecp sgn 1)
                              (formatp f))))
  (if (explicitp f)
      (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 1 1 0 (1- (sigw f)))
    (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 0 (sigw f))))

(defund nanp (x f)
  (declare (xargs :guard (encodingp x f)))
  (and (mbt (encodingp x f))
       (= (expf x f) (1- (expt 2 (expw f))))
       (not (unsupp x f))
       (not (= (manf x f) 0))))

(defund qnanp (x f)
  (declare (xargs :guard (encodingp x f)))
  (and (nanp x f) (= (bitn x (- (prec f) 2)) 1)))

(defund snanp (x f)
  (declare (xargs :guard (encodingp x f)))
  (and (nanp x f) (= (bitn x (- (prec f) 2)) 0)))

(defund qnanize (x f)
  (declare (xargs :guard (encodingp x f)))
  (logior x (expt 2 (- (prec f) 2))))

(defund indef (f)
  (declare (xargs :guard (formatp f)))
  (if (explicitp f)
      (cat (1- (expt 2 (+ (expw f) 2)))
           (+ (expw f) 2)
           0
           (- (sigw f) 2))
    (cat (1- (expt 2 (+ (expw f) 1)))
         (+ (expw f) 1)
         0
         (1- (sigw f)))))

)
;;;***************************************************************
;;;                Rebiasing Exponents
;;;***************************************************************

(defsection-rtl |Rebiasing Exponents| |Floating-Point Formats|

(defund rebias (expo old new)
  (declare (xargs :guard (and (integerp expo)
                              (posp old)
                              (posp new))))
  (+ expo (- (expt 2 (1- new)) (expt 2 (1- old)))))

(defthm natp-rebias-up
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (natp (rebias x m n))))

(defthm natp-rebias-down
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (natp (rebias x n m))))

(defthm bvecp-rebias-up
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (bvecp (rebias x m n) n)))

(defthm bvecp-rebias-down
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (bvecp (rebias x n m) m)))

(defthmd rebias-lower
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
			 (1- m)))))

(defthmd rebias-higher
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
			 (1- m)))))
)
