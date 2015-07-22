; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic 
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc. 
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT ANY
; WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
; PARTICULAR PURPOSE.  See the GNU General Public License for more details.
;
; You should have received a copy of the GNU General Public License along with
; this program; see the file "gpl.txt" in this directory.  If not, write to the
; Free Software Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA
; 02110-1335, USA.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "../support/top"))

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
;;;               Classification of Formats
;;;***************************************************************

(defsection-rtl |Classification of Formats| |Floating-Point Formats|

;;Format parameters:

(defund formatp (f)
  (declare (xargs :guard t))
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

(defund encodingp (x f)
  (declare (xargs :guard (formatp f)))
  (bvecp x (+ 1 (expw f) (sigw f))))

;;Examples:

(defund sp () (declare (xargs :guard t)) '(nil 24 8))

(defund dp () (declare (xargs :guard t)) '(nil 53 11))

(defund ep () (declare (xargs :guard t)) '(t 64 15)) 

(in-theory (disable (sp) (dp) (ep)))

;;Field extractors:

(defund sgnf (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (bitn x (+ (expw f) (sigw f))))

(defund expf (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (bits x (1- (+ (expw f) (sigw f))) (sigw f)))

(defund sigf (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (bits x (1- (sigw f)) 0))

(defund manf (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (bits x (- (prec f) 2) 0))

;;Exponent bias:

(defund bias (f) (declare (xargs :guard (formatp f))) (- (expt 2 (- (expw f) 1)) 1))

)
;;;***************************************************************
;;;                    Normal Encodings
;;;***************************************************************

(defsection-rtl |Normal Encodings| |Floating-Point Formats|

(defund normp (x f)
  (declare (xargs :guard (formatp f)))
  (and (encodingp x f)
       (< 0 (expf x f))
       (< (expf x f) (1- (expt 2 (expw f))))
       (implies (explicitp f) (= (bitn x (1- (prec f))) 1))))

(defund unsupp (x f)
  (declare (xargs :guard (formatp f)))
  (and (explicitp f)
       (encodingp x f)
       (< 0 (expf x f))
       (= (bitn x (1- (prec f))) 0)))

;;Decoding function:

(defund ndecode (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (* (if (= (sgnf x f) 0) 1 -1)
     (expt 2 (- (expf x f) (bias f)))
     (1+ (* (manf x f) (expt 2 (- 1 (prec f)))))))

(defthmd sgn-ndecode
    (implies (and (formatp f)
                  (normp x f))
	     (equal (sgn (ndecode x f))
		    (if (= (sgnf x f) 0) 1 -1))))

(defthmd expo-ndecode
    (implies (and (formatp f)
		  (normp x f))
	     (equal (expo (ndecode x f))
		    (- (expf x f) (bias f)))))

(defthmd sig-ndecode
    (implies (and (formatp f)
		  (normp x f))
	     (equal (sig (ndecode x f))
		    (+ 1 (/ (manf x f) (expt 2 (1- (prec f))))))))


;;Representable normals:

(defund nrepp (x f)
  (and (rationalp x)
       (not (= x 0))
       (< 0 (+ (expo x) (bias f)))
       (< (+ (expo x) (bias f)) (1- (expt 2 (expw f))))
       (exactp x (prec f))))

;;Encoding function:

(defund nencode (x f)
  (cat (if (= (sgn x) 1) 0 1)
       1
       (+ (expo x) (bias f))
       (expw f)
       (* (sig x) (expt 2 (1- (prec f))))
       (sigw f)))

;;Inversions:

(defthm nrepp-ndecode
    (implies (and (formatp f)
                  (normp x f))
	     (nrepp (ndecode x f) f)))

(defthm nencode-ndecode
    (implies (and (formatp f)
                  (normp x f))
	     (equal (nencode (ndecode x f) f)
		    x)))

(defthm normp-nencode
    (implies (and (formatp f)
                  (nrepp x f))
             (normp (nencode x f) f)))

(defthm ndecode-nencode
    (implies (and (formatp f)
                  (nrepp x f))
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
  (implies (and (formatp f)
                (nrepp x f))
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
  (implies (and (formatp f)
                (nrepp x f))
           (<= x (lpn f)))
  :rule-classes
  ((:rewrite :match-free :once)))
)

;;;***************************************************************
;;;               Denormals and Zeroes
;;;***************************************************************

(defsection-rtl |Denormals and Zeroes| |Floating-Point Formats|

(defund zerp (x f)
  (declare (xargs :guard (formatp f)))
  (and (encodingp x f)
       (= (expf x f) 0)
       (= (sigf x f) 0)))

(defund zencode (sgn f) (cat sgn 1 0 (+ (sigw f) (expw f))))

(defund denormp (x f)
  (declare (xargs :guard (formatp f)))
  (and (encodingp x f)
       (= (expf x f) 0)
       (not (= (sigf x f) 0))
       (implies (explicitp f) (= (bitn x (1- (prec f))) 0))))

(defund pseudop (x f)
  (declare (xargs :guard (formatp f)))
  (and (explicitp f)
       (encodingp x f)
       (= (expf x f) 0)
       (= (bitn x (1- (prec f))) 1)))

(defund ddecode (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (* (if (= (sgnf x f) 0) 1 -1)
     (sigf x f)
     (expt 2 (+ 2 (- (bias f)) (- (prec f))))))

(defund decode (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (if (= (expf x f) 0)
      (ddecode x f)
    (ndecode x f)))

(defthm sgn-ddecode
  (implies (and (formatp f)
                (or (denormp x f) (pseudop x f)))
           (equal (sgn (ddecode x f))
                  (if (= (sgnf x f) 0) 1 -1))))

(defthm expo-ddecode
  (implies (and (formatp f)
                (or (denormp x f) (pseudop x f)))
	   (equal (expo (ddecode x f))
	          (+ 2 (- (prec f)) (- (bias f)) (expo (sigf x f))))))

(defthm sig-ddecode
  (implies (and (formatp f)
                (or (denormp x f) (pseudop x f)))
           (equal (sig (ddecode x f))
                  (sig (sigf x f)))))

(defund drepp (x f)
  (and (rationalp x)
       (not (= x 0))
       (<= (- 2 (prec f)) (+ (expo x) (bias f)))
       (<= (+ (expo x) (bias f)) 0)
       (exactp x (+ (1- (prec f)) (bias f) (expo x)))))

(defund dencode (x f)
  (cat (if (= (sgn x) 1) 0 1)
       1
       0
       (expw f)
       (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f))))
       (sigw f)))

(defthm drepp-ddecode
  (implies (and (formatp f)
                (denormp x f))
           (drepp (ddecode x f) f))
  :hints (("Goal" :in-theory (enable drepp)
                  :use (drepp-dencode-1 drepp-dencode-3 drepp-dencode-5))))

(defthm dencode-ddecode
  (implies (and (formatp f)
                (denormp x f))
           (equal (dencode (ddecode x f) f)
                  x)))

(defthm denormp-dencode
  (implies (and (formatp f)
                (drepp x f))
           (denormp (dencode x f) f)))

(defthm ddecode-dencode
  (implies (and (formatp f)
                (drepp x f))
           (equal (ddecode (dencode x f) f)
                  x)))

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
  (implies (and (formatp f)
                (drepp r f))
           (>= (abs r) (spd f))))

(defthmd spd-mult
  (implies (and (formatp f)
		(rationalp r)
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
  (declare (xargs :guard (formatp f)))
  (and (encodingp x f)
       (= (expf x f) (1- (expt 2 (expw f))))
       (not (unsupp x f))
       (= (manf x f) 0)))

(defun iencode (sgn f)
  (if (explicitp f)
      (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 1 1 0 (1- (sigw f)))
    (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 0 (sigw f))))

(defund nanp (x f)
  (declare (xargs :guard (formatp f)))
  (and (encodingp x f)
       (= (expf x f) (1- (expt 2 (expw f))))
       (not (unsupp x f))
       (not (= (manf x f) 0))))

(defund qnanp (x f)
  (declare (xargs :guard (formatp f)))
  (and (nanp x f) (= (bitn x (- (prec f) 2)) 1)))

(defund snanp (x f)
  (declare (xargs :guard (formatp f)))
  (and (nanp x f) (= (bitn x (- (prec f) 2)) 0)))

(defund qnanize (x f) 
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (logior x (expt 2 (- (prec f) 2))))

(defund indef (f)
  (if (explicitp f)
      (cat (1- (expt 2 (+ (expw f) 3))) 
           (+ (expw f) 3)
           0
           (- (sigw f) 2))
    (cat (1- (expt 2 (+ (expw f) 2))) 
         (+ (expw f) 2)
         0
         (1- (sigw f)))))

)
;;;***************************************************************
;;;                Rebiasing Exponents
;;;***************************************************************

(defsection-rtl |Rebiasing Exponents| |Floating-Point Formats|

(defund rebias (expo old new)
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
