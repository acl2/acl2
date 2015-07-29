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

(include-book "../rel9-rtl-pkg/lib/util")

(local (include-book "../rel9-rtl-pkg/lib/basic"))
(local (include-book "../rel9-rtl-pkg/lib/bits"))
(local (include-book "float"))

(local (include-book "arithmetic-5/top" :dir :system))

;; The following lemmas from arithmetic-5 have given me trouble:

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-< 
                    |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)|))

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

;;Format parameters:

(defun formatp (f)
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
  (declare (xargs :guard (formatp f)
                  :guard-hints (("goal" :in-theory (enable prec))))) 
  (if (explicitp f)
      (prec f)
    (1- (prec f))))

(in-theory (disable formatp))

(defthm natp-prec
  (implies (formatp f)
           (natp (prec f)))
  :hints (("Goal" :in-theory (enable formatp prec)))
  :rule-classes (:rewrite :type-prescription))

(defthm natp-expw
  (implies (formatp f)
           (natp (expw f)))
  :hints (("Goal" :in-theory (enable formatp expw)))
  :rule-classes (:rewrite :type-prescription))

(defthm natp-sigw
  (implies (formatp f)
           (natp (sigw f)))
  :hints (("Goal" :in-theory (enable formatp prec sigw)))
  :rule-classes (:rewrite :type-prescription))

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

(defund bias (f)
  (declare (xargs :guard (formatp f)))
  (- (expt 2 (- (expw f) 1)) 1))

(defthm natp-bias
  (implies (formatp f)
           (natp (bias f)))
  :hints (("Goal" :in-theory (enable expw formatp bias)))
  :rule-classes (:rewrite :type-prescription))


;;;***************************************************************
;;;                    Normal Encodings
;;;***************************************************************

(defund normp (x f)
  (declare (xargs :guard (formatp f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (and (encodingp x f)
       (< 0 (expf x f))
       (< (expf x f) (1- (expt 2 (expw f))))
       (implies (explicitp f) (= (bitn x (1- (prec f))) 1))))

(defund unsupp (x f)
  (declare (xargs :guard (formatp f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
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
		    (if (= (sgnf x f) 0) 1 -1)))
  :hints (("Goal" :in-theory (enable sgn normp ndecode))))

(local-defthmd expo-ndecode-1
    (implies (and (formatp f)
		  (normp x f))
             (equal (abs (ndecode x f))
                    (* (+ 1 (/ (manf x f) (expt 2 (1- (prec f)))))
                       (expt 2 (- (expf x f) (bias f))))))
  :hints (("Goal" :in-theory (enable ndecode))))

(local-defthm hack-1
  (implies (and (rationalp x)
                (rationalp y)
                (> y 0)
                (< x y))
           (< (* x (/ y)) 1))
  :rule-classes ())

(local-defthm hack-2
  (implies (and (rationalp x)
                (integerp n)
                (< x (expt 2 n)))
           (< (* x (expt 2 (- n))) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance hack-1 (y (expt 2 n)))))))

(local-defthmd expo-ndecode-2
    (implies (and (formatp f)
		  (normp x f))
             (and  (<= 0 (/ (manf x f) (expt 2 (1- (prec f)))))
                   (< (/ (manf x f) (expt 2 (1- (prec f)))) 1)))
  :hints (("Goal" :in-theory (enable manf)
                  :use ((:instance hack-2 (x (manf x f)) (n (1- (prec f))))
                        (:instance bits-bounds (i (- (prec f) 2)) (j 0))))))

(defthmd expo-ndecode
    (implies (and (formatp f)
		  (normp x f))
	     (equal (expo (ndecode x f))
		    (- (expf x f) (bias f))))
  :hints (("Goal" :in-theory (e/d (expo-ndecode-1 bias expw formatp prec) (abs)) 
                  :use (expo-ndecode-2
                        (:instance fp-rep-unique (x (ndecode x f)) (e (- (expf x f) (bias f))) (m (+ 1 (/ (manf x f) (expt 2 (1- (prec f)))))))))))

(defthmd sig-ndecode
    (implies (and (formatp f)
		  (normp x f))
	     (equal (sig (ndecode x f))
		    (+ 1 (/ (manf x f) (expt 2 (1- (prec f)))))))
  :hints (("Goal" :in-theory (e/d (expo-ndecode-1 bias expw formatp prec) (abs)) 
                  :use (expo-ndecode-2
                        (:instance fp-rep-unique (x (ndecode x f)) (e (- (expf x f) (bias f))) (m (+ 1 (/ (manf x f) (expt 2 (1- (prec f)))))))))))

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
           (nrepp (ndecode x f) f))
  :hints (("Goal" :in-theory (enable formatp prec normp nrepp expo-ndecode sig-ndecode exactp))))
                  

(local-defthmd nencode-ndecode-1
    (implies (and (formatp f)
                  (normp x f))
	     (equal (bitn (nencode (ndecode x f) f) (+ (expw f) (sigw f)))
		    (bitn x (+ (expw f) (sigw f)))))
  :hints (("Goal" :in-theory (enable bitn-cat sgnf nencode)
                  :use (sgn-ndecode))))

(local-defthmd nencode-ndecode-2
    (implies (and (formatp f)
                  (normp x f))
	     (equal (bits (nencode (ndecode x f) f) (1- (+ (expw f) (sigw f))) (sigw f))
		    (bits x (1- (+ (expw f) (sigw f))) (sigw f))))
  :hints (("Goal" :in-theory (enable bits-cat expf nencode)
                  :use (expo-ndecode))))

(local-defthmd nencode-ndecode-3
    (implies (and (formatp f)
                  (normp x f))
	     (equal (bits (nencode (ndecode x f) f) (1- (sigw f)) 0)
		    (bits (+ (expt 2 (1- (prec f))) (manf x f)) (1- (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable bits-cat nencode)
                  :use (sig-ndecode))))

(local-defthmd nencode-ndecode-4
    (implies (and (formatp f)
                  (explicitp f)
                  (normp x f))
	     (equal (bits x (1- (sigw f)) 0)
		    (bits (+ (expt 2 (1- (prec f))) (manf x f)) (1- (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable formatp sigw prec normp manf)
                  :use ((:instance bitn-plus-bits (n (1- (prec f))) (m 0))))))

(local-defthmd nencode-ndecode-5
    (implies (and (formatp f)
                  (not (explicitp f))
                  (normp x f))
	     (equal (bits x (1- (sigw f)) 0)
		    (bits (+ (expt 2 (1- (prec f))) (manf x f)) (1- (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable formatp sigw prec normp manf)
                  :use ((:instance bits-plus-mult-2 (x (manf x f)) (n (- (prec f) 2)) (m 0) (k (1- (prec f))) (y 1))))))

(local-defthmd nencode-ndecode-6
    (implies (and (formatp f)
                  (normp x f))
	     (equal (bits (nencode (ndecode x f) f) (1- (sigw f)) 0)
		    (bits x (1- (sigw f)) 0)))
  :hints (("Goal" :use (nencode-ndecode-3 nencode-ndecode-4 nencode-ndecode-5))))

(local-defthmd nencode-ndecode-7
    (implies (and (formatp f)
                  (normp x f))
	     (equal (bits (nencode (ndecode x f) f) (+ (expw f) (sigw f)) 0)
		    (bits x (+ (expw f) (sigw f)) 0)))
  :hints (("Goal" :use (nencode-ndecode-1 nencode-ndecode-2 nencode-ndecode-6
                        (:instance bitn-plus-bits (n (+ (expw f) (sigw f))) (m 0))
                        (:instance bitn-plus-bits (x (nencode (ndecode x f) f)) (n (+ (expw f) (sigw f))) (m 0))
                        (:instance bits-plus-bits (n (1- (+ (expw f) (sigw f)))) (p (sigw f)) (m 0))
                        (:instance bits-plus-bits (x (nencode (ndecode x f) f)) (n (1- (+ (expw f) (sigw f)))) (p (sigw f)) (m 0))))))

(local-defthmd nencode-ndecode-8
    (implies (and (formatp f)
                  (normp x f))
	     (and (bvecp (nencode (ndecode x f) f) (1+ (+ (expw f) (sigw f))))
		  (bvecp x (1+ (+ (expw f) (sigw f))))))
  :hints (("Goal" :in-theory (enable normp encodingp nencode))))

(defthm nencode-ndecode
    (implies (and (formatp f)
                  (normp x f))
	     (equal (nencode (ndecode x f) f)
		    x))
  :hints (("Goal" :use (nencode-ndecode-7 nencode-ndecode-8))))

(local-defthmd normp-nencode-1
    (implies (and (formatp f)
                  (nrepp x f))
             (bvecp (+ (bias f) (expo x)) (expw f)))
  :hints (("Goal" :in-theory (enable bvecp encodingp formatp bias expw nrepp))))

(local-defthm normp-nencode-2
    (implies (and (formatp f)
                  (nrepp x f))
             (encodingp (nencode x f) f))
  :hints (("Goal" :in-theory (enable encodingp formatp nencode expw sigw prec nrepp))))

(local-defthm normp-nencode-3
    (implies (and (formatp f)
                  (nrepp x f))
             (equal (expf (nencode x f) f)
                    (+ (bias f) (expo x))))
  :hints (("Goal" :use (normp-nencode-1)
                  :in-theory (enable bits-cat expf formatp nencode expw sigw prec nrepp))))

(local-defthmd normp-nencode-4
    (implies (and (formatp f)
                  (explicitp f)
                  (nrepp x f))
             (equal (bitn (nencode x f) (1- (prec f)))
                    (bitn (* (sig x) (expt 2 (1- (prec f)))) (1- (prec f)))))
  :hints (("Goal" :in-theory (enable bitn-cat expf sigf formatp nencode expw sigw prec nrepp))))

(local-defthmd normp-nencode-5
    (implies (and (formatp f)
                  ;(explicitp f)
                  (nrepp x f))
             (>= (* (sig x) (expt 2 (1- (prec f)))) (expt 2 (1- (prec f)))))
  :hints (("Goal" :use (sig-lower-bound)
                  :in-theory (enable formatp prec nrepp))))

(local-defthmd normp-nencode-6
    (implies (and (formatp f)
                  ;(explicitp f)
                  (nrepp x f))
             (< (* (sig x) (expt 2 (1- (prec f)))) (expt 2 (prec f))))
  :hints (("Goal" :use (sig-upper-bound)
                  :in-theory (enable formatp prec nrepp))))

(local-defthmd normp-nencode-7
    (implies (and (formatp f)
                  ;(explicitp f)
                  (nrepp x f))
             (equal (bitn (* (sig x) (expt 2 (1- (prec f)))) (1- (prec f))) 1))
  :hints (("Goal" :use (normp-nencode-5 normp-nencode-6
                        (:instance bvecp-bitn-1 (x (* (sig x) (expt 2 (1- (prec f))))) (n (1- (prec f)))))
                  :in-theory (enable exactp bvecp formatp prec nrepp))))

(defthm normp-nencode
    (implies (and (formatp f)
                  (nrepp x f))
             (normp (nencode x f) f))
  :hints (("Goal" :in-theory (enable nrepp normp)
                  :use (normp-nencode-2 normp-nencode-3 normp-nencode-4 normp-nencode-7))))

(local-defthmd ndecode-nencode-1
    (implies (and (formatp f)
                  (nrepp x f))
	     (equal (sgn (ndecode (nencode x f) f))
		    (sgn x)))
  :hints (("Goal" :in-theory (enable sgn nrepp bitn-cat sgnf nencode)
                  :use (normp-nencode
                        (:instance sgn-ndecode (x (nencode x f)))))))

(local-defthmd ndecode-nencode-2
    (implies (and (formatp f)
                  (nrepp x f))
	     (equal (expo (ndecode (nencode x f) f))
		    (expo x)))
  :hints (("Goal" :in-theory (enable nrepp bits-cat expf expo-ndecode)
                  :use (normp-nencode))))

(local-defthmd ndecode-nencode-3
    (implies (and (formatp f)
                  (nrepp x f))
             (bvecp (* (sig x) (expt 2 (1- (prec f)))) (prec f)))
  :hints (("Goal" :in-theory (enable exactp nrepp bvecp)
                  :use (normp-nencode-5 normp-nencode-6 normp-nencode))))

(local-defthmd ndecode-nencode-4
    (implies (and (formatp f)
                  (nrepp x f))
             (equal (bits (* (sig x) (expt 2 (+ -1 (prec f)))) (+ -2 (prec f)) 0)
                    (- (* (sig x) (expt 2 (1- (prec f))))
                       (expt 2 (1- (prec f))))))
  :hints (("Goal" :use (ndecode-nencode-3 normp-nencode-7
                        (:instance bitn-plus-bits (x (* (sig x) (expt 2 (1- (prec f))))) (n (1- (prec f))) (m 0))))))

(local-defthmd ndecode-nencode-5
    (implies (and (formatp f)
                  (nrepp x f))
	     (equal (manf (nencode x f) f)
		    (bits (* (sig x) (expt 2 (1- (prec f)))) (- (prec f) 2) 0)))
  :hints (("Goal" :in-theory (enable formatp sigw prec nrepp bits-cat manf nencode))))

(local-defthmd ndecode-nencode-6
    (implies (and (formatp f)
                  (nrepp x f))
	     (equal (sig (ndecode (nencode x f) f))
		    (sig x)))
  :hints (("Goal" :in-theory (enable ndecode-nencode-4 ndecode-nencode-5)
                  :use (normp-nencode
                        (:instance sig-ndecode (x (nencode x f)))))))

(defthm ndecode-nencode
    (implies (and (formatp f)
                  (nrepp x f))
	     (equal (ndecode (nencode x f) f)
		    x))
  :hints (("Goal" :use (fp-rep (:instance fp-rep (x (ndecode (nencode x f) f))))
                  :in-theory (enable nrepp ndecode-nencode-1 ndecode-nencode-2 ndecode-nencode-6))))

;; Smallest positive normal:

(defund spn (f)
  (declare (xargs :guard (formatp f)))
  (expt 2 (- 1 (bias f))))

(defthmd positive-spn
  (> (spn f) 0)
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable spn))))

(defthmd nrepp-spn
  (implies (formatp f)
           (nrepp (spn f) f))
  :hints (("Goal" :in-theory (enable bias exactp-2**n formatp expw prec nrepp spn))))

(defthmd smallest-spn
  (implies (and (formatp f)
                (nrepp x f))
           (>= (abs x) (spn f)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal" :use ((:instance expo<= (x (abs x)) (n (- (bias f)))))
                  :in-theory (enable expo spn nrepp))))

;; Largest positive normal:

(defund lpn (f)
  (declare (xargs :guard (formatp f)))
  (* (expt 2 (- (expt 2 (expw f)) (+ 2 (bias f))))
     (- 2 (expt 2 (- 1 (prec f))))))

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
  (implies (and (formatp f)
                (> x 0)
                (nrepp x f))
           (<= x (lpn f)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal" :in-theory (enable exactp-2**n lpn fp- nrepp)
                  :use (positive-lpn
                        (:instance expo>= (n (- (expt 2 (expw f)) (1+ (bias f)))))
                        (:instance fp-2 (n (prec f)) (x (expt 2 (- (expt 2 (expw f)) (1+ (bias f))))) (y x))))))

(defthmd largest-lpn
  (implies (and (formatp f)
                (nrepp x f))
           (<= x (lpn f)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal" :use (largest-lpn-1 positive-lpn))))


;;;***************************************************************
;;;               Denormals and Zeroes
;;;***************************************************************

(defund zerp (x f)
  (declare (xargs :guard (formatp f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (and (encodingp x f)
       (= (expf x f) 0)
       (= (sigf x f) 0)))

(defund zencode (sgn f) (cat sgn 1 0 (+ (sigw f) (expw f))))

(defund denormp (x f)
  (declare (xargs :guard (formatp f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (and (encodingp x f)
       (= (expf x f) 0)
       (not (= (sigf x f) 0))
       (implies (explicitp f) (= (bitn x (1- (prec f))) 0))))

(defund pseudop (x f)
  (declare (xargs :guard (formatp f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
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

(local-defthm sgn-ddecode-1
  (implies (and (formatp f)
                (pseudop x f))
           (not (= (sigf x f) 0)))
  :hints (("Goal" :in-theory (enable formatp prec sigw sigf pseudop)
                  :use (:instance bitn-bits (i (1- (prec f))) (j 0) (k (1- (prec f)))))))

(defthm sgn-ddecode
  (implies (and (formatp f)
                (or (denormp x f) (pseudop x f)))
           (equal (sgn (ddecode x f))
                  (if (= (sgnf x f) 0) 1 -1)))
  :hints (("Goal" :in-theory (enable sgn sigw sigf denormp pseudop ddecode)
                  :use (sgn-ddecode-1))))

(defthm expo-ddecode
  (implies (and (formatp f)
                (or (denormp x f) (pseudop x f)))
	   (equal (expo (ddecode x f))
	          (+ 2 (- (prec f)) (- (bias f)) (expo (sigf x f)))))
  :hints (("Goal" :in-theory (enable ddecode denormp)
                  :use (sgn-ddecode-1
                        (:instance expo-shift (x (sigf x f)) (n (+ 2 (- (bias f)) (- (prec f)))))))))

(defthm sig-ddecode
  (implies (and (formatp f)
                (or (denormp x f) (pseudop x f)))
           (equal (sig (ddecode x f))
                  (sig (sigf x f))))
  :hints (("Goal" :in-theory (enable ddecode denormp)
                  :use ((:instance sig-shift (x (sigf x f)) (n (+ 2 (- (bias f)) (- (prec f)))))))))

(defund drepp (x f)
  (and (rationalp x)
       (not (= x 0))
       (<= (- 2 (prec f)) (+ (expo x) (bias f)))
       (<= (+ (expo x) (bias f)) 0)
       ;number of bits available in the sig field is p - 1 - ( - bias - expo(x))
       (exactp x (+ (1- (prec f)) (bias f) (expo x)))))

(defund dencode (x f)
  (cat (if (= (sgn x) 1) 0 1)
       1
       0
       (expw f)
       (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f))))
       (sigw f)))

(local-defthmd drepp-dencode-1
  (implies (and (formatp f)
                (denormp x f))
           (not (zerop (ddecode x f))))
  :hints (("Goal" :in-theory (enable sgn)
                  :use (sgn-ddecode))))

(local-defthm drepp-dencode-2
  (implies (and (formatp f)
                (denormp x f))
           (and (< 0 (sigf x f))
                (< (sigf x f) (expt 2 (1- (prec f))))))
  :hints (("Goal" :in-theory (enable sigf denormp sigw)
                  :use ((:instance bits-bounds (i (- (prec f) 2)) (j 0))
                        (:instance bitn-plus-bits (n (1- (prec f))) (m 0))))))

(local-defthmd drepp-dencode-3
  (implies (and (formatp f)
                (denormp x f))
           (and (<= 0 (expo (sigf x f)))
                (< (expo (sigf x f)) (1- (prec f)))))
  :hints (("Goal" :use (drepp-dencode-2
                        (:instance expo<= (x (sigf x f)) (n (- (prec f) 2)))
                        (:instance expo>= (x (sigf x f)) (n 0))))))

(local-defthmd drepp-dencode-4
  (implies (and (formatp f)
                (denormp x f))
           (exactp (sigf x f) (1+ (expo (sigf x f)))))
  :hints (("Goal" :in-theory (enable exactp2))))

(local-defthmd drepp-dencode-5
  (implies (and (formatp f)
                (denormp x f))
           (exactp (ddecode x f) (+ (1- (prec f)) (bias f) (expo (ddecode x f)))))
  :hints (("Goal" :in-theory (enable exactp sig-ddecode expo-ddecode)
                  :use (drepp-dencode-4))))

(defthm drepp-ddecode
  (implies (and (formatp f)
                (denormp x f))
           (drepp (ddecode x f) f))
  :hints (("Goal" :in-theory (enable drepp)
                  :use (drepp-dencode-1 drepp-dencode-3 drepp-dencode-5))))

(local-defthmd dencode-ddecode-1
    (implies (and (formatp f)
                  (denormp x f))
	     (equal (bitn (dencode (ddecode x f) f) (+ (expw f) (sigw f)))
		    (bitn x (+ (expw f) (sigw f)))))
  :hints (("Goal" :in-theory (enable bitn-cat sgnf dencode)
                  :use (sgn-ddecode))))

(local-defthmd dencode-ddecode-2
    (implies (and (formatp f)
                  (denormp x f))
	     (equal (bits (dencode (ddecode x f) f) (1- (+ (expw f) (sigw f))) (sigw f))
		    (bits x (1- (+ (expw f) (sigw f))) (sigw f))))
  :hints (("Goal" :in-theory (enable bits-cat expf expw sigw prec formatp denormp dencode)
                  :use (expo-ddecode))))

(local-defthmd dencode-ddecode-3
    (implies (and (formatp f)
                  (denormp x f))
	     (equal (bits (dencode (ddecode x f) f) (1- (sigw f)) 0)
		    (bits (* (sig (sigf x f)) (expt 2 (expo (sigf x f)))) (1- (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable bits-cat dencode sig-ddecode expo-ddecode))))

(local-defthmd dencode-ddecode-4
    (implies (and (formatp f)
                  (denormp x f))
	     (equal (bits (dencode (ddecode x f) f) (1- (sigw f)) 0)
		    (bits (sigf x f) (1- (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable sgn)
                  :use (dencode-ddecode-3 (:instance fp-rep (x (sigf x f)))))))

(local-defthmd dencode-ddecode-5
    (implies (and (formatp f)
                  (denormp x f))
	     (equal (bits (dencode (ddecode x f) f) (1- (sigw f)) 0)
		    (bits x (1- (sigw f)) 0)))
  :hints (("Goal" :in-theory (enable bits-bits sigf)
                  :use (dencode-ddecode-4 (:instance fp-rep (x (sigf x f)))))))

(local-defthmd dencode-ddecode-6
    (implies (and (formatp f)
                  (denormp x f))
	     (equal (bits (dencode (ddecode x f) f) (+ (expw f) (sigw f)) 0)
		    (bits x (+ (expw f) (sigw f)) 0)))
  :hints (("Goal" :use (dencode-ddecode-1 dencode-ddecode-2 dencode-ddecode-5
                        (:instance bitn-plus-bits (n (+ (expw f) (sigw f))) (m 0))
                        (:instance bitn-plus-bits (x (dencode (ddecode x f) f)) (n (+ (expw f) (sigw f))) (m 0))
                        (:instance bits-plus-bits (n (1- (+ (expw f) (sigw f)))) (p (sigw f)) (m 0))
                        (:instance bits-plus-bits (x (dencode (ddecode x f) f)) (n (1- (+ (expw f) (sigw f)))) (p (sigw f)) (m 0))))))

(local-defthmd dencode-ddecode-7
    (implies (and (formatp f)
                  (denormp x f))
	     (and (bvecp (dencode (ddecode x f) f) (1+ (+ (expw f) (sigw f))))
		  (bvecp x (1+ (+ (expw f) (sigw f))))))
  :hints (("Goal" :in-theory (enable denormp encodingp dencode))))

(defthm dencode-ddecode
    (implies (and (formatp f)
                  (denormp x f))
	     (equal (dencode (ddecode x f) f)
		    x))
  :hints (("Goal" :use (dencode-ddecode-7 dencode-ddecode-6))))

(local-defthm denormp-dencode-1
    (implies (and (formatp f)
                  (drepp x f))
             (encodingp (dencode x f) f))
  :hints (("Goal" :in-theory (enable encodingp formatp dencode expw sigw prec nrepp))))

(local-defthm denormp-dencode-2
    (implies (and (formatp f)
                  (drepp x f))
             (equal (expf (dencode x f) f) 0))
  :hints (("Goal" :in-theory (enable bits-cat expf formatp dencode expw sigw prec drepp))))

(local-defthmd denormp-dencode-3
    (implies (and (formatp f)
                  (explicitp f)
                  (drepp x f))
             (equal (bitn (dencode x f) (1- (prec f)))
                    (bitn (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f)))) (1- (prec f)))))
  :hints (("Goal" :in-theory (enable bitn-cat expf sigf formatp dencode expw sigw prec drepp))))

(local-defthm hack-3
  (implies (and (rationalp x)
                (integerp n)
                (< x (expt 2 m))
                (integerp m)
                (<= m n))
           (< (* x (expt 2 (- n))) 1))
  :rule-classes ()
  :hints (("Goal" :use (hack-2))))

(local-defthmd denormp-dencode-4
    (implies (and (formatp f)
                  (drepp x f))
             (< (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f)))) (expt 2 (1- (prec f)))))
  :hints (("Goal" :use (sig-upper-bound
                        (:instance hack-3 (x (sig x)) (m 1) (n (- 1 (+ (expo x) (bias f))))))
                  :in-theory (enable formatp prec drepp))))

(local-defthmd denormp-dencode-5
    (implies (and (formatp f)
                  (drepp x f))
             (equal (bitn (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f)))) (1- (prec f))) 0))
  :hints (("Goal" :use (denormp-dencode-4
                        (:instance bvecp-bitn-0 (x (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f))))) (n (1- (prec f)))))
                   :in-theory (enable exactp bvecp formatp prec drepp))))

(local-defthmd denormp-dencode-6
    (implies (and (formatp f)
                  (drepp x f))
             (bvecp (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f)))) (1- (prec f))))
  :hints (("Goal" :use (denormp-dencode-4)
                   :in-theory (enable exactp bvecp formatp prec drepp))))

(local-defthmd denormp-dencode-7
    (implies (and (formatp f)
                  (drepp x f))
             (equal (manf (dencode x f) f) (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f))))))
  :hints (("Goal" :use (denormp-dencode-6)
                   :in-theory (enable manf bits-bits sigw bits-cat dencode))))

(local-defthmd denormp-dencode-8
    (implies (and (formatp f)
                  (drepp x f))
             (< 0 (manf (dencode x f) f)))
  :hints (("Goal" :use (denormp-dencode-7 sig-lower-bound)
                   :in-theory (enable drepp))))

(local-defthmd denormp-dencode-9
    (implies (and (formatp f)
                  (drepp x f))
             (not (= (sigf (dencode x f) f) 0)))
  :hints (("Goal" :use (denormp-dencode-8
                        (:instance bitn-plus-bits (x (dencode x f)) (n (1- (prec f))) (m 0)))
                   :in-theory (enable manf sigf sigw drepp))))

(defthm denormp-dencode
  (implies (and (formatp f)
                (drepp x f))
           (denormp (dencode x f) f))
  :hints (("Goal" :use (denormp-dencode-1 denormp-dencode-2 denormp-dencode-3 denormp-dencode-5 denormp-dencode-9)
                  :in-theory (enable denormp))))

(local-defthmd ddecode-dencode-1
    (implies (and (formatp f)
                  (drepp x f))
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
    (implies (and (formatp f)
                  (drepp x f))
             (equal (sigf (dencode x f) f) (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f))))))
  :hints (("Goal" :use (denormp-dencode-7 denormp-dencode
                        (:instance bitn-plus-bits (x (dencode x f)) (n (1- (prec f))) (m 0))) 
                   :in-theory (e/d (formatp prec expw sigw manf sigf denormp) (denormp-dencode)))))

(local-defthmd ddecode-dencode-4
    (implies (and (formatp f)
                  (drepp x f))
             (equal (expo (sigf (dencode x f) f))
                    (+ -2 (prec f) (expo x) (bias f))))
  :hints (("Goal" :use (sig-lower-bound (:instance expo-shift (x (sig x)) (n (+ -2 (prec f) (expo x) (bias f)))))
                   :in-theory (enable ddecode-dencode-3 drepp))))

(local-defthmd ddecode-dencode-5
    (implies (and (formatp f)
                  (drepp x f))
	     (equal (expo (ddecode (dencode x f) f))
		    (expo x)))
  :hints (("Goal" :in-theory (enable ddecode-dencode-4 expo-ddecode))))

(local-defthmd ddecode-dencode-6
    (implies (and (formatp f)
                  (drepp x f))
	     (equal (sig (ddecode (dencode x f) f))
		    (sig x)))
  :hints (("Goal" :in-theory (enable ddecode-dencode-3 sig-ddecode)
                  :use (denormp-dencode
                        (:instance sig-shift (x (sig x)) (n (+ -2 (prec f) (expo x) (bias f))))))))

(defthm ddecode-dencode
  (implies (and (formatp f)
                (drepp x f))
           (equal (ddecode (dencode x f) f)
                  x))
  :hints (("Goal" :use (fp-rep (:instance fp-rep (x (ddecode (dencode x f) f))))
                  :in-theory (enable drepp ddecode-dencode-1 ddecode-dencode-5 ddecode-dencode-6))))


;; Smallest positive denormal:

(defund spd (f)
  (declare (xargs :guard (formatp f)))
  (expt 2 (+ 2 (- (bias f)) (- (prec f)))))

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
  (implies (and (formatp f)
                (drepp r f))
           (>= (abs r) (spd f)))
  :hints (("Goal" :use ((:instance expo<= (x (abs r)) (n (- 1 (+ (prec f) (bias f))))))
                  :in-theory (enable spd drepp))))

(local (include-book "spd-mult"))

(local-defthm bias-rewrite
  (equal (bias f) (bias$ (expw f)))
  :hints (("Goal" :in-theory (enable bias bias$))))

(local-defthm spd-rewrite
  (equal (spd f) (spd$ (prec f) (expw f)))
  :hints (("Goal" :in-theory (enable spd$ spd))))

(local-defthm drepp-rewrite
  (implies (formatp f)
           (equal (drepp r f) (drepp$ r (prec f) (expw f))))
  :hints (("Goal" :in-theory (enable bias$ formatp prec expw drepp drepp$))))

(defthmd spd-mult
  (implies (and (formatp f)
		(rationalp r)
                (> r 0)
		(= m (/ r (spd f))))
	   (iff (drepp r f)
		(and (natp m)
		     (<= 1 m)
		     (< m (expt 2 (1- (prec f)))))))
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use ((:instance spd-mult$ (p (prec f)) (q (expw f)))))))


;;;***************************************************************
;;;                 Infinities and NaNs
;;;***************************************************************

(defund infp (x f)
  (declare (xargs :guard (formatp f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (and (encodingp x f)
       (= (expf x f) (1- (expt 2 (expw f))))
       (not (unsupp x f))
       (= (manf x f) 0)))

(defun iencode (sgn f)
  (if (explicitp f)
      (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 1 1 0 (1- (sigw f)))
    (cat sgn 1 (1- (expt 2 (expw f))) (expw f) 0 (sigw f))))

(defund nanp (x f)
  (declare (xargs :guard (formatp f)
                  :guard-hints (("goal" :in-theory (enable encodingp)))))
  (and (encodingp x f)
       (= (expf x f) (1- (expt 2 (expw f))))
       (not (unsupp x f))
       (not (= (manf x f) 0))))

(defund qnanp (x f)
  (declare (xargs :guard (formatp f)
                  :guard-hints (("goal" :in-theory (enable nanp encodingp)))))
  (and (nanp x f) (= (bitn x (- (prec f) 2)) 1)))

(defund snanp (x f)
  (declare (xargs :guard (formatp f)
                  :guard-hints (("goal" :in-theory (enable nanp encodingp)))))
  (and (nanp x f) (= (bitn x (- (prec f) 2)) 0)))

(defund qnanize (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))
                  :guard-hints (("goal" :in-theory (enable formatp prec)))))
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


;;;***************************************************************
;;;                Rebiasing Exponents
;;;***************************************************************

(defund rebias (expo old new)
  (+ expo (- (expt 2 (1- new)) (expt 2 (1- old)))))

(local-defthm rebias-rewrite
  (implies (and (natp old) (natp new) (bvecp expo old))
           (equal (rebias expo old new) (rebias$ expo old new)))
  :hints (("Goal" :in-theory (enable bias$ rebias rebias$))))

(defthm natp-rebias-up
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (natp (rebias x m n)))
  :hints (("Goal" :use natp-rebias-up$)))

(defthm natp-rebias-down
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (natp (rebias x n m)))
  :hints (("Goal" :use natp-rebias-down$)))

(defthm bvecp-rebias-up
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (bvecp (rebias x m n) n))
  :hints (("Goal" :use bvecp-rebias-up$)))

(defthm bvecp-rebias-down
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (bvecp (rebias x n m) m))
  :hints (("Goal" :use bvecp-rebias-down$)))

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
			 (1- m))))
  :hints (("Goal" :use rebias-lower$)))

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
			 (1- m))))
  :hints (("Goal" :use rebias-higher$)))
