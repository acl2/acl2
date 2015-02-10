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

(in-package "ACL2")

(set-enforce-redundancy t) ; for some reason, acl2 4.3 complains about  logand-natp 

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


;;;**********************************************************************
;;;                       LOGAND, LOGIOR, and LOGXOR
;;;**********************************************************************

(defsection-rtl |Binary Operations| |Logical Operations|

(in-theory (disable logand logior logxor))

(defthmd logand-def
  (equal (logand x y)
         (if (or (zip x) (zip y))
             0
           (if (= x y)
               x
             (+ (* 2 (logand (fl (/ x 2)) (fl (/ y 2))))
                (logand (mod x 2) (mod y 2))))))
  :rule-classes ((:definition :controller-alist ((binary-logand t t)))))

(defthmd logior-def
  (implies (and (integerp x) (integerp y))
           (equal (logior x y)
                  (if (or (zip x) (= x y))
                      y
                    (if (zip y)
                        x
                      (+ (* 2 (logior (fl (/ x 2)) (fl (/ y 2))))
                         (logior (mod x 2) (mod y 2)))))))
  :rule-classes ((:definition :controller-alist ((binary-logior t t)))))

(defthmd logxor-def
  (implies (and (integerp x) (integerp y))
           (equal (logxor x y)
                  (if (zip x)
                      y
                    (if (zip y)
                        x
                      (if (= x y)
                          0
                        (+ (* 2 (logxor (fl (/ x 2)) (fl (/ y 2))))
                           (logxor (mod x 2) (mod y 2))))))))
  :rule-classes ((:definition :controller-alist ((binary-logxor t t)))))

(defthm logand-bnd
    (implies (<= 0 x)
	     (and (<= 0 (logand x y))
                  (<= (logand x y) x)))
  :rule-classes :linear)

(defthm logand-bvecp
    (implies (and (natp n)
		  (bvecp x n)
		  (integerp y))
	     (bvecp (logand x y) n)))

(defthm logior-bvecp
    (implies (and (bvecp x n)
		  (bvecp y n))
	     (bvecp (logior x y) n)))

(defthm logxor-bvecp
    (implies (and (bvecp x n)
		  (bvecp y n)
                  (natp n))
	     (bvecp (logxor x y) n)))

(defthmd logand-mod
  (implies (and (integerp x)
                (integerp y)
		(integerp n))
	     (equal (mod (logand x y) (expt 2 n))
		    (logand (mod x (expt 2 n))
                            (mod y (expt 2 n))))))

(defthmd logior-mod
  (implies (and (integerp x)
                (integerp y)
		(integerp n))
	     (equal (mod (logior x y) (expt 2 n))
		    (logior (mod x (expt 2 n))
                            (mod y (expt 2 n))))))

(defthmd logxor-mod
  (implies (and (integerp x)
                (integerp y)
		(integerp n))
	     (equal (mod (logxor x y) (expt 2 n))
		    (logxor (mod x (expt 2 n))
                            (mod y (expt 2 n))))))

(defthmd fl-logand
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (fl (* (expt 2 (- n)) (logand x y)))
                  (logand (fl (* (expt 2 (- n)) x)) (fl (* (expt 2 (- n)) y))))))

(defthmd fl-logior
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (fl (* (expt 2 (- n)) (logior x y)))
                  (logior (fl (* (expt 2 (- n)) x)) (fl (* (expt 2 (- n)) y))))))

(defthmd fl-logxor
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (fl (* (expt 2 (- n)) (logxor x y)))
                  (logxor (fl (* (expt 2 (- n)) x)) (fl (* (expt 2 (- n)) y))))))


(defthmd logand-cat
  (implies (and (case-split (integerp x1))
	        (case-split (integerp y1))
	        (case-split (integerp x2))
	        (case-split (integerp y2))
                (case-split (natp n))
		(case-split (natp m)))
	   (equal (logand (cat x1 m y1 n) (cat x2 m y2 n))
		  (cat (logand x1 x2) m (logand y1 y2) n))))

(defthmd logior-cat
  (implies (and (case-split (integerp x1))
	        (case-split (integerp y1))
	        (case-split (integerp x2))
	        (case-split (integerp y2))
                (case-split (natp n))
		(case-split (natp m)))
	   (equal (logior (cat x1 m y1 n) (cat x2 m y2 n))
		  (cat (logior x1 x2) m (logior y1 y2) n))))

(defthmd logxor-cat
  (implies (and (case-split (integerp x1))
	        (case-split (integerp y1))
	        (case-split (integerp x2))
	        (case-split (integerp y2))
                (case-split (natp n))
		(case-split (natp m)))
	   (equal (logxor (cat x1 m y1 n) (cat x2 m y2 n))
		  (cat (logxor x1 x2) m (logxor y1 y2) n))))

(defthmd logand-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logand (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logand x y)))))

(defthmd logior-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logior (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logior x y)))))

(defthmd logxor-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logxor (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logxor x y)))))

(defthmd logand-expt
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (equal (logand (* (expt 2 n) x) y)
                    (* (expt 2 n) (logand x (fl (/ y (expt 2 n))))))))

(defthmd logior-expt
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (equal (logior (* (expt 2 n) x) y)
                    (+ (* (expt 2 n) (logior x (fl (/ y (expt 2 n)))))
                       (mod y (expt 2 n))))))

(defthmd logxor-expt
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (equal (logxor (* (expt 2 n) x) y)
		    (+ (* (expt 2 n) (logxor x (fl (/ y (expt 2 n)))))
                       (mod y (expt 2 n))))))

(defthmd logior-expt-cor
    (implies (and (natp n)
		  (integerp x)
		  (bvecp y n))
	     (equal (logior (* (expt 2 n) x) y)
		    (+ (* (expt 2 n) x) y))))

(defthmd logand-bits
    (implies (and (integerp x)
		  (natp n)
		  (natp k)
		  (< k n))
	     (equal (logand x (- (expt 2 n) (expt 2 k)))
		    (* (expt 2 k) (bits x (1- n) k)))))

(defthmd logand-bit
    (implies (and (integerp x)
		  (natp n))
	     (equal (logand x (expt 2 n))
		    (* (expt 2 n) (bitn x n)))))

(defthmd bits-logand
    (implies (and (integerp x)
		  (integerp y)
		  (integerp i)
		  (integerp j))
	     (equal (bits (logand x y) i j)
		    (logand (bits x i j) (bits y i j)))))

(defthmd bits-logior
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j))
	     (equal (bits (logior x y) i j)
                    (logior (bits x i j) (bits y i j)))))

(defthmd bits-logxor
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j))
           (equal (bits (logxor x y) i j)
                  (logxor (bits x i j) (bits y i j))))
  :hints (("Goal" :use bits-logxor$)))

(defthmd bitn-logand
    (implies (and (integerp x)
		  (integerp y)
		  (integerp n))
	     (equal (bitn (logand x y) n)
		    (logand (bitn x n) (bitn y n)))))

(defthmd bitn-logior
    (implies (and (integerp x)
		  (integerp y)
		  (integerp n))
	     (equal (bitn (logior x y) n)
		    (logior (bitn x n) (bitn y n)))))

(defthmd bitn-logxor
    (implies (and (case-split (integerp x))
		  (case-split (integerp y))
		  (case-split (integerp n)))
	     (equal (bitn (logxor x y) n)
		    (logxor (bitn x n) (bitn y n)))))
)

;;;**********************************************************************
;;;                               LOGNOT
;;;**********************************************************************

(defsection-rtl |Complementation| |Logical Operations|

(in-theory (disable lognot))

(defthmd lognot-def
    (implies (integerp x)
	     (equal (lognot x)
		    (1- (- x)))))

(defthmd lognot-shift
  (implies (and (integerp x)
                (natp k))
           (equal (lognot (* (expt 2 k) x))
		  (+ (* (expt 2 k) (lognot x))
		     (1- (expt 2 k))))))

(defthmd lognot-fl
  (implies (and (integerp x)
                (not (zp n)))
           (equal (lognot (fl (/ x n)))
                  (fl (/ (lognot x) n)))))

(defthmd mod-lognot
  (implies (and (integerp x)
                (natp n))
           (equal (mod (lognot x) (expt 2 n))
                  (1- (- (expt 2 n) (mod x (expt 2 n)))))))

(defthmd bits-lognot
    (implies (and (natp i)
		  (natp j)
		  (<= j i)
		  (integerp x))
	     (equal (bits (lognot x) i j)
		    (- (1- (expt 2 (- (1+ i) j))) (bits x i j)))))

(defthm bitn-lognot
    (implies (and (integerp x)
		  (natp n))
	     (not (equal (bitn (lognot x) n)
			 (bitn x n))))
  :rule-classes ())

(defthmd bits-lognot-bits
  (implies (and (integerp x)
                (natp i)
                (natp j)
                (natp k)
                (natp l)
                (<= l k)
                (<= k (- i j)))
           (equal (bits (lognot (bits x i j)) k l)
                  (bits (lognot x) (+ k j) (+ l j)))))

(defthmd bits-lognot-bits-lognot
  (implies (and (integerp x)
                (natp i)
                (natp j)
                (natp k)
                (natp l)
                (<= l k)
                (<= k (- i j)))
           (equal (bits (lognot (bits (lognot x) i j)) k l)
                  (bits x (+ k j) (+ l j)))))

(defthmd logand-bits-lognot
  (implies (and (integerp x)
                (integerp n)
                (bvecp y n))
           (equal (logand y (bits (lognot x) (1- n) 0))
                  (logand y (lognot (bits x (1- n) 0))))))
)

;;;**********************************************************************
;;;                         Algebraic Properties
;;;**********************************************************************

(defsection-rtl |Algebraic Properties| |Logical Operations|

(defthm logand-x-0
    (equal (logand x 0) 0))

(defthm logand-0-y
    (equal (logand 0 y) 0))

(defthm logior-x-0
    (implies (integerp x)
	     (equal (logior x 0) x)))

(defthm logior-0-y
    (implies (integerp y)
	     (equal (logior 0 y) y)))

(defthm logxor-x-0
    (implies (integerp x)
	     (equal (logxor x 0) x)))

(defthm logxor-0-y
    (implies (integerp y)
	     (equal (logxor 0 y) y)))

(defthm logand-self
  (implies (case-split (integerp x))
           (equal (logand x x) x)))

(defthm logior-self
    (implies (case-split (integerp x))
	     (equal (logior x x) x)))

(defthm logxor-self
  (equal (logxor x x) 0)
  :hints (("Goal" :use logxor-self$)))

; Matt K. edit: changed variable x to i to match ihs/logops-lemmas.lisp.
(defthm lognot-lognot
    (implies (case-split (integerp i))
	     (equal (lognot (lognot i))
		    i)))

(defthmd logior-not-0
  (implies (and (integerp x)
                (integerp y))
           (iff (equal (logior x y) 0)
                (and (= x 0) (= y 0)))))

(defthmd logxor-not-0
  (implies (and (integerp x)
                (integerp y))
           (iff (equal (logxor x y) 0)
                (= x y))))

(defthm logand-x-1
    (implies (bvecp x 1)
	     (equal (logand x 1) x)))

(defthm logand-1-x
    (implies (bvecp x 1)
	     (equal (logand 1 x) x)))

(defthm logior-1-x
  (implies (bvecp x 1)
           (equal (logior 1 x) 1)))

(defthm logior-x-1
  (implies (bvecp x 1)
           (equal (logior x 1) 1)))

(defthm logand-x-m1
    (implies (integerp x)
	     (equal (logand x -1) x)))

(defthm logand-m1-y
    (implies (integerp y)
	     (equal (logand -1 y) y)))

(defthm logior-x-m1
    (implies (integerp x)
	     (equal (logior x -1) -1)))

(defthm logior-m1-y
    (implies (integerp y)
	     (equal (logior -1 y) -1)))

(defthm logxor-x-m1
    (implies (integerp x)
	     (equal (logxor x -1)
		    (lognot x))))

(defthm logxor-m1-x
    (implies (integerp x)
	     (equal (logxor -1 x)
		    (lognot x))))

(defthm logand-commutative
    (equal (logand y x) (logand x y)))

(defthm logior-commutative
    (equal (logior y x) (logior x y)))

(defthm logxor-commutative
    (equal (logxor y x) (logxor x y)))

(defthm logand-commutative-2
  (equal (logand y x z)
	 (logand x y z)))

(defthm logior-commutative-2
  (equal (logior y x z)
	 (logior x y z)))

(defthm logxor-commutative-2
  (equal (logxor y x z)
	 (logxor x y z)))

(defthm logand-associative
    (equal (logand (logand x y) z)
           (logand x (logand y z))))

(defthm logior-associative
    (equal (logior (logior x y) z)
	   (logior x (logior y z))))

(defthm logxor-associative
    (equal (logxor (logxor x y) z)
	   (logxor x (logxor y z))))

(defthmd logior-logand
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (logior x (logand y z))
                  (logand (logior x y) (logior x z)))))

(defthmd logand-logior
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
    (equal (logand x (logior y z))
	   (logior (logand x y) (logand x z)))))

(defthmd logior-logand-2
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
    (equal (logand (logior y z) x)
	   (logior (logand y x) (logand z x)))))

(defthmd log3
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
    (equal (logior (logand x y) (logior (logand x z) (logand y z)))
	   (logior (logand x y) (logand (logxor x y) z)))))

(defthmd logxor-rewrite
  (implies (and (integerp x)
                (integerp y))
           (equal (logxor x y)
                  (logior (logand x (lognot y))
                          (logand y (lognot x))))))

(defthmd lognot-logxor
    (and (equal (logxor (lognot x) y)
                (lognot (logxor x y)))
         (equal (logxor y (lognot x))
                (lognot (logxor x y)))))
)
