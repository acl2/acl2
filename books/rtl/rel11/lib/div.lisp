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

(local (include-book "../support/div"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

;; From bits.lisp:

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

;; From reps.lisp:

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

(defund bias (f) (declare (xargs :guard (formatp f))) (- (expt 2 (- (expw f) 1)) 1))

(defund sp () (declare (xargs :guard t)) '(nil 24 8))

(defund ndecode (x f)
  (declare (xargs :guard (and (integerp x) (formatp f))))
  (* (if (= (sgnf x f) 0) 1 -1)
     (expt 2 (- (expf x f) (bias f)))
     (1+ (* (manf x f) (expt 2 (- 1 (prec f)))))))

(defund nencode (x f)
  (cat (if (= (sgn x) 1) 0 1)
       1
       (+ (expo x) (bias f))
       (expw f)
       (* (sig x) (expt 2 (1- (prec f))))
       (sigw f)))

;; From round.lisp:

(defund rtz (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x) 
     (fl (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(defund raz (x n)
  (* (sgn x) 
     (cg (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(defun re (x)
  (- x (fl x)))

(defund rne (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(rtz x n)
      (if (> f 1/2)
	  (raz x n)
	(if (evenp z)
	    (rtz x n)
	  (raz x n))))))

(defund rto (x n)
  (if (exactp x (1- n))
      x
    (+ (rtz x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(defun rup (x n)
  (if (>= x 0)
      (raz x n)
    (rtz x n)))

(defun rdn (x n)
  (if (>= x 0)
      (rtz x n)
    (raz x n)))

(defund rna (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz x n)
    (raz x n)))

(defund IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defun common-mode-p (mode)
  (or (IEEE-rounding-mode-p mode) (equal mode 'raz) (equal mode 'rna)))

(defund rnd (x mode n)
  (case mode
    (raz (raz x n))
    (rna (rna x n))
    (rtz (rtz x n))
    (rup (rup x n))
    (rdn (rdn x n))
    (rne (rne x n))
    (otherwise 0)))

;;;**********************************************************************
;;;		    	    Quotient Refinement
;;;**********************************************************************

(defsection-rtl |Quotient Refinement| |FMA-Based Division|

(defthm init-approx
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp y)
                (rationalp ep)
                (not (zp p))
                (> a 0)
                (> b 0)
                (<= (abs (- 1 (* b y))) ep))
           (<= (abs (- 1 (* (/ b a) (rne (* a y) p))))
               (+ ep (* (expt 2 (- p)) (1+ ep)))))
  :rule-classes ())

(defthm r-exactp
  (implies (and (rationalp a)
                (rationalp b)
                (integerp p)
                (> p 1)
                (exactp a p)
                (exactp b p)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (rationalp q)
                (exactp q p)
                (< (abs (- (/ a b) q)) (expt 2 (- (1+ (if (> a b) 0 -1)) p))))
           (exactp (- a (* b q)) p))
  :rule-classes ())

(defthm markstein-lemma
  (let ((e (if (> a b) 0 -1))
        (r (- a (* b q))))
    (implies (and (rationalp a)
                  (rationalp b)
                  (rationalp q)
                  (rationalp y)
                  (integerp p)
                  (<= 1 a)
                  (< a 2)
                  (<= 1 b)
                  (< b 2)
                  (> p 1)
                  (exactp a p)
                  (exactp b p)
                  (exactp q p)
                  (< (abs (- 1 (* b y))) (/ (expt 2 p)))            
                  (< (abs (- (/ a b) q)) (expt 2 (- (1+ e) p)))
                  (ieee-rounding-mode-p mode))
             (= (rnd (+ q (* r y)) mode p)
                (rnd (/ a b) mode p))))
  :rule-classes ())

(defthm quotient-refinement-1
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp y)
                (rationalp q0)
                (rationalp ep)
                (rationalp de)
                (not (zp p))
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (<= (abs (- 1 (* b y))) ep)
                (<= (abs (- 1 (* (/ b a) q0))) de))
            (let* ((r (rne (- a (* b q0)) p))
                   (q (rne (+ q0 (* r y)) p)))
              (<= (abs (- q (/ a b)))
                  (* (/ a b)
                     (+ (expt 2 (- p))
                        (* (1+ (expt 2 (- p))) de ep)
                        (* (expt 2 (- p)) de (1+ ep))
                        (* (expt 2 (- (* 2 p))) de (1+ ep)))))))
  :rule-classes ())

(defthm quotient-refinement-2
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp y)
                (rationalp q0)
                (rationalp ep)
                (rationalp de)
                (not (zp p))
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (<= (abs (- 1 (* b y))) ep)
                (<= (abs (- 1 (* (/ b a) q0))) de)
                (< (+ (* ep de) (* (expt 2 (- p)) de (1+ ep))) (expt 2 (- (1+ p)))))
            (let* ((r (rne (- a (* b q0)) p))
                   (q (rne (+ q0 (* r y)) p))
                   (e (if (> a b) 0 -1)))
              (< (abs (- q (/ a b)))
                 (expt 2 (- (1+ e) p)))))
  :rule-classes ())
)

;;;**********************************************************************
;;;		    	  Reciprocal Refinement
;;;**********************************************************************

(defsection-rtl |Reciprocal Refinement| |FMA-Based Division|

(defthm recip-refinement-1
  (let* ((e1 (rne (- 1 (* b y1)) p))
         (y3p (+ y1 (* e1 y2)))
         (ep3p (* ep1 (+ ep2 (* (expt 2 (- p)) (1+ ep2))))))
    (implies (and (rationalp y1)
                  (rationalp y2)
                  (rationalp b)
                  (rationalp ep1)
                  (rationalp ep2)
                  (integerp p)
                  (> p 0)
                  (<= (abs (- 1 (* b y1))) ep1)
                  (<= (abs (- 1 (* b y2))) ep2))
             (<= (abs (- 1 (* b y3p)))
                 ep3p)))
  :rule-classes ())

(defthm recip-refinement-2
  (let* ((e1 (rne (- 1 (* b y1)) p))
         (y3p (+ y1 (* e1 y2)))
         (y3 (rne y3p p))
         (ep3p (* ep1 (+ ep2 (* (expt 2 (- p)) (1+ ep2)))))
         (ep3 (+ ep3p (* (expt 2 (- p)) (1+ ep3p)))))
    (implies (and (rationalp y1)
                  (rationalp y2)
                  (rationalp b)
                  (rationalp ep1)
                  (rationalp ep2)
                  (integerp p)
                  (> p 0)
                  (<= (abs (- 1 (* b y1))) ep1)
                  (<= (abs (- 1 (* b y2))) ep2))
             (<= (abs (- 1 (* b y3)))
                 ep3)))
  :rule-classes ())

(defund h-excps (d p)
  (if (zp d)
      ()
    (cons (- 2 (* (expt 2 (- 1 p)) d))
          (h-excps (1- d) p))))

(defthm harrison-lemma
  (let ((y (rne yp p))
        (d (cg (* (expt 2 (* 2 p)) ep))))
    (implies (and (rationalp b)
                  (rationalp yp)
                  (rationalp ep)
                  (integerp p)
                  (> p 1)
                  (<= 1 b)
                  (< b 2)
                  (exactp b p)
                  (not (member b (h-excps d p)))
                  (< ep (expt 2 (- (1+ p))))
                  (<= (abs (- 1 (* b yp))) ep))
             (< (abs (- 1 (* b y))) (expt 2 (- p)))))
  :rule-classes ())
)

;;;**********************************************************************
;;;		    	      Examples
;;;**********************************************************************

(include-book "rcp") ; must precede the defsection-rtl

(defsection-rtl |Examples| |FMA-Based Division|

(defund rcp24 (b)
  (ndecode (frcp (nencode b (sp))) (sp)))

(defthm rcp24-spec
  (implies (and (rationalp b)
                (exactp b 24)
                (<= 1 b)
                (< b 2))
           (and (exactp (rcp24 b) 24)
                (<= 1/2 (rcp24 b))
                (<= (rcp24 b) 1)
                (< (abs (- 1 (* b (rcp24 b)))) (expt 2 -23))))
  :rule-classes ())

(defund divsp (a b mode)
  (let* ((y0 (rcp24 b))
         (q0 (rne (* a y0) 24))
         (e0 (rne (- 1 (* b y0)) 24))
         (r0 (rne (- a (* b q0)) 24))
         (y1 (rne (+ y0 (* e0 y0)) 24))
         (q1 (rne (+ q0 (* r0 y1)) 24))
         (r1 (rne (- a (* b q1)) 24)))
    (rnd (+ q1 (* r1 y1)) mode 24)))

(defthm divsp-correct
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 24)
                (exactp b 24)
                (ieee-rounding-mode-p mode))
           (= (divsp a b mode) (rnd (/ a b) mode 24)))
  :rule-classes ())

(defthm rcp24-rtz-error
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2))
           (<= (abs (- 1 (* b (rcp24 (rtz b 24))))) (expt 2 -22)))
  :rule-classes ())

(defund divdp (a b mode)
  (let* ((y0 (rcp24 (rtz b 24)))
         (q0 (rne (* a y0) 53))
         (e0 (rne (- 1 (* b y0)) 53))
         (r0 (rne (- a (* b q0)) 53))
         (y1 (rne (+ y0 (* e0 y0)) 53))
         (e1 (rne (- 1 (* b y1)) 53))
         (y2 (rne (+ y0 (* e0 y1)) 53))
         (q1 (rne (+ q0 (* r0 y1)) 53))
         (y3 (rne (+ y1 (* e1 y2)) 53))
         (r1 (rne (- a (* b q1)) 53)))
    (rnd (+ q1 (* r1 y3)) mode 53)))

(defthm divdp-correct
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 53)
                (exactp b 53)
                (ieee-rounding-mode-p mode))
           (= (divdp a b mode) (rnd (/ a b) mode 53)))
  :rule-classes ())
)
