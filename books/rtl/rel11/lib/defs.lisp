; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
;
; Contact:
;   David M. Russinoff
;   1106 W 9th St., Austin, TX 78703
;   david@russinoff.com
;   http://www.russinoff.com
;
; See license file books/rtl/rel11/license.txt.
;

;; This file contains definitions that are shared between books of lib.

(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "../support/top"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

(defund congruent (a b n)
  (declare (xargs :guard (and (real/rationalp a)
                              (real/rationalp b)
                              (real/rationalp n)
                              (not (= n 0)))))
  (equal (mod a n) (mod b n)))

(defund chop (x k)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp k))))
  (/ (fl (* (expt 2 k) x)) (expt 2 k)))



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

(defn formal-+ (x y)
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defun cat-size (x)
  (declare (xargs :guard (and (true-listp x)
                              (evenp (length x)))))
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
  (declare (xargs :guard (and (natp l)
                              (natp n)
                              (natp x))))
  (if (and (integerp n) (> n 0))
      (cat (mulcat l (1- n) x)
           (* l (1- n))
           x
           l)
    0))

(defnd ui (r) r)

(defund si (r n)
  (declare (xargs :guard (and (integerp r)
                              (natp n))))
  (if (= (bitn r (1- n)) 1)
      (- r (expt 2 n))
    r))

(defund sextend (m n r)
  (declare (xargs :guard (and (natp m)
                              (natp n)
                              (integerp r))))
  (bits (si r n) (1- m) 0))

(defund uf (r n m)
  (declare (xargs :guard (and (natp r)
                              (natp n)
                              (natp m))))
  (* (expt 2 (- m n)) (ui r)))

(defund sf (r n m)
  (declare (xargs :guard (and (integerp r)
                              (natp n)
                              (natp m))))
  (* (expt 2 (- m n)) (si r n)))

(defnd sgn (x)
  (if (or (not (rationalp x)) (equal x 0))
      0
    (if (< x 0) -1 +1)))

(defnd expo (x)
  (declare (xargs :measure (:? x)))
  (mbe :logic (cond ((or (not (rationalp x)) (equal x 0)) 0)
                    ((< x 0) (expo (- x)))
                    ((< x 1) (1- (expo (* 2 x))))
                    ((< x 2) 0)
                    (t (1+ (expo (/ x 2)))))
       :exec (if (rationalp x)
                 (let* ((n (abs (numerator x)))
                        (d (denominator x))
                        (ln (integer-length n))
                        (ld (integer-length d))
                        (l (- ln ld)))
                   (if (>= ln ld)
                       (if (>= (ash n (- l)) d) l (1- l))
                     (if (> ln 1)
                         (if (> n (ash d l)) l (1- l))
                       (- (integer-length (1- d))))))
               0)))

(defnd sig (x)
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

(defund exactp (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (integerp (* (sig x) (expt 2 (1- n)))))

(defnd formatp (f)
  (and (consp f)
       (consp (cdr f))
       (consp (cddr f))
       (natp (cadr f))
       (> (cadr f) 1)
       (natp (caddr f))
       (> (caddr f) 1)))

(defund explicitp (f)
  (declare (xargs :guard (formatp f)))
  (car f))

(defund prec (f)
  (declare (xargs :guard (formatp f)))
  (cadr f))

(defund expw (f)
  (declare (xargs :guard (formatp f)))
  (caddr f))

(defund sigw (f)
  (declare (xargs :guard (formatp f)))
  (if (explicitp f)
      (prec f)
    (1- (prec f))))

(defnd encodingp (x f)
  (and (formatp f) (bvecp x (+ 1 (expw f) (sigw f)))))

(defnd hp () '(nil 11 5))

(defnd sp () '(nil 24 8))

(defnd dp () '(nil 53 11))

(defnd ep () '(t 64 15))

(defnd bf () '(nil 8 8))

(in-theory (disable (sp) (dp) (ep) (bf)))

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

(defund bias (f)
  (declare (xargs :guard (formatp f)))
  (- (expt 2 (- (expw f) 1)) 1))

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

(defund ndecode (x f)
  (declare (xargs :guard (encodingp x f)))
  (* (if (= (sgnf x f) 0) 1 -1)
     (expt 2 (- (expf x f) (bias f)))
     (1+ (* (manf x f) (expt 2 (- 1 (prec f)))))))

(defnd nrepp (x f)
  (and (rationalp x)
       (formatp f)
       (not (= x 0))
       (< 0 (+ (expo x) (bias f)))
       (< (+ (expo x) (bias f)) (1- (expt 2 (expw f))))
       (exactp x (prec f))))

(defund nencode (x f)
  (declare (xargs :guard (nrepp x f)))
  (cat (if (= (sgn x) 1) 0 1)
       1
       (+ (expo x) (bias f))
       (expw f)
       (* (sig x) (expt 2 (1- (prec f))))
       (sigw f)))

(defund spn (f)
  (declare (xargs :guard (formatp f)))
  (expt 2 (- 1 (bias f))))

(defund lpn (f)
  (declare (xargs :guard (formatp f)))
  (* (expt 2 (- (expt 2 (expw f)) (+ 2 (bias f))))
     (- 2 (expt 2 (- 1 (prec f))))))

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

(defnd drepp (x f)
  (and (rationalp x)
       (formatp f)
       (not (= x 0))
       (<= (- 2 (prec f)) (+ (expo x) (bias f)))
       (<= (+ (expo x) (bias f)) 0)
       (exactp x (+ (1- (prec f)) (bias f) (expo x)))))

(defund dencode (x f)
  (declare (xargs :guard (drepp x f)))
  (cat (if (= (sgn x) 1) 0 1)
       1
       0
       (expw f)
       (* (sig x) (expt 2 (+ -2 (prec f) (expo x) (bias f))))
       (sigw f)))

(defund spd (f)
     (declare (xargs :guard (formatp f)))
     (expt 2 (+ 2 (- (bias f)) (- (prec f)))))

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

(defund rebias (expo old new)
  (declare (xargs :guard (and (integerp expo)
                              (posp old)
                              (posp new))))
  (+ expo (- (expt 2 (1- new)) (expt 2 (1- old)))))

(defund rtz (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (* (sgn x)
     (fl (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(defund raz (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (* (sgn x)
     (cg (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(defun re (x)
  (declare (xargs :guard (real/rationalp x)))
  (- x (fl x)))

(defund rne (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(rtz x n)
      (if (> f 1/2)
	  (raz x n)
	(if (evenp z)
	    (rtz x n)
	  (raz x n))))))

(defund rna (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz x n)
    (raz x n)))

(defund rto (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (if (exactp x (1- n))
      x
    (+ (rtz x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(defun rup (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (if (>= x 0)
      (raz x n)
    (rtz x n)))

(defun rdn (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (if (>= x 0)
      (rtz x n)
    (raz x n)))

(defnd IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defnd common-mode-p (mode)
  (or (IEEE-rounding-mode-p mode) (equal mode 'raz) (equal mode 'rna)))

(defund rnd (x mode n)
  (declare (xargs :guard (and (real/rationalp x)
                              (common-mode-p mode)
                              (integerp n))))
  (case mode
    (raz (raz x n))
    (rna (rna x n))
    (rtz (rtz x n))
    (rup (rup x n))
    (rdn (rdn x n))
    (rne (rne x n))
    (otherwise 0)))

(defund flip-mode (m)
  (declare (xargs :guard (common-mode-p m)))
  (case m
    (rup 'rdn)
    (rdn 'rup)
    (t m)))

(defun rnd-const (e mode n)
  (declare (xargs :guard (and (integerp e)
                              (common-mode-p mode)
                              (integerp n))))
  (case mode
    ((rne rna) (expt 2 (- e n)))
    ((rup raz) (1- (expt 2 (1+ (- e n)))))
    (otherwise 0)))

(defund drnd (x mode f)
  (declare (xargs :guard (and (real/rationalp x)
                              (common-mode-p mode)
                              (formatp f))))
  (rnd x mode (+ (prec f) (expo x) (- (expo (spn f))))))

(defund rtz-sqrt (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (natp n))))
  (if (zp n)
      0
    (let* ((lower (rtz-sqrt x (1- n)))
           (upper (+ lower (expt 2 (- n)))))
      (if (<= (* upper upper) x)
          upper
        lower))))

(defund rto-sqrt (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (posp n))))
  (let ((trunc (rtz-sqrt x (1- n))))
    (if (< (* trunc trunc) x)
        (+ trunc (expt 2 (- n)))
      trunc)))

(defund qsqrt (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (posp n))))
  (let ((e (1+ (fl (/ (expo x) 2)))))
    (* (expt 2 e)
       (rto-sqrt (/ x (expt 2 (* 2 e))) n))))

(defun fp+ (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (+ x (expt 2 (- (1+ (expo x)) n))))

(defun fp- (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (if (= x (expt 2 (expo x)))
      (- x (expt 2 (- (expo x) n)))
    (- x (expt 2 (- (1+ (expo x)) n)))))
