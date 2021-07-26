;ordinal arithmetic definitions
(in-package "ACL2")
(local (disable-forcing))

(defun firstn (n l)
  "The sublist of L consisting of its first N elements."
  (declare (xargs :guard (and (true-listp l)
                              (integerp n)
                              (<= 0 n))))
  (cond ((endp l) nil)
        ((zp n) nil)
        (t (cons (car l)
                 (firstn (1- n) (cdr l))))))

(defun dropn (n a)
  "Behaves similarly to nthcdr"
  (declare (xargs :guard (and (natp n))))
  (if (or (atom a) (zp n))
      a
    (dropn (1- n) (cdr a))))

(defun wcmp (a b)
  "A comparitor function for numbers"
  (declare (xargs :guard (and (rationalp a) (rationalp b))))
  (cond ((= a b) 'eq)
	((< a b) 'lt)
	(t 'gt)))

(defun ocmp-aux (x y)
  "The efficient version of the comparitor function for ordinals"
  (declare (xargs :guard (and (o-p x) (o-p y))))
  (cond ((and (o-finp x)
	      (o-finp y))
	 (wcmp x y))
	((o-finp x) 'lt)
	((o-finp y) 'gt)
	(t
	 (let ((cmp-fe (ocmp-aux (o-first-expt x)
                                 (o-first-expt y))))
	   (if (eq cmp-fe 'eq)
	       (let ((cmp-fco (wcmp (o-first-coeff x)
				    (o-first-coeff y))))
		 (if (equal cmp-fco 'eq)
		     (ocmp-aux (o-rst x)
                               (o-rst y))
		   cmp-fco))
	     cmp-fe)))))

(defun ocmp (x y)
  "An efficient comparitor function for ordinals"
  (declare (xargs :guard (and (o-p x) (o-p y))
		  :verify-guards nil))
  (mbe :logic (cond ((o< x y) 'lt)
		    ((o> x y) 'gt)
		    (t 'eq))
       :exec (ocmp-aux x y)))

(defun omega-term (x k)
  "Creates (w^x)*k"
  (declare (xargs :guard (and (not (equal x 0)) (o-p x) (posp k))))
  (make-ord x k 0))

(defmacro first-term (x)
  "Gives the first term of x"
  `(omega-term (o-first-expt ,x) (o-first-coeff ,x)))

(defun omega ()
  (declare (xargs :guard t))
  (omega-term 1 1))

(defun o-max (a b)
  (declare (xargs :guard (and (o-p a) (o-p b))))
  (if (o< a b) b a))

(defexec limitpart (a)
  "Returns the maximum limit ordinal (or 0) that is < a"
  (declare (xargs :guard (o-p a)
		  :verify-guards nil))
  (mbe :logic (if (o-finp a)
		  0
		(make-ord (o-first-expt a) (o-first-coeff a) (limitpart (o-rst a))))
       :exec (if (o-finp a)
		 0
	       (cons (car a)
		     (limitpart (o-rst a))))))

(defun natpart (a)
  "Returns the natural number part of a"
  (declare (xargs :guard (o-p a)))
  (if (o-finp a)
      a
    (natpart (o-rst a))))

(defun limitp (a)
  (declare (xargs :guard (o-p a)))
  (and (o-infp a)
       (o-p a)
       (equal (natpart a) 0)))

(defun olen (a)
  "Returns the length of an ordinal"
  (declare (xargs :guard (o-p a)))
  (if (o-infp a)
      (1+ (olen (o-rst a)))
    0))

(defexec o-last-expt (x)
  "The last non-zero exponent of a cnf ordinal"
  (declare (xargs :guard (and (o-infp x) (o-p x))))
  (mbe :logic (cond ((o-finp x) 0)
		    ((o-finp (o-rst x)) (o-first-expt x))
		    (t (o-last-expt (o-rst x))))
       :exec (if (o-finp (o-rst x))
		 (o-first-expt x)
	       (o-last-expt (o-rst x)))))

(defun ob+ (x y)
  "Efficient ordinal addition"
  (declare (xargs :guard (and (o-p x) (o-p y))
		  :verify-guards nil))
  (let* ((fe-x (o-first-expt x))
	 (fe-y (o-first-expt y))
	 (fco-x (o-first-coeff x))
	 (fco-y (o-first-coeff y))
	 (cmp-fe (ocmp fe-x fe-y)))
    (cond ((and (o-finp x) (o-finp y)) (+ x y))
	  ((or (o-finp x) (eq cmp-fe 'lt)) y)
	  ((eq cmp-fe 'gt)
	   (make-ord fe-x fco-x (ob+ (o-rst x) y)))
	  (t (make-ord fe-y (+ fco-x fco-y) (o-rst y))))))

(defmacro o+ (&rest rst)
; based on the macro +
  (if rst
      (if (cdr rst)
          (xxxjoin 'ob+ rst)
        (car rst))
    0))

(defun o- (x y)
  "Efficient ordinal subtraction"
  (declare (xargs :guard (and (o-p x) (o-p y))
		  :verify-guards nil))
  (cond ((and (o-finp x) (o-finp y) (<= x y))
	 0)
	((and (o-finp x) (o-finp y))
	 (- x y))
	(t
	 (let ((fco-x (o-first-coeff x))
	       (fco-y (o-first-coeff y))
	       (cmp-fe (ocmp (o-first-expt x)
			     (o-first-expt y))))
	   (cond ((or (o-finp x) (eq cmp-fe 'lt)) 0)
		 ((or (o-finp y) (eq cmp-fe 'gt)) x)
		 ((< fco-x fco-y) 0)
		 ((> fco-x fco-y)
		  (make-ord (o-first-expt x)
			    (- fco-x fco-y)
			    (o-rst x)))
		 (t (o- (o-rst x) (o-rst y))))))))

(defun count1 (x y)
  "Returns the index of the first exp of a that is < the o-first-expt of b"
  (declare (xargs :guard (and (o-p x) (o-p y))))
  (cond ((o-finp x) 0)
	((o< (o-first-expt y) (o-first-expt x))
	 (+ 1 (count1 (o-rst x) y)))
	(t 0)))

(defun count2 (x y n)
  "Does the same as count1 if n < (count1 a b)"
  (declare (xargs :guard (and (o-p x) (o-p y) (natp n))
		  :verify-guards nil))
  (+ n (count1 (dropn n x) y)))

(defun padd (x y n)
  "Pseudo-add function used in pmult"
  (declare (xargs :guard (and (o-p x) (o-p y) (natp n) (<= n (count1 x y)))
		  :verify-guards nil))
  (if (or (o-finp x) (zp n))
      (o+ x y)
    (make-ord (o-first-expt x) (o-first-coeff x) (padd (o-rst x) y (1- n)))))

(defun pmult (x y n)
  "Pseudo-multiplication function"
  (declare (xargs :guard (and (o-p x)
			      (o-p y)
			      (natp n)
			      (<= n (count1 (o-first-expt x)
					    (o-first-expt y))))
		  :verify-guards nil))
  (let* ((fe-x (o-first-expt x))
	 (fe-y (o-first-expt y))
	 (fco-x (o-first-coeff x))
	 (fco-y (o-first-coeff y))
	 (m (count2 fe-x fe-y n)))
    (cond ((or (equal x 0) (equal y 0)) 0)
	  ((and (o-finp x) (o-finp y)) (* x y))
	  ((o-finp y)
	   (make-ord fe-x (* fco-x fco-y) (o-rst x)))
	  (t
	   (make-ord (padd fe-x fe-y m)
		     fco-y
		     (pmult x (o-rst y) m))))))

(defun ob* (x y)
  "Efficient ordinal multiplication"
  (declare (xargs :guard (and (o-p x) (o-p y))
		  :verify-guards nil))
  (mbe :logic (let ((fe-x (o-first-expt x)) (fe-y (o-first-expt y))
		    (fco-x (o-first-coeff x)) (fco-y (o-first-coeff y)))
		(cond ((or (equal x 0) (equal y 0)) 0)
		      ((and (o-finp x) (o-finp y)) (* x y))
		      ((o-finp y)
		       (make-ord fe-x
				 (* fco-x fco-y)
				 (o-rst x)))
		      (t (make-ord (o+ fe-x fe-y)
				   fco-y
				   (ob* x (o-rst y))))))
       :exec (pmult x y 0)))

(defmacro o* (&rest rst)
; based on the macro *
  (cond ((null rst) 1)
        ((null (cdr rst))
         (car rst))
        (t (xxxjoin 'ob* rst))))

(defun o^1 (x y)
  "Raises a natural number to an infinite power (x^y)"
  (declare (xargs :guard (and (posp x)
			      (not (equal x 1))
			      (o-p y))
		  :verify-guards nil))
  (cond ((o-finp y) (expt x y))
	((equal (o-first-expt y) 1)
	 (omega-term (o-first-coeff y)
		     (expt x (o-rst y))))
	(t
	 (let ((fe-y (o-first-expt y))
	       (fco-y (o-first-coeff y))
	       (z (o^1 x (o-rst y))))
	   (omega-term (make-ord (o- fe-y 1) fco-y (o-first-expt z))
		       (o-first-coeff z))))))

(defun o^2 (a b)
  "Raises a limit ordinal to a finite power"
  (declare (xargs :guard (and (o-p a) (o-infp a) (natp b))
		  :verify-guards nil))
  (cond ((zp b) 1)
	((= b 1) a)
	(t
	 (o* (omega-term (o* (o-first-expt a)
			     (1- b))
			   1)
	       a))))

(defun o^3h (a p n q)
  "Helper function for o^3"
  (Declare (xargs :guard (and (o-p a)
			      (o-infp a)
			      (equal (natpart a) 0)
			      (posp p)
			      (equal n (olen a))
			      (natp q))
		  :verify-guards nil))
  (if (zp q)
      p
    (padd (o* (o^2 a q) p)
	  (o^3h a p n (1- q))
	  n)))

(defun o^3 (a q)
  "Raises an infinite ordinal to a finite power"
  (declare (xargs :guard (and (o-infp a)
			      (natp q)
			      (o-p a))
		  :verify-guards nil))
  (cond ((= q 0) 1)
	((= q 1) a)
	((limitp a) (o^2 a q))
	(t
	 (let ((c (limitpart a))
	       (n (olen a)))
	   (padd (o^2 c q) (o^3h c (natpart a) n (1- q)) n)))))

(defun o^4 (a b)
  "Raises an infinite ordinal to an infinite power"
  (declare (xargs :guard (and (o-infp a)
			      (o-infp b)
			      (o-p a)
			      (o-p b))
		  :verify-guards nil))
  (o* (omega-term (o* (o-first-expt a)
		      (limitpart b))
		  1)
      (o^3 a (natpart b))))

(defun ob^ (x y)
  "Efficient ordinal exponentiation"
  (declare (xargs :guard (and (o-p x) (o-p y))
		  :verify-guards nil))
  (mbe
   :logic (let ((fe-x (o-first-expt x))
		(fe-y (o-first-expt y))
		(fco-y (o-first-coeff y)))
	    (cond ((or (and (o-finp y)
			    (not (posp y))) ;(zp y))
		       (equal x 1))
		   1)
		  ((equal x 0)
		   0)
		  ((o-finp y)
		   (o* x (ob^ x (1- y))))
		  ((o-finp x)
		   (if (equal fe-y 1)
		       (o* (omega-term fco-y 1)
			   (ob^ x (o-rst y)))
		     (o* (omega-term (omega-term (o- fe-y 1)
						 fco-y)
				     1)
			 (ob^ x (o-rst y)))))
		  (t
		   (o* (omega-term (o* fe-x (first-term y))
				   1)
		       (ob^ x (o-rst y))))))
   :exec (cond ((or (equal y 0)
		    (equal x 1))
		1)
	       ((equal x 0) 0)
	       ((and (o-finp x)
		     (o-finp y))
		(expt x y))
	       ((o-finp x) (o^1 x y))
	       ((o-finp y) (o^3 x y))
	       (t (o^4 x y)))))

(defmacro o^ (&rest rst)
; based on the macro *
  (cond ((null rst) 1)
        ((null (cdr rst))
         (car rst))
        (t (xxxjoin 'ob^ rst))))

(add-binop o+ ob+)
(add-binop o* ob*)
(add-binop o^ ob^)
