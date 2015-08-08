(in-package "MODEL-CHECK")
(include-book "models")

(defun mu-symbolp (s)
  (and (symbolp s)
       (not (in s '(+ & MU NU true false)))))

(defun basic-m-calc-formulap (f ap v)
"True iff f is a mu-calculus formula given that ap is the list of
atomic proposition constants and v is the set of atomic proposition
variables. This checks that f is a basic mu-calc formula.  We allow
for abbreviations (e.g. =>) with translate. Formats of formulas are: p
-propositional variable or constant (EX f), (f1 & f2), (f1 + f2),
 (~ f), (MU y f(y)), (NU y f(y))"
  (cond ((symbolp f)
	 (or (in f '(true false))
	     (and (mu-symbolp f)
		  (or (in f ap) (in f v)))))
	((equal (len f) 2)
	 (and (in (first f) '(~ EX))
	      (basic-m-calc-formulap (second f) ap v)))
	((equal (len f) 3)
	 (let ((first (first f))
	       (second (second f))
	       (third (third f)))
	   (or (and (in second '(& +))
		    (basic-m-calc-formulap first ap v)
		    (basic-m-calc-formulap third ap v))
	       (and (or (in first '(MU NU)))
		    (mu-symbolp second)
		    (not (in second ap))
		    (basic-m-calc-formulap third ap (cons second v))))))))


(defun translate-f (f)
"This is how I chose to extend the syntax of the Mu-calculus so one
now has AX, \| (same as +), => and -> (both are implies), and =, <->,
<=> (all are for boolean equality).  This function just rewrites these
in terms of the basic boolean operators."
  (cond ((symbolp f) f)
	((equal (len f) 2)
	 (let ((first (first f))
	       (second (second f)))
	   (cond ((equal first 'AX)
		  `(~ (EX (~ ,(translate-f second)))))
		 (t `(,first ,(translate-f second))))))
	((equal (len f) 3)
	 (let ((first (first f))
	       (second (second f))
	       (third (third f)))
	   (cond ((equal second '\|)
		  `(,(translate-f first) + ,(translate-f third)))
		 ((in second '(=> ->))
		  `((~ ,(translate-f first)) + ,(translate-f third)))
		 ((in second '(= <=> <->))
		  `(((~ ,(translate-f first)) + ,(translate-f third)) &
		    ((~ ,(translate-f third)) + ,(translate-f first))))
		 ((in first '(MU NU))
		  `(,first ,second ,(translate-f third)))
		 (t `(,(translate-f first) ,second ,(translate-f third))))))
	(t f)))

(defun m-calc-formulap (f ap v)
  (basic-m-calc-formulap (translate-f f) ap v))

(defun m-calc-sentencep (f ap)
"Top level function.  True if f is a mu-calculus formula.  We require
that variable names and constant names do not overlap.  Also, we do
not allow free variables."
  (m-calc-formulap f ap nil))

