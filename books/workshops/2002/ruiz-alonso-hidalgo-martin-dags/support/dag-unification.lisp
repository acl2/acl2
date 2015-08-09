;;; dag-unification.lisp
;;; A unification algorithm representing terms as directed acyclic
;;; graphs (dags)
;;; ==========================================================================

#| To certify this book:

(in-package "ACL2")
(certify-book "dag-unification")
|#

(in-package "ACL2")

(include-book "terms")

(set-compile-fns t)

;;; One stobj, used to store the unification problem.
;;; terms-dag store the terms as dags, as we describe below.

(defstobj terms-dag
  (dag :type (array t (1000))
       :resizable t))

;;; There are three kinds of nodes: function nodes, variable nodes and
;;; is nodes. Depending on the kind of the node, we will store the
;;; following information, used to know its neighbors.

;;; - Variable nodes: they are of the form (X . t), where X is a
;;;   variable symbol.
;;; - Function nodes: they are of the form (F . L) where F is a function
;;;   symbol and L is the list of its arguments (and it is different
;;;   from T).
;;; - "Is" nodes: they are if the form N, where N is an integer.




;;; Some functions to show the stobjs
;;; ---------------------------------

(defun show-dag (min max terms-dag)
  (declare (xargs :mode :program
		  :stobjs terms-dag))
  (if (<= min max)
      (cons (dagi min terms-dag)
	    (show-dag (1+ min) max terms-dag))
    nil))



;;; Reset the stobjs

(defun reset-unif-problem (min max terms-dag)
  (declare (xargs :mode :program
		  :stobjs (terms-dag)))
  (if (not (<= min max))
      terms-dag
    (let* ((terms-dag (update-dagi min nil terms-dag)))
      (reset-unif-problem (1+ min) max terms-dag))))


;;; A function to store a term (or list of terms) in a dag:
;;; -------------------------------------------------------

(defun term-as-dag-aux (flg term terms-dag h variables)
  (declare (xargs :stobjs (terms-dag)
                  :verify-guards nil))
  (if flg
      (if (variable-p term)
	  (let* ((bound (assoc term variables))
		 (terms-dag
		  (update-dagi h (if bound (cdr bound) (cons term t))
			       terms-dag))
		 (new-variables
		  (if bound variables (acons term h variables))))
	    (mv terms-dag (1+ h) nil new-variables))
	(mv-let (terms-dag h1 hsl var1)
		(term-as-dag-aux
		 nil (cdr term) terms-dag (1+ h) variables)
		(let* ((terms-dag
			(update-dagi h (cons (car term) hsl) terms-dag)))
		  (mv terms-dag h1 nil var1))))
    (if (endp term)
	(mv terms-dag h term variables)
      (mv-let (terms-dag hcar ign varcar)
	      (term-as-dag-aux t (car term) terms-dag h variables)
	      (declare (ignore ign))
	      (mv-let (terms-dag hcdr hsl varcdr)
		      (term-as-dag-aux
		       nil (cdr term) terms-dag hcar varcar)
		      (mv terms-dag hcdr (cons h hsl) varcdr))))))


(defun term-as-dag (term terms-dag)
  (declare (xargs :stobjs (terms-dag)
                  :verify-guards nil))
  (mv-let (terms-dag h hs var)
	  (term-as-dag-aux t term terms-dag 0 nil)
	  (declare (ignore h hs var))
	  terms-dag))

;;; Example:
;;; --------

(defun unif-two-terms-problem (t1 t2 terms-dag)
  (declare (xargs :mode :program
		  :stobjs (terms-dag)))
  (let* ((size (+ (length-term t t1) (length-term t t2) 1))
	 (terms-dag (resize-dag size terms-dag)))
    (term-as-dag (list 'equ t1 t2) terms-dag)))

;;; Examples:

;(unif-two-terms-problem
;    '(f x (g (a) y)) '(f x (g y x)) terms-dag)
; (show-dag 0 10 terms-dag)
; ===> ((EQU 1 6) (F 2 3) (X . T) (G 4 5) (A) (Y . T)
;                 (F 7 8) 2 (G 9 10) 5 2)
;(unif-two-terms-problem
;   '(f (h z) (g (h x) (h u))) '(f x (g (h u) v)) terms-dag)
;(show-dag 0 14 terms-dag)
; ===> ((EQU 1 9) (F 2 4) (H 3) (Z . T) (G 5 7) (H 6) (X . T) (H 8) (U . T)
;                 (F 10 11) 6 (G 12 14) (H 13) 8 (V . T))

;;; Some macros, to improve readability:
;;; ------------------------------------



(defmacro dag-variable-p (x)
  `(equal (cdr ,x) t))

(defmacro dag-args (x)
  `(cdr ,x))

(defmacro dag-symbol (x)
  `(car ,x))

(defmacro dag-bound-p (x)
  `(integerp ,x))

;;; Before defining the unification algorithm, we need some auxiliary
;;; functions:

;;; The function dag-deref finds the end of a instantiation chain

(defun dag-deref (x terms-dag)
  (declare (xargs :mode :program
		  :stobjs terms-dag))
  (let ((p (dagi x terms-dag)))
    (if (dag-bound-p p) (dag-deref p terms-dag) x)))


;;; A function that checks if a variable node x is in the term dag h (or
;;; list of terms, depending on flg)

(defun occur-check (flg x h terms-dag)
  (declare (xargs :mode :program
		  :stobjs terms-dag))
  (if flg
      (let ((p (dagi h terms-dag)))
	(if (dag-bound-p p)
	    (occur-check flg x p terms-dag)
	  (let ((args (dag-args p)))
	    (if (equal args t)
		(= x h)
	      (occur-check nil x args terms-dag)))))
    (if (endp h)
	nil
      (or (occur-check t x (car h) terms-dag)
	  (occur-check nil x (cdr h) terms-dag)))))

;;; Note that this function is non-terminating in general (for example
;;; if g is cyclic).

;;; Application of a transformation step
;;; -----------------------------------

;;; This function applies one step of transformation w.r.t. the set of
;;; rules given by Martelli and Montanari (M-M).

;;; It receives as input a system S of equations to be
;;; unified and a substitution U (partially) computed. Depending on the
;;; form of the first equation of S, one of the rules of M-M is
;;; applied. The main point here is that S and U only contain pointers
;;; to the terms stored in dag. In particular, S is a list of pairs of
;;; indexes, and U is a list of indexes pointing to the nodes where the
;;; instantiated variables are stored (i.e. a substitution). The
;;; function returns a multivalue with the following components,
;;; obtained after the application of one step of M-M: the resulting
;;; system of equations to be solved, the resulting substitution, a
;;; boolean value (to detect unsovability) and the stobj terms-dag.

(defun dag-transform-mm (S U terms-dag)
  (declare (xargs :stobjs (terms-dag)
		  :mode :program))
  (let* ((ecu (car S))
	 (t1 (dag-deref (car ecu) terms-dag))
	 (t2 (dag-deref (cdr ecu) terms-dag))
	 (R (cdr S))
	 (p1 (dagi t1 terms-dag))
	 (p2 (dagi t2 terms-dag)))
    (cond
     ((= t1 t2) (mv R U t terms-dag))
     ((dag-variable-p p1)
      (if (occur-check t t1 t2 terms-dag)
	  (mv nil nil nil terms-dag)
	(let ((terms-dag (update-dagi t1 t2 terms-dag)))
	  (mv R (cons (cons (dag-symbol p1) t2) U) t terms-dag))))
     ((dag-variable-p p2)
      (mv (cons (cons t2 t1) R) U t terms-dag))
     ((not (eql (dag-symbol p1)
		(dag-symbol p2)))
      (mv nil nil nil terms-dag))
     (t (mv-let (pair-args bool)
		(pair-args (dag-args p1) (dag-args p2))
		(if bool
		    (mv (append pair-args R) U t terms-dag)
		  (mv nil nil nil terms-dag)))))))

;;; REMARK: If we want to be able to reconstruct the original
;;; unification problem, we could apply the elimination rule returning
;;; (mv R (cons (cons (dag-symbol p1) t1) U) t terms-dag) instead of
;;; (mv R (cons (cons (dag-symbol p1) t2) U) t terms-dag)
;;; This would be equally sound.


;;; Iterative application of transformation steps until failure is
;;; detected or there are no more equations to be solved
;;; ---------------------------------------------------------------

(defun dag-solve-system (S U bool terms-dag)
  (declare (xargs :stobjs (terms-dag)
		  :mode :program))
  (if (or (not bool) (endp S))
      (mv S U bool terms-dag)
    (mv-let (S1 U1 bool1 terms-dag)
	    (dag-transform-mm S U terms-dag)
	    (dag-solve-system S1 U1 bool1 terms-dag))))


;;; Note that this function is not terminating in general, even if
;;; occur-check is never applied: the decompose rule is a possible
;;; source of non-termination. For example

;;; (update-dagi 0 '(equ 1 2) terms-dag)
;;; (update-dagi 1 '(f 1) terms-dag)
;;; (update-dagi 2 '(f 2) terms-dag)
;;; (dag-solve-system '((1 . 2)) nil t terms-dag) ===> NON TERMINATING!!!

;;; The term (or list of terms) stored in the stobj as dag, starting in
;;; a given node h (or list of nodes)
;;; --------------------------------------------------------------------

(defun dag-as-term (flg h terms-dag)
  (declare (xargs :mode :program
		  :stobjs (terms-dag)))
  (if flg
      (let ((p (dagi h terms-dag)))
	(if (dag-bound-p p)
	    (dag-as-term flg p terms-dag)
	  (let ((args (dag-args p))
		(symb (dag-symbol p)))
	    (if (equal args t)
		symb
	      (cons symb (dag-as-term nil args terms-dag))))))
    (if (endp h)
	h
      (cons (dag-as-term t (car h) terms-dag)
	    (dag-as-term nil (cdr h) terms-dag)))))


;;; Example:
;;; ACL2 !>(unif-two-terms-problem
;;; 			 '(f (h z) (g (h x) (h u))) '(f x (g (h u) v))
;;; 			 terms-dag)
;;; <terms-dag>
;;; ACL2 !>(dag-as-term t 0 terms-dag)
;;; (EQU (F (H Z) (G (H X) (H U)))
;;;      (F X (G (H U) V)))

;;; Given a list of pairs (symbols . variable nodes), it obtains the
;;; substitution of those variables stored in the dag.
;;; --------------------------------------------------------------------


(defun show-umg (vars terms-dag)
  (declare (xargs :stobjs (terms-dag)
		  :mode :program))
  (if (endp vars)
      nil
    (cons
     (cons (caar vars)
	   (dag-as-term t (cdar vars) terms-dag))
     (show-umg (cdr vars) terms-dag))))

;;; MGU of two terms
;;; -------------------

(defun initial-to-be-solved (terms-dag)
  (declare (xargs :stobjs terms-dag
		  :mode :program))
  (list (cons (first (cdr (dagi  0 terms-dag)))
	      (second (cdr (dagi 0 terms-dag))))))

(defun dag-mgu (t1 t2 terms-dag)
  (declare (xargs :stobjs (terms-dag)
		  :mode :program))
  (let ((terms-dag
	 (unif-two-terms-problem t1 t2 terms-dag)))
    (mv-let (S U bool terms-dag)
	    (dag-solve-system
	     (initial-to-be-solved terms-dag) nil t terms-dag)
	    (declare (ignore S))
	    (if bool
		(mv (show-umg U terms-dag) terms-dag)
	      (mv nil terms-dag)))))

;;; Unifiability of two terms
;;; -------------------------

;;; Note that this is esentially the same function as dag-mgu, but we
;;; are not interested in the unifier, only in unifiability.

(defun dag-unifiable (t1 t2 terms-dag)
  (declare (xargs :stobjs (terms-dag)
		  :mode :program))
  (let ((terms-dag
	 (unif-two-terms-problem t1 t2 terms-dag)))
    (mv-let (S U bool terms-dag)
	    (dag-solve-system
	     (initial-to-be-solved terms-dag)
	     nil t terms-dag)
	    (declare (ignore S U))
	    (if bool
		(mv t terms-dag)
	      (mv nil terms-dag)))))


;;;;
;;; Exponential problems
;;;;

;;; See pages 85 and 86 of "Term Rewriting and All That...", Baader &
;;; Nipkow.

;;; Auxiliary functions to build the unification problem
(defun list-of-n (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (if (zp n)
      nil
    (cons n (list-of-n (1- n)))))

(defun list-of-f (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (if (zp n)
      nil
    (cons (list 'f (1- n) (1- n))
	  (list-of-f (1- n)))))

(defun exp-unif-problem-t1 (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (list-of-n n)))

(defun exp-unif-problem-t2 (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (list-of-f n)))


(defun exp-unif-problem (n terms-dag)
  (declare (xargs :stobjs (terms-dag)
		  :mode :program))
  (dag-unifiable (exp-unif-problem-t1 n)
		 (exp-unif-problem-t2 n)
		 terms-dag))

;;; (exp-unif-problem 100 terms-dag)
;;; Very fast!!!

;;; ------------------------------------------------------------------

;;; NOTE: If we change the order in which the equations are selected,
;;; the algorithm is much more ineffcient.


(defun exp-unif-problem-t1-rev (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (reverse (list-of-n n))))

(defun exp-unif-problem-t2-rev (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (reverse (list-of-f n))))


(defun exp-unif-problem-rev (n terms-dag)
  (declare (xargs :stobjs (terms-dag)
		  :mode :program))
  (dag-unifiable (exp-unif-problem-t1-rev n)
		 (exp-unif-problem-t2-rev n)
		 terms-dag))


;;; (exp-unif-problem-rev 20 terms-dag)
;;; For n>20, very slow.




;;; ------------------------------------------------------------------

;;; The above algorithm is still exponential in time. The
;;; following unification problem reach that complexity.

(defun list-of-n- (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (if (zp n)
      nil
    (cons (- n) (list-of-n- (1- n)))))

(defun list-of-f- (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (if (zp n)
      nil
    (cons (list 'f (- (1- n)) (- (1- n)))
	  (list-of-f- (1- n)))))

(defun exp-unif-problem-t1-q (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (append (list-of-n n) (list-of-n- n) (list n))))

(defun exp-unif-problem-t2-q (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (append (list-of-f n) (list-of-f- n) (list (- n)))))

(defun exp-unif-problem-q (n terms-dag)
  (declare (xargs :stobjs (terms-dag)
		  :mode :program))
  (dag-unifiable (exp-unif-problem-t1-q n)
		 (exp-unif-problem-t2-q n)
		 terms-dag))

; (comp t)

;;; ACL2 !>(exp-unif-problem-q 20 terms-dag)
;;; (T <terms-dag>)
;;; For n>20, impractical...


;;; Analogue to the previous unification problem, but not unifiable.

(defun exp-unif-problem-t1-qn (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (append (list-of-n n) (list-of-n- n) (list n '(a)))))

(defun exp-unif-problem-t2-qn (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (append (list-of-f n) (list-of-f- n) (list (- n) '(b)))))

(defun exp-unif-problem-qn (n terms-dag)
  (declare (xargs :stobjs (terms-dag)
		  :mode :program))
  (dag-unifiable (exp-unif-problem-t1-qn n)
		 (exp-unif-problem-t2-qn n)
		 terms-dag))


;;; ACL2 !>(exp-unif-problem-qn 20 terms-dag)
;;; (NIL <terms-dag>)
