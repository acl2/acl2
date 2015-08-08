(in-package "ACL2")

(include-book "bash")

#|

PATH=/projects/hvg/SULFA/linux-bin:$PATH

/projects/hvg/SULFA/acl2/saved_acl2

|#

;(include-book "/projects/hvg/SULFA/books/sat/sat")
;(include-book "/projects/hvg/SULFA/books/sat/sat-setup")
;(include-book "/projects/hvg/SULFA/books/clause-processors/sat-clause-processor")


(defun rv (x)
  (if (endp x)
      nil
    (append (rv (cdr x)) (list (car x)))))


(set-state-ok t)

(defun usepath (p x)
  (if (endp p)
      x
    (usepath (cdr p) (nth (car p) x))))

(defun recp (x state)
  (getprop (car x) 'recursivep nil 'current-acl2-world (w state)))


; find the left innermost recursive term in x
; returns (path err state)
(mutual-recursion
 (defun find-rec (x state)
  (if (atom x)
      (mv nil t state)
    (mv-let (p err state) (find-rec-l (cdr x) 1 state)
	    (if err
		(if (recp x state)
		    (mv nil nil state)
		  (mv nil t state))
	      (mv p nil state)))))
 (defun find-rec-l (x n state)
   (if (endp x)
       (mv nil t state)
     (mv-let (p err state) (find-rec (car x) state)
	     (if err
		 (find-rec-l (cdr x) (1+ n) state)
	       (mv (cons n p) nil state))))))

(defun find-def (x)
  (if (endp x)
      nil
    (if (equal (car (cadr (car x)))
	       ':definition)
	(car x)
      (find-def (cdr x)))))

(defun getdef (x state)
  (let* ((lems
	  (getprop (car x) 'lemmas nil 'current-acl2-world (w state)))
	 (def
	  (find-def lems))
	 (body (nth 6 def))
	 (fmls (nth 5 def)))
	  (mv `(,fmls ,body)
	      state)))


(defun bind (pat tgt b)
  (let ((a (assoc pat b)))
    (if a
	(if (equal (cadr a) tgt)
	    (mv b nil)
	  (mv nil t))
      (mv (cons (list pat  tgt) b) nil))))

(defun rep-l (x l)
  (if (endp l)
      x
    (if (equal x (caar l))
	(cadar l)
      (rep-l x (cdr l)))))

(mutual-recursion
 (defun inst (tm bind)
   (if (atom tm)
       (rep-l tm bind)
     (if (quotep tm)
	 tm
       (cons (car tm)
	     (inst-l (cdr tm) bind)))))
 (defun inst-l (tm bind)
   (if (endp tm)
       nil
     (cons (inst (car tm) bind)
	   (inst-l (cdr tm) bind)))))

(defun inst-ll (l bind)
  (if (endp l)
      nil
    (cons (inst-l (car l) bind)
	  (inst-ll (cdr l) bind))))

(defun constant (x)
  (or
   (integerp x)
   (stringp x)
   (characterp x)))

(mutual-recursion
 (defun pmatch (pat tgt b)
   (if (atom pat)
       (if (constant pat)
	   (mv b (not (equal pat tgt)))
	 (mv-let (b err) (bind pat tgt b)
		 (if err
		     (mv nil t)
		   (mv b nil))))
     (if (or (not (consp tgt))
	     (not (eq (car pat) (car tgt))))
	 (mv nil t)
       (if (equal (car pat) 'quote)
	   (mv b (not (equal (cadr pat) (cadr tgt))))
	 (pmatch-l (cdr pat) (cdr tgt) b)))))
 (defun pmatch-l (pat tgt b)
   (if (endp pat)
       (if (eq pat tgt) (mv b nil) (mv nil t))
     (if (endp tgt)
	 (mv nil t)
       (mv-let (b1 err) (pmatch (car pat) (car tgt) b)
	       (if err
		   (mv nil t)
		 (pmatch-l (cdr pat) (cdr tgt) b1)))))))

(defun rwrite (tm rl)
  (let ((lhs (car rl))
	(rhs (cadr rl)))
    (mv-let (bind err) (pmatch lhs tm nil)
	    (if err
		(mv nil t)
	      (mv (inst rhs bind) nil)))))

(defun add-disj (d x)
  (if (endp x)
      nil
    (cons
     (list (cons d (caar x)) (cadar x))
     (add-disj d (cdr x)))))

(mutual-recursion
 (defun contains-call (rl x)
  (if (atom x)
      nil
    (if (member-eq (car x) rl)
	t
      (contains-call-l rl (cdr x)))))
(defun contains-call-l (rl x)
  (if (endp x)
      nil
    (or (contains-call rl (car x))
	(contains-call-l rl (cdr x))))))

; we assume x is the body of a recursive function which
; is composed of an if tree with terms at the leaves
; rl is the list of recursive functions for this
; body
(defun get-cases1 (x rl)
  (if (atom x)
      (mv (list (list nil x)) 1)
    (if (equal (car x) 'if)
	(mv-let (c b) (get-cases1 (caddr x) rl)
		(mv-let (c2 b2) (get-cases1 (cadddr x) rl)
			(if (< b b2)
			    (mv (append 	(add-disj (cadr x) c2)
						(add-disj `(not ,(cadr x)) c))
				(+ b b2))
			  (mv (append (add-disj `(not ,(cadr x)) c)
					(add-disj (cadr x) c2))
				(+ b b2)))))
      (mv (list (list nil x)) (if (contains-call rl x) 0 1)))))

(defun get-cases (x rl)
  (mv-let (c b) (get-cases1 x rl) (declare (ignore b))
	  c))

(mutual-recursion
 (defun decidable (x state)
  (if (atom x)
      t
    (and
     (not (recp x state))
     (decidable-l (cdr x) state))))
 (defun decidable-l (x state)
   (if (endp x)
       t
     (and
      (decidable (car x) state)
      (decidable-l (cdr x) state)))))


(defun replace-at (p nt x)
  (if (endp p)
      nt
    (if (atom x)
	x
      (update-nth (car p) (replace-at (cdr p) nt (nth (car p) x)) x))))


; l is a list of tuples (c r) where c is a clause and r is the new value
; for x at p under that clause
; we create a new clause that replaces r at p in x for each tuple
(defun new-clauses (p l x)
  (if (endp l)
      nil
    (cons
     (append (caar l) (replace-at p (cadar l) x))
     (new-clauses p (cdr l) x))))


#|
(mutual-recursion
 (defun refute (x depth sat::$sat state)
  (declare (xargs :stobjs sat::$sat :mode :program))
  (if (decidable-l x state)
      (acl2::sat x nil sat::$sat state)
    (if (zp depth)
	(mv nil nil sat::$sat state)
      (mv-let (p err state) (find-rec-l x 0 state) (declare (ignore err))
	      (mv-let (def state) (getdef (usepath p x) state)
		      (mv-let (x2 err) (rwrite (usepath p x) def) (declare (ignore err))
			      (let ((rn (recp (usepath p x) state)))
				      (let ((xl (get-cases x2 rn)))
					(refute-l (new-clauses p xl x) (1- depth) sat::$sat state)))))))))
 (defun refute-l (x depth sat::$sat state)
     (declare (xargs :stobjs sat::$sat :mode :program))
   (if (endp x)
       (mv nil nil sat::$sat state)
     (mv-let (r nop sat::$sat state)
	     (refute (car x) depth sat::$sat state)  (declare (ignore nop))
	     (if r
		 (mv r nil sat::$sat state)
	       (refute-l (cdr x) depth sat::$sat state))))))

(set-ignore-ok t)



(defun refute4 (x depth sat::$sat state)
  (declare (xargs :stobjs sat::$sat :mode :program))
  (let ((nop (cw "~x0~%" x))) (declare (ignore nop))
       (refute x depth sat::$sat state)))

|#

(mutual-recursion
 (defun refute5 (x depth  state)
   (declare (xargs  :mode :program))
  (if (decidable-l x state)
      (mv-let (err r state) (bash-term-to-dnf2 `(or ,@x) nil nil state) (declare (ignore err))
	      (mv r nil  state))
    (if (zp depth)
	(mv nil nil  state)
      (mv-let (p err state) (find-rec-l x 0 state) (declare (ignore err))
	      (mv-let (def state) (getdef (usepath p x) state)
		      (mv-let (x2 err) (rwrite (usepath p x) def) (declare (ignore err))
			      (let ((rn (recp (usepath p x) state)))
				      (let ((xl (get-cases x2 rn)))
					(refute5-l (new-clauses p xl x) (1- depth)  state)))))))))
 (defun refute5-l (x depth  state)
     (declare (xargs  :mode :program))
   (if (endp x)
       (mv nil nil  state)
     (mv-let (r nop  state)
	     (refute5 (car x) depth  state)  (declare (ignore nop))
	     (if r
		 (mv r nil  state)
	       (refute5-l (cdr x) depth  state))))))

(defun refute6 (x depth  state)
  (declare (xargs  :mode :program))
  (let ((nop (cw "~x0~%" x))) (declare (ignore nop))
       (refute5 x depth  state)))

(defmacro refute (x)
 `(let ((nop (cw "~%ATTEMPTING TO REFUTE~%~%~x0~%~%" ',x))) (declare (ignore nop))
  (mv-let (err r state)
	   (refute5 (list ',x) 6 state)
	   (declare (ignore r))
	   (if err
	       (let ((nop (cw "CEX~%~%~x0~%~%REFUTED~%" err))) (declare (ignore nop))
		 (mv nil nil state))
	     (let ((nop (cw "NO CEX FOUND~%"))) (declare (ignore nop))
	       (mv nil nil  state))))))




