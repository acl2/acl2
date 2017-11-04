(in-package "ACL2")

(include-book "refute")
;(include-book "exdefs")
(include-book "gen")

;(include-book "bash3")
;(include-book "../induct/myutil")
;(include-book "cprove")

(set-state-ok t)

;(set-ld-redefinition-action '(:doit . :overwrite) state)

(set-ignore-ok t)
(set-irrelevant-formals-ok t)


(logic)

(defthm car-ap-cons
  (equal (car (append (cons a b) c))
	 a))

(defthm cdr-ap-cons
  (equal (cdr (append (cons a nil) c))
	 c))

(defthm append-cons (CONSP (BINARY-APPEND (CONS X3 'NIL) z)) :rule-classes :type-prescription)

(defthm cons-ap
  (implies (syntaxp (not (equal x ''nil)))
	   (equal (cons a x)
		  (append (cons a nil) x))))

;(defthm cons-ap-ap
;  (implies (syntaxp (not (equal x ''nil)))
;	   (equal (append (append (cons a x) y) z)
;		  (append (cons a nil) (append x y)))))


(defthm ap-ap
  (equal (append (append x y) z) (append x y z)))

(program)



(defun basicp (x)
  (if (endp x)
      t
    (and
     (atom (car x))
     (basicp (cdr x)))))

(defun basic-on-call (x c)
  (if (endp x)
      t
    (and (or (atom (car c))
	     (atom (car x)))
	 (basic-on-call (cdr x) (cdr c)))))

(defun basic-on-calls (x l)
  (if (endp l)
      t
    (and (basic-on-call (cdr x) (cdr (car l)))
	 (basic-on-calls x (cdr l)))))

(defun get-calls (l)
  (if (endp l)
      nil
    (append (cddr (car l))
	    (get-calls (cdr l)))))

(defun ind-vars-basicp (x state)
  (let* ((im (getprop (car x) 'induction-machine nil 'current-acl2-world (w state)))
	 (calls (get-calls im)))
    (if (null im)
	nil
      (basic-on-calls x calls))))

;(ind-vars-basicp '(BINARY-APPEND Y (CONS X1 'NIL)) state)

(mutual-recursion
 (defun get-schemes (x state)
   (if (atom x)
       nil
     (append
      (if (ind-vars-basicp x state)
	  (list x)
	nil)
      (get-schemes-l (cdr x) state))))
 (defun get-schemes-l (x state)
   (if (endp x)
       nil
     (append (get-schemes (car x) state)
	     (get-schemes-l (cdr x) state)))))


;(get-schemes '(implies (equal (rv (rv x)) x)))

;(get-schemes '(implies (and (true-listp x) (true-listp y)) (equal (rot2 x (ap x y)) (ap y x))))

;(TRANSLATE '(implies (and (true-listp x) (true-listp y)) (equal (rot2 x (append x y)) (append y x))) nil NIL nil nil (W state) STATE)


(mutual-recursion
 (defun expand-implies (x)
   (if (atom x)
       x
     (let ((cdrx (expand-implies-l (cdr x))))
       (if (eq (car x) 'implies)
	   (mv-let (b err) (pmatch-l '(p q) cdrx nil) (declare (ignore err))
		   (inst '(IF P (IF Q T NIL) T) b))
	 (cons (car x) cdrx)))))
 (defun expand-implies-l (x)
   (if (endp x)
       nil
     (cons (expand-implies (car x))
	   (expand-implies-l (cdr x))))))

#|
(expand-implies
 '(IMPLIES (IF (TRUE-LISTP X) (TRUE-LISTP Y) 'NIL)
          (EQUAL (ROT2 X (BINARY-APPEND X Y))
                 (BINARY-APPEND Y X))))
|#


#|
(clausify '(IF (IF (TRUE-LISTP X) (TRUE-LISTP Y) 'NIL)
    (IF (EQUAL (ROT2 X (BINARY-APPEND X Y))
               (BINARY-APPEND Y X))
        T NIL)
    T) nil nil (sr-limit (w state)))
|#

(defun triv-clause (x)
  (if (endp x)
      nil
    (if (eq (car x) t)
	t
      (triv-clause (cdr x)))))

(defun simp-clause (x)
  (if (endp x)
      nil
    (if (eq (car x) nil)
	(simp-clause (cdr x))
      (cons (car x) (simp-clause (cdr x))))))

(defun simp-and-filter (x)
  (if (endp x)
      nil
    (if (triv-clause (car x))
	(simp-and-filter (cdr x))
      (cons (simp-clause (car x))
	    (simp-and-filter (cdr x))))))

(set-state-ok t)
(set-ignore-ok t)


(defun norm (x state)
  (mv-let (nop x state) (TRANSLATE x nil NIL nil nil (W state) STATE)
	  (let* ((x (expand-implies x))
		 (x (clausify x nil nil (sr-limit (w state))))
		 (x (simp-and-filter x)))
    (mv x state))))

(defun norm-l (x state)
  (if (endp x)
      (mv nil state)
    (mv-let (r state) (norm (car x) state)
	    (mv-let (r2 state) (norm-l (cdr x) state)
		    (mv (append r r2) state)))))


;(norm  '(implies (and (true-listp x) (true-listp y)) (equal (rot2 x (append x y)) (append y x))) state)

#|
(get-schemes-l '((NOT (TRUE-LISTP X))
   (NOT (TRUE-LISTP Y))
   (EQUAL (ROT2 X (BINARY-APPEND X Y))
          (BINARY-APPEND Y X))))



|#


(defun new-fsymbol (n)
  (intern (concatenate 'string "G" (coerce (explode-nonnegative-integer n 10 nil) 'string)) "ACL2"))

(defun new-var (n)
  (intern (concatenate 'string "NV" (coerce (explode-nonnegative-integer n 10 nil) 'string)) "ACL2"))

(defun new-thm (n)
  (intern (concatenate 'string "T" (coerce (explode-nonnegative-integer n 10 nil) 'string)) "ACL2"))

(defun new-ifn (n)
  (intern (concatenate 'string "IFN" (coerce (explode-nonnegative-integer n 10 nil) 'string)) "ACL2"))

(defun new-label (n)
  (intern (concatenate 'string "L" (coerce (explode-nonnegative-integer n 10 nil) 'string)) "ACL2"))



(program)


(defun err-fun () t)
;(trace! (err-fun :entry (break)))


(defrec pv (bind schemes log max-fun max-var max-ifn max-thm max-label depth) t)

(defmacro ld+ (&rest args)

; Matt K. mod: ACL2 now requires keyword :ld-user-stobjs-modified-warning in
; code.  I'm introducing LD+ here simply as a way to avoid writing that keyword
; repeatedly below.  Perhaps more thought should be given to whether or not we
; want a warning here when a user stobj is modified.

  `(ld ,@args :ld-user-stobjs-modified-warning :same))

(mutual-recursion
(defun intro-constr-funs (x ind-vars all-vars bind pv state)
  (if (atom x)
      (if (member x ind-vars)
	  (mv x bind pv state)
	(if (assoc x bind)
	    (mv (cadr (assoc x bind)) bind pv state)
	  (let* ((nf (new-fsymbol (access pv pv :max-fun)))
		 (nc `(,nf ,@all-vars))
		 (pv (change pv pv :max-fun (1+ (access pv pv :max-fun))))
		 (bind (cons (list x nc) bind)))
	    (mv-let (erp val state) (ld+ (list `(defstub ,nf (,@all-vars) t)))
 		    (if (or erp (equal val :error))
			(mv (err-fun) bind pv state)
		      (let ((pv (change pv pv :log (append
							    (access pv pv :log)
							    (list `(defstub ,nf (,@all-vars) t))))))
				      (mv nc bind pv state)))))))
    (if (quotep x)
	(mv x bind pv state)
      (mv-let (r bind pv state) (intro-constr-funs-l (cdr x) ind-vars all-vars bind pv state)
	      (mv (cons (car x) r) bind pv state)))))
(defun intro-constr-funs-l (x ind-vars all-vars bind pv state)
  (if (endp x)
      (mv nil bind pv state)
    (mv-let (r bind pv state) (intro-constr-funs (car x) ind-vars all-vars bind pv state)
	    (mv-let (r2 bind pv state) (intro-constr-funs-l (cdr x) ind-vars all-vars bind pv state)
		    (mv (cons r r2) bind pv state))))))



(defun rm-nop-subs (x)
  (if (endp x)
      nil
    (if (equal (car (car x)) (cadr (car x)))
	(rm-nop-subs (cdr x))
      (cons (car x) (rm-nop-subs (cdr x))))))

(defun strip-unmeas (x m)
  (if (endp x)
      nil
    (if (member-equal (car (car x)) m)
	(cons (car x) (strip-unmeas (cdr x) m))
      (strip-unmeas (cdr x) m))))

(defun ih-from-calls (x varsub fcall calls measured pv state)
  (if (endp calls)
      (mv nil nil pv state)
    (let* ((call (car calls)))
      (mv-let (isub err) (pmatch fcall call nil)
	      (let ((isub (strip-unmeas isub measured)))
		(let ((realsub (inst-ll isub varsub)))
		  (mv-let (r bind pv state)
			  (intro-constr-funs
			   (inst x realsub)
			   (strip-cars realsub)
			   (all-vars x)
			   nil
			   pv
			   state)
			  (mv-let (r2 calls2 pv state)
				  (ih-from-calls x varsub
						 fcall
						 (cdr calls)
						 measured
						 pv
						 state)
				  (mv (cons r r2) (append (list (append realsub bind)) calls2) pv state)))))))))




(defun subgoal-from-tc (x scheme tests calls just pv state)
  (let* ((fmls (formals (car scheme) (w state)))
	 (fcall `(,(car scheme) ,@fmls))
	 (measured (cadr just)))
    (mv-let (varsub err) (pmatch fcall scheme nil) ; a variable may match twice?
	      (mv-let (r subs pv state)
		      (ih-from-calls x varsub fcall calls measured pv state)
		      (mv `(implies
			    (and
			     ,@(inst-l tests varsub)
			     ,@r)
			    ,x)
			  (list (inst-l tests varsub) subs) pv state)))))


(defun subgoals-from-im (x scheme im just pv state)
  (if (endp im)
      (mv nil nil pv state)
    (let ((tests (cadr (car im)))
	  (calls (cddr (car im))))
      (mv-let (r tc pv state) (subgoal-from-tc x scheme tests calls just pv state)
	      (mv-let (r2 tcl pv state) (subgoals-from-im x scheme (cdr im) just pv state)
      (mv (cons r r2) (cons tc tcl) pv state))))))

(defun get-induct-goals (x scheme pv state)
  (let ((im (getprop (car scheme) 'induction-machine nil 'current-acl2-world (w state)))
	(just (getprop (car scheme) 'justification nil 'current-acl2-world (w state))))
    (mv-let (r tcs pv state) (subgoals-from-im x scheme im just pv state)
	    (mv t r tcs pv state))))

(logic)
(defstub goo (x y) t)

(defun foo (x)
  (if (atom x)
      nil
    (cons (foo (car x)) (foo (cdr x)))))
(program)

					;(get-induct-goals '(goo x y) '(foo x) state)

					;(get-induct-goals '(implies (and (true-listp x) (true-listp y)) (equal (rot2 x (append x y)) (append y x))) '(true-listp x) 0 state)

					#|

(wfall '(IMPLIES (AND (CONSP X)
		      (IMPLIES (AND (TRUE-LISTP (CDR X))
				    (TRUE-LISTP (G0 Y X)))
			       (EQUAL (ROT2 (CDR X) (APPEND (CDR X) (G0 Y X)))
				      (APPEND (G0 Y X) (CDR X)))))
		 (IMPLIES (AND (TRUE-LISTP X) (TRUE-LISTP Y))
			  (EQUAL (ROT2 X (APPEND X Y))
				 (APPEND Y X)))) state)

(wfall '(IMPLIES (AND (NOT (CONSP X)))
		 (IMPLIES (AND (TRUE-LISTP X) (TRUE-LISTP Y))
			  (EQUAL (ROT2 X (APPEND X Y))
				 (APPEND Y X)))) state)

(wfall '(and (IMPLIES (AND (CONSP X)
			   (IMPLIES (AND (TRUE-LISTP (CDR X))
					 (TRUE-LISTP (G0 Y X)))
				    (EQUAL (ROT2 (CDR X) (APPEND (CDR X) (G0 Y X)))
					   (APPEND (G0 Y X) (CDR X)))))
		      (IMPLIES (AND (TRUE-LISTP X) (TRUE-LISTP Y))
			       (EQUAL (ROT2 X (APPEND X Y))
				      (APPEND Y X))))
	     (IMPLIES (AND (NOT (CONSP X)))
		      (IMPLIES (AND (TRUE-LISTP X) (TRUE-LISTP Y))
			       (EQUAL (ROT2 X (APPEND X Y))
				      (APPEND Y X))))) state)


|#


(mutual-recursion
 (defun find-rec2 (x p state)
  (if (atom x)
      (mv nil state)
    (mv-let (r state) (find-rec2-l (cdr x) p 1 state)
	    (if (recp x state)
		(mv (cons p r) state)
	      (mv r state)))))
 (defun find-rec2-l (x p n state)
   (if (endp x)
       (mv nil state)
     (mv-let (r state) (find-rec2 (car x) (append p (list n)) state)
	     (mv-let (r2 state) (find-rec2-l (cdr x) p (1+ n) state)
	       (mv (append r r2) state))))))

(defun expand-def (p x state)
  (mv-let (d state) (getdef (usepath p x) state)
	  (mv-let (x2 err) (rwrite (usepath p x) d)
		  (mv-let (x3 state) (norm `(or ,@(replace-at p x2 x)) state)
			  (if (equal (len x3) 1)
			      (mv t (car x3) state)
			    (mv nil x state))))))

(defun try-paths (l x state)
  (if (endp l)
      (mv x state)
    (mv-let (changed x state) (expand-def (car l) x state)
	    (if changed
		(mv-let (r state) (find-rec2 (usepath (car l) x) (car l) state)
			(try-paths (append r (cdr l)) x state))
	      (try-paths (cdr l) x state)))))

(defun expand-defs (x state)
  (mv-let (pl state) (find-rec2-l x nil 0 state)
	  (try-paths (reverse pl) x state)))

(defun expand-defs-l (x state)
  (if (endp x)
      (mv nil state)
    (mv-let (r state) (expand-defs (car x) state)
	    (mv-let (r2 state) (expand-defs-l (cdr x) state)
		    (mv (cons r r2) state)))))


(defun norm-lc (x state)
  (if (endp x)
      (mv nil state)
    (mv-let (r state) (norm (car x) state)
	    (mv-let (r2 state) (norm-lc (cdr x) state)
		    (mv (append r r2) state)))))






#|



(NIL (TRUE-LISTP X)
     (((NOT (CONSP X))
       (TRUE-LISTP (G0 Y X))
       (NOT (TRUE-LISTP (CDR X)))
       (NOT (TRUE-LISTP Y))
       (EQUAL (ROT2 (CDR X)
                    (BINARY-APPEND (BINARY-APPEND (CDR X) Y)
                                   (CONS (CAR X) 'NIL)))
              (BINARY-APPEND Y X)))
      ((NOT (CONSP X))
       (NOT (EQUAL (ROT2 (CDR X)
                         (BINARY-APPEND (CDR X) (G0 Y X)))
                   (BINARY-APPEND (G0 Y X) (CDR X))))
       (NOT (TRUE-LISTP (CDR X)))
       (NOT (TRUE-LISTP Y))
       (EQUAL (ROT2 (CDR X)
                    (BINARY-APPEND (BINARY-APPEND (CDR X) Y)
                                   (CONS (CAR X) 'NIL)))
              (BINARY-APPEND Y X)))
      ((CONSP X)
       X (NOT (TRUE-LISTP Y))
       (EQUAL Y (BINARY-APPEND Y 'NIL))))
     <state>)

(hl
 '(EQUAL (ROT2 (CDR X)
	       (BINARY-APPEND (BINARY-APPEND (CDR X) Y)
			      (CONS (CAR X) 'NIL)))
	 (BINARY-APPEND Y X))
 '(EQUAL (ROT2 (CDR X)
	       (BINARY-APPEND (CDR X) (G0 Y X)))
	 (BINARY-APPEND (G0 Y X) (CDR X))))

(hl
 (BINARY-APPEND (BINARY-APPEND (CDR X) Y)
		(CONS (CAR X) 'NIL))
 (BINARY-APPEND (CDR X) (G0 Y X)))

(hl
 '(G1 Y X)
 '(BINARY-APPEND  Y (CONS (CAR X) 'NIL))
 )

(hl
 '(BINARY-APPEND (G1 Y X) (CDR X))
 '(BINARY-APPEND Y X)
 )

|#


(defun conp (x state)
  (getprop (car x) 'constrainedp nil 'current-acl2-world (w state)))

(mutual-recursion
 (defun constrainedp (x state)
   (if (atom x)
       nil
     (or (conp x state)
	 (constrainedp-l (cdr x) state))))
 (defun constrainedp-l (x state)
   (if (endp x)
       nil
     (or (constrainedp (car x) state)
	 (constrainedp-l (cdr x) state)))))


(defun pairs (x y)
  (if (endp x)
      nil
    (cons (list (car x) (car y))
	  (pairs (cdr x) (cdr y)))))

(defun try-decomp (x y)
  (if (and (consp x)
	   (consp y)
	   (equal (car x) (car y)))
      (mv nil (pairs (cdr x) (cdr y)))
    (mv t nil)))


(mutual-recursion
 (defun use-subst (x y l)
   (if (atom l)
       l
     (mv-let (r err) (rwrite l `(,x ,y))
	     (if err
		 (use-subst-l x y l)
	       r))))
 (defun use-subst-l (x y l)
  (if (endp l)
      nil
    (cons (use-subst x y (car l))
	  (use-subst-l x y (cdr l))))))

(defun rwritel (b x)
  (if (endp b)
      (mv nil t)
    (mv-let (r err) (rwrite x (car b))
	    (if err
		(rwritel (cdr b) x)
	      (mv r nil)))))

(mutual-recursion
 (defun use-substl (b l)
   (if (atom l)
       l
     (mv-let (r err) (rwritel b l)
	     (if err
		 (use-substl-l b l)
	       r))))
 (defun use-substl-l (b l)
  (if (endp l)
      nil
    (cons (use-substl b (car l))
	  (use-substl-l b(cdr l))))))


(program)

(defun rm-el (e x)
  (if (endp x)
      nil
    (if (equal e (car x))
	(cdr x)
      (cons (car x) (rm-el e (cdr x))))))

(defun rm-hyps (hyps x)
  (if (endp hyps)
      x
    (rm-hyps (cdr hyps) (rm-el (car hyps) x))))


(mutual-recursion
 (defun find-csub2 (x y e)
  (if (atom y)
      (mv t y)
    (if (equal x y)
	(mv nil e)
      (mv-let (err cdry) (find-csub2-l x (cdr y) e)
	      (mv err (cons (car y) cdry))))))
(defun find-csub2-l (x y e)
  (if (endp y)
      (mv t nil)
    (mv-let (err cary) (find-csub2 x (car y) e)
	    (if err
		(mv-let (err cdry) (find-csub2-l x (cdr y) e)
			(mv err (cons (car y) cdry)))
	      (mv err (cons cary (cdr y))))))))

(mutual-recursion
 (defun find-csub (x y e)
  (if (atom x)
      (mv t x y)
    (mv-let (err y) (find-csub2 x y e)
	    (if err
		(mv-let (err cdrx y) (find-csub-l (cdr x) y e)
			(mv err (cons (car x) cdrx) y))
	      (mv err e y)))))
 (defun find-csub-l (x y e)
   (if (endp x)
       (mv t nil y)
     (mv-let (err carx y) (find-csub (car x) y e)
	     (if err
		 (mv-let (err cdrx y) (find-csub-l (cdr x) y e)
			 (mv err (cons (car x) cdrx) y))
	       (mv err (cons carx (cdr x)) y))))))


(defun gen-common (x)
  (let ((a (cadr x))
	(b (caddr x)))
    (mv-let (err a b) (find-csub a b 'x0)
	    `(equal ,a ,b))))

(defun orient-eq (x state)
  (let ((a (cadr x))
	(b (caddr x)))
    (if (and
	 (consp a)
	 (conp a state))
	x
      `(equal ,b ,a))))

(mutual-recursion
(defun replace-consts (x max-var)
  (if (atom x)
      (mv x max-var)
    (if (quotep x)
	(let ((max-var (1+ max-var)))
	  (mv (new-var max-var) max-var))
      (mv-let (r max-var) (replace-consts-l (cdr x) max-var)
	      (mv (cons (car x) r) max-var)))))
(defun replace-consts-l (x max-var)
  (if (endp x)
      (mv nil max-var)
    (mv-let (r1 max-var) (replace-consts (car x) max-var)
	    (mv-let (r2 max-var) (replace-consts-l (cdr x) max-var)
		    (mv (cons r1 r2) max-var))))))

; replace any constants on the left side with new variables
(defun gen-unused (x max-var)
  (let* ((a (cadr x))
	 (b (caddr x))
	 )
    (mv-let (r max-var) (replace-consts a max-var)
	    (mv `(equal ,r ,b) max-var))))


(defun csubstp (d1 state)
  (and (consp d1)
       (equal (car d1) 'equal)
       (consp (cdr d1))
       (consp (cddr d1))
       (let* ( (x (cadr d1))
	       (y (caddr d1)))
	 (or (and
	      (consp x)
	      (conp x state))
	     (and
	      (consp y)
	      (conp y state))))))


					;(access pv (change pv (make pv) :max-fun 1) :max-fun)


(mutual-recursion
 (defun find-rec-nocon (x state)
   (if (atom x)
       (mv nil t state)
     (if (conp x state)
     (mv nil t state)
     (mv-let (p err state) (find-rec-nocon-l (cdr x) 1 state)
	     (if err
		 (if (recp x state)
		     (mv nil nil state)
		   (mv nil t state))
	       (mv p nil state))))))
 (defun find-rec-nocon-l (x n state)
   (if (endp x)
       (mv nil t state)
     (mv-let (p err state) (find-rec-nocon (car x) state)
     (if err
	 (find-rec-nocon-l (cdr x) (1+ n) state)
       (mv (cons n p) nil state))))))


(defun add-disj2 (d x)
  (if (endp x)
      nil
    (cons
     `(case (and ,@(cons d (cdr (cadr (car x))))) ,(caddr (car x)))
     (add-disj2 d (cdr x)))))

					; we assume x is the body of a recursive function which
					; is composed of an if tree with terms at the leaves
					; rl is the list of recursive functions for this
					; body
(defun get-cases12 (x rl)
  (if (atom x)
      (mv `((case (and) ,x)) 1)
    (if (equal (car x) 'if)
	(mv-let (c b) (get-cases12 (caddr x) rl)
		(mv-let (c2 b2) (get-cases12 (cadddr x) rl)
			(if (< b b2)
			    (mv (append 	(add-disj2 (cadr x) c2)
						(add-disj2 `(not ,(cadr x)) c))
				(+ b b2))
			  (mv (append (add-disj2 `(not ,(cadr x)) c)
				      (add-disj2 (cadr x) c2))
			      (+ b b2)))))
      (mv `((case (and) ,x)) (if (contains-call rl x) 0 1)))))

(defun get-cases2 (x rl)
  (mv-let (c b) (get-cases12 x rl) (declare (ignore b))
	  c))

(defun new-clauses2 (p l x)
  (if (endp l)
      nil
    (cons
     (append (cdr (cadr (car l))) (replace-at p (caddr (car l)) x))
     (new-clauses2 p (cdr l) x))))

(defun str-cat (m s)
  (intern (concatenate 'string (symbol-name m) s) "ACL2"))


(defmacro simp-term-trans (name args base cond trans)
  `(mutual-recursion
    (defun ,name ,args
     (if (atom ,(car args))
	 ,base
       (if ,cond
	   ,trans
	 (cons (car ,(car args)) (,(str-cat name "-L") (cdr ,(car args)) ,@(cdr args))))))
   (defun ,(str-cat name "-L") ,args
     (if (endp ,(car args))
	 nil
       (cons (,name (car ,(car args)) ,@(cdr args))
	     (,(str-cat name "-L") (cdr ,(car args)) ,@(cdr args)))))))

(simp-term-trans hide-constr (x state) x (conp x state) `(hide ,x))

(simp-term-trans rm-hide (x) x (equal (car x) 'hide) (cadr x))


#|

(hide-constr
'(OR (NOT (CONSP (BINARY-APPEND (CONS X1 'NIL) X2)))
                             (NOT (TRUE-LISTP X2))
                             (NOT (TRUE-LISTP Y))
                             (CONSP X2)
                             (EQUAL (G0 Y (BINARY-APPEND (CONS X1 'NIL) X2))
                                    (BINARY-APPEND (BINARY-APPEND X2 Y)
                                                   (CONS X1 'NIL))))
state)


|#


(defun find-csubst (x state)
  (if (endp x)
      (mv t nil)
    (if (csubstp (car x) state)
	(mv nil (orient-eq (car x) state))
      (find-csubst (cdr x) state))))

; take the clause x and simplify it by locating a
; recursive function and assuming a base case for that
; function
(defun gen-constr (x hyps pv state)
  (mv-let (p err state) (find-rec-nocon-l x 0 state)
	  (if err
	      (mv t nil pv state)
	    (mv-let (def state) (getdef (usepath p x) state)
		    (mv-let (bind err) (pmatch (car def) (usepath p x) nil)
		    (let* (
			   (rn (recp (usepath p x) state))
			   (cases (get-cases2 (cadr def) rn))
			   (icases (inst-l cases bind)))
		      ; hide g0? f
		      (mv-let (err r state) (bash-term-to-dnf `(or ,@hyps ,@(hide-constr-l (car (new-clauses2 p icases x)) state)) nil nil state) (declare (ignore err)) ;elim dtors ?
					(if (equal (len r) 1)
					    (mv-let (err subst) (find-csubst (rm-hide-l (car r)) state)
						    (if err
							(mv t nil pv state)
						      ;(mv-let (r max-var) (gen-unused (orient-eq subst state) (access pv pv :max-var))
							      (mv nil (orient-eq subst state) pv state)))
					  (mv t nil pv state)))))))))



;(untrace$ bash-term-to-dnf find-csubst gen-unused getdef get-cases1 hide-constr new-clauses2 find-rec-nocon add-disj2 get-cases2)

;(use-subst '(g x y) '(binary-append (cdr y) (cons (car x) nil)) '((g (cdr x) y)))

; d is a list of differences that we are trying to resolve
; we are at a base case when one side of an equality is a
; basic constrained function

(defun remove-nth (n x)
  (if (zp n)
      (cdr x)
    (cons (car x)
	  (remove-nth (1- n) (cdr x)))))






(defun clausify-diffs (x)
  (if (endp x)
      nil
    (cons `((equal ,(car (car x)) ,(cadr (car x))))
	  (clausify-diffs (cdr x)))))


(defun gnext (s)
  (cons (list (remove-nth (cadr (car s)) (car (car s))) 0) s))

(defun bnext (s)
  (if (endp s)
      nil
    (if (< (1+ (cadr (car s))) (len (car (car s))))
	(cons (list (car (car s)) (1+ (cadr (car s)))) (cdr s))
      (bnext (cdr s)))))

;(gnext '(((1 2) 0) ((0 1 2) 0)))

;(bnext '(((2) 0) ((1 2) 0) ((0 1 2) 0)))

(defun trav (s)
  (if (endp s)
      nil
    (if (< 2 (len s))
	(trav (bnext s))
      (trav (gnext s)))))

;(trav '(((0 1 2) 0)))



(defun cons-calls (l fcall)
  (if (endp l)
      nil
    `(cons ,(inst fcall (car l))
	   ,(cons-calls (cdr l) fcall))))



#|
(mutual-recursion
 (defun all-vars (x)
   (if (atom x)
       (if (constant x)
	   nil
	 (list x))
     (if (eq (car x) 'quote)
	 nil
       (all-vars-l (cdr x)))))
 (defun all-vars-l (x)
   (if (endp x)
       nil
     (append (all-vars (car x))
	     (all-vars-l (cdr x))))))
|#

(defun all-terms-c2 (l)
  (if (endp l)
      nil
    (list* (car (car l))
	   (cadr (car l))
	   (all-terms-c2 (cdr l)))))

(defun all-terms-c (l)
  (if (endp l)
      nil
    (append (all-terms-c2 (car l))
	    (all-terms-c (cdr l)))))

(defun all-terms-tcs (l)
  (if (endp l)
      nil
    (append (car (car l))
	    (all-terms-c (cadr (car l)))
	    (all-terms-tcs (cdr l)))))

(defun tcs-to-ifun2 (l fcall)
  (if (endp l)
      nil
    (let ((tests (car (car l)))
	  (calls (cadr (car l))))
      (cons `((and ,@tests) ,(cons-calls calls fcall))
	    (tcs-to-ifun2 (cdr l) fcall)))))

(mutual-recursion
 (defun expand-conses (x al)
  (if (atom x)
      (if (or (member-equal `(not (endp ,x)) al)
	      (member-equal `(consp ,x) al))
	  `(binary-append (cons (car ,x) 'nil) (cdr ,x))
	x)
    (if (quotep x)
	x
      (if (equal (car x) 'if)
	  `(if ,(cadr x)
	       ,(expand-conses (caddr x) (cons (cadr x) al))
	     ,(expand-conses (cadddr x) (cons (dumb-negate-lit (cadr x)) al)))
	(cons (car x) (expand-conses-l (cdr x) al))))))
 (defun expand-conses-l (x al)
   (if (endp x)
       nil
     (cons (expand-conses (car x) al)
	   (expand-conses-l (cdr x) al)))))

(defun cdrs-to-cadrs (x)
  (if (endp x)
      nil
    (cons (list (car (car x)) (cdr (car x)))
	  (cdrs-to-cadrs (cdr x)))))

(defun blrewrite (l x)
  (if (endp l)
      (mv t x)
    (let ((lhs (car (car l)))
	  (rhs (cadr (car l))))
      (mv-let (good bind) (one-way-unify lhs x)
	      (if (not good)
		  (blrewrite (cdr l) x)
		(mv nil (inst rhs (cdrs-to-cadrs bind))))))))

(mutual-recursion
 (defun lrewrite (x l)
   (if (atom x)
       (mv t x)
     (if (quotep x)
	 (mv t x)
       (mv-let (err r) (lrewrite-l (cdr x) l)
	       (mv-let (err r) (blrewrite l (cons (car x) r))
		      (if err
			  (mv t r)
			(lrewrite r l)))))))
 (defun lrewrite-l (x l)
   (if (endp x)
       (mv t nil)
     (mv-let (err r1) (lrewrite (car x) l)
	     (mv-let (err r2) (lrewrite-l (cdr x) l)
		     (mv t (cons r1 r2)))))))

(defun simp (x r)
  (mv-let (err r) (lrewrite x r) r))

(defun cond-simp (tbody bind)
  (let ((body2 (expand-conses tbody nil)))
    (simp (simp body2 bind) `(((cons (car x) (cdr x)) x)) )))


(defun tcs-to-ifun (tcs fn bind state)
  (let* ((fmls (all-vars (cons 'dummy (all-terms-tcs tcs))))
	 (body (tcs-to-ifun2 tcs (cons fn fmls)))
	 (body `(cond ,@body)))
    (mv-let (err val state) (ld+ (list `(defun ,fn (,@fmls) nil)))
	    (mv-let (nop tbody state) (TRANSLATE body nil NIL nil nil (W state) STATE)
		    (let ((sbody (cond-simp tbody bind)))
		      (mv-let (err val state) (ld+ (list (list 'ubt! (list 'quote fn))))
		      (mv
		       `(defun ,fn (,@fmls)
			  ,sbody)
		       `(,fn ,@fmls)
		       state)))))))



; rl must contain err and pv2 and must not contain pv
(defmacro try-ubt (rl call err nerr)
  `(let ((nl (new-label (access pv pv :max-label)))
	 (pv (change pv pv :max-label (1+ (access pv pv :max-label)))))
     (mv-let (err val state) (ld+ (list (list 'deflabel nl)))
	     (mv-let ,rl ,call
		     (if err
			 (let ((pv (change pv pv :max-label (1- (access pv pv :max-label)))))
			   (mv-let (er val state) (ld+ (list (list 'ubt! (list 'quote nl))))
				   ,err))
		       (let ((pv pv2))
			 ,nerr))))))


(defun prune-clause (p x  state)
  (declare (xargs   :mode :program))
  (if (endp x)
      (mv p  state)
    (mv-let (err nop  state) (refute5 (append p (cdr x)) 6  state)
	    (if err
		(prune-clause (append p (list (car x))) (cdr x)  state)
	      (prune-clause p (cdr x)  state)))))

(defun insert-sorted (a lst)
  (if (or (endp lst)
          (>= (acl2-count a) (acl2-count (car lst))))
      (cons a lst)
    (cons (car lst) (insert-sorted a (cdr lst)))))

(defun insertion-sort (lst)
  (if (endp lst)
      lst
    (insert-sorted (car lst) (insertion-sort (cdr lst)))))




(defun find-equal (x)
  (if (endp x)
      0
    (if (and (consp (car x))
	     (equal (car (car x)) 'equal))
	0
      (1+ (find-equal (cdr x))))))


(defun tcmp (x y)
  (if (atom x)
      (if (consp y)
	  1
	0)
    (if (atom y)
	-1
      (let ((r (tcmp (car x) (car y))))
	(if (equal r 0)
	    (tcmp (cdr x) (cdr y))
	  r)))))

(defun align-equal (x)
  (if (or
       (not (consp x))
       (not (equal (car x) 'equal)))
      x
    (if (< (acl2-count (cadr x)) (acl2-count (caddr x)))
	`(equal ,(caddr x) ,(cadr x))
      (if (= (acl2-count (cadr x)) (acl2-count (caddr x)))
	  (if (equal (tcmp (cadr x) (caddr x)) 1)
	      `(equal ,(caddr x) ,(cadr x))
	    x)
	x))))

(defun make-rewrite (x)
  (let ((disj (cdr x)))
    (if (equal (len disj) 1)
	(align-equal (car disj))
      (let ((eqd (find-equal disj)))
	(let ((eqd (if (equal eqd (len disj)) 0 eqd)))
	      `(implies
		(and
		 ,@(dumb-negate-lit-lst (remove-nth eqd disj)))
		,(align-equal (nth eqd disj))))))))

(defmacro inc-depth (bind call rest)
  `(if (< 2 (access pv pv :depth))
       (mv t nil pv state)
     (mv-let ,bind
	  (let ((pv (change pv pv :depth (1+ (access pv pv :depth)))))
	    ,call)
	  (let ((pv (change pv pv :depth (1- (access pv pv :depth)))))
	    ,rest))))

(mutual-recursion
 (defun match2-0 (d hyps pv  state)
   (declare (xargs   :mode :program))
   (if (endp d)
       (mv nil nil pv  state)
     (let* ((d1 (car d))
	    (x (car d1))
	    (y (cadr d1)))
       (if (and (atom x)
		(atom y))
	   (if (not (equal x y))
	       (mv t nil pv  state)
	     (match2-0 (cdr d) hyps pv  state))
	 (if (not (constrainedp `(equal ,x ,y) state))
	     (mv-let (err r pv  state) (prove2 `(equal ,x ,y) pv  state)
		     (if err
			 (mv t nil pv  state)
		       (match2-0 (cdr d) hyps pv  state)))
	   (if (and
		(consp x)
		(conp x state))
	       (mv-let (err r pv2 state) (match2-0 (use-subst-l x y (cdr d)) hyps (change pv pv :bind (append (access pv pv :bind) (list (list x y))))  state)
		       (if err
			   (mv t nil pv state)
			 (mv nil nil pv2 state)))
	     (if (and
		  (consp y)
		  (conp y state))
		 (mv-let (err r pv2 state) (match2-0 (use-subst-l y x (cdr d)) hyps (change pv pv :bind (append (access pv pv :bind) (list (list y x))))  state)
			 (if err
			     (mv t nil pv state)
			   (mv nil nil pv2 state)))

	       (mv-let (err r) (try-decomp x y) ; if x and y have the same top function symbol, then decompose them
		       (if (not err)
			   (mv-let (err r pv state) (match2-0 (append r (cdr d)) hyps pv  state)
				   (if err
				       (mv-let (err r pv state) (gen-constr `((equal ,@(car d))) hyps pv state)
					       (if err
						   (mv t nil pv state)
						 (mv-let (err r pv  state)
							 (match2-0 (cons (list (cadr r) (caddr r)) (cdr d)) hyps pv  state)
							 (if err
							     (mv t r pv state)
							   (match2-0 (list (use-substl-l (access pv pv :bind) (car d))) hyps pv state)))))
				     (mv nil r pv state)))
			 (mv-let (err r pv state) (gen-constr `((equal ,@(car d))) hyps pv state)
				 (if err
				     (mv t nil pv state)
				   (mv-let (err r pv  state)
					   (match2-0 (cons (list (cadr r) (caddr r)) (cdr d)) hyps pv  state)
					   (if err
					       (mv t r pv state)
					     (match2-0 (list (use-substl-l (access pv pv :bind) (car d))) hyps pv state))))))))))))))

; take an equality and attempt to match it against another disjunct.
; if a match is found, use any bindings present to substitute rhs for lhs
; and return the new y.
; we check that the top symbol of rhs and lhs are the same before attempting a match.
 (defun match2-0-fert (x y hyps pv state)
   (if (atom y)
       (mv t nil pv state)
     (mv-let (err r pv state) (match2-0-fert-l x (cdr y) hyps pv state)
	     (if err
		 (if (and (consp (cadr x)) ; if the top symbols are equal, attempt a match
			  (equal (car (cadr x))
				 (car y)))
		     (mv-let (err r pv state) (match2-0 (list (list (cadr x) y)) hyps pv state)
			     (if err
				 (mv t nil pv state)
					;replace lhs with rhs in y and attempt to prove new clause
			       (mv nil (caddr x) pv state)))
		   (mv t nil pv state))
	       (mv nil (cons (car y) r) pv state)))))

 (defun match2-0-fert-l (x y hyps pv state)
   (if (endp y)
       (mv t nil pv state)
     (mv-let (err r pv state) (match2-0-fert x (car y) hyps pv state)
	     (if err
		 (mv-let (err r pv state)  (match2-0-fert-l x (cdr y) hyps pv state)
			 (if err
			     (mv t nil pv state)
			   (mv nil (cons (car y) r) pv state)))
	       (mv nil (cons r (cdr y)) pv state)))))



 (defun match2 (x y hyps pv  state)
   (declare (xargs   :mode :program))
   (if (or (atom x) (atom y))
       (mv t nil pv  state)
     (if (equal (car x) 'not)
	 (if (and (consp (cdr x))
		  (equal (car (cadr x)) 'equal))
	     (mv-let (err r pv state) (match2-0-fert (cadr x) y hyps pv state) ;we should probably match the eq oriented the other way too
		     (if err
			 (mv t nil pv state)
		       (prove2 (use-substl-l (access pv pv :bind) `(or ,@hyps ,x ,r)) pv state)))
	   (match2-0 (list (list (cadr x) y)) hyps pv  state))
       (if (equal (car y) 'not)
	   (match2-0 (list (list x (cadr y))) hyps pv  state)
	 (mv t nil pv  state)))))

; i and j are the indices of two disjuncts in clause x
; that we are trying to match against each other
 (defun match-l (i j x pv  state)
   (declare (xargs   :mode :program))
   (if (<= (len x) j)
       (mv t nil pv  state)
     (if (or (constrainedp (nth i x) state)
	     (constrainedp (nth j x) state))
	 (try-ubt
	  (err r pv2  state)
	  (match2 (nth i x) (nth j x) (remove-nth i (remove-nth j x)) pv  state)
	  (match-l i (1+ j) x pv  state)
	  (mv nil r pv2  state))
       (match-l i (1+ j) x pv  state))))

; try to prove a clause that has constraints in it by finding
; definitions that allow two disjuncts to match modulo negation.
; cross fertilization is performed if possible.
 (defun try-match (i x pv  state)
   (declare (xargs   :mode :program))
   (if (<= (len x) i)
       (mv t nil pv  state)
     (try-ubt
      (err r pv2  state)
      (match-l i (1+ i) x pv  state)
      (try-match (1+ i) x pv  state)
      (mv nil r pv2  state))))

(defun induct1 (schemes x pv  state)
   (declare (xargs   :mode :program))
   (if (endp schemes)
       (mv t nil pv  state)
     (try-ubt (err pv2 r tcs state)
	      (mv-let (err r tcs pv state) (get-induct-goals x (car schemes) pv state)
		      (mv-let (err r pv state) (prove2 `(and ,@r) pv  state)
			      (mv err pv r tcs state)))
	      (induct1 (cdr schemes) x pv state)
	      (let* ((nthm (new-thm (access pv pv :max-thm)))
		     (pv (change pv pv :max-thm (1+ (access pv pv :max-thm))))
		     (ifn (new-ifn (access pv pv :max-ifn)))
		     (pv (change pv pv :max-ifn (1+ (access pv pv :max-ifn)))))
		(mv-let (ifun ifun-call state) (tcs-to-ifun tcs ifn (access pv pv :bind) state)
			(let ((xrr (make-rewrite x)))
			  (let ((ithm `(defthm
					 ,nthm
					 ,xrr
					 :hints
					 (("Goal" :induct ,ifun-call :do-not-induct t :do-not '(generalize)))
					 )))
			    (mv-let (err val state) (ld+ (list ifun))
				    (if err
					(mv (err-fun) r pv  state)
				      (mv-let (err val state) (ld+ (list ithm))
					      (if err
						  (mv (err-fun) r pv  state)
						(mv nil
						    r
						    (change pv pv :log (append (access pv pv :log)
									       `(,ifun
										 ,ithm)))
						    state))))))))))))

 (defun ind (x pv  state)
   (declare (xargs   :mode :program))
   (induct1 (get-schemes x state) x pv  state))

; x is a clause to prove
(defun prove2-0 (x pv state)
  (declare (xargs :mode :program))
  (if (constrainedp-l x state)
      (try-match 0 x pv  state)
    (mv-let
     (err r state)
     (bash-term-to-dnf `(or ,@x) nil nil state) (declare (ignore err)) ;removes tautolgies introduced by constrained defs
     (if (null r)
         (mv nil t pv  state)
       (mv-let
        (err nop  state)
        (refute5 x 6  state)
        (if err
            (mv err nil pv  state)
;(inc-depth (err r pv state)
;    (ind `(or ,@x) pv state)
;   (if err
          (mv-let
           (x  state)
           (prune-clause nil (insertion-sort x)  state) ;how reliable is prune? used to throw away ih after xfert

           (mv-let
            (hit lcl tt pspv)
            (generalize-clause2
             x
             nil
             (change prove-spec-var
                     (initial-pspv *t* ; term (don't-care)
                                   *t* ; displayed-goal (don't-care)
                                   nil ; otf-flg (don't-care)
                                   (ens state)
                                   (w state)
                                   state
                                   nil
; Matt K. addition: new orig-hints argument of nil matches old behavior.
                                   nil)
                     :pool '((being-proved-by-induction . nil)))
             (w state)
             state)
            (if (equal hit 'hit)
                (inc-depth (err r pv state)
                           (ind `(or ,@(car lcl))
                                pv
                                state)
                           (if err
                               (mv err r pv  state)
                             (mv nil r pv  state)))
              (inc-depth (err r pv state)
                         (ind `(or ,@x) pv state)
                         (if err
                             (mv err r pv  state)
                           (mv nil r pv  state))))

            ))))))))

;					      (mv err r pv  state))))))

; eventually we should change this to try each clause independently and
; generate a list of all possible binding for the constrained functions,
; then try each possibility instead of doing this exponential backtracking
(defun prove2-l (x n pv  state)
   (declare (xargs   :mode :program))
   (if (<= (len x) n)
       (if (< 0 (len x))
	   (mv t nil pv  state)
	 (mv nil nil pv  state))
     (try-ubt (err r pv2 state)
	      (mv-let (err r pv state) (prove2-0 (nth n x) pv  state)
		      (if err
			  (mv t nil pv state)
			(prove2-l (use-substl-l (access pv pv :bind) (remove-nth n x)) 0 pv  state)))
	      (prove2-l x (1+ n) pv state)
	      (mv nil nil pv state))))

 (defun prove2 (x pv  state)
   (declare (xargs   :mode :program))
   (mv-let (err r state)
	   (bash-term-to-dnf x nil nil state) (declare (ignore err))
	   (prove2-l (insertion-sort r) 0 pv  state))))


(defmacro bprove (x)
  `(encapsulate nil
		(set-ignore-ok t)
		(set-irrelevant-formals-ok t)
		(make-event
		 (mv-let (err max-fun state) (table bprove 'max-fun)
		 (mv-let (err max-var state) (table bprove 'max-var)
		 (mv-let (err max-ifn state) (table bprove 'max-ifn)
		 (mv-let (err max-thm state) (table bprove 'max-thm)
		 (mv-let (err max-label state) (table bprove 'max-label)
		 (mv-let (err r pv state)
			 (prove2 ',x (make pv :bind nil :schemes nil :log nil :max-fun (or max-fun 0) :max-var (or max-var 0) :max-ifn (or max-ifn 0) :max-thm (or max-thm 0) :max-label (or max-label 0) :depth 0)  state)
			 (mv nil (cons 'progn (append
					       (list
			    `(table bprove 'max-fun ,(access pv pv :max-fun))
			    `(table bprove 'max-var ,(access pv pv :max-var))
			    `(table bprove 'max-ifn ,(access pv pv :max-ifn))
			    `(table bprove 'max-thm ,(access pv pv :max-thm))
			    `(table bprove 'max-label ,(access pv pv :max-label)))
			    (access pv pv :log))) state))))))))))



;(prove2 '(equal (rv1 x 'nil) (rv x)) (make pv :bind nil :schemes nil :log nil :max-fun 0 :max-var 0 :max-ifn 0 :max-thm 0 :max-label 0 :depth 0)  state)

;(GENERALize-clause '((equal (f (rv x)) (g (rv x))))  nil (change prove-spec-var nil :pool '((being-proved-by-induction . nil))) (w state) state)

;(GENERALize-clause '((equal (f (rv (cons x1 'nil))) (g (rv (cons x1 'nil)))))  nil (change prove-spec-var nil :pool '((being-proved-by-induction . nil))) (w state) state)

;(GENERALize-clause2 '((equal (f (cons x1 'nil)) (g (cons x1 'nil))))  nil (change prove-spec-var nil :pool '((being-proved-by-induction . nil))) (w state) state)

;(GENERALize-clause2 '((EQUAL (ROT2 X2 (BINARY-APPEND X2 (CONS X1 'NIL))) (BINARY-APPEND (CONS X1 'NIL) X2)))  nil (change prove-spec-var nil :pool '((being-proved-by-induction . nil))) (w state) state)

;(fertilize-clause 0 '((not (equal (f (rv x)) (g (rv x)))) (p (f (rv x))))  nil (change prove-spec-var nil :pool '((being-proved-by-induction . nil))) (w state) state)


;(trace$ match2 match2-0 try-match match-l)
;(trace$ bash-term-to-dnf)

;(trace$ prove2-l prove2-0 ind induct1 get-induct-goals)

;(trace$ gen-constr try-decomp  rm-hyps get-induct-goals)

;(set-ld-redefinition-action '(:query . :overwrite) state)

;(set-ld-redefinition-action nil state)

;(proclaim '(optimize (speed 2) (safety 1) (space 1) (debug 3)))

(comp t)

(logic)




;(prove2 '(implies (and (true-listp x) (true-listp y)) (equal (rot2 x (append x y)) (append y x))) (make pv :bind nil :schemes nil :log nil :max-fun 0 :max-var 0 :max-ifn 0 :max-thm 0 :max-label 0 :depth 0)  state)

;(prove2 '(implies (and (true-listp x)) (equal (rot2 x x) x)) (make pv :bind nil :schemes nil :log nil :max-fun 0 :max-var 0 :max-ifn 0 :max-thm 0 :max-label 0 :depth 0)  state)


;(prove2 '(equal (ilen x '0) (len x)) (make pv :bind nil :schemes nil :log nil :max-fun 0 :max-var 0 :max-ifn 0 :max-thm 0 :max-label 0 :depth 0)  state)

;fails?
;(prove2 '(equal (rv1 x 'nil) (rv x)) (make pv :bind nil :schemes nil :log nil :max-fun 0 :max-var 0 :max-ifn 0 :max-thm 0 :max-label 0 :depth 0)  state)



