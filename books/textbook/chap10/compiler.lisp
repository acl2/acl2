; Section 10.6 Compiler for Stack Machine

; See also compiler.acl2 for certification instructions and the
; definition of the package "compile".

(in-package "COMPILE")

(defun exprp (exp)
  (cond
   ((atom exp) (or (symbolp exp) (acl2-numberp exp)))
   ((equal (len exp) 2)
    (and (or (equal (car exp) 'inc)
	     (equal (car exp) 'sq))
	 (exprp (cadr exp))))
   (t (and (equal (len exp) 3)
	   (or (equal (cadr exp) '+)
	       (equal (cadr exp) '*))
	   (exprp (car exp))
	   (exprp (caddr exp))))))

(defun lookup (var alist)
  (cond ((endp alist) 0)
        ((equal var (car (car alist)))
         (cdr (car alist)))
        (t (lookup var (cdr alist)))))

(defun eval (exp alist)
  (cond
   ((atom exp)
    (cond ((symbolp exp) (lookup exp alist))
	  (t exp)))
   ((equal (len exp) 2)
    (cond ((equal (car exp) 'inc)
	   (+ 1 (eval (cadr exp) alist)))
	  (t (* (eval (cadr exp) alist)
		(eval (cadr exp) alist)))))
   (t (cond ((equal (cadr exp) '+)
	     (+ (eval (car exp) alist)
		(eval (caddr exp) alist)))
	    (t (* (eval (car exp) alist)
		  (eval (caddr exp) alist)))))))

(defun pop (stk) (cdr stk))
(defun top (stk) (if (consp stk) (car stk) 0))
(defun push (val stk) (cons val stk))

(defun step (ins alist stk)
  (let ((op (car ins)))
    (case op
      (pushv (push (lookup (cadr ins) alist) stk))
      (pushc (push (cadr ins) stk))
      (dup   (push (top stk) stk))
      (add   (push (+ (top (pop stk)) (top stk))
		   (pop (pop stk))))
      (mul   (push (* (top (pop stk)) (top stk))
		   (pop (pop stk))))
      (t stk))))

(defun run (program alist stk)
  (cond ((endp program) stk)
        ((run (cdr program)
	      alist
	      (step (car program) alist stk)))))

(defun compile (exp)
  (cond
   ((atom exp)
    (cond ((symbolp exp)
           (list (list 'pushv exp)))
          (t (list (list 'pushc exp)))))
   ((equal (len exp) 2)
    (cond ((equal (car exp) 'inc)
	   (append (compile (cadr exp)) '((pushc 1) (add))))
	  (t (append (compile (cadr exp)) '((dup)(mul))))))
   (t (cond ((equal (cadr exp) '+)
	     (append (compile (car exp))
		     (compile (caddr exp))
		     '((add))))
	    (t (append (compile (car exp))
		       (compile (caddr exp))
		       '((mul))))))))


(defthm composition
  (equal (run (append prg1 prg2) alist stk)
	 (run prg2 alist (run prg1 alist stk))))

(defun compiler-induct (exp alist stk)
  (cond
   ((atom exp) stk)
   ((equal (len exp) 2)
    (compiler-induct (cadr exp) alist stk))
   (t
    (append (compiler-induct (car exp) alist stk)
            (compiler-induct (caddr exp)
			     alist
			     (cons (eval (car exp) alist) stk))))))

(defthm compile-is-correct-general
  (implies (exprp exp)
           (equal (run (compile exp) alist stk)
                  (cons (eval exp alist) stk)))
  :hints (("Goal"
	   :induct (compiler-induct exp alist stk))))

(defthm compile-is-correct
  (implies (exprp exp)
           (equal (top (run (compile exp) alist stk))
                  (eval exp alist)))
  :hints (("Goal"
	   :induct (compiler-induct exp alist stk))))
