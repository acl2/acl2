;  Copyright (C) 2000 Panagiotis Manolios

;  This program is free software; you can redistribute it and/or modify
;  it under the terms of the GNU General Public License as published by
;  the Free Software Foundation; either version 2 of the License, or
;  (at your option) any later version.

;  This program is distributed in the hope that it will be useful,
;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;  GNU General Public License for more details.

;  You should have received a copy of the GNU General Public License
;  along with this program; if not, write to the Free Software
;  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;  Written by Panagiotis Manolios who can be reached as follows.

;  Email: pete@cs.utexas.edu

;  Postal Mail:
;  Department of Computer Science
;  The University of Texas at Austin
;  Austin, TX 78701 USA

(in-package "ACL2")

#|

This is the weak defun-sk macro and it is based on the defun-sk macro.
I only thought about existential quantification.  Do a macro-expansion
to see what it produces, but essentially it produces a function with
only one constraint: this allows you to prove the function is non-nil
if you can exhibit a witness.  Many times that is all one needs.

|#

(defmacro defun-weak-sk (name args body &key quant-ok skolem-name thm-name)
  (let* ((exists-p (and (true-listp body)
                        (symbolp (car body))
                        (equal (symbol-name (car body)) "EXISTS")))
         (bound-vars (let ((var-lst (cadr body)))
		       (and (true-listp body)
			    (or (symbolp var-lst)
				(true-listp var-lst))
			    (cond ((atom var-lst)
				   (list var-lst))
				  (t var-lst)))))
         (body-guts (and (true-listp body) (caddr body)))
         (skolem-name
          (or skolem-name
              (intern-in-package-of-symbol
               (concatenate 'string (symbol-name name) "-WITNESS")
               name)))
	 (skolem-constraint-name
	  (intern-in-package-of-symbol
	   (concatenate 'string (symbol-name skolem-name) "-CONSTRAINT")
	   skolem-name))
         (thm-name
          (or thm-name
              (intern-in-package-of-symbol
               (concatenate 'string (symbol-name name)
                            (if exists-p "-SUFF" "-NECC"))
               name)))
         (msg (non-acceptable-defun-sk-p name args body quant-ok nil exists-p
                                         nil ; dcls (Matt K. mod)
                                         )))
    (if msg
        `(er soft '(defun-sk . ,name)
             "~@0"
             ',msg)
      `(encapsulate
	((,name ,args ,(if (= (length bound-vars) 1)
			   (car bound-vars)
			 (cons 'mv bound-vars))))
	(local
	 (encapsulate
	  ((,skolem-name ,args
			 ,(if (= (length bound-vars) 1)
			      (car bound-vars)
			    (cons 'mv bound-vars))))
	  (local (in-theory '(implies)))
	  (local
	   (defchoose ,skolem-name ,bound-vars ,args
	     ,(if exists-p
		  body-guts
		`(not ,body-guts))))

       	; A :type-prescription lemma is needed in the case of more than one bound
   	; variable, in case we want to do guard proofs.

	  ,@(cond
	     ((null (cdr bound-vars)) nil)
	     (t
	      `((local (defthm ,(intern-in-package-of-symbol
				 (concatenate 'string (symbol-name skolem-name) "-TYPE-PRESCRIPTION")
				 skolem-name)
			 (true-listp ,(cons skolem-name args))
			 :rule-classes :type-prescription
			 :hints (("Goal" :by ,skolem-name)))))))
	  (defthm ,skolem-constraint-name
	    (implies ,body-guts
		     ,(if (= (length bound-vars) 1)
			  `(let ((,(car bound-vars) (,skolem-name ,@args)))
			     ,body-guts)
			`(mv-let (,@bound-vars)
				 (,skolem-name ,@args)
				 ,body-guts)))
	    :hints (("Goal"
		     :use ,skolem-name))
	    :rule-classes nil)))
	(local
	 (defun ,name ,args (declare (xargs :normalize nil))
	   ,(if (= (length bound-vars) 1)
		`(let ((,(car bound-vars) (,skolem-name ,@args)))
		   ,body-guts)
	      `(mv-let (,@bound-vars)
		       (,skolem-name ,@args)
		       ,body-guts))))
	(defthm ,thm-name
	  ,(if exists-p
	       `(implies ,body-guts
			 (,name ,@args))
	     `(implies (not ,body-guts)
		       (not (,name ,@args))))
	  :hints (("Goal"
		   :in-theory nil
		   :use ((:instance ,skolem-constraint-name)
			 (:instance ,name)))))

	; The above was added to make sure that nothing
	; interferes with the proof (e.g., function definitions and
	; rewrites).

	))))

