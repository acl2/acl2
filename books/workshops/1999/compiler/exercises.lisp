;;===========================================================================
;; Copyright (C) 1999 Institut fuer Informatik, University of Kiel, Germany
;;===========================================================================
;; File:         exercises.lisp
;; Author:       Wolfgang Goerigk
;; Content:      ACL2 book for "Compiler Verification Revisited"
;; as of:        08/23/99, University of Kiel, Germany
;;---------------------------------------------------------------------------
;; $Revision: 1.2 $
;; $Id: exercises.lisp,v 1.2 1999/09/09 13:44:36 wg Exp wg $
;;===========================================================================
;; This book is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;---------------------------------------------------------------------------
;; This book is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;---------------------------------------------------------------------------
;; You should have received a copy of the GNU General Public License along
;; with this book; if not, write to the Free Software Foundation, Inc., 675
;; Mass Ave, Cambridge, MA 02139, USA.
;;===========================================================================
;;
;; This book is part of a series of books that come with and are described in
;; the article "Wolfgang Goerigk: Compiler Verification Revisited" as part of
;; "Computer Aided Reasoning: ACL2 Case Studies" edited by Matt Kaufmann, Pete
;; Manolios and J Strother Moore.
;;
;;===========================================================================
;;
;; Examples and Solutions to the Exercises
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;; This book contains some examples and the solutions to the exercises. In
;; order to perform the following exercises, that is to execute the events we
;; provide, you should include the books "machine" and "compiler".
;;
;;===========================================================================

(in-package "ACL2")

(include-book "compiler")

;;===========================================================================
;;
;; Solution to Exercise 1.1:
;; ~~~~~~~~~~~~~~~~~~~~~~~~~
;;
;; Well, we should not define the function subst in ACL2, because actually it
;; is a standard function. Well, probably this exercise is too trivial.
;;
;;  (defun subst (new old tree)
;;    (if (equal old tree) new
;;      (if (atom tree) tree
;;        (cons (subst new old (car tree))
;;  	    (subst new old (cdr tree))))))
;;
;;===========================================================================

;;===========================================================================
;;
;; Solution to Exercise 1.2:
;; ~~~~~~~~~~~~~~~~~~~~~~~~~
;;
;;
;;  The function compiler-target from "compiler.lisp" returns the compiled
;;  compiler. Thus, we can execute the result on the machine and apply it to the
;;  compiler source, that is
;;
;;  (execute
;;   (compiler-target)
;;   (list '(compile-program defs vars main)
;;         '(defs vars main)
;;         (compiler-source))
;;   1000000)
;;
;;  The result is the same as that of (compiler-target). We find, that such a
;;  theorem has been proved within "compiler.lisp" already.
;;

(defthm exercise-1-2
  (equal (compiler-target)
	 (car
	  (execute
	   (compiler-target)
	   (list '(compile-program defs vars main)
		 '(defs vars main)
		 (compiler-source))
	   1000000)))
  :rule-classes nil)


;;===========================================================================
;;
;; Self-reproduction by Substitution
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;

(defun selfrep ()
  (let ((b '(defun selfrep ()
              (let ((b '2000)) (subst b (+ 1999 1) b)))))
    (subst b (+ 1999 1) b)))


(defthm selfrep-reproduces-itself
  (equal (selfrep)
	 '(defun selfrep ()
	    (let ((b '(defun selfrep ()
			(let ((b '2000)) (subst b (+ 1999 1) b)))))
	      (subst b (+ 1999 1) b))))
  :rule-classes nil)


(defun selfrep-1 ()
  (subst
   '(defun selfrep-1 () (subst '2000 (+ 1999 1) '2000))
   (+ 1999 1)
   '(defun selfrep-1 () (subst '2000 (+ 1999 1) '2000))))


(defthm selfrep-1-reproduces-itself
  (equal (selfrep-1)
	 '(defun selfrep-1 ()
	    (subst
	     '(defun selfrep-1 () (subst '2000 (+ 1999 1) '2000))
	     (+ 1999 1)
	     '(defun selfrep-1 () (subst '2000 (+ 1999 1) '2000)))))
  :rule-classes nil)



;;===========================================================================
;;
;; Conditionally self-reproducing Code
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;
;; Let us replay the construction of the conditionally self-reproducing
;; "ident" function that we show in the article. The main goal here is to
;; learn how the construction of such functions works.
;;
;; First, we define our function but do not care about the self-reproducing
;; case:
;;
;;  (defun ident (x)
;;    (cond ((equal x 'ident) ...)
;;          ((equal x 'login) 'Oops)
;;          (t x)))
;;
;; Then, we add the pattern (let ((b '2000)) ... (subst b (+ 1999 1) b) ...)
;; (here as a surrounding block) in order to reproduce the functions code
;; using (subst b (+ 1999 1) b) within that block (after the final
;; copy-and-paste step):
;;
;;  (defun ident (x)
;;    (let ((b '2000))
;;      (cond ((equal x 'ident)
;;             (subst b (+ 1999 1) b))
;;            ((equal x 'login) 'Oops)
;; 	      (t x))))
;;
;; Finally, we replace the 2000 by the function definition we constructed so
;; far. That gives the final result:
;;

(defun ident (x)
  (let ((b '(defun ident (x)
	      (let ((b '2000))
		(cond ((equal x 'ident)
		       (subst b (+ 1999 1) b))
		      ((equal x 'login) 'Oops)
		      (t x))))))
    (cond ((equal x 'ident) (subst b (+ 1999 1) b))
          ((equal x 'login) 'Oops)
          (t x))))

;;
;; The following three theorems are to prove that this function actually
;; behaves as intended, i.e. that it returns 'Oops for the argument 'login,
;; its own code for the argument 'ident, and the argument itself in any other
;; (normal) case. Note that all the proofs are trivial and simply by
;; execution.
;;

(defthm ident-catastrophy
  (equal (ident 'login) 'Oops)
  :rule-classes nil)

(defthm ident-reproduction
  (equal (ident 'ident)
	 '(defun ident (x)
	    (let ((b '(defun ident (x)
			(let ((b '2000))
			  (cond ((equal x 'ident)
				 (subst b (+ 1999 1) b))
				((equal x 'login) 'Oops)
				(t x))))))
	      (cond ((equal x 'ident) (subst b (+ 1999 1) b))
		    ((equal x 'login) 'Oops)
		    (t x)))))
  :rule-classes nil)

(defthm ident-normal
  (implies (not (or (equal x 'ident) (equal x 'login)))
	   (equal (ident x) x))
  :rule-classes nil)

;;
;;---------------------------------------------------------------------------


;;===========================================================================
;;
;; Reflective Programs
;; ~~~~~~~~~~~~~~~~~~~
;;
;; In order to show that we can not only write self-reproducing functions we
;; will now demonstrate how to write a simple reflective program with two
;; functions. We call those programs reflective because they compute with
;; their own source code. Self-reproduction is a special case.
;;
;; As a simple and of course useless example we add another function "com" to
;; "selfrep" which returns the reverse of its argument list. Then we return
;; the result of applying "com" to the entire program instead of just the
;; definition of "selfrep". The point here is not the program itself but the
;; way we are constructing it.
;;
;; We start again defining the two functions as usual:
;;
;;  (defun com (l) (reverse l))
;;
;;  (defun srep () (com ... ))
;;
;; Now we replace "(com ... )" by
;;     "(let ((b '2000)) (com (subst b (+ 1999 1) b))) :
;;
;;  (defun com (l) (reverse l))
;;
;;  (defun srep ()
;;    (let ((b '2000))
;;      (com (subst b (+ 1999 1) b))))
;;
;; and finally we replace the place holder 2000 by a list containing exactly
;; these two functions. Thus we get
;;

(defun com (defs) (reverse defs))

(defun srep ()
  (let ((b '((defun com (defs) (reverse defs))
	     (defun srep ()
	       (let ((b '2000))
		 (com (subst b (+ 1999 1) b)))))))
    (com (subst b (+ 1999 1) b))))

(defthm selfrep-reflective-program
  (equal (srep)
	 '((defun srep nil
	     (let ((b '((defun com (defs) (reverse defs))
			(defun srep nil
			  (let ((b '2000))
			    (com (subst b (+ 1999 1) b)))))))
	       (com (subst b (+ 1999 1) b))))
	   (defun com (defs) (reverse defs))))
  :rule-classes nil)

;;
;; Calling srep returns the reverse of the list of these two function
;; definitions.
;;
;;---------------------------------------------------------------------------



;;===========================================================================
;;
;; Solution to Exercise 1.3:
;; ~~~~~~~~~~~~~~~~~~~~~~~~~
;;
;; In order to construct a let- and cond-free version of ident, we start again
;; by defining the desired function leaving the self-reproducing case open:
;;
;;  (defun ident1 (x)
;;    (if (equal x 'ident) ...
;;      (if (equal x 'login) 'Oops
;;        x)))
;;
;;
;; Then, we add the form (subst '2000 (+ 1999 1) '2000) which is to reproduce
;; the function's code (after the final copy-and-paste step):
;;
;;  (defun ident1 (x)
;;    (if (equal x 'ident)
;;        (subst
;;         '2000
;;         (+ 1999 1)
;;         '2000)
;;      (if (equal x 'login) 'Oops
;;        x)))
;;
;; Finally, we replace the two occurences of 2000 by the function definition
;; we constructed so far. That gives the final result:
;;

(defun ident1 (x)
  (if (equal x 'ident)
      (subst
       '(defun ident1 (x)
	  (if (equal x 'ident)
	      (subst
	       '2000
	       (+ 1999 1)
	       '2000)
	    (if (equal x 'login) 'Oops
	      x)))
       (+ 1999 1)
       '(defun ident1 (x)
	  (if (equal x 'ident)
	      (subst
	       '2000
	       (+ 1999 1)
	       '2000)
	    (if (equal x 'login) 'Oops
	      x))))
    (if (equal x 'login) 'Oops
      x)))




;;---------------------------------------------------------------------------
;;
;; We prove that the new function ident1 workes as expected, i.e. that it
;; returns 'Oops for the argument 'login, its own code for the argument
;; 'ident, and the argument itself in any other (normal) case:
;;

(defthm ident1-catastrophy
  (equal (ident1 'login) 'Oops)
  :rule-classes nil)

(defthm ident1-reproduction
  (equal (ident1 'ident)
	 '(defun ident1 (x)
  (if (equal x 'ident)
      (subst
       '(defun ident1 (x)
	  (if (equal x 'ident)
	      (subst
	       '2000
	       (+ 1999 1)
	       '2000)
	    (if (equal x 'login) 'Oops
	      x)))
       (+ 1999 1)
       '(defun ident1 (x)
	  (if (equal x 'ident)
	      (subst
	       '2000
	       (+ 1999 1)
	       '2000)
	    (if (equal x 'login) 'Oops
	      x))))
    (if (equal x 'login) 'Oops
      x))))
  :rule-classes nil)

(defthm ident-1-normal
  (implies (not (or (equal x 'ident) (equal x 'login)))
	   (equal (ident1 x) x))
  :rule-classes nil)

;;
;;===========================================================================


;;---------------------------------------------------------------------------
;;
;; Solution to Exercise 1.4:
;; ~~~~~~~~~~~~~~~~~~~~~~~~~
;;
;; The following function returns its target code if applied to 'ident. We
;; have to construct a let- and cond-free function, because the compiler does
;; not know let or cond, therefore, just changing ident will not work. So we
;; start with
;;
;;  (defun ident2 (x)
;;    (if (equal x 'ident)
;;        (car (compile-def ... ))
;;      (if (equal x 'login) 'Oops
;;        x)))
;;
;; and get the following function in the second step:
;;
;;  (defun ident2 (x)
;;    (if (equal x 'ident)
;;        (car (compile-def
;;               (subst '2000
;;  	                (+ 1999 1)
;;  	                '2000)))
;;      (if (equal x 'login) 'Oops
;;        x)))
;;
;; Note, that compile-def returns a one-element list of the target code
;; subroutine. Therefore, we take the car of it. After the final step we get
;;

(defun ident2 (x)
  (if (equal x 'ident)
      (car (compile-def
	    (subst '(defun ident2 (x)
		      (if (equal x 'ident)
			  (car (compile-def
				(subst '2000
				       (+ 1999 1)
				       '2000)))
			(if (equal x 'login) 'Oops
			  x)))
		   (+ 1999 1)
		   '(defun ident2 (x)
		      (if (equal x 'ident)
			  (car (compile-def
				(subst '2000
				       (+ 1999 1)
				       '2000)))
			(if (equal x 'login) 'Oops
			  x))))))
    (if (equal x 'login) 'Oops
      x)))


;; Now let's see. First we observe that ident2 returns its own compiled code,
;; that is its result is equal to the car of compiling its own function
;; definition:

(defthm ident2-compiles-itself
  (equal (ident2 'ident)
	 (car (compile-def
	       '(defun ident2 (x)
		  (if (equal x 'ident)
		      (car (compile-def
			    (subst '(defun ident2 (x)
				      (if (equal x 'ident)
					  (car (compile-def
						(subst '2000
						       (+ 1999 1)
						       '2000)))
					(if (equal x 'login) 'Oops
					  x)))
				   (+ 1999 1)
				   '(defun ident2 (x)
				      (if (equal x 'ident)
					  (car (compile-def
						(subst '2000
						       (+ 1999 1)
						       '2000)))
					(if (equal x 'login) 'Oops
					  x))))))
		    (if (equal x 'login) 'Oops
		      x))))))
  :rule-classes nil)

;; Again, ident2 returns 'Oops for 'login:

(defthm ident2-catstrophe
  (equal (ident2 'login) 'Oops)
  :rule-classes nil)

;; And finally it is like the identity function for any other argument:



(defthm ident2-normal
  (implies (and (not (equal x 'ident))
		(not (equal x 'login)) )
	   (equal (ident2 x) x))
  :rule-classes nil)


;; eof




