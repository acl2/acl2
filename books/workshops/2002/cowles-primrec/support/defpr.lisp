; Automatic introduction of an arbitrary primitive-recursive function.
; Copyright (C) 2002  John R. Cowles, University of Wyoming

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:
; John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071 U.S.A.

; email: cowles@uwyo.edu

; Winter 2002
; Last modified 15 March 2002.
#|
 To certify in ACL2 Version 2.6:

 (certify-book "defpr"
               0
               t ; compile-flg
	       :defaxioms-okp nil
	       :skip-proofs-okp nil)
|#
#|
In the spirit of Pete & J's work reported in defpun.lisp, their
construction of a function f that satisfies the equation in the
following theorem,

(defthm generic-tail-recursive-f
  (equal (f x)
	 (if (test x) (base x) (f (st x))))),

is extended to a construction of a function f that satisfies
the equation, for certain h's, in the theorem:

(defthm generic-primitive-recursive-f
    (equal (f x)
	   (if (test x) (base x) (h x (f (st x)))))).

Four examples are included below:
  Example 1. Tail recursion as a special case.
  Example 2. Pete & J's cons example (modified).
  Example 3. Naive Factorial
  Example 4. Example with parameters.

 These examples each construct a function using a minor variation
 of the construction outlined in defpun.lisp for tail-recursive
 functions.

As shown by Pete & J, for some h's, such an f does not exist.
Their example, showing such an f need not exist, has
  (test x) = (equal x 0),
  (base x) = nil,
  (h x y$)  = (cons nil y$), and
  (st x)   = (- x 1).

A sufficient (but not necessary) condition on h for the
existence of f is that h have a right fixed point, i.e., there is
some c such that (h x c) = c.

An example, also due to Pete & J, showing that h having a right
fixed point is not necessary for the existence of f has
  (test x) = (equal x 0)
  (base x) = 0
  (h x y$)  = (+ 1 y$), and
  (st x)   = (- x 1).
The ACL2 function fix satisfies the recursive equation in
generic-primitive-recursive-f, for these choices for test, base,
h, and st.  Here (fix x) returns x if x is an ACL2 number and
returns 0 otherwise.

Note:
A function f satisfying the equation
    (equal (f x)
	   (if (test x) (base x) (h x (f (st x)))))).
is called primitive recursive because a recursive equation of
this form is a generalization of the definitions by primitive
recursion studied in computability theory:
    F(x_1,...,x_n, 0)   = k(x_1,...,x_n)
    F(x_1,...,x_n, t+1) = h(t, F(x_1,...,x_n,t), x_1,...,x_n).
|#
#|
At this point, the contents of Pete & J's defpun.list are closely
followed (with the modifications required to accommodate primitive
recursive definitions in place of tail recursive definitions).
|#
; To introduce an arbitrary primitive-recursive function (assuming
; the existence of an appropriate fixed point), we proceed in three
; steps.  First is the proof that we can admit the generic one
; argument primitive recursive function.  This ``generic theorem''
; is proved once; the proof is not redone for each new function.
; Second, the generic theorem is used to introduce the arity one
; version of the desired function.  Third, we prove that the arity
; one version is a witness for the desired equation.

; Here is an example.  Suppose we wish to admit the following
; primitive recursive function for computing (a^b) * b!.

; (defun
;   k (a b)
;   (if (equal b 0)
;       1
;       (* a b (k a (- b 1)))))

; Note that 0 is a right fixed point of (* a b y).

; We first recognize that this is probably primitive recursive
; (without checking that k is new, that the vars are distinct,
; etc.).  Successful recognition produces

;  (mv '((a (car x))    ;; args decomposition
;        (b (cadr x)))
;      '(equal b 0)     ;; test body
;      '1               ;; base body
;      '(list a (- b 1));; list of args to recursive call to k
;      '(* a b y$))     ;; h body

; Using the output of this check, we introduce four defuns

; (defun test1 (x)
;   (let ((a (car x))
;         (b (cadr x)))
;     (equal b 0)))

; (defun base1 (x)
;   (let ((a (car x))
;         (b (cadr x)))
;     1))

; (defun step1 (x)
;   (let ((a (car x))
;         (b (cadr x)))
;     (list a (- b 1))))

; (defun h (x y$)
;   (let ((a (car x))
; 	(b (cadr x)))
;     (* a b y$)))

; We then use the generic theorem to introduce

; (defun k1 (x)
;   (if (test1 x)
;       (base1 x)
;     (h x (k1 (step1 x)))))

; We then define

; (defun k (a b)
;   (k1 (list a b)))

; and we prove that it satisfies the constraint

; (equal
;   k (a b)
;   (if (equal b 0)
;       1
;       (* a b (k a (- b 1)))))

; Now we write the code to do all this.

;; First, the generic theorem is proved, assuming h$ has a right
;;  fixed point:
;;
;;  (defthm generic-primitive-recursive-f$
;;      (equal (f$ x)
;;             (if (test x) (base x) (h$ x (f$ (st x)))))

(in-package "ACL2")

(defstub test (*) => *)
(defstub base (*) => *)
(defstub st (*) => *)
(defstub h$-fix () => *)

(encapsulate
 (((h$ * *) => *))

 (local
  (defun h$ (x y$)
    (declare (ignore x y$))
    (h$-fix)))

 (defthm
   h$-fix-is-fixed-point
   (equal (h$ x (h$-fix))(h$-fix)))
 ) ;; end encapsulate

(defun stn (x n)
  (if (zp n) x (stn (st x) (1- n))))

(defchoose f$ch (n) (x)
	   (test (stn x n)))

(defun f$n (x n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (test x))
      (base x)
      (h$ x (f$n (st x) (1- n)))))

(defun f$ (x)
  (if (test (stn x (f$ch x)))
      (f$n x (f$ch x))
      (h$-fix)))

;;; This proof of generic-primitive-recursive-f is a minor
;;;  variation of Pete & J's proof of generic-tail-recursive-f
;;;  in defpun.lisp
(encapsulate
 ()
 (local (defthm test-f$ch
	    (implies (test x)
		     (test (stn x (f$ch x))))
            :hints
	    (("goal" :use ((:instance f$ch (n 0)))))))

;; Not needed for Pete & J's proof of generic-tail-recursive-f.
;;  Also not needed for proof of generic-primitive-recursive-f.
;;(local (defthm test-f-def
;;	 (implies (test x)
;;		  (equal (f x) (base x)))))

 (local (defthm open-stn
	    (implies (and (integerp n) (< 0 n))
		     (equal (stn x n)
			    (stn (st x) (1- n))))))

 (local (defthm +1-1 (equal (+ -1 +1 x) (fix x))))

 (local (defthm st-stn-f$ch
	    (implies (test (stn (st x) (f$ch (st x))))
		     (test (stn x (f$ch x))))
	    :hints
	    (("goal" :use
		     ((:instance f$ch (n (1+ (nfix (f$ch (st x))))))
		      (:instance f$ch (n 1)))))
	    :rule-classes :forward-chaining))

 (local (defthm test-nil-f$ch
	    (implies (not (test x))
		     (iff (test (stn (st x)
				     (f$ch (st x))))
			  (test (stn x (f$ch x)))))
	    :hints
	    (("subgoal 2" :expand (stn x (f$ch x))
			  :use
			  ((:instance f$ch (x (st x))
				      (n (+ -1 (f$ch x)))))))))

 (local (defthm f$n-st
	    (implies (and (test (stn x n))
			  (test (stn x m)))
		     (equal (f$n x n) (f$n x m)))
	    :rule-classes nil))

 (defthm generic-primitive-recursive-f$
     (equal (f$ x)
	    (if (test x) (base x) (h$ x (f$ (st x)))))
     :hints
     (("subgoal 2" :expand (f$n x (f$ch x)))
      ("subgoal 2.2'" :use
		      ((:instance f$n-st (x (st x))
				  (n (+ -1 (f$ch x)))
				  (m (f$ch (st x)))))))
     :rule-classes nil)
 ) ;; end encapsulate

(defun arity-1-primitive-recursive-encap (f test base st h h-fix)

; Execution of this function produces an encapsulation that
;  introduces a constrained primitive recursive f with the
;  constraint (equal (f x)
;                    (if (test x) (base x) (h x (f (st x))))),
; where test, base and st are previously defined functions of
; arity 1, h is a previously defined function of arity 2, and
; h-fix is a previously defined constant (function of arity 0).

  (declare (xargs :mode :program))

  (let ((stn (packn-pos (list f "-stn") f))
        (fch (packn-pos (list f "-fch") f))
        (fn  (packn-pos (list f "-fn") f))
	(thm (packn-pos (list h "-fixpt") h)))

    `(encapsulate
      (((,f *) => *))

      (local (in-theory (disable ,test ,base ,st ,h ,h-fix
;; This last entry is needed when h-fix is defined in terms of
;; a 0-ary functions introduced by defstub.
			       (:executable-counterpart ,h-fix))))

      (local (defun ,stn (x n)
               (if (zp n)
                   x
                 (,stn (,st x) (1- n)))))

      (local (defchoose ,fch (n) (x)
               (,test (,stn x n))))

      (local (defun ,fn (x n)
               (declare (xargs :measure (nfix n)))
               (if (or (zp n)
                       (,test x))
                   (,base x)
		   (,h x (,fn (,st x) (1- n))))))

      (local (defun ,f (x)
               (if (,test (,stn x (,fch x)))
                   (,fn x (,fch x))
                   (,h-fix))))

      (local (in-theory (enable ,h ,h-fix)))

      (local (defthm ,thm
	       (equal (,h x (,h-fix))(,h-fix))
	       :rule-classes nil))

      (local (in-theory '(,f ,test ,base ,st
			     ,h ,h-fix
			     ,stn ,fn
; This last entry is needed when fn is a constant function
; returning T, NIL, or 0 (one of the singleton type sets)
                             (:type-prescription ,fn))))

      (defthm ,(packn-pos (list f "-DEF") f)
        (equal (,f x)
               (if (,test x)
                   (,base x)
                   (,h x (,f (,st x)))))
        :hints (("Goal"
                 :use (:functional-instance
		       generic-primitive-recursive-f$
		       (f$ ,f)
		       (test ,test)
		       (base ,base)
		       (st ,st)
		       (stn ,stn)
		       (f$ch ,fch)
		       (f$n ,fn)
		       (h$ ,h)
		       (h$-fix ,h-fix)
		       ))
                ("Subgoal 2" :use ,fch)
		("Subgoal 5" :use ,thm))

        :rule-classes nil)
      )
    ))

; Second, we recognize probably primitive-recursive definitions
; and introduce the appropriate functions of arity 1.

; Note that probably-primitive-recursivep and destructure-primitive-recursion
; should be kept in sync.

(defun
  list-all-f-terms (f tree)
  "Return a list of all subtrees, with car equal to f, of tree."
  (cond ((atom tree) nil)
	((equal (car tree) f)
	 (cons tree (list-all-f-terms f (cdr tree))))
	(t (append (list-all-f-terms f (car tree))
		   (list-all-f-terms f (cdr tree))))))

(defun probably-primitive-recursivep (f vars body)
  (and (symbolp f)
       (symbol-listp vars)
       (true-listp body)
       (eq (car body) 'IF)
       (or (and (consp (caddr body))
                (not (eq (car (caddr body)) f))
		;; Determine if unique f-term occurs in
                ;; (cdr (caddr body)):
                (eql (length
		      (remove-duplicates-equal
		       (list-all-f-terms f (cdr (caddr body)))))
		     1))
           (and (consp (cadddr body))
                (not (eq (car (cadddr body)) f))
                ;; Determine if unique f-term occurs in
                ;; (cdr (cadddr body)):
                (eql (length
		      (remove-duplicates-equal
		       (list-all-f-terms f (cdr (cadddr body)))))
		     1)))))

(defun subst-equal (new old tree)
  (cond ((equal tree old) new)
	((atom tree) tree)
	(t (cons (subst-equal new old (car tree))
		 (subst-equal new old (cdr tree))))))

(defun destructure-primitive-recursion-aux (vars x)
  ;;(declare (xargs :mode :program))
  (cond ((endp vars) nil)
        (t (cons (list (car vars)
                       (list 'car x))
                 (destructure-primitive-recursion-aux (cdr vars)
                                               (list 'cdr x))))))

(defun destructure-primitive-recursion (f vars body)
  ;;(declare (xargs :mode :program))
  (cond
   ((and (consp (caddr body))
	 (not (eq (car (caddr body)) f))
	 ;; Determine if unique f-term occurs in
         ;; (cdr (caddr body)):
	 (eql (length
	       (remove-duplicates-equal
		(list-all-f-terms f (cdr (caddr body)))))
	      1))
    (let ((f-term
	   (car (list-all-f-terms f (cdr (caddr body))))))
         (mv (destructure-primitive-recursion-aux vars 'x)
	     (list 'NOT (cadr body))
	     (cadddr body)
	     (cons 'LIST (cdr f-term))
	     (subst-equal 'y$$ f-term (caddr body)))))
   (t
    (let ((f-term
	   (car (list-all-f-terms f (cdr (cadddr body))))))
         (mv (destructure-primitive-recursion-aux vars 'x)
	     (cadr body)
	     (caddr body)
	     (cons 'LIST (cdr f-term))
	     (subst-equal 'y$$ f-term (cadddr body)))))))

(defun arbitrary-primitive-recursive-encap (f vars body h-fix)
  (declare (xargs :mode :program))
  (mv-let
   (bindings test-body base-body step-body h-body)
   (destructure-primitive-recursion f vars body)
   (let ((f1 (packn-pos (list f "-arity-1") f))
         (test1 (packn-pos (list f "-arity-1-test") f))
         (base1 (packn-pos (list f "-arity-1-base") f))
         (step1 (packn-pos (list f "-arity-1-step") f))
	 (h1    (packn-pos (list f "-arity-1-h") f)))
     `(encapsulate
       ((,f ,vars t))
       (set-ignore-ok t)
       (set-irrelevant-formals-ok t)
       (local (defun ,test1 (x) (let ,bindings ,test-body)))
       (local (defun ,base1 (x) (let ,bindings ,base-body)))
       (local (defun ,step1 (x) (let ,bindings ,step-body)))
       (local (defun ,h1 (x y$$)(let ,bindings ,h-body   )))
       (local (defun h-fix-arity-1 () ,h-fix))
       (local ,(arity-1-primitive-recursive-encap
		f1 test1 base1 step1 h1 'h-fix-arity-1))
       (local (defun ,f ,vars (,f1 (list ,@vars))))
       (defthm ,(packn-pos (list f "-DEF") f)
         (equal (,f ,@vars) ,body)
         :hints (("Goal" :use (:instance ,(packn-pos (list f1 "-DEF") f)
                                         (x (list ,@vars)))))
         :rule-classes :definition)))))

(defun defpr-syntax-er nil
  '(er soft 'defpr
       "The proper shape of a defpr event is~%~
        (defpr g (v1 ... vn) dcl body).~%~
        The single declare form, dcl, must be of the form
        (DECLARE (XARGS :fixpt const)).~%~
        The declare form gives the ~
        required fixed point, const, which can be an ACL2 ~
        constant or the application of a 0-ary function. "))

(defmacro defpr (g vars &rest rest)
  (if (and (symbolp g)
	   (symbol-listp vars)
	   (eql (length rest) 2))

; This form may be legal, so we will destructure it and proceed.
;  Otherwise, we will cause an error.

      (let* ((dcl (first rest))
	     (body (second rest))
	     (xargs (second dcl)))
	    (if (and (eq (first dcl) 'DECLARE)
		     (eq (first xargs) 'XARGS)
		     (eq (second xargs) ':fixpt)
		     (probably-primitive-recursivep g vars body))
		(arbitrary-primitive-recursive-encap
		 g vars body (third xargs))
	        (defpr-syntax-er)))
      (defpr-syntax-er)))

;; Examples:
#|
;;This succeeds:
(defpr
  f (x)
  (declare (xargs :fixpt 0))
  (if (equal x 0)
      1
      (* (f (- x 1))
	 (f (- x 1)))))

;; Test error msg:
(defpr
  f1 (x)
  (declare (xargs :fixpt 0))
  (if (equal x 0)
      1
      (* (f1 (- x 1))
	 (f1 (+ x 1)))))

;; Test error msg:
(defpr
  f1 (x)
  ;;(declare (xargs :fixpt 0))
  (if (equal x 0)
      1
      (* (f1 (- x 1))
	 (f1 (- x 1)))))

This succeeds:
(defpr
  f1 (x)
  (declare (xargs :fixpt 0))
  (if (not (equal x 0))
      (* (f1 (- x 1))
	 (f1 (- x 1)))
      1))
|#
#| Example 1. Tail recursion as a special case.
;     Tail recursion is a special case of primitive recursion:
;        The projection function defined by
;              (Id-2-2 x1 x2) <== x2
;          is used for the function h in the primitive recursive
;          definition. Any constant can be used for the fixed
;          point.

(defun
  Id-2-2 (x1 x2)
  (declare (ignore x1))
  x2)

(defstub tail-test (*) => *)

(defstub tail-base (*) => *)

(defstub tail-st (*) => *)

(defpr
  tail-f (x)
  (declare (xargs :fixpt nil))
  (if (tail-test x)
      (tail-base x)
      (Id-2-2 x (tail-f (tail-st x)))))

(defthm
  tail-f-is-tail-recursive
  (equal (tail-f x)
	 (if (tail-test x)
	     (tail-base x)
	     (tail-f (tail-st x)))))
|#
#| Example 2. Pete & J's cons example (modified).

No ACL2 function g satisfies this equation:
(equal (g x)
       (if (equal x 0)
	   nil
	   (cons nil (g (- x 1)))))

The ``problem'' from the point of view of this note is that cons
does not have a right fixed point, so one is provided by the
following:

(defstub
    cons-fix () => *)

(defun
    cons$ (x y)
    (if (equal y (cons-fix))
	(cons-fix)
        (cons x y)))

;; The following equation has an ACL2 solution for g.

(equal (g x)
       (if (equal x 0)
	   nil
	   (cons$ nil (g (- x 1)))))

(defpr
  g (x)
  (declare (xargs :fixpt (cons-fix)))
  (if (equal x 0)
      nil
      (cons$ nil (g (- x 1)))))
|#
#| Example 3. Naive Factorial
;;  This example illustrates that any fixed point will do:
;;   Multiplication already has a right fixed point, namely 0.
;;   That is (* x 0) = 0.
;;  The following equation has an ACL2 solution for fact.

(equal (fact x)
       (if (equal x 0)
	   1
	   (* x (fact (- x 1)))))

  Note:
   ACL2 would accept the definition that uses the zero-test idiom
    (zp x) in place of the test (equal x 0):

(defun
    fact (x)
    (if (zp x)
	1
        (* x (fact (- x 1)))))

(defpr
  fact (x)
  (declare (xargs :fixpt 0))
  (if (equal x 0)
      1
      (* x (fact (- x 1)))))
|#
#| Example 4. Example with parameters.
;;   A naive version of the recursive equation added to ACL2
;;   by the following definition.

(defun
    k (a b)
    (if (zp b)
        1
        (* a b (k a (- b 1)))))

Note: This (k a b) computes (a^b) * b!:

(defun
  fact1 (x)
  (if (zp x)
      1
    (* x (fact1 (- x 1)))))

(defun
  exp1 (x y)
  (if (zp y)
      1
    (* x (exp1 x (- y 1)))))

(defthm
  reverse-associativity-of-*
 (equal (* x y z)
	(* (* x y) z)))

(defthm
  commutativity-2-of-*
  (equal (* x y z)
	 (* y x z))
  :hints (("Goal"
	   :in-theory (disable COMMUTATIVITY-OF-*
			       ASSOCIATIVITY-OF-*)
	   :use COMMUTATIVITY-OF-*)))

(in-theory (disable reverse-associativity-of-*))

(thm
 (equal (k x y)
	(* (exp1 x y)(fact1 y))))

Here are some naive versions:

(defpr
  k (a b)
  (declare (xargs :fixpt 0))
  (if (equal b 0)
      1
      (* a b (k a (- b 1)))))

(defpr
  k1 (a b)
  (declare (xargs :fixpt 0))
  (if (equal b 0)
      1
      (* a (k1 a (- b 1)) b)))
|#
