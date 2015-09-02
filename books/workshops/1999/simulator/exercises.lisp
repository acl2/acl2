(in-package "ACL2")
#|

This file contains solutions to the exercises in "High-Speed
Analyzable Simulators", Chapter 8 of the book "Computer-Aided
Reasoning: ACL2 Case Studies".

David Greve and Matt Wilding
February 2000

|#

(include-book "tiny")

; Some basic function/macro definitions that will be used throughout.

(defmacro Int32 (x) `(the (signed-byte 32) ,x))

(defmacro MAX_INT<32> ()  2147483647)
(defmacro MIN_INT<32> () -2147483648)

(defmacro +<32> (x y) `(Int32 (+ ,x ,y)))

#|
-------------------------------------------------------------------------
Exercise 8.1

Extend the reader macro presented above to handle the special Lisp
forms case and cond.  (Remember, case key forms are not evaluated!)
Expand its capability to handle some of the other basic integer
operations such as logand, logior, etc.  Try automatically inserting
type declarations into simple let bindings, assuming that each let
binds a fixnum value.
-------------------------------------------------------------------------
|#

(defun map-fn (fn form)

  "Map the reader macro (fn) over a list of function arguments"

  (if (consp form)
      `((,fn ,(car form)) ,@(map-fn fn (cdr form)))
    nil))

(defun make-let-decls (let-body)

  "Create let declarations for each of the bound variables contained
  within the let form."

  (if (consp let-body)
      (let ((binding (car let-body)))
	`((type (signed-byte 32) ,(first binding))
	  ,@(make-let-decls (cdr let-body))))
    nil))

(defun map-fn-let-body (fn let-body)

  "Map the reader macro (fn) over the body of a let form"

  (if (consp let-body)
      (let ((binding (car let-body)))
	`((,(first binding) (,fn ,(second binding)))
	  ,@(map-fn-let-body fn (cdr let-body))))
    nil))

(defun map-fn-cond-body (fn cond-body)

  "Map the reader macro (fn) over the body of a cond form"

  (if (consp cond-body)
      (let ((term (car cond-body)))
	`(((,fn ,(first term)) (,fn ,(second term)))
	  ,@(map-fn-cond-body fn (cdr cond-body))))
    nil))

(defun map-fn-case-body (fn case-body)

  "Map the reader macro (fn) over the body of a case form.  Note
   that the keys of the case form are not evaluated at read time,
   thus we cannot map the macro reader over them!"

  (if (consp case-body)
      (let ((term (car case-body)))
	`((,(first term) (,fn ,(second term)))
	  ,@(map-fn-case-body fn (cdr case-body))))
    nil))

; Define some additional "wrapper macros" that declare the arguments
; and retun values for some of the common lisp arithmetic forms.

(defmacro      -<32> (a b) `(Int32 (-  (Int32 ,a) (Int32 ,b))))
(defmacro     1+<32> (a)   `(Int32 (+  (Int32 ,a) 1)))
(defmacro     1-<32> (a)   `(Int32 (-  (Int32 ,a) 1)))
(defmacro logxor<32> (a b) `(Int32 (logxor (Int32 ,a) (Int32 ,b))))
(defmacro logand<32> (a b) `(Int32 (logand (Int32 ,a) (Int32 ,b))))
(defmacro logior<32> (a b) `(Int32 (logior (Int32 ,a) (Int32 ,b))))
(defmacro lognot<32> (a)   `(Int32 (lognot (Int32 ,a))))

(defun reader_fn (form)

  "Change the meaning of some of the arithmetic forms and recursively
   map the macro reader over the various lisp sub-forms contained
   within form"

  (if (consp form)
      (case (first form)

	    ; Replace some of the common lisp arithmetic forms with
	    ; declared versions thereof.

	    (+      `(+<32>      ,@(map-fn `reader (cdr form))))
	    (-      `(-<32>      ,@(map-fn `reader (cdr form))))
	    (1+     `(1+<32>     ,@(map-fn `reader (cdr form))))
	    (1-     `(1+<32>     ,@(map-fn `reader (cdr form))))
	    (logand `(logand<32> ,@(map-fn `reader (cdr form))))
	    (logior `(logior<32> ,@(map-fn `reader (cdr form))))
	    (logxor `(logxor<32> ,@(map-fn `reader (cdr form))))
	    (lognot `(lognot<32> ,@(map-fn `reader (cdr form))))

	    ; Map the reader macro over some of the the common lisp
	    ; special forms.

	    (case `(case (reader ,(second form)) ,@(map-fn-case-body `reader (nthcdr 2 form))))
	    (cond `(cond ,@(map-fn-cond-body `reader (cdr form))))
	    (let  `(let ,(map-fn-let-body `reader (second form))
		     (declare ,@(make-let-decls (second form)))
		     (reader ,@(nthcdr 2 form))))

	    ; Map the reader macro over the arguments of any remaining
	    ; functions.

	    (t    `(,(first form) ,@(map-fn `reader (cdr form))))
	    )

    form))

(defmacro reader (form)

  "The top level reader macro is now pretty simple."

  (reader_fn form))

#|
-------------------------------------------------------------------------
Exercise 8.2

Write a progn-style macro that binds single threaded object updates
and allows for the introduction of let bindings of intermediate
variables.  For example,

(ST-PROGN HWSTATE
   (update-1 HWSTATE)
   (let ((value1 (+ 4 5))))
     (update-2 value1 HWSTATE))

should expand to the following.

(let ((HWSTATE (update-1 HWSTATE)))
  (let ((value1 (+ 4 5)))
    (let ((HWSTATE (update-2 value1 HWSTATE)))
      HWSTATE)))
-------------------------------------------------------------------------
|#

(defun st-progn-fn (st progn-form)

  "In this function we assume that the progn-form is a simple list
   containing only implicit state updates and explicit let bindings."

  (if (consp progn-form)

      (let ((form (car progn-form)))

	(if (consp form)

	    (case (first form)

		  (let  `(,@form
			  ,(st-progn-fn st (cdr progn-form))))

		  (t    `(let ((,st ,form))
			   ,(st-progn-fn st (cdr progn-form)))))

	  form))

    st))

(defmacro st-progn (s &rest progn-form)

  (st-progn-fn s progn-form))

#|
ACL2 !>:trans1 (ST-PROGN HWSTATE
                 (update-1 HWSTATE)
                 (let ((value1 (+ 4 5))))
                   (update-2 value1 HWSTATE))

 (LET ((HWSTATE (UPDATE-1 HWSTATE)))
      (LET ((VALUE1 (+ 4 5)))
           (LET ((HWSTATE (UPDATE-2 VALUE1 HWSTATE)))
                HWSTATE)))
ACL2 !>
|#



#|

-------------------------------------------------------------------------
Exercise 8.3

Prove that, given two 32-bit integers arguments, plus<32> implements
32-bit modular integer addition.  Hint: You may want to use logext and
logext-+-logext from the ihs books provided with the ACL2 distribution
to specify and prove this behavior.
-------------------------------------------------------------------------

See plus<32> and plus<32>-works in tiny.lisp

-------------------------------------------------------------------------
Exercise 8.4

Implement a function that accepts two 32-bit integer values and
returns their 32-bit integer bitwise logical and.  Was this function
simpler or more complex than plus<32>? Why?
-------------------------------------------------------------------------
The 32-bit version of logand is simpler than the 32-bit version of
plus because there is no overflow conditions with logand.  Simple
declarations suffice for efficiency and the guards are proved easily.

Note that ACL2's interpretation of the declarations does not use the
functions of the IHS library, so in order to use it we must do so
manually, using a guard-hint
|#

(defun and<32> (a b)
  (declare (type (signed-byte 32) a)
           (type (signed-byte 32) b)
	   (xargs :guard-hints (("goal" :use (:instance signed-byte-p-logops (size 32) (i a) (j b))
				 :in-theory (union-theories
					     '(signed-byte-p)
					     (disable signed-byte-p-logops))))))

  (Int32 (logand a b)))


#|
-------------------------------------------------------------------------
Exercise 8.5

Calculate a symbolic expression that expresses the result of executing
the TINY interpreter on the first two instructions of the remainder
program.  Simplify that expression using the fact that an update of an
element of the state does not affect the other elements.
-------------------------------------------------------------------------

We generated a term that answers this question by symbolically
executing the tiny interpreter 2 steps by trying to "prove" a rule of
the form

(equal (tiny st 2) st)

under suitable hypotheses.  This "proof" failed, of course, but we
derived the rewritten expression from the prover output.  We show
below that this term in fact answers the question.

|#

(defthm tiny-remainder-2-steps
  (implies
   (and
    (stp st)
    (< (dtos st) 1000) (>= (dtos st) 100)
    (equal (progc st) 20)
    (program-loaded st *mod-prog* 20))
   (equal
    (tiny st 2)
    (update-nth
     0 24
     (update-nth 1
                 (update-nth 18 (nth (+ 2 (nth 2 st)) (nth 1 st))
                             (update-nth 19 (nth (+ 1 (nth 2 st)) (nth 1 st))
                                         (nth 1 st)))
                 (update-nth 2 (+ 2 (nth 2 st)) st)))))
  :hints (("goal" :in-theory (enable next unsigned-byte-p))))


#|
-------------------------------------------------------------------------
Exercise 8.6

Read the ACL2 documentation of loop-stopper.  Give an example term
that is simplified by the rewrite rule update-nth-update-nth-diff, but
which would not have simplified had update-nth-update-nth-diff not
overridden the default heuristics with an explicit :loop-stopper
argument.
-------------------------------------------------------------------------

One such term is

(update-nth 4 'cat
	    (update-nth 3 '(pig chicken)
			(update-nth 4 '(mouse horse snake) l)))

With update-nth-update-nth-diff defined as it is, the following
theorem succeeds

|#

(defthm update-nth-simplify1
 (equal
  (update-nth 4 'cat
	    (update-nth 3 '(pig chicken)
			(update-nth 4 '(mouse horse snake) l)))
  (update-nth 4 'cat
	    (update-nth 3 '(pig chicken) l)))
 :rule-classes nil)

;; We introduce a version of update-nth-update-nth-diff that uses the
;; default loop-stopper.

(defthm update-nth-update-nth-diff-default
  (implies
   (not (equal (nfix i1) (nfix i2)))
   (equal (update-nth i1 v1 (update-nth i2 v2 l))
	  (update-nth i2 v2 (update-nth i1 v1 l)))))

#|

The theorem that formerly proved fails, because the loop-stopper keeps
update-nth-update-nth-diff-default from applying, and we disabled the
more effective rule update-nth-update-nth-diff.

(defthm update-nth-simplify2
 (equal
  (update-nth 4 'cat
	    (update-nth 3 '(pig chicken)
			(update-nth 4 '(mouse horse snake) l)))
  (update-nth 4 'cat
	    (update-nth 3 '(pig chicken) l)))
 :hints (("goal" :in-theory (disable update-nth-update-nth-diff))))

|#