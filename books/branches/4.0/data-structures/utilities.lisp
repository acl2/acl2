; utilities.lisp -- utility functions 
; Copyright (C) 1997  Computational Logic, Inc.

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Bill Bevier (bevier@cli.com) and Bishop Brock
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    utilities.lisp
;;;
;;;    A book of utility functions and macros for use by the books in the
;;;    public library.  This book is defined in the "U" (for utilities)
;;;    package.  To certify this book:
#|
 (in-package "ACL2")
 (defpkg "U" (union-eq *acl2-exports*
                       *common-lisp-symbols-from-main-lisp-package*))
 (certify-book "utilities" 1)
|#
;;;
;;;    Bill Bevier  -- bevier@cli.com
;;;    Bishop Brock -- brock@cli.com
;;;    Computational Logic, Inc.
;;;    1717 West 6th Street, Suite 290
;;;    Austin, Texas 78703
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "U")

(deflabel utilities
  :doc ":doc-section utilities
  A book of utility functions residing in the package \"U\".
  ~/
  The available utilities include the following:
  ~/~/")

;;;****************************************************************************
;;;
;;;    IMPORT-AS-MACROS package-symbol &rest symbols
;;;
;;;    The definitions included in this book use a few select routines from the
;;;    Acl2 system code.  To avoid having to prefix these names with the
;;;    ACL2:: package name everywhere, we provide a general purpose method of
;;;    importing external symbols by defining a macro in the current package
;;;    that simply expands to a macro call of the actual symbol.
;;;
;;;    One could also, from time to time, simply add the accumulated list of
;;;    imported symbols to the package definition above.
;;;
;;;****************************************************************************

(defun import-as-macros-fn (package-symbol symbols)
  (declare (xargs :guard (and (symbolp package-symbol)
			      (acl2::symbol-listp symbols))
		  :verify-guards nil))
  (cond
   ((atom symbols) ())
   (t (cons
       (let ((sym (car symbols)))
	 `(DEFMACRO ,sym (&REST FORMS)
	    (CONS
	     ',(acl2::intern-in-package-of-symbol
		(string sym) package-symbol)
	     FORMS)))
       (import-as-macros-fn package-symbol (cdr symbols))))))

(defmacro import-as-macros (package-symbol &rest symbols)
  `(PROGN ,@(import-as-macros-fn package-symbol symbols)))

; The symbols commented out below have been added to *acl2-exports* since this
; book was written.  This change was made between ACL2 Version 2.4 and 2.5.

(import-as-macros
 ACL2::A-SYMBOL-UNIQUE-TO-THE-ACL2-PACKAGE
; assoc-keyword
; true-list-listp
  arglistp
  conjoin
; duplicates
; eqlable-listp
; explode-nonnegative-integer
; intern-in-package-of-symbol
; keyword-value-listp
; member-equal
  msg
; program
  translate-declaration-to-guard-var-lst
; true-listp
  #|red|#				; Now PROGRAM
; set-difference-equal
; symbol-listp
  untranslate)


;;;****************************************************************************
;;;
;;;    DEFLOOP
;;;
;;;    Documentation appears with the DEFLOOP macro below.  This code appears
;;;    here so that other utilities may be defined with DEFLOOP.  All of
;;;    DEFLOOP is :RED.
;;;
;;;****************************************************************************

(encapsulate ()

(program)

(defmacro bomb (ctx str &rest args)
  `(ACl2::ER ACL2::HARD ,ctx ,str ,@args))

(defconst *defloop-accumulators* '("COLLECT" "APPEND"))
(defconst *defloop-conditionals* '("IF" "WHEN" "UNLESS"))
(defconst *defloop-terminators* '("ALWAYS" "NEVER" "THEREIS"))

(defconst *defloop-main-clause-legal-cars*
  (append *defloop-accumulators*
	  *defloop-conditionals*
	  *defloop-terminators*))

(defconst *defloop-value-clause-legal-cars*
  (cons "RETURN" *defloop-accumulators*))

(defconst *defloop-accum/terms*
  (append *defloop-accumulators* *defloop-terminators*))

(defun defloop-strip-nth (n l)
  (declare (xargs :guard (and (integerp n)
			      (>= n 0)
			      (true-list-listp l))))
  (cond ((endp l) ())
	(t (cons (nth n (car l)) (defloop-strip-nth n (cdr l))))))

(defun defloop-main-clause-syntax-error (main-clause)
  (cond ((not (and (true-listp main-clause)
		   (symbolp (first main-clause))
		   (member-equal (string (first main-clause))
				 *defloop-main-clause-legal-cars*)))
	 (msg "The main-clause must be a true list whose first ~
          element is a symbol whose print name is one of ~v0."
	      *defloop-main-clause-legal-cars*))
	((member-equal (string (first main-clause)) *defloop-accumulators*)
	 (and (not (equal (length main-clause) 2))
	      (msg "Invalid list-accumulation: ~p0." main-clause)))
	((member-equal (string (first main-clause)) *defloop-terminators*)
	 (and (not (equal (length main-clause) 2))
	      (msg "Invalid termination form: ~p0." main-clause)))
	((member-equal (string (first main-clause)) *defloop-conditionals*)
	 (cond
	  ((not (equal (length main-clause) 3))
	   (msg "Invalid conditional form: ~p0." main-clause))
	  (t
	   (let ((value-clause (third main-clause)))
	     (and (not (true-listp value-clause))
		  (not (equal (length value-clause) 2))
		  (not (symbolp (first value-clause)))
		  (not (member-equal (string (first value-clause))
				     *defloop-value-clause-legal-cars*))
		  (msg "Invalid value-clause: ~p0." value-clause))))))))

(defun defloop-for-clauses-syntax-error1 (for-clauses arglist)
  (cond ((atom for-clauses) nil)
	(t
	 (let ((clause (car for-clauses)))
	   (cond ((not (and (true-listp clause)
			    (>= (length clause) 3)
			    (symbolp (first clause))
			    (symbolp (second clause))
			    (member-equal (string (second clause))
					  '("IN" "ON"))
			    (symbolp (third clause))
			    (member (third clause) arglist)
			    (implies
			     (> (length clause) 3)
			     (and (equal (length clause) 5)
				  (symbolp (fourth clause))
				  (equal (string (fourth clause)) "BY")
				  (symbolp (fifth clause))))))
		  (msg "A for-clause must be of the form:
 (var {IN | ON} arg [ BY fn ])
where var is a symbol, arg is a symbol in ~
the arglist, and fn is a symbol, but ~p0 does not satisfy these constraints."
		       clause))
	    (t (defloop-for-clauses-syntax-error1 (cdr for-clauses) arglist)))))))

(defun defloop-for-clauses-syntax-error (for-clauses arglist)
  (cond
   ((not (and (true-listp for-clauses)
	      for-clauses))
    (msg "The for-clauses must be a non-empty true list but ~p0 is not."
	 for-clauses))
   ((defloop-for-clauses-syntax-error1 for-clauses arglist))
   ((duplicates (defloop-strip-nth 0 for-clauses))
    (msg "Multiple bindings for free-var~#0~[~/s~] ~&0."
	 (duplicates (defloop-strip-nth 0 arglist))))
   ((duplicates (defloop-strip-nth 2 for-clauses))
    (msg "Multiple for-clauses for arg~#0~[~/s~] ~&0."
	 (duplicates (defloop-strip-nth 2 arglist))))
   (t NIL)))

(defun defloop-syntax-error (name arglist forms)
  (let
    ((err
      (cond
       ((not (symbolp name))
	(msg "The name must be a symbol, but ~p0 is not." name))
       ((not (arglistp arglist))
	(msg "The arglist must be a valid functional argument list as defined ~
          by ACL2::ARGLISTP, but ~p0 is not." arglist))
       ((null forms)
	(msg "You neglected to include a function body!"))
       (t
	(let ((loop-form (car (last forms))))
	  (cond
	   ((not (and (true-listp loop-form)
		      (equal (length loop-form) 3)
		      (symbolp (first loop-form))
		      (equal (string (first loop-form)) "FOR")))
	    (msg "The loop-form must be a true list of length 3 whose CAR is ~
              a symbol named FOR, but ~p0 is not." loop-form))
	   ((defloop-for-clauses-syntax-error (second loop-form) arglist))
	   ((defloop-main-clause-syntax-error (third loop-form)))
	   (t nil)))))))
    (if err
	(bomb 'DEFLOOP "Syntax error. ~@0" err)
      nil)))

(defun defloop-atomize (l)
  (cond
   ((null l) ())
   (t (cons `(ATOM ,(car l)) (defloop-atomize (cdr l))))))

(defun defloop-disjoin (l)
  (cond
   ((atom l) l)
   ((and (consp l) (atom (cdr l))) (car l))
   (t `(OR ,@l))))

(defun defloop-by-alist (for-clauses)
  (cond
   ((atom for-clauses) ())
   (t (let ((clause (car for-clauses)))
	(cons (cons (third clause)
		    (cond
		     ((fifth clause) `(,(fifth clause) ,(third clause)))
		     (t `(CDR ,(third clause)))))
	      (defloop-by-alist (cdr for-clauses)))))))

(defun defloop-reduce-args1 (arglist alist)
  (cond
   ((atom arglist) ())
   (t (cons
       (let ((pair (assoc (car arglist) alist)))
	 (if pair
	     (cdr pair)
	   (car arglist)))
       (defloop-reduce-args1 (cdr arglist) alist)))))

(defun defloop-reduce-args (arglist for-clauses)
  (defloop-reduce-args1 arglist (defloop-by-alist for-clauses)))

(defun defloop-lambda-args (for-clauses)
  (cond
   ((atom for-clauses) ())
   (t (cons
       (let ((clause (car for-clauses)))
	 (cond
	  ((equal (string (second clause)) "IN") `(CAR ,(third clause)))
	  ((equal (string (second clause)) "ON") (third clause))
	  (t (bomb 'DEFLOOP-LAMBDA-ARGS "Bug."))))
       (defloop-lambda-args (cdr for-clauses))))))

(defun defloop-applied-lambda (for-clauses body invertp)
  `((LAMBDA ,(defloop-strip-nth 0 for-clauses) ,(if invertp `(NOT ,body) body))
    ,@(defloop-lambda-args for-clauses)))

(defun defloop-atom-null-check (for-clauses)
  ;;  There must be at least 1 for-clause.
  (cond
   ((null (cdr for-clauses)) `(NULL ,(nth 2 (car for-clauses))))
   (t `(IF (ATOM ,(nth 2 (car for-clauses)))
	   (NULL ,(nth 2 (car for-clauses)))
	 ,(defloop-atom-null-check (cdr for-clauses))))))

(defun defloop-accum/term
  (name arglist decls for-clauses main-clause main-car)
  `(DEFUN ,name ,arglist
     ,@decls
     (COND
      (,(defloop-disjoin (defloop-atomize (defloop-strip-nth 2 for-clauses)))
       ,(cond
	 ((member-equal main-car '("COLLECT" "APPEND" "THEREIS")) '())
	 ((member-equal main-car '("ALWAYS" "NEVER"))
	  (defloop-atom-null-check for-clauses))))
      (T (,(cond
	    ((equal main-car "COLLECT") 'CONS)
	    ((equal main-car "APPEND") 'APPEND)
	    ((equal main-car "ALWAYS") 'AND)
	    ((equal main-car "NEVER") 'AND)
	    ((equal main-car "THEREIS") 'OR)
	    (t (bomb 'DEFLOOP-ACCUM/TERM "Bug.")))
	  ,(defloop-applied-lambda for-clauses
	     (second main-clause) (equal main-car "NEVER"))
	  (,name ,@(defloop-reduce-args arglist for-clauses)))))))

(defun defloop-conditional
  (name arglist decls for-clauses main-clause main-car)
  (let* ((test (second main-clause))
	 (value-clause (third main-clause))
	 (value-car (string (car value-clause))))
    `(DEFUN ,name ,arglist
       ,@decls
       (COND
	(,(defloop-disjoin (defloop-atomize (defloop-strip-nth 2 for-clauses)))
	 '())
	(,(defloop-applied-lambda for-clauses test (equal main-car "UNLESS"))
	 ,(cond
	   ((equal value-car "COLLECT")
	    `(CONS ,(defloop-applied-lambda for-clauses (second value-clause)
		      nil)
		   (,name ,@(defloop-reduce-args arglist for-clauses))))
	   ((equal value-car "APPEND")
	    `(APPEND ,(defloop-applied-lambda for-clauses (second value-clause)
			nil)
		     (,name ,@(defloop-reduce-args arglist for-clauses))))
	   ((equal value-car "RETURN")
	    (defloop-applied-lambda for-clauses (second value-clause) nil))
	   (t (bomb 'DEFLOOP-CONDITIONAL "Bug."))))
	(T (,name ,@(defloop-reduce-args arglist for-clauses)))))))
      
(defmacro defloop (name arglist &rest forms)
  ":doc-section utilities
   Macro for defining simple iteration schemes as functions.
   ~/~/
 
 Syntax:
 
   DEFLOOP name arglist [documentation] {declaration}* loop-form
 
   loop-form ::= (FOR ({!for-clause}+) main-clause)
 
   for-clause ::= for-in-clause | for-on-clause
 
   for-in-clause ::= (var IN arg [ BY fn ])
 
   for-on-clause ::= (var ON arg [ BY fn ])
 
   main-clause ::= !list-accumulation | (!conditional form !value-clause) |
                   (!termination-test form)
 
   value-clause ::= !list-accumulation | (RETURN form)
 
   list-accumulation ::= ({COLLECT | APPEND} form)
 
   value-clause ::= ({COLLECT | APPEND | RETURN} form)
 
   conditional ::= IF | WHEN | UNLESS
 
   termination-test ::= ALWAYS | THEREIS | NEVER
 
 Arguments and Values:
 
   arg -- a symbol appearing in the arglist.
 
   arglist -- an argument list satisfying ACL2::ARGLISTP.
 
   declaration -- any valid declaration.
 
   documentation -- a string; not evaluated.
 
   form -- a form.
 
   fn -- a symbol; must be the function symbol of a unary function
         well-defined on true lists.
 
   var -- a symbol.
 
   name -- a symbol.
 
 Special Note:
 
   The symbols FOR, IN, ON, BY, RETURN, COLLECT, APPEND, IF, WHEN, UNLESS,
   ALWAYS, THEREIS, and NEVER appearing above may be in any package; DEFLOOP
   checks the print name of the symbol, not the symbol itself.
  
 Description
 
   DEFLOOP is a macro that creates iterative functions.  The description of
 the iteration is specified with an abstract syntax based on a small but
 useful subset of the Common Lisp LOOP construct (as defined by ANSI X3J13).
 Using DEFLOOP one can easily define functions analogous to MAPCAR and MAPCAN,
 list type recognizers, and MEMBER- and ASSOC-like functions.
 
   The syntax of DEFLOOP is similar to DEFUN: The function name is followed by
 the arglist, optional documentation and declarations, and the function body.
 Note that any guards on any of the arguments are the responsibility of the
 user.  
 
   The function body is in a special format, i.e., the loop-form as defined 
 in the Syntax description.
 
   Each for-clause defines an iteration on one of the args in arglist.  The
 for-in-clause
 
   (var IN arg [ BY fn ])
 
 specifies that in each iteration, var will be bound to successive CARs
 of arg, and arg will be reduced by fn on each iteration.  The default value
 of fn is CDR.  The for-on-clause
 
   (var ON arg [ BY fn ])
 
 specifies that var will first be bound to arg, and then reduced by fn on
 each iteration.  Again, the default value of fn is CDR.
 
   Using a list-accumulation one can specify MAPCAR- and MAPCAN-like functions.
 Here is an example of how the Acl2 function STRIP-CARS could be defined with
 DEFLOOP: 
 
 (DEFLOOP STRIP-CARS (L)
   (DECLARE (XARGS :GUARD (ALISTP L)))
   (FOR ((X IN L))
        (COLLECT (CAR X))))
 
   Iteration on multiple lists may be specified; iteration will terminate as
 soon as any of the lists are ATOMic, e.g.,
 
 (DEFLOOP PAIRLIS$ (KEYS VALS)
   (DECLARE (XARGS :GUARD (AND (TRUE-LISTP KEYS)
                               (TRUE-LISTP VALS))))
   (FOR ((KEY IN KEYS) (VAL IN VALS))
        (COLLECT (CONS KEY VAL))))
 
   This example shows reduction by a function other than CDR:
 
 (DEFLOOP EVENS (L) (FOR ((X IN L BY CDDR)) (COLLECT X)))
 
   List-accumulations can be coupled with a test, e.g., this function that
 selects all of the numbers <= n from l, and the ODDS function:
 
 (DEFLOOP <=-LIST (N L)
   (DECLARE (XARGS :GUARD (AND (INTEGERP N)
                               (INTEGERP-LISTP L))))
   (FOR ((X IN L))
        (WHEN (<= X N)
          (COLLECT X))))

 (DEFLOOP ODDS (L)
   (DECLARE (XARGS :GUARD (TRUE-LISTP L)))
   (FOR ((TAIL ON L BY CDDR))
        (UNLESS (NULL (CDR TAIL))
          (COLLECT (CADR TAIL)))))

 The definition of <=-LIST shows that any functional arguments may
 appear free in the various DEFLOOP forms.  Non-iterated arguments are simply
 passed unchanged during recursive calls.  Also note that IF and WHEN are
 synonymous as DEFLOOP tests. 
 
   A RETURN can also be coupled with a test.  If the test is never satisfied
 then the resulting function will return NIL.  Here are examples of how
 ASSOC-EQUAL and MEMBER-EQUAL could have been defined with DEFLOOP:
 
 (DEFLOOP ASSOC-EQUAL (KEY ALIST)
   (DECLARE (XARGS :GUARD (ALISTP ALIST)))
   (FOR ((PAIR IN ALIST))
        (WHEN (EQUAL KEY (CAR PAIR))
          (RETURN PAIR))))
 
 (DEFLOOP MEMBER-EQUAL (X L)
   (DECLARE (XARGS :GUARD (TRUE-LISTP L)))
   (FOR ((TAIL ON L))
        (WHEN (EQUAL X (CAR TAIL))
          (RETURN TAIL))))
        
   The termination-tests can be used to create various recognizers and
 `un'-recognizers.  Note that a DEFLOOP with a termination test of ALWAYS or
 NEVER will only return T if iteration terminates on NIL, i.e, they only
 recognize true lists.  The termination test (THEREIS form) will return
 the first non-NIL value returned by form, or NIL if there is none.
 Here for example are functions that recognize true lists of integers,
 true lists of un-integers, and lists containing an integer:
 
 (DEFLOOP INTEGERP-LISTP (L) (FOR ((X IN L)) (ALWAYS (INTEGERP X))))
 
 (DEFLOOP NO-INTEGERP-LISTP (L) (FOR ((X IN L)) (NEVER (INTEGERP X))))
 
 (DEFLOOP HAS-INTEGERP-LISTP (L) (FOR ((X IN L)) (THEREIS (INTEGERP X))))
 
 Note that in accordance with the semantics of the LOOP construct, the THEREIS
 form above simply returns the first non-NIL result computed.  If you want a
 function that returns the first integer in a list then you can use a
 conditional return: 
 
 (DEFLOOP FIRST-INTEGER (L)
   (FOR ((X IN L)) (IF (INTEGERP X) (RETURN X))))
 
   Final note: If in doubt, simply TRANS1 the DEFLOOP form and have a look at
 the generated function.
   ~/"

  (let ((ignre (defloop-syntax-error name arglist forms)))
    (declare (ignore ignre))
    (let* ((loop-form (car (last forms)))
	   (for-clauses (second loop-form))
	   (main-clause (third loop-form))
	   (main-car (string (first main-clause))))
      (cond
       ((member-equal main-car *defloop-accum/terms*)
	(defloop-accum/term name arglist (butlast forms 1)
	  for-clauses main-clause main-car))
       ((member-equal main-car *defloop-conditionals*)
	(defloop-conditional name arglist (butlast forms 1)
	  for-clauses main-clause main-car))
       (t (bomb 'DEFLOOP "Bug."))))))

;  End ENCAPSULATE
)


;;;****************************************************************************
;;;
;;;    Keyword Option List Parsing
;;;
;;;****************************************************************************

(defloop keyword-listp (l)
  "Recognizes lists of keywords."
  (declare (xargs :guard t))
  (for ((x in l)) (always (keywordp x))))

(defloop keyword-pair-alistp (l)
  "Recognizes alists whose entries are all pairs of keywords."
  (declare (xargs :guard t))
  (for ((pair in l))
       (always (and (consp pair)
		    (keywordp (car pair))
		    (keywordp (cdr pair))))))

(defun string-designator-p (x)
  "The guard of the Common Lisp function STRING."
  (declare (xargs :guard t))
  (or (stringp x) (symbolp x) (and (characterp x) (standard-char-p x))))

(deflabel get-option
  :doc ":doc-section utilities
  A set of routines for parsing keyword option lists.
  ~/
  The following functions are included:
  ~/
  A keyword option list is a true list, each element of which is either a
  keyword, or a true list whose car is a keyword. Here is an example:

  (:READ-ONLY (:PREFIX \"Foo\") (:DO-NOT :TAG :NORMALIZE))

  The GET-OPTION routines provide an easy to use interface that in can handle a
  lot of the parsing and syntax checking for keyword option lists.  Some
  routines exist in 2 forms: The first form, e.g., 

  (GET-OPTION-AS-FLAG ctx option option-list)

  takes a context (a name printed in case of an error), an option keyword,
  an option list, (possible other args as well) and looks for the option in
  the list.  The function will abort if any syntax errors occur.  The second
  form, e.g., 

  (GET-OPTION-AS-FLAG-MV option option-list)  

  returns 2 values.  The first value, if non-NIL, is an object produced by 
  ACL2::MSG that describes the syntax error.  The second value is the actual
  return value of the function.  To avoid redundancy the -MV forms of the
  functions are not documnented.

  To begin processing, use the function:

  (GET-OPTION-CHECK-SYNTAX ctx option-list valid-options duplicate-options
                           mutex-options) 

  (or GET-OPTION-CHECK-SYNTAX-MV) to check for basic option list syntax, and
  then use the various option list parsing functions listed above to get the
  values associated with the individual options.~/")

(defloop keyword-option-listp (l)
  ":doc-section get-option
  Checks a list for basic syntax as a keyword option list.
  ~/~/~/"
  (declare (xargs :guard t))
  (for ((x in l))
       (always (if (atom x)
		   (keywordp x)
		 (and (true-listp x)
		      (keywordp (car x)))))))

(defun reason-for-not-keyword-option-listp (l)
  "Completes the sentence `L is not a keyword option list because ..."
  (cond
   ((atom l) (if (null l)
		 (msg "BUG! BUG! BUG!")
	       (msg "it is not a proper list.")))
   ((atom (car l)) (if (keywordp (car l))
		       (reason-for-not-keyword-option-listp (cdr l))
		     (msg "the entry ~p0 is not a keyword." (car l))))
   ((and (keywordp (caar l)) (true-listp (car l)))
    (reason-for-not-keyword-option-listp (cdr l)))
   (t (msg "the entry ~p0 is not a proper list whose car is a keyword."
	   (car l)))))
  
(defloop get-option-keywords (l)
  ":doc-section get-option
  Strip the option keywords from a keyword option list.
  ~/~/~/"
  (declare (xargs :guard (keyword-option-listp l)))
  (for ((x in l)) (collect (if (atom x) x (car x)))))

(defloop get-option-entry (option l)
  ":doc-section get-option
  Returns the first occurrence of an option entry for option in l.
  ~/~/~/"
  (declare (xargs :guard (and (keywordp option)
			      (keyword-option-listp l))))
  (for ((x in l))
       (when (or (eq option x)
		 (and (consp x) (eq option (car x))))
	 (return x))))

(defloop get-option-entries (option l)
  ":doc-section get-option
  Returns all occurrences of option entries for option in l.
  ~/~/~/"
  (declare (xargs :guard (and (keywordp option)
			      (keyword-option-listp l))))
  (for ((x in l))
       (when (or (eq option x)
		 (and (consp x) (eq option (car x))))
	 (collect x))))

(defun get-option-check-mutex-mv (options mutex-options)
  (declare (xargs :guard (and (keyword-listp options)
			      (keyword-pair-alistp mutex-options))))
  (cond
   ((atom mutex-options) (mv NIL T))
   ((and (member (caar mutex-options) options)
	 (member (cdar mutex-options) options))
    (mv (msg "it contains the options ~p0 and ~p1 which are mutually ~
              exclusive." (caar mutex-options) (cdar mutex-options))
	NIL))
   (t (get-option-check-mutex-mv options (cdr mutex-options)))))

(defun get-option-check-syntax-mv
  (option-list valid-options duplicate-options mutex-options)

  (declare (xargs :guard (and (keyword-listp valid-options)
			      (keyword-listp duplicate-options)
			      (keyword-pair-alistp mutex-options))
		  :mode :program))
  (cond
   ((not (keyword-option-listp option-list))
    (mv (reason-for-not-keyword-option-listp option-list) NIL))
   (t
    (let* ((options (get-option-keywords option-list))
	   (dupes (duplicates options)))
      (cond
       ((not (subsetp options valid-options))
	(mv (msg "it contains the option~#0~[~/s~] ~&0 ~
                  which ~#0~[is~/are~] not ~
                  recognized.  The only recognized option~#1~[~/s~] ~
                  ~#1~[is~/are~] ~&1."
		 (set-difference-equal options valid-options)
		 valid-options)
	    NIL))
       ((not (subsetp dupes duplicate-options))
	(mv (msg "it contains duplicate occurrences of the ~
                  option~#0~[~/s~] ~&0. ~#1~[~
                  The only option~#2~[~/s~] which may be duplicated ~
                  ~#2~[is~/are~] ~&2.~/.~]"
		 (set-difference-equal duplicate-options dupes)
		 (if duplicate-options 0 1)
		 duplicate-options)
	    NIL))
       (t (get-option-check-mutex-mv options mutex-options)))))))

(defun get-option-check-syntax
  (ctx option-list valid-options duplicate-options mutex-options)
  ":doc-section get-option
  Check the option list for gross syntax, returning NIL if it's OK, and
  crashing otherwise.
  ~/
  The argument option-list is the option list entered by the user.
  Valid-options is a list of keywords that specifies which options are valid.
  Duplicate-options is a list of keywords which specifies which options may be
  duplicated.  Mutex-options is an alist of pairs (keyword1 . keyword2) which
  has the meaning `if keyword1 appears as an option then keyword2 may not
  appear as an option'.
  ~/~/"
  (declare (xargs :guard (and (keyword-listp valid-options)
			      (keyword-listp duplicate-options)
			      (keyword-pair-alistp mutex-options))
		  :mode :program))

  (mv-let (msg flag)
    (get-option-check-syntax-mv option-list valid-options duplicate-options
				mutex-options)
    (declare (ignore flag))
    (if msg
	(bomb ctx "The keyword option list ~p0 is invalid because ~@1"
	      option-list msg)
      nil)))

(defun get-option-as-flag-mv (option option-list)
  (declare (xargs :guard (and (keywordp option)
			      (keyword-option-listp option-list))))
  (let ((opt (get-option-entry option option-list)))
    (cond
     (opt
      (cond
       ((consp opt)
	(mv (msg "The ~p0 option descriptor may only be specified as ~p0, ~
                  thus ~p1 is illegal." option opt)
	    NIL))
       (t (mv NIL T))))
     (t (mv NIL NIL)))))

(defun get-option-as-flag (ctx option option-list)
  ":doc-section get-option
  Look for an stand-alone option, check the syntax, and return T if the 
  option is found and NIL otherwise.
  ~/
  This function is for options that take no arguments, where the simple 
  presence or absence of the option is meant to signal the user's intention.
  ~/~/"
  (declare (xargs :guard (and (keywordp option)
			      (keyword-option-listp option-list))
		  :mode :program))
  (mv-let (msg flag) (get-option-as-flag-mv option option-list)
    (if msg
	(bomb ctx "~@0" msg)
      flag)))

(defun get-option-member-mv
  (option option-list choices default-if-missing default-if-unspecified)
  (declare (xargs :guard (and (keywordp option)
			      (keyword-option-listp option-list)
			      (eqlable-listp choices))))
  (let ((opt (get-option-entry option option-list)))
    (cond
     (opt
      (cond
       ((or (atom opt) (atom (cdr opt))) (mv NIL default-if-unspecified))
       ((or (cddr opt)
	    (not (member (cadr opt) choices)))
	(mv (msg "The option specification ~p0 is illegal because the ~
                  ~p1 option requires at most one ~
                   argument which is one of ~v2."
		 opt option choices)
	    NIL))
       (t (mv NIL (cadr opt)))))
     (t (mv NIL default-if-missing)))))

(defun get-option-member
  (ctx option option-list choices default-if-missing default-if-unspecified)
  ":doc-section get-option
  Process an option whose (optional) argument is a MEMBER of a set of
  choices.
  ~/
  This function checks for an option that may be specified as either
  :OPTION, (:OPTION), or (:OPTION choice), where in the latter form the 
  choice must be a member of the set of choices.  The choice is returned if
  the option is specified by the latter form, otherwise the
  default-if-missing is returned if the option is not present in the
  option-list, and default-if-unspecified is returned if the option if
  specified as :OPTION or (:OPTION).
  ~/~/"
  (declare (xargs :guard (and (keywordp option)
			      (keyword-option-listp option-list)
			      (eqlable-listp choices))
		  :mode :program))
  (mv-let (msg value)
    (get-option-member-mv option option-list choices
			  default-if-missing default-if-unspecified)
    (if msg
	(bomb ctx "~@0" msg)
      value)))

(defun get-option-subset-mv (option option-list the-set default)
  (declare (xargs :guard (and (keywordp option)
			      (keyword-option-listp option-list)
			      (eqlable-listp the-set))
		  :verify-guards nil))
  (let ((opt (get-option-entry option option-list)))
    (cond
     (opt
      (cond
       ((or (atom opt)
	    (not (subsetp (cdr opt) the-set)))
        (mv (msg "The ~p0 option must be specified as ~p0 consed to a ~
                  true-list l, where l is a subset of the set whose ~
                  elements are ~&1. Thus ~p2 is illegal."
		 option the-set opt)
	    NIL))
       (t (mv NIL (cdr opt)))))
     (t (mv NIL default)))))

(defthm true-listp-cdr-get-option-entry
  (implies (keyword-option-listp option-list)
	   (acl2::true-listp (cdr (get-option-entry option option-list)))))

(verify-guards get-option-subset-mv)

(defun get-option-subset (ctx option option-list the-set default)
  ":doc-section get-option
  Process an option of the form (:OPTION . l), where l must be a SUBSETP
  of a given set.
  ~/
  This function checks for an option that is specified as (:OPTION . l),
  where l must be a proper list and a SUBSETP of the-set. Thus (:OPTION)
  specifies the empty set, and :OPTION by itself is illegal.  If the option
  is missing then the default value is returned, otherwise the subset l
  is returned.
  ~/~/"
  (declare (xargs :guard (and (keywordp option)
			      (keyword-option-listp option-list)
			      (eqlable-listp the-set))
		  :mode :program))

  (mv-let (msg value)
    (get-option-subset-mv option option-list the-set default)
    (if msg
	(bomb ctx "~@0" msg)
      value)))

(defun get-option-argument-mv
  (option option-list kind default-if-missing default-if-unspecified)
  (declare (xargs :guard (and (keywordp option)
			      (keyword-option-listp option-list)
			      (member kind '(:FORM :SYMBOL :STRING
						   :STRING-DESIGNATOR)))))
  (let ((opt (get-option-entry option option-list)))
    (cond
     (opt
      (cond
       ((or (atom opt) (atom (cdr opt))) (mv NIL default-if-unspecified))
       ((or (cddr opt)
	    (case kind
	      (:SYMBOL (not (symbolp (cadr opt))))
	      (:STRING (not (stringp (cadr opt))))
	      (:STRING-DESIGNATOR (not (string-designator-p (cadr opt))))
	      (t nil)))
	(mv (msg "The option specification ~p0 is illegal because the ~p1 ~
                  option requires at most 1 argument~@2."
		 opt option (case kind
			      (:SYMBOLP " which must be a symbol")
			      (:STRING " which must be a string")
			      (:STRING-DESIGNATOR " which must be a symbol, ~
                                               string, or character")
			      (t "")))
	    NIL))
       (t (mv NIL (cadr opt)))))
     (t (mv NIL default-if-missing)))))

(defun get-option-argument
  (ctx option option-list kind default-if-missing default-if-unspecified)
  ":doc-section get-option
  Process an option of the form :OPTION, (:OPTION), or (:OPTION arg),
  where arg is required to be of a certain type.
  ~/
  This function checks for an option that in the full form is specified as
  (:OPTION arg), where arg must be of a certain kind.  Recognized values
  for kind include:

  :FORM              -- arg can be anything.
  :SYMBOL            -- arg must be a symbol.
  :STRING            -- arg must be a string.
  :STRING-DESIGNATOR -- arg must be a symbol, string, or character.

  If the option is missing from the option-list, then default-if-missing
  is returned.  If the option is specified as :OPTION or (:OPTION), then
  default-if-unspecified is returned.  Otherwise the arg is returned.
  ~/~/"

  ;;  It's easy to add new `kind's.  Just update the guards and the CASE
  ;;  statements here and in GET-OPTION-ARGUMENT-MV. Don't forget to update
  ;;  the documentation as well.

  (declare (xargs :guard (and (keywordp option)
			      (keyword-option-listp option-list)
			      (member kind '(:FORM :SYMBOL :STRING
						   :STRING-DESIGNATOR)))
		  :mode :program))

  (mv-let (msg value)
    (get-option-argument-mv option option-list kind
			    default-if-missing default-if-unspecified)
    (if msg
	(bomb ctx "~@0" msg)
      value)))


;;;****************************************************************************
;;;
;;;    Strings and Symbols
;;;
;;;****************************************************************************

(defmacro naturalp (x)
  `(AND (INTEGERP ,x)
	(<= 0 ,x)))

(defloop string-designator-listp (l)
  "Recognizes lists of STRING-DESIGNATOR-P objects."
  (declare (xargs :guard t))
  (for ((x in l)) (always (string-designator-p x))))

(defloop mapcar-string (l)
  "STRING each element of l."
  (declare (xargs :guard (string-designator-listp l)))
  (for ((sd in l)) (collect (string sd))))

(defloop coerce-string-designator-list (l)
  "Coerce a list of string-designators to a list of characters."
   (declare (xargs :guard (string-designator-listp l)))
   (for ((sd in l)) (append (coerce (string sd) 'LIST))))

(defmacro pack-string (&rest l)
  ":doc-section utilities
   Given a series of string-designators l, append the STRING of each and return
   the resulting string.
   ~/~/~/"
   `(COERCE (COERCE-STRING-DESIGNATOR-LIST (LIST ,@l)) 'STRING))

(defmacro pack-intern (sym &rest l)
  ":doc-section utilities
   Given a list of string-designators l, append the STRING of each and intern
   the resulting string in the package of sym.
   ~/~/~/"
   `(INTERN-IN-PACKAGE-OF-SYMBOL (PACK-STRING ,@l) ,sym))

(defun unique-symbols1 (n seed sym-list counter gen-list)
  (declare (xargs :guard (and (naturalp n)
			      (symbolp seed)
			      (symbol-listp sym-list)
			      (naturalp counter))
		  :mode :program))
  (cond
   ((equal n 0) gen-list)
   (t (let ((sym (pack-intern
		  seed seed (coerce (explode-nonnegative-integer counter 10 ())
				    'string))))
	(cond
	 ((member sym sym-list)
	  (unique-symbols1 n seed (remove sym sym-list) (1+ counter)
			     gen-list))
	 (t (unique-symbols1 (1- n) seed sym-list (1+ counter)
			       (cons sym gen-list))))))))

(defun unique-symbols (n seed sym-list)
  ":doc-section utilities
  Return a list of symbols guaranteed unique with respect to a symbolic
  seed and every symbol in a list of symbols.
  ~/
  Given a symbolic seed, we generate symbols <seed>0, <seed>1, etc. until
  we have generated n symbols not appearing in sym-list.  This is a 
  `poor-man's' GENSYM, and is the best we can do without STATE.  All
  generated symbols are INTERNed in the package of seed.
  ~/~/"
  (declare (xargs :guard (and (naturalp n)
			      (symbolp seed)
			      (symbol-listp sym-list))
		  :mode :program))
  (reverse (unique-symbols1 n seed sym-list 0 ())))


;;;****************************************************************************
;;;
;;;    GET-GUARDS-FROM-BODY
;;;
;;;****************************************************************************

(defloop force-term-list (l)
  "Given a list of terms, `FORCE' each term."
  (for ((x in l)) (collect `(ACL2::FORCE ,x))))

(defloop get-guards-from-declare-body (declare-body)
  "This is similar to ACL2::GET-GUARDS-1, but is believed to be `fail-safe'."
  (declare (xargs :mode :program))
  (for ((form in declare-body))
       (append
	(cond
	 ((and (true-listp form)
	       (eq (car form) 'ACL2::XARGS)
	       (keyword-value-listp (cdr form)))
	  (let ((temp (assoc-keyword :GUARD (cdr form))))
	    (if temp (list (cadr temp)) nil)))
	 ((and (true-listp form)
	       (equal (car form) 'ACL2::TYPE)
	       (cadr form)
	       (cddr form)
	       (symbol-listp (cddr form)))
	  (translate-declaration-to-guard-var-lst (cadr form) (cddr form) nil))
	 (t ())))))

(defloop get-guards-from-body1 (body)
  (declare (xargs :mode :program))
  (for ((form in body))
       (when (and (true-listp form)
		  (eq (car form) 'ACL2::DECLARE))
	 (append (get-guards-from-declare-body (cdr form))))))
  
(defun get-guards-from-body (body)
  ":doc-section utilities
  A user-level function to extract guards from a definition body.
  ~/
  This function takes a definition body, that is, a list of forms valid as
  the body of a DEFUN, and returns a guard for the DEFUN that consists of all
  guards specified either by (DECLARE (XARGS ... :GUARD g ...)) or (DECLARE
  (TYPE ...)) forms in body. This function is designed to be used by macros
  that create function definitions and lemmas that may depend on the guards
  of the newly defined function.  The guard will be returned as a
  conjunction: either T, NIL (?) a single conjunct, or (AND . conjuncts)
  where conjuncts is a list of the conjuncts.
  ~/
  Restrictions on the form of macros in Acl2 make it impossible for a macro
  to query the Acl2 database to determine any property of a function,
  including its guards. Therefore we provide this function which parses
  function bodies and extracts the guards from the source text of a function.

  This is a `fail-safe' procedure.  If any syntax errors are encountered
  during guard parsing, those illegal guard specifications are simply
  ignored, under the assumption that when the function is finally submitted
  to Acl2 that Acl2's more powerful error checking facilities will uncover
  and report the errors to the user.  Thus this routine may return garbage,
  but it shouldn't crash!~/"

  (declare (xargs :mode :program))

  (untranslate (conjoin (get-guards-from-body1 body)) nil nil))
