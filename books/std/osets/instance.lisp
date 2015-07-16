; Fully Ordered Finite Sets
; Copyright (C) 2003-2012 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>


; instance.lisp
;
; This is a system for dynamically instantiating ACL2 "theories" (which are
; represented as constants) to create new, concrete "theories".

; BOZO this whole file is probably subsumed by something better, in the
; make-event era.

(in-package "INSTANCE")


; Everything in this file is in program mode.  We do not intend to reason about
; these functions -- instead, we intend to use these functions to create new
; functions, which the user will reason about.

(program)


; Introduction
;
;
; The following work has been motivated by my work with quantification over
; sets.  When I started on this file, I had roughly 2000 lines of complicted
; macros in order to be able to instantiate generic and concrete theories for
; this work, and it was just becoming unmanageable.  My hope was that rewriting
; the definitions and theorems into concrete forms would provide a more concise
; way of instantiating the theory, and make it easier to keep everything
; consistent.
;
; Originally, I wanted to extract the definitions for generic functions from
; ACL2's state (well, actually from the current world).  But, to do so becomes
; very complicated, because of the restrictions on macros that they cannot take
; state as a parameter.  So, the best that I could ever accomplish that way
; would be to display a list of events, which a user could copy into a file.
; But, that is wholly unsatisfying, because it would mean that the resulting
; theories could never be "automagically" updated when new theorems are added
; to the generic theory.
;
; So, instead of doing things that way, I now simply store events in constants.
; These constants can then be rewritten to create new but related theories.
;
; A first step towards this is to introduce a simple rewriter.  Originally I
; had based my rewriter on the built in one-way-unify function in ACL2, but it
; operates only on pseudo-terms, and pseudo-terms cannot contain atoms other
; than symbols.  This gave me serious trouble when trying to rewrite theorems
; involving constants, e.g., to say that something was an integerp and greater
; than zero.  So, instead of using one-way-unify, I introduce a simple
; unification algorithm which has been adapted from Warren Hunt's work.

; The system treats all symbols beginning with a ? as variables, and all other
; atoms as literals.

(defun instance-variablep (x)
  (and (symbolp x)
       (equal (car (explode-atom x 10)) #\?)))



; We return two values: a boolean flag which indicates if we are successful in
; finding a match, and a list of substitutions of the form (variable . value).
; This is all be fairly standard stuff.
;
; For example:
;
;    (instance-unify-term '(predicate ?x) '(predicate (car a)) nil)
;    ==>
;    (t ((?x . (car a))))

(mutual-recursion

  (defun instance-unify-term (pattern term sublist)
    (if (atom pattern)
	(if (instance-variablep pattern)
	    (let ((value (assoc pattern sublist)))
	      (if (consp value)
		  (if (equal term (cdr value))
		      (mv t sublist)
		    (mv nil nil))
		(mv t (acons pattern term sublist))))
	  (if (equal term pattern)
	      (mv t sublist)
	    (mv nil nil)))
      (if (or (atom term)
	      (not (eq (car term) (car pattern))))
	  (mv nil nil)
	(if (or (eq (car term) 'quote)
		(eq (car pattern) 'quote))
	    (if (equal term pattern)
		(mv t sublist)
	      (mv nil nil))
	  (instance-unify-list (cdr pattern) (cdr term) sublist)))))

  (defun instance-unify-list (pattern-list term-list sublist)
    (if (or (atom term-list)
	    (atom pattern-list))
	(if (and (atom term-list)
		 (atom pattern-list))
	    (mv t sublist)
	  (mv nil nil))
      (mv-let (successp new-sublist)
	      (instance-unify-term (car pattern-list)
				   (car term-list)
				   sublist)
	      (if successp
		  (instance-unify-list (cdr pattern-list)
				       (cdr term-list)
				       new-sublist)
		(mv nil nil)))))
)


; After a list of substitutions has been generated, we typically want to apply
; them to a term.  We recur over the list of substitutions, simply calling
; subst to do our work throughout a term.
;
; For example:
;
;   (instance-substitute '((?x . (car a))) '(not (predicate ?x)))
;   ==>
;   (not (predicate (car a)))

(defun instance-substitute (sublist term)
  (if (endp sublist)
      term
    (let* ((old (car (car sublist)))
           (new (cdr (car sublist)))
	   (result (subst new old term)))
      (instance-substitute (cdr sublist) result))))



; We now introduce our actual rewriter.  We take three arguments: pat is the
; pattern to look for throughout the term, e.g., (predicate ?x), repl is the
; replacement to use, e.g., (not (predicate ?x)), and term is the term to match
; the pattern against in order to get the substitutions.
;
; For Example:
;
;   (instance-rewrite1 '(predicate ?x)
;                      '(not (predicate ?x))
;                      '(if (predicate (car x)) t nil))
;   =>
;   (if (not (predicate (car x))) t nil)

(mutual-recursion

  (defun instance-rewrite1 (pat repl term)
    (mv-let (successful sublist)
            (instance-unify-term pat term nil)
	    (if successful
		(instance-substitute sublist repl)
	      (if (atom term)
		  term
		(cons (instance-rewrite1 pat repl (car term))
		      (instance-rewrite-lst1 pat repl (cdr term)))))))

  (defun instance-rewrite-lst1 (pat repl lst)
    (if (endp lst)
        nil
      (cons (instance-rewrite1 pat repl (car lst))
            (instance-rewrite-lst1 pat repl (cdr lst)))))
)



; Finally, given that we can apply a rewrite a term with a single replacement,
; we go ahead and extend this notion to multiple replacements.  In other words,
; we walk through a list of substitutions, sequentially rewriting the term
; using each substitution.

(defun instance-rewrite (term subs)
  (if (endp subs)
      term
    (let ((first-sub (car subs)))
      (instance-rewrite (instance-rewrite1 (first first-sub)
					   (second first-sub)
					   term)
			(cdr subs)))))




; Instantiating Defuns
;
;
; Theories consist mainly of definitions and theorems.  Given generic theorems,
; we will want to rewrite them so that they perform different functions.  For
; example, a generic "all" function might need to be rewritten so that its
; calls to (predicate x) are replaced with calls to (not (predicate x)) for all
; x.
;
; To begin, we instantiate the function's declarations (e.g., comment strings,
; xargs, ignores, and so forth).  We simply duplicate comment strings, but for
; declare forms we allow rewriting to occur.

(defun instance-decls (decls subs)
  (if (endp decls)
      nil
    (if (pseudo-termp (car decls))
	(cons (instance-rewrite (car decls) subs)
	      (instance-decls (cdr decls) subs))
      (cons (car decls)
	    (instance-decls (cdr decls) subs)))))


; For the defun itself, we retain the same defun symbol (e.g., defun or
; defund), but we change the name and args of the function by first creating
; the list '(oldname oldarg1 oldarg2 ...) then applying our substitutions to
; the new function.
;
; As a trivial example,
;  (instance-defun '(defun f (x) (+ x 1)) '(((f x) (g x))))
;    =>
;  (defun g (x) (+ x 1))

(defun instance-defun (defun subs)
  (let* ((defun-symbol  (first defun))
 	 (defun-name    (second defun))
	 (defun-args    (third defun))
         (defun-decls   (butlast (cdddr defun) 1))
	 (defun-body    (car (last defun)))
	 (name/args     (cons defun-name defun-args))
	 (new-body      (instance-rewrite defun-body subs))
	 (new-name/args (instance-rewrite name/args subs))
	 (new-decls     (instance-decls defun-decls subs))
	 (new-name      (car new-name/args))
	 (new-args      (cdr new-name/args)))
    `(,defun-symbol
       ,new-name ,new-args
       ,@new-decls
       ,new-body)))

; We also provide a convenience function that allows you to instance a list of
; defuns.

(defun instance-defuns (defun-list subs)
  (if (endp defun-list)
      nil
    (cons (instance-defun (car defun-list) subs)
	  (instance-defuns (cdr defun-list) subs))))



; Renaming theorems

(defun defthm-names (event-list)
  (if (endp event-list)
      nil
    (let* ((first-event (car event-list))
	   (event-type  (first first-event)))
      (cond ((or (eq event-type 'defthm)
		 (eq event-type 'defthmd))
	     (cons (second first-event)
		   (defthm-names (cdr event-list))))
	    ((eq event-type 'encapsulate)
	     (append (defthm-names (cddr first-event))
		     (defthm-names (cdr event-list))))
	    (t (defthm-names (cdr event-list)))))))

(defun create-new-names (name-list suffix)
  (if (endp name-list)
      nil
    (acons (car name-list)
	   (intern-in-package-of-symbol (string-append (symbol-name (car name-list))
						       (symbol-name suffix))
					suffix)
	   (create-new-names (cdr name-list) suffix))))

(defun rename-defthms (event-list suffix)
  (sublis (create-new-names (defthm-names event-list) suffix)
	  event-list))



; Instantiating Theorems
;
;
; To instantiate defthms, we will want to be able to provide functional
; instantiations of the generic theory.  This is much more complicated than
; instancing definitions, and involves:
;
;   a) determining what functional substitutions to make
;   b) determining the theory in which to conduct the proofs
;   c) handling rule classes and other optional components
;   d) generating the actual defthm event
;
; My idea is essentially that if a substitution list can be used for
; functionally instantiating theorems, then it can also be used for creating
; the new theorem.
;
; (a) Determining what functional substitutions to make.
;
; I pass in a list of substitutions of the following form.
;
;   (((predicate ?x)  (not (in ?x y)))
;    ((all ?x)        (all-not-in ?x y))
;    ((exists ?x)     (exists-not-in ?x y)))
;
; From this list we can generate the functional instantiation hints.  So, for
; example, we simply convert ((predicate ?x) (not (in ?x y))) into the
; substitution:
;
;   (predicate (lambda (?x) (not (in ?x y))))
;
; This is easy to do with the following functions:

(defun sub-to-lambda (sub)
  (let ((term (first sub))
	(repl (second sub)))
    (let ((function-symbol (car term))
	  (lambda-args (cdr term)))
      `(,function-symbol (lambda ,lambda-args ,repl)))))

(defun subs-to-lambdas (subs)
  (if (endp subs)
      nil
    (cons (sub-to-lambda (car subs))
	  (subs-to-lambdas (cdr subs)))))


; (b) Determining the theory in which to conduct the proofs.
;
; When we prove the functional instantiation constraints, ideally we should
; work in an environment where the only definitions that are enabled are the
; definitions used in the functional instantiation hints.
;
; Well, the definitions we need are (almost) simply all of the function symbols
; in the right-hand side of the substitution list.  In other words, for the
; above substitutions, I would want to have the definitions of not, in,
; all-not-in, and exists-not-in available.
;
; Now, the problem with this approach is, what if those symbols don't have
; definitions?  This can occur if, for example, we are using a constrained
; function in the substitution list.  This is actually useful, e.g., for
; substituting (predicate ?x) -> (not (predicate ?x)).
;
; My solution is a stupid hack.  We simply pass in the names of the generic
; functions for which we do not want to generate definitions along with the
; substitutinos.
;
; To begin, the following function will extract all function symbols that occur
; within a term.

(mutual-recursion

  (defun term-functions (term)
    (if (atom term)
        nil
      (cons (car term)
	    (term-list-functions (cdr term)))))

  (defun term-list-functions (list)
    (if (endp list)
	nil
      (append (term-functions (car list))
	      (term-list-functions (cdr list)))))
)

; Next, I wrote the following function, which walks over the substitution list
; and extracts the function symbols from each right hand side, using
; term-functions.  The net result is the list of all functions that were used
; in replacements.

(defun subs-repl-functions (subs)
  (if (endp subs)
      nil
    (let* ((sub1 (car subs))
	   (repl (second sub1)))
      (append (term-functions repl)
	      (subs-repl-functions (cdr subs))))))

; Given the above, we could then convert the list of function symbols into a
; list of (:definition f)'s with the following function.  We now use :d instead
; of :definition to better support macro aliases.

(defun function-list-to-definitions (funcs)
  (if (endp funcs)
      nil
    (cons `(:d ,(car funcs))
	  (function-list-to-definitions (cdr funcs)))))

; And finally, here is a function that does "all of the work", calling
; function-list-to-definitions for all of the functions found in the
; substitution list, minus all of the generic functions that we don't want to
; generate :definition hints for.

(defun subs-to-defs (subs generics)
  (let* ((all-fns (subs-repl-functions subs))
	 (real-fns (set-difference-eq all-fns generics)))
    (function-list-to-definitions real-fns)))


; (c) Handling rule classes and other optional components.
;
; We are interested in several parts of a defthm.  In addition to the
; conjecture itself, we need to consider the rule-classes used by the theorem,
; and the other optional attributes such as the :hints, :doc, :otf-flg, etc.
; We parse these attributes into a five-tuple of pairs of the form (present
; . value), where present is a boolean that says whether or not the flag has
; been seen, value is its value, and the order of the elements is rule-classes,
; instructions, hints, otf-flg, and finally doc.  We parse these options with
; the following code:

(defconst *default-parse-values*
  '((nil . nil) (nil . nil) (nil . nil) (nil . nil) (nil . nil)))

(defun parse-defthm-option (option return-value)
  (cond ((equal (first option) :rule-classes)
         (update-nth 0 (list t (second option)) return-value))
	((equal (first option) :instructions)
	 (update-nth 1 (list t (second option)) return-value))
	((equal (first option) :hints)
	 (update-nth 2 (list t (second option)) return-value))
	((equal (first option) :otf-flg)
	 (update-nth 3 (list t (second option)) return-value))
	((equal (first option) :doc)
	 (update-nth 4 (list t (second option)) return-value))
	(t (er hard "Unknown flag in defthm options ~x0." (first option)))))

(defun parse-defthm-options (options return-value)
  (if (endp options)
      return-value
    (parse-defthm-options (cddr options)
			  (parse-defthm-option options return-value))))


; (d) Generating the actual defthm event.
;
; When we are ready to instance a defthm event, we combine the above work with
; a few new things.  First of all, we need the original theorem event, a new
; name to use, the substitutions to use, and the list of generic function
; symbols in use so that we do not create (:definition f) entries for them.
;
; We begin by making our substitutions in the body of the theorem.  We then
; parse the optional components of the defthm, but we only are interested in
; the rule-classes.  (Hints, instructions, and otf-flg will not be needed,
; because we will be proving this via functional instantiation.  Doc we ignore
; for no good reason.)  We construct a new theorem that has our new name and
; body, replicating the rule classes if necessary.  We also provide a
; functional instantiation hint of the generic theorem's name, along with a
; list of lambda substitutions to make.

(defun instance-defthm (event new-name subs generics extra-defs)
  (let* ((defthm-symbol (first event))
	 (defthm-name   (second event))
	 (defthm-body   (third event))
	 (new-body      (instance-rewrite defthm-body subs))
	 (options       (parse-defthm-options (cdddr event)
					      *default-parse-values*))
	 (rc-opt        (first options)))
    `(,defthm-symbol ,new-name
       ,new-body
       :hints(("Goal"
	       :use (:functional-instance ,defthm-name
					  ,@(subs-to-lambdas subs))
	       :in-theory (union-theories (theory 'minimal-theory)
			   (union-theories ',extra-defs
					   ',(subs-to-defs subs generics)))))
       ,@(if (car rc-opt) `(:rule-classes ,(cdr rc-opt)) nil))))



; Instantiating Encapsulates
;
;
; There are two reasons that I typically use encapsulation.  The first is as a
; purely structural/organizational purpose, where I am trying to prove some
; theorem is true, but I need some lemmas to do so.  In this case I use an
; (encapsulate nil ...) and wrap my lemmas in local forms.  The other reason is
; to actually go ahead and introduce constrained functions.
;
; Two strategies will be necessary for handling these situations.  In
; particular, if we are in an encapsulate which has no constrained function
; symbols, we will want to skip all local events and only add the non-local
; events (using functional instantiation to create the theorems).  On the other
; hand, for the case when we are introducing constrained functions, we will
; want to introduce new constrained functions based on the encapsulate.
;
; So, encapsulates are handled separately based on whether or not any functions
; are constrained.
;
; Within an (encapsulate nil ...), local events will be skipped and defthm
; events will be proven using the functional instantiation of their generic
; counterparts.
;
; Within an (encapsulate (...) ...), local events will not be skipped but will
; instead be reintroduced with new names.  Further, defthm events will be
; copied using new names and will not be proven using functional instantiation.
;
; The only "extra" thing we really need for handling encapsulates is a system
; to make the substitutions within the signatures.  We do that here by simple
; rewriting.  Note that we do not allow the number of return values to change.
; I don't really think of this as a major limitation, since almost always my
; constrained functions return a single value.  If you have an example of where
; this would be useful, it would be interesting to see it.

(defun instance-signature (signature subs)
  (let ((name (first signature))
	(rest (rest signature)))
    (cons (instance-rewrite subs name) rest)))

(defun instance-signatures (signatures subs)
  (if (endp signatures)
      nil
    (cons (instance-signature (car signatures) subs)
	  (instance-signatures (cdr signatures) subs))))

; Because encapsulates can contain many events within them, it is natural to
; make them mutually recursive with the main event list handler, which we are
; now ready to introduce.





; Instantiating Entire Theories
;
;
; We are now ready to introduce the functions which will walk through a theory
; and call the appropriate instancing functions on each of the forms we
; encounter.  To support encapsulation, our functions here are all mutually
; recursive.
;
; The arguments that we pass around are the following:
;
;   - The event or event list to instantiate
;
;   - The global list of substitutions used to derive the instance
;
;   - A suffix which will be appended to generate new names
;
;   - A list of generic functions which have no definitions
;
;   - A mode, which is either 'constrained to indicate that the nearest
;     encapsulate event has constrained functions, or is nil to indicate that
;     the nearest encapsulate is merely a structural wrapper for local lemmas.
;
; Finally, we overload our behavior based on suffix, so that if no suffix is
; given, we simply replicate the generic theory instead of instantiating a
; concrete instance of it.


(mutual-recursion

  (defun instance-event (event subs suffix generics mode extra-defs)
    (if (null suffix)
	event
      (cond ((or (eq (car event) 'defun)
		 (eq (car event) 'defund))
	     (instance-defun event subs))
	    ((or (eq (car event) 'defthm)
		 (eq (car event) 'defthmd))
	     (let* ((name (second event))
		    (new-name (intern-in-package-of-symbol
			       (acl2::string-upcase
				(concatenate 'string
					     (symbol-name name)
					     (symbol-name suffix)))
			       suffix)))
	       (instance-defthm event new-name subs generics extra-defs)))
	    ((equal (car event) 'local)
	     (if (eq mode 'constrained)
		 (instance-event (second event) subs suffix generics mode extra-defs)
	       nil))
	    ((equal (car event) 'encapsulate)
	     (instance-encapsulate event subs suffix generics mode extra-defs))
	    (t (er hard "Don't know how to handle ~x0" (car event))))))

  (defun instance-event-list (events subs suffix generics mode extra-defs)
    (if (endp events)
	nil
      (let ((first (instance-event (car events) subs suffix generics mode extra-defs))
	    (rest  (instance-event-list (cdr events) subs suffix generics mode extra-defs)))
	(if first
	    (cons first rest)
	  rest))))

  (defun instance-encapsulate (event subs suffix generics mode extra-defs)
    (declare (ignore mode))
    (let* ((signatures (second event))
	   (new-sigs   (if signatures
			   (instance-signatures subs signatures)
			 nil))
	   (new-events (instance-event-list (cddr event) subs suffix generics
					    (if signatures
						'constrained
					      nil)
					    extra-defs)))
      `(encapsulate ,new-sigs ,@new-events)))

)


; To be able to actually introduce the events, we need to emit a macro that can
; be used to actually perform substitutions.

(defmacro instance (theory)
  (let ((macro-name (intern-in-package-of-symbol
		     (acl2::string-upcase (concatenate 'string
                                                       "instance-" (string theory)))
		     theory)))
    `(defmacro ,macro-name (&key subs suffix generics extra-defs)
       (list* 'encapsulate
	      nil
	      (instance-event-list ,theory subs suffix generics nil extra-defs)))))




; Some thoughts
;
; A fundamental issue seems to be that a function and its arguments are not
; always used in a consistent manner.  For example, say we want to rewrite (all
; ?x) to (all-foo ?x y) and we want to rewrite (predicate ?x) to (not (foo ?x
; y)).  How can we accurately say just what it is that we want to rewrite in
; each case?
;
; Right now our substitutions are based on
;  ( (predicate ?x)  (not (foo ?x y)) )
;  ( (all ?x)        (all-foo ?x y) )
;
; We can easily pick out and say "all" is replaced by "all-foo", but if we try
; to just use the car of the term as its symbol replacement, then "predicate"
; would be "not".
;
; OK, so we could do some kind of preprocessing step where we fill in argument
; guards.  The "generics" list right now is a big huge hack that allows us to
; ignore the fact that :predicate doens't have a definition.  Really the issue
; that this is trying to solve is to tell us how to build our :in-theory event.
; Right now the :in-theory event is just a hack that we don't really
; understand.
