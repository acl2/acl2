; Fully Ordered Finite Sets, Version 0.9
; Copyright (C) 2003, 2004 Kookamara LLC
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
;
; computed-hints.lisp
;
;   We provide support for the development of "pick a point" style
;   proofs through computed hints.

(in-package "COMPUTED-HINTS")

;;; Introduction
;;;
;;; Suppose we have some predicate, P, of any number of arguments.  A
;;; natural operation is to extend this predicate to every element of
;;; a list, set, or other collection.  In other words, we would like
;;; to know if every element in the set, list, tree, or whatever has
;;; the property when applied to arguments.
;;;
;;; For example, we might have the predicate:
;;;
;;;  (defun integer-lessp (a b)
;;;    (and (integerp a)
;;;         (< a b)))
;;;
;;; We could now extend this concept to an entire list, to ask if
;;; every element in the list was an integer that is less than b.  The
;;; function might be written as:
;;;
;;;  (defun list-integer-lessp (a-list b)
;;;    (declare (xargs :guard (true-listp a-list)))
;;;    (or (endp a-list)
;;;        (and (integer-lessp (car a-list) b)
;;;             (list-integer-lessp (cdr a-list) b))))
;;;
;;; Similarly, we might want to map the function across sets or other
;;; types of collections.
;;;
;;; Take an abstract mathematical view for a moment.  Given some
;;; predicate P, what we would really like to do is be able to express
;;; the idea that given some collection x, every element of x
;;; satisfies P.  In other words, we want to define:
;;;
;;;  (collection-P x [args]) = forall a in x, (P x [args])
;;;
;;; And indeed, it would be nice to be working with this very abstract
;;; mathematical definition, for which we will not need to make
;;; inductive arguments.  Unfortunately, because all variables in
;;; ACL2's rewrite rules are implicitly universally quantified, we
;;; cannot express the above as a rewrite rule.
;;;
;;; However, through the use of constrained function symbols and
;;; functional instantiation, we can effectively accomplish the above
;;; reduction when it suits our purposes.  And, the process can be
;;; automated through the use of computed hints.  Overall, this is not
;;; as nice as working with a pure rewrite rule, and in fact has some
;;; unfortunate limitations.  However, it does turn out to be very
;;; broadly applicable and invaluable for reasoning about set
;;; theoretic concepts, where concepts such as "subset" are really
;;; nothing more than the extension of the predicate "in" across a
;;; set.
;;;
;;; Moreover, the reduction that we set out to achieve will reduce
;;; (collection-P x [args]) to the following implication:
;;;
;;;   (implies (in a x)
;;;            (P a [args]))
;;;
;;; I call this a "pick a point" reduction, because it is similar to
;;; and takes its inspiration from the well known set theoretic
;;; technique of picking an arbitrary element (or point) in one set,
;;; then showing it is also a member of another set.



;;; Preliminaries
;;;
;;; We will make minor use of the rewriting system developed in
;;; instance.lisp.  We also enter program mode, because we are not
;;; interested in reasoning about these functions.

(include-book "instance")
(program)


;;; Tagging
;;;
;;; Suppose that we have (collection-P x a0 a1 ... an)  to a simpler
;;; argument.  We begin by defining a synonym for collection-P, e.g.,
;;;
;;; (defun collection-P-tag (x a0 a1 ... an)
;;;   (collection-P x a0 a1 ... an))
;;;
;;; Now we instruct the theorem prover to rewrite instances of
;;; conclusion into conclusion-tag, as long as we are not backchaining
;;; and as long as conclusion occurs as the goal.  For example,
;;;
;;; (defthm tagging-theorem
;;;   (implies
;;;     (and (syntaxp (rewriting-goal-lit mfc state))
;;;          (syntaxp (rewriting-conc-lit `(collection-P ,x ,a0 ... ,an)
;;;                                       mfc state)))
;;;            (equal (collection-P x a0 ... an)
;;;                   (collection-P-tag x a0 ... an))))
;;;
;;; This theorem is trivial to prove, since collection-P-tag is merely
;;; a synonym for collection-P.  After the theorem is proven,
;;; collection-P-tag should be disabled.

(defun rewriting-goal-lit (mfc state)
  (declare (xargs :stobjs state)
	   (ignore state))
  (null (mfc-ancestors mfc)))

(defun rewriting-conc-lit (term mfc state)
  (declare (xargs :stobjs state)
	   (ignore state))
  (let ((clause (mfc-clause mfc)))
    (member-equal term (last clause))))




;;; Computing a Hint
;;;
;;; Now, what we are going to do next is create a computed hint that
;;; will look for instances of a trigger, and if it sees one, we will
;;; try to provide a functional instantiation hint.  This takes some
;;; work.  Our computed hint function is called as ACL2 is working to
;;; simplify terms, and it is allowed to examine the current clause.
;;; The current clause will be a a disjunction of literals.  For
;;; example,
;;;
;;;   (a ^ b ^ ...) => P  is  (~a v ~b v ... v P)
;;;   (a v b v ...) => P  is  subgoal1: (~a v P), sg2: (~b v P), ...
;;;
;;; Our first step is to see if our computed hint should even be
;;; applied to this clause.  We only allow the hint to be applied if
;;; the current clause is stable under simplification, i.e., if other
;;; attempts to prove it have failed.  At that point, we check the
;;; clause to see if our trigger occurs as a term within it.  If so,
;;; the tagging theorem has applied and thinks we should try to use
;;; our computed hint!
;;;
;;; We check for the existence of our trigger using the following
;;; function, (harvest-trigger clause trigger-fn), which extracts all
;;; the terms from clause whose function symbol is trigger-fn, and
;;; returns them as a list.
;;;
;;; Now, our intention is to functionally instantiate the theorem in
;;; question.  To do this, we need to provide values for the
;;; hypotheses and arguments a0 ... an.
;;;
;;; In order to recover the hypotheses, we first remove from the
;;; clause all of our trigger terms.  We then negate each of the
;;; remaining literals as they occur in the clause.  And, if there are
;;; more than one of them, we are going to AND their negations
;;; together.  This is done by the functions others-to-negated-list,
;;; and others-to-hyps.
;;;
;;; For example, if we originally had the conjecture (a ^ b ^ ...) =>
;;; P Then this became the clause: (~a v ~b v ... v P), which is
;;; represented by the list ((not a) (not b) ... P).  Suppose that P
;;; was our trigger term.  We remove P from the clause, yielding ((not
;;; a) (not b) ...), and then we negate all of these literals,
;;; creating the list (a b ...).  We now and these together, creating
;;; the the term (and a b ...), which was our original hypotheses!

(defun harvest-trigger (clause trigger-fn)
  (if (endp clause)
      nil
    (if (eq (caar clause) trigger-fn)
        (cons (car clause) (harvest-trigger (cdr clause) trigger-fn))
      (harvest-trigger (cdr clause) trigger-fn))))

(defun others-to-negated-list (others)
  (if (endp others)
      nil
    (if (equal (caar others) 'not)  ; don't create ugly double not's
        (cons (second (car others))
              (others-to-negated-list (cdr others)))
      (cons (list 'not (car others))
            (others-to-negated-list (cdr others))))))

(defun others-to-hyps (others)
  (if (endp others)
      t
    (let ((negated (others-to-negated-list others)))
      (if (endp (cdr negated))  ; don't wrap single literals in and's
          (car negated)
        (cons 'and (others-to-negated-list others))))))



;;; Absolute Restrictions:
;;;
;;; Collection predicate must have a first argument which is the
;;; collection to traverse!!
;;;
;;; Need to be able to create hint for predicate as well.



;;; Building Hints
;;;
;;; Our ultimate goal now is to be able to create functional
;;; instantiation hints for each trigger which was found.  In other
;;; words, we now have a set of triggers which look like the following:
;;;
;;;  ((collection-P-tag col1 [extra-args1])
;;;   (collection-P-tag col2 [extra-args2])
;;;    ...)
;;;
;;; We want to instantiate generic theorems of the form:
;;;
;;;   (defthm generic-theorem
;;;     (implies (hyps)
;;;              (collection-P-tag (collection) [extra-args])))
;;;
;;; Where we have the following generic constraint:
;;;
;;;   (implies (hyps)
;;;            (implies (in a (collection))
;;;                     (predicate a)))
;;;
;;; So, the functional instantiation hints we want to create will look
;;; like the following:
;;;
;;;  (:functional-instance generic-theorem
;;;    (hyps         (lambda ()  [substitution for hyps]))
;;;    (collection   (lambda ()  [substitution for collection]))
;;;    (predicate    (lambda (x) [substitution for predicate]))
;;;    (collection-P (lambda (x) [substitution for collection-P])))
;;;
;;; Lets consider how we can build these substitutions for some
;;; trigger = (collection-P-tag col1 [extra-args1]).  Some of this
;;; is easy:
;;;
;;;   The substitution for hyps is actually built using the process
;;;   described above, e.g., they are extracted from the clause and
;;;   eventually restored to normal using others-to-hyps, so I will
;;;   not spend any time on them.
;;;
;;;   The collection is simply (second trigger), since we require that
;;;   the collection predicate has the collection as its first
;;;   argument.
;;;
;;;   The substitution for collection-P is also fairly easy.  Since
;;;   we require that the collection function's first argument is
;;;   the collection under examination, we simply need to write
;;;   (lambda (?x) (actual-collection-P ?x [extra-args])), where the
;;;   extra arguments are taken from the trigger we are looking at.
;;;
;;;   This leaves us with predicate.  The substitution for predicate
;;;   is difficult, because we want to support very flexible
;;;   predicates involving many arguments and various weird terms.
;;;   To do this, we will allow the user to provide a rewrite rule
;;;   that says how to handle the predicate.
;;;
;;;   In other words, given the trigger (trigger-term col a0 a1 a2
;;;   ... an) we will create the following "base predicate" to
;;;   rewrite:
;;;
;;;     (predicate ?x a0 a1 a2 ... an)
;;;
;;;   Where "predicate" is literally the name of the generic
;;;   predicate.  The user can then provide a substitution such
;;;   as:
;;;
;;;     (predicate ?x ?y) -> (not (integer-lessp ?x ?y))
;;;
;;;   And this will transform the above into the desired result.


(defun build-hint (trigger                ; list, the actual trigger to use
		   generic-theorem        ; symbol, the name of generic-theorem
		   generic-hyps           ; symbol, the name of (hyps)
		   generic-collection     ; symbol, the name of (collection)
		   generic-predicate      ; symbol, the name of predicate
		   generic-collection-P   ; symbol, the name of collection-P
		   collection-P-sub       ; symbol, name of actual collection-P
		   hyps-sub               ; the computed substitution for hyps
		   predicate-rewrite)     ; rewrite rule for predicate
  (let* ((base-pred (cons generic-predicate (cons '?x (cddr trigger))))
	 (pred-sub  (instance-rewrite base-pred predicate-rewrite)))
    `(:functional-instance
      ,generic-theorem
      (,generic-hyps
       (lambda () ,hyps-sub))
      (,generic-collection
       (lambda () ,(second trigger)))
      (,generic-collection-P
       (lambda (?x) ,(cons collection-P-sub (cons '?x (cddr trigger)))))
      (,generic-predicate
       (lambda (?x) ,pred-sub)))))

(defun build-hints (triggers
		    generic-theorem
		    generic-hyps
		    generic-collection
		    generic-predicate
		    generic-collection-P
		    collection-P-sub
		    hyps-sub
		    predicate-rewrite)
  (if (endp triggers)
      nil
    (cons (build-hint (car triggers)
		      generic-theorem
		      generic-hyps
		      generic-collection
		      generic-predicate
		      generic-collection-P
		      collection-P-sub
		      hyps-sub
		      predicate-rewrite)
	  (build-hints (cdr triggers)
		       generic-theorem
		       generic-hyps
		       generic-collection
		       generic-predicate
		       generic-collection-P
		       collection-P-sub
		       hyps-sub
		       predicate-rewrite))))


(defconst *message*
 "~|~%We suspect this conjecture should be proven by functional ~
  instantiation of ~x0.  This suspicion is caused by ~x2, so ~
  if this is not what you want to do, then you should disable ~
  ~x2.  Accordingly, we suggest the following hint: ~
  ~%~%~x1~%")



;;; Of course, some of those hints can be computed.  Here we write a function
;;; to actually provide these hints and install the computed hint function.

(defun automate-instantiation-fn (new-hint-name
				  generic-theorem
				  generic-hyps
				  generic-collection
				  generic-predicate
				  generic-collection-P
				  collection-P-sub
				  predicate-rewrite
				  trigger-symbol
				  tagging-theorem)
  `(encapsulate ()

     (defun ,new-hint-name (id clause world stable)
       (declare (xargs :mode :program)
	        (ignore world))
       (if (not stable)
	   nil
	 (let ((triggers (harvest-trigger clause ,trigger-symbol)))
	   (if (not triggers)
	       nil
	     (let* ((others   (set-difference-equal clause triggers))
		    (hyps     (others-to-hyps others))
		    (phrase   (string-for-tilde-@-clause-id-phrase id))
		    (fi-hints (build-hints triggers
					   ,generic-theorem
					   ,generic-hyps
					   ,generic-collection
					   ,generic-predicate
					   ,generic-collection-P
					   ,collection-P-sub
					   hyps
					   ,predicate-rewrite))
		    (hints    (list :use fi-hints
				    :expand triggers)))
	       (prog2$ (cw *message*
			   ,generic-theorem
			   (list phrase hints)
			   ,tagging-theorem)
		       hints))))))

     (add-default-hints!
      '((,new-hint-name id clause world stable-under-simplificationp)))

     ))




(defmacro automate-instantiation (&key new-hint-name
				       generic-theorem
                                       generic-hyps
				       generic-collection
				       generic-predicate
				       generic-collection-predicate
				       actual-collection-predicate
				       predicate-rewrite
				       actual-trigger
				       tagging-theorem)
  (automate-instantiation-fn new-hint-name
			     (list 'quote generic-theorem)
			     (list 'quote generic-hyps)
			     (list 'quote generic-collection)
			     (list 'quote generic-predicate)
			     (list 'quote generic-collection-predicate)
			     (list 'quote actual-collection-predicate)
			     (list 'quote predicate-rewrite)
			     (list 'quote actual-trigger)
			     (list 'quote tagging-theorem)))

