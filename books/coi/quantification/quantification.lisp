; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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

(in-package "QUANT")
(include-book "xdoc/top" :dir :system)

;; TODO:
;; - match on predicate *as well* as body.

(include-book "misc/records" :dir :system)

(include-book "misc/bash" :dir :system)

(include-book "coi/generalize/generalize" :dir :system)
(include-book "coi/util/mv-nth" :dir :system)
(include-book "coi/util/table" :dir :system)
(include-book "coi/util/skip-rewrite" :dir :system)
(include-book "coi/util/in-conclusion" :dir :system)

(set-state-ok t)

(defmacro local-events (&rest args)
  `(local
    (encapsulate
     ()
     (local
      (encapsulate
       ()
       ,@args)))))

(defun acons+ (key val alist)
  (s key val alist))

#|
;; This books is a first attempt to give ACL2 at least as much (perhaps
;; more?) capability to deal with quantification as PVS.

;; It is going to be easiest to manipulate quanified terms in their
;; unopened state.

;; The clause processor can instantiate the quantified term if it is
;; able to find a suitable instantiation.  Note that complete
;; instantiation of the term is essential.

;; I'm using the tail-recursive function

(defun-sk forall-p (x)
  (forall a (implies (member a x) (p a))))

(defun-sk forall-p (x)
  (forall a (implies (member a x) (equiv (foo a x) (goo a x)))))

(forall-p zed)

(or (not (member a x))
    (p a))

;; We begin by instantiating the formula using the
;; actuals provided.  We then search the term for

;; Step 1 : detect the presence of the witness/predicate
;; If it appears as a (forall):
;;
;; If it appears as an (exists):
;;

;; - instantiate the theorem.
;; -

(implies
 (forall-p x)
 (implies (member a x) (pred x)))

(implies
 (and
  (forall-p x)
  (memberp b x))
 (pred x))


(and
 (forall-p x)
 (memberp b x)
 (not (pred x)))

(or
 (not (forall-p x))
 (not (memberp b x))
 (pred x))

(or (not (member a x))
    (pred x))

;; - Instantiation with elements from the goal.  This
;;   is just drop dead basic.

(forall-x-thm y)
(thm z y)


(implies
 (hyps)
 (equal x y))

(or (not (and x y z)) (equal x y))

(or (not x) (equal (foo x y z) (zed x y z)))

;; Instantiation should be "smart" about equivalence relations,
;; (at least equal and iff) .. allowing partial matches to
;;

;; It is OK for a match to introduce new function symbols.
;; A binding is considered a match when

;; Unification allows a match to bein with any position.

(defun find-match (pattern)


;; If a variable appears in any context, that context is
;; sufficient to establish binding.

;; Start with the leaves and begin binding there.  Every
;; atomic

;; A binding tree collects every possible match for
;; a set of free variables.

(defun construct-binding-tree (term)
  (

- each binding site may suggest different bindings .. computing
  all possible bindings would require evaluating the bindings in
  every possible order.  There may be simplifications such as
  the fact that certain bindings may dominate others .. bindings
  may be classified by how restrictive they are.

- (foo 'x) .. we look for an instance of the pattern (foo ?) and
  bind 'x to the result of that instance.  This binding reduces


- Each join within a term becomes a restriction.

;; Here are all of the first order unifications that are
;; possible.  Following first order unification, you have
;; some number of possible bindings.  Each binding has
;; associated with it some number of restrictions on future
;; bindings.

`((name . (x) . (joe x) (foo x))
  ((x y) . (pred x y))
  )

;; Second order bindings

`((z) (x y) (foo (bar x) (zed y) z))

`((a b c) (x y)

(defun find-instances (free bound pattern ))

(equal (foo x) (goo x))



(defun insert-pattern (level pattern res)
  (let ((pset (nth level res)))
    (let ((pset (cons pattern pset)))
      (update-nth level res))))

(defun new-pattern (bound pattern)
  (list bound pattern))

(defun levalize-pattern-list (pattern-list res)
  (if (consp pattern-list)
      (met ((max1 bound1 res) (levelize-pattern-list (cdr pattern-list) res))
	(let ((pattern (car pattern-list)))
	  ;; levalize-pattern
	  (if (consp pattern)
	      (let ((max2 bound2 res) (levalize-pattern-list (cdr pattern) res))
		(let ((max2    (1+ max2))
		      (pattern (new-pattern bound pattern)))
		  (let ((res (insert-pattern max2 pattern res)))
		    (mv (max max1 max2) bound1 res))))
	    (let ((res (insert-pattern 0 (new-pattern (list pattern) pattern) res)))
	      (mv max1 (cons pattern bound1) res)))))
    (mv 0 nil res)))

(defun levalize-pattern (pattern)
  (if (consp pattern)
      (let ((max2 bound2 res) (levalize-pattern-list (cdr pattern) nil))
	(let ((max2    (1+ max2))
	      (pattern (new-pattern bound pattern)))
	  (let ((res (insert-pattern max2 pattern res)))
	    (mv (max max1 max2) bound1 res))))
    (list (list (new-pattern (list pattern) pattern)))))


;; How about a weak binding scheme that would allow for the introduction
;; of new function symbols provided that full unification was possible
;; without them.

;; I'm willing to ignore the function "equal" appearing here ..
;;  if I can find an instance of t


;; multiple ocurrances of a particular function symbol signify
;; that there may be many ways to instantiate the term.  If
;; I can find a binding that satisfies


;; We allow a rule to introduce no more than one new fact.
;; - a new fact is a fact that does not unify with current
;;   term.


;; - All terms must be completely instantiated.
;;   + if any symbol appears only once, that term
;;     must be instantiated.
;;   + any symbols appearing in conjunction with
;;     restricted symbols must be bound by that
;;     symbol .. or that term must be the free term.


`((s1 . t1)
  (s2 . t2)
  ..)


- number of ocurrances
- variable depth

;; We order the instantiation process by variables.  We choose to
;; instantiate the variables that will prove most difficult first.
;; For each variable, there is a metric based on number of occurrances
;; and the depth of the variable that establishes its relative degree
;; of difficulty.

;; The instantiation process allows a binding to be discarded once.

;; Any one of the terms that has more than one variable binding may be
;; last.  The terms are orderd from least to most likely to succeed.

;; Essential terms

;; + Essential bindings are those bindings that
;; +


|#

(defun soft-alistify (alist)
  (if (consp alist)
      (acons+ (caar alist) (list (cdar alist))
	     (soft-alistify (cdr alist)))
    nil))

(defun term-vars-args (args)
  (if (consp args)
      (let ((fapp (car args)))
	(if (consp fapp)
	    (if (not (equal (car fapp) 'quote))
		(append (term-vars-args (cdr fapp))
			(term-vars-args (cdr args)))
	      (term-vars-args (cdr args)))
	  (cons fapp (term-vars-args (cdr args)))))
    nil))

(defun term-vars (fapp)
  (if (consp fapp)
      (term-vars-args (cdr fapp))
    (list fapp)))

(defun alist-keys (alist)
  (if (consp alist)
      (cons (caar alist) (alist-keys (cdr alist)))
    nil))

(defun memberp (x list)
  (if (consp list)
      (or (equal x (car list))
	  (memberp x (cdr list)))
    nil))

(defun subset (x y)
  (if (consp x)
      (and (memberp (car x) y)
	   (subset (cdr x) y))
    t))

(defun remove-list (x y)
  (if (consp y)
      (if (memberp (car y) x)
	  (remove-list x (cdr y))
	(cons (car y) (remove-list x (cdr y))))
    nil))

(defun subalist (x y)
  (if (consp x)
      (and (equal (car x) (assoc (caar x) y))
	   (subalist (cdr x) y))
    t))

(defun add-new-alist (x list)
  (if (consp list)
      (if (subalist x (car list)) list
	(cons (car list) (add-new-alist x (cdr list))))
    (list x)))

(defun merge-alist-list (x y)
  (if (consp x)
      (let ((y (add-new-alist (car x) y)))
	(merge-alist-list (cdr x) y))
    y))

(defun sub-alist (keys alist)
  (if (consp keys)
      (let ((hit (assoc (car keys) alist)))
	(if (consp hit)
	    (acons+ (car hit) (cdr hit)
		    (sub-alist (cdr keys) alist))
	  (sub-alist (cdr keys) alist)))
    nil))

(defun minimal-pattern-list-args (bound args res)
  (if (consp args)
      (met ((lnew lvars res) (minimal-pattern-list-args bound (cdr args) res))
	(let ((term (car args)))
	  (if (consp term)
	      (if (equal (car term) 'quote)
		  (mv lnew lvars res)
		(met ((fnew fvars res) (minimal-pattern-list-args bound (cdr term) res))
		  (if fnew
		      (mv lnew (append fvars lvars) (acons+ fvars term res))
		    (mv lnew (append fvars lvars) res))))
	    (if (memberp term bound)
		(mv lnew lvars res)
	      (mv (not (memberp term lvars)) (cons term lvars) res)))))
    (mv nil nil res)))

(defun minimal-pattern-list (bound term)
  (let ((res nil))
    (if (consp term)
	(if (equal (car term) 'quote)
	    nil
	  (met ((fnew fvars res) (minimal-pattern-list-args bound (cdr term) res))
	    (if fnew
		(acons+ fvars term res)
	      res)))
      (if (memberp term bound) res
	(acons+ (list term) term res)))))

(defun greedy-patterns (vars acc plist res)
  (if (consp plist)
      (append (greedy-patterns vars acc (cdr plist) res)
	      (and (not (subset (caar plist) acc))
		   (let ((acc (append (caar plist) acc)))
		     (greedy-patterns vars acc (cdr plist) (cons (cdar plist) res)))))
    (if (subset vars acc) (list res)
      nil)))

(defun instantiate-term-args (alist args)
  (if (consp args)
      (let ((term (car args)))
	(if (consp term)
	    (if (not (equal (car term) 'quote))
		(cons `(,(car term) ,@(instantiate-term-args alist (cdr term)))
		      (instantiate-term-args alist (cdr args)))
	      (cons term (instantiate-term-args alist (cdr args))))
	  (let ((hit (assoc term alist)))
	    (let ((term (if (consp hit) (cdr hit) term)))
	      (cons term (instantiate-term-args alist (cdr args)))))))
    nil))

(defun instantiate-term (alist term)
  (if (consp term)
      `(,(car term) ,@(instantiate-term-args alist (cdr term)))
    (let ((hit (assoc term alist)))
      (if (consp hit) (cdr hit) term))))

(defun instantiate-clause (alist clause)
  (if (consp clause)
      (cons (instantiate-term alist (car clause))
	    (instantiate-clause alist (cdr clause)))
    nil))

(defun filter-negations (alist-list pattern goal)
  (if (consp alist-list)
      (let ((alist (car alist-list)))
	(let ((term (instantiate-term alist pattern)))
	  (if (memberp term goal)
	      (filter-negations (cdr alist-list) pattern goal)
	    (cons alist
		  (filter-negations (cdr alist-list) pattern goal)))))
    nil))

(defun negate-term (term)
  (if (and (consp term)
	   (equal (car term) 'not))
      (cadr term)
    `(not ,term)))

(defun new-quant-fn (name type vars bound instantiate skolemize body witness)
  `(,name ,type ,vars ,bound ,instantiate ,skolemize ,body ,witness))

(defmacro new-quant (&key (name    'nil)
			  (type    'nil)
			  (vars    'nil)
			  (bound   'nil)
			  (instantiate   'nil)
			  (skolemize 'nil)
			  (body    'nil)
			  (witness 'nil))
  `(new-quant-fn ,name ,type ,vars ,bound ,instantiate ,skolemize ,body ,witness))

(defun quant-name (quant)
  (nth 0 quant))

(defun quant-type (quant)
  (nth 1 quant))

(defun quant-vars (quant)
  (nth 2 quant))

(defun quant-bound (quant)
  (nth 3 quant))

(defun quant-instantiate (quant)
  (nth 4 quant))

(defun quant-skolemize (quant)
  (nth 5 quant))

(defun quant-body (quant)
  (nth 6 quant))

(defun quant-witness (quant)
  (nth 7 quant))

(defun bind-witness (vars n witness)
  (if (endp vars) nil
    (acons (car vars) `(mv-nth (quote ,n) ,witness)
	   (bind-witness (cdr vars) (1+ n) witness))))

(defun quant-witness-binding (quant)
  (let ((witness (quant-witness quant)))
    (let ((vars (quant-vars quant)))
      (if (< (len vars) 2) (acons (car vars) witness nil)
	(bind-witness vars 0 witness)))))

(defun quant-forall? (quant)
  (equal (quant-type quant) :forall))

(defun quant-instance-body (type quant)
  (declare (ignorable type))
  (let ((body (quant-body quant)))
    (let ((body (if (equal type (quant-type quant)) (negate-term body) body)))
      (let ((witness (quant-witness-binding quant)))
	(instantiate-term witness body)))))

(defun quant-instantiation-body (quant)
  (let ((body (quant-body quant)))
    (if (quant-forall? quant) body (negate-term body))))

(defun quant-instance-pattern-list (hints quant state)
  (declare (xargs :mode :program))
  (let ((body (quant-body quant)))
    (let ((body (if (quant-forall? quant) (negate-term body) body)))
      (bash-term-to-dnf body hints nil nil state))))

(defun quant-instantiate-pattern-list (hints quant alist state)
  (declare (xargs :mode :program))
  (let ((body (quant-body quant)))
    (let ((body (if (quant-forall? quant) body (negate-term body))))
      (let ((body (instantiate-term alist body)))
	(bash-term-to-dnf body hints nil nil state)))))

(defun rekey (key value)
  (and value `(,key ,value)))

(defun generalize-witness-rec (n vars witness)
  (if (consp vars)
      (cons `(,(car vars) (gensym::generalize (acl2::hide (acl2::val ,n ,witness))))
	    (generalize-witness-rec (1+ n) (cdr vars) witness))
    nil))

(defun generalize-witness (vars witness)
  (if (equal (len vars) 1)
      `((,(car vars) (gensym::generalize (acl2::hide ,witness))))
    (generalize-witness-rec 0 vars witness)))

(defun defun-sk-fn (name args body disable doc quant-ok skolem-name skolemize thm-name rewrite witness-dcls strengthen)
  (let* ((formula `(,name ,@args))
	 (formula-by-multiplicity (intern-in-package-of-symbol
				   (concatenate 'string
						(symbol-name name)
						"-BY-MULTIPLICITY")
				   name))
	 (exists-p (and (true-listp body)
			(symbolp (car body))
			(equal (symbol-name (car body))
			       "EXISTS")))
	 (skolemize (or skolemize
			(intern-in-package-of-symbol
			 (concatenate 'string
				      (symbol-name name)
				      "-SKOLEMIZATION")
			 name)))
	 (bound-vars
	  (and (true-listp body)
	       (or (symbolp (cadr body))
		   (true-listp (cadr body)))
	       (cond ((atom (cadr body)) (list (cadr body)))
		     (t (cadr body)))))
	 (avoid (append bound-vars args))
	 (nvar  (gensym::gensym 'n avoid))
	 (mv (< 1 (len bound-vars)))
	 (body-guts (and (true-listp body) (caddr body)))
	 (skolem-name (or skolem-name
			  (intern-in-package-of-symbol
			   (concatenate 'string
					(symbol-name name)
					"-WITNESS")
			   name)))
	 (witness `(,skolem-name ,@args))
	 (witness-instance (if mv `(val ,nvar ,witness) witness))
	 (thm-name
	  (or thm-name
	      (intern-in-package-of-symbol
	       (concatenate 'string
			    (symbol-name name)
			    (if exists-p "-SUFF" "-NECC"))
	       name)))
	 (quant (new-quant :name name
			   :type (if exists-p :exists :forall)
			   :vars bound-vars
			   :bound args
			   :instantiate thm-name
			   :skolemize   skolemize
			   :body        body-guts
			   :witness    `(,skolem-name ,@args))))

    `(encapsulate
      ()

      (local (in-theory (cons 'acl2::MV-NTH-TO-VAL (theory 'acl2::minimal-theory))))

      (defun-sk ,name ,args ,body
	,@(rekey :doc doc)
	,@(rekey :quant-ok quant-ok)
	,@(rekey :skolem-name skolem-name)
	,@(rekey :thm-name thm-name)
	,@(rekey :rewrite rewrite)
	,@(rekey :witness-dcls witness-dcls)
        ,@(rekey :strengthen strengthen))

      (in-theory (disable ,thm-name))

      (defthmd ,skolemize
	(equal ,witness-instance
	       (gensym::generalize (hide ,witness-instance)))
	:hints (("Goal" :expand (:free (x) (hide x))
		 :in-theory (enable gensym::generalize))))

      (defthm ,formula-by-multiplicity
	(implies
	 (acl2::in-conclusion-check ,formula :top ,(if exists-p t :negated))
	 (equal ,formula
		(let ,(generalize-witness bound-vars witness)
		  ,body-guts)))
	:hints (("Goal" :expand ((:free (x) (hide x))
				 (:free (x) (gensym::generalize x))))))

      (add-generalization-pattern (hide ,witness-instance))

      (table::set 'quant-list (cons ',quant (table::get 'quant-list)))

      ,@(and disable `((in-theory (disable ,name))))

      )))

(defmacro def::un-sk (name args body &key doc quant-ok skolem-name skolemize thm-name rewrite witness-dcls strengthen)
  (defun-sk-fn name args body nil doc quant-ok skolem-name skolemize thm-name rewrite witness-dcls strengthen))

(defmacro def::un-skd (name args body &key doc quant-ok skolem-name skolemize thm-name rewrite witness-dcls strengthen)
  (defun-sk-fn name args body t doc quant-ok skolem-name skolemize thm-name rewrite witness-dcls strengthen))

;; ===========================================================================

(defun pattern-match-args-directly (pattern-list args alist)
  (if (and (consp pattern-list)
	   (consp args))
      (let ((pattern (car pattern-list))
	    (fapp    (car args)))
	(met ((good alist) (pattern-match-args-directly (cdr pattern-list) (cdr args) alist))
	  (if good
	      (if (consp pattern)
		  (if (equal (car pattern) 'quote)
		      (if (equal pattern fapp) (mv t alist)
			(mv nil nil))
		    (if (consp fapp)
			(if (equal (car pattern) (car fapp))
			    (pattern-match-args-directly (cdr pattern) (cdr fapp) alist)
			  (mv nil nil))
		      (mv nil nil)))
		(let ((hit (assoc pattern alist)))
		  (if (consp hit)
		      (if (equal fapp (cdr hit))
			  (mv t alist)
			(mv nil nil))
		    (mv t (acons+ pattern fapp alist)))))
	    (mv nil nil))))
    (mv t alist)))

(defun pattern-match-term-directly (pattern fapp alist)
  (if (consp pattern)
      (if (equal (car pattern) 'quote)
	  (if (equal pattern fapp) (mv t alist)
	    (mv nil nil))
	(if (consp fapp)
	    (if (equal (car pattern) (car fapp))
		(pattern-match-args-directly (cdr pattern) (cdr fapp) alist)
	      (mv nil nil))
	  (mv nil nil)))
    (let ((hit (assoc pattern alist)))
      (if (consp hit)
	  (if (equal fapp (cdr hit))
	      (mv t alist)
	    (mv nil nil))
	(mv t (acons+ pattern fapp alist))))))

;; Searches the args for every match of "pattern" under "alist" and adds each
;; new match to the "alist-list".

(defun pattern-match-args-subterm (pattern args alist alist-list)
  (if (endp args) alist-list
    (let ((term (car args)))
      (let ((alist-list (pattern-match-args-subterm pattern (cdr args) alist alist-list)))
	(met ((good nlist) (pattern-match-term-directly pattern term alist))
	     (let ((alist-list (if good (add-new-alist nlist alist-list) alist-list)))
	       (if (consp term)
		   (if (or (equal (car term) 'quote))
		       alist-list
		     (pattern-match-args-subterm pattern (cdr term) alist alist-list))
		 alist-list)))))))

;; Searches the term for every match of "pattern" under "alist" and adds each
;; new match to the "alist-list".

(defun pattern-match-term-subterm (pattern term alist alist-list)
  (met ((good nlist) (pattern-match-term-directly pattern term alist))
       (let ((alist-list (if good (add-new-alist nlist alist-list) alist-list)))
	 (if (consp term)
	     (if (equal (car term) 'quote)
		 alist-list
	       (pattern-match-args-subterm pattern (cdr term) alist alist-list))
	   alist-list))))

;; Searches the goal for every match of "pattern" under "alist" and adds each
;; new match to the "alist-list"

;; Extends alist via every possible match of pattern from the goal,
;; adding it to alist-list

(defun pattern-match-goal-subterm (pattern goal alist alist-list)
  (if (endp goal) alist-list
    (let ((term (car goal)))
      (let ((alist-list (pattern-match-term-subterm pattern term alist alist-list)))
	(pattern-match-goal-subterm pattern (cdr goal) alist alist-list)))))

;; Extends each alist-list entry via every possible match of pattern from
;; goal, adding the results to res.

(defun map-pattern-match-goal-subterm (pattern goal alist-list res)
  (if (endp alist-list) res
    (let ((res (pattern-match-goal-subterm pattern goal (car alist-list) res)))
      (map-pattern-match-goal-subterm pattern goal (cdr alist-list) res))))

;; Continually refines alist-list via each of the patterns in plist.

(defun pattern-match-list-goal-subterm (plist goal alist-list)
  (if (endp plist) alist-list
    (let ((alist-list (map-pattern-match-goal-subterm (car plist) goal alist-list nil)))
      (pattern-match-list-goal-subterm (cdr plist) goal alist-list))))

;; Given a list of pattern lists, independently expand alist for each and
;; return the resulting alist-list.

(defun pattern-match-list-list-goal-subterm (plist-list goal alist res)
  (if (endp plist-list) res
    (let ((alist-list (pattern-match-list-goal-subterm (car plist-list) goal (list alist))))
      (let ((res (merge-alist-list alist-list res)))
	(pattern-match-list-list-goal-subterm (cdr plist-list) goal alist res)))))

;; This is the boundary ....

;; Given a pattern, expand alist for every possible subterm match.

(defun greedy-match-pattern (vars pattern goal alist res)
  (let ((bound (alist-keys alist)))
    (let ((plist (minimal-pattern-list bound pattern)))
      (let ((plist-list (greedy-patterns vars bound plist nil)))
	(pattern-match-list-list-goal-subterm plist-list goal alist res)))))

(defun greedy-match-pattern-alist-list (vars pattern goal alist-list res)
  (if (endp alist-list) res
    (let ((alist (car alist-list)))
      (let ((res (greedy-match-pattern vars pattern goal alist res)))
	(greedy-match-pattern-alist-list vars pattern goal (cdr alist-list) res)))))

(defun greedy-match-pattern-list (vars plist goal alist-list)
  (if (endp plist) alist-list
    (let ((alist-list (greedy-match-pattern-alist-list vars (car plist) goal alist-list nil)))
      (greedy-match-pattern-list vars (cdr plist) goal alist-list))))

(defun greedy-match-pattern-list-list (vars plist-list goal alist res)
  (if (endp plist-list) res
    (let ((plist (car plist-list)))
      (let ((alist-list (greedy-match-pattern-list vars plist goal (list alist))))
	(let ((res (merge-alist-list alist-list res)))
	  (greedy-match-pattern-list-list vars (cdr plist-list) goal alist res))))))

(defun contains-subclause (clist goal)
  (if (consp clist)
      (or (subset (car clist) goal)
	  (contains-subclause (cdr clist) goal))
    nil))

(defun keep-pattern-instances (hints pattern alist-list goal res state)
  (declare (xargs :mode :program))
  (if (endp alist-list) (mv res state)
    (let ((alist (car alist-list)))
      (let ((pinst (instantiate-term alist pattern)))
	(met ((err clist state) (bash-term-to-dnf pinst hints nil nil state))
	     (declare (ignore err))
	     (let ((res (if (contains-subclause clist goal)
			    (add-new-alist alist res)
			  res)))
	       (keep-pattern-instances hints pattern (cdr alist-list) goal res state)))))))

(defun rebind-args-vars (args base avoid rebind)
  (if (consp args)
      (let ((term (car args)))
	(met ((args avoid rebind) (rebind-args-vars (cdr args) base avoid rebind))
	  (if (consp term)
	      (if (equal (car term) 'quote)
		  (mv (cons term args) avoid rebind)
		(met ((fargs avoid rebind) (rebind-args-vars (cdr term) base avoid rebind))
		  (mv (cons (cons (car term) fargs) args) avoid rebind)))
	    (let ((hit (assoc term rebind)))
	      (if (consp hit)
		  (mv (cons (car hit) args) avoid rebind)
		(let ((symbol (gensym::gensym base avoid)))
		  (let ((avoid  (cons symbol avoid))
			(rebind (acons+ symbol term rebind)))
		    (mv (cons symbol args) avoid rebind))))))))
    (mv nil avoid rebind)))

(defun rebind-term-vars (term base avoid rebind)
  (if (consp term)
      (if (equal (car term) 'quote)
	  (mv term avoid rebind)
	(met ((fargs avoid rebind) (rebind-args-vars (cdr term) base avoid rebind))
	  (mv (cons (car term) fargs) avoid rebind)))
    (let ((hit (assoc term rebind)))
      (if (consp hit)
	  (mv (car hit) avoid rebind)
	(let ((symbol (gensym::gensym base avoid)))
	  (let ((avoid  (cons symbol avoid))
		(rebind (acons+ symbol term rebind)))
	    (mv symbol avoid rebind)))))))

(defun rebind-alist-instance-vars-rec (alist base avoid rebind)
  (if (consp alist)
      (let ((entry (car alist)))
	(met ((term avoid rebind) (rebind-term-vars (cdr entry) base avoid rebind))
	  (met ((alist rebind) (rebind-alist-instance-vars-rec (cdr alist) base avoid rebind))
	    (mv (acons+ (car entry) term alist) rebind))))
    (mv nil rebind)))

(defun invert-alist (alist)
  (if (consp alist)
      (acons+ (cdar alist) (caar alist) (invert-alist (cdr alist)))
    nil))

(defun rebind-alist-instance-vars (alist base avoid)
  (met ((alist rebind) (rebind-alist-instance-vars-rec alist base avoid nil))
    (mv alist rebind)))

(defun extend-alist-list (alist alist-list)
  (if (consp alist-list)
      (cons (append alist (car alist-list))
	    (extend-alist-list alist (cdr alist-list)))
    nil))

(defun sub-alist-list (vars alist-list)
  (if (consp alist-list)
      (cons (sub-alist vars (car alist-list))
	    (sub-alist-list vars (cdr alist-list)))
    nil))

(defun maximal-match-pattern (hints quant vars pattern goal alist state)
  (declare (xargs :mode :program))
  (let ((keys (alist-keys alist)))
    (let ((vars (remove-list keys vars)))
      (met ((subst inst-alist) (rebind-alist-instance-vars alist (quant-name quant)
							   (revappend (quant-bound quant)
								      (quant-vars quant))))
	   (let ((pinst (instantiate-term subst pattern)))
	     (met ((err plist-list state) (bash-term-to-dnf pinst hints nil nil state))
		  (declare (ignore err))
		  (let ((alist-list (greedy-match-pattern-list-list vars plist-list goal inst-alist nil)))
		    (let ((alist-list (sub-alist-list vars alist-list)))
		      (let ((alist-list (extend-alist-list alist alist-list)))
			(mv alist-list state))))))))))

(defun maximal-match-pattern-alist-list (hints quant vars pattern goal alist-list res state)
  (declare (xargs :mode :program))
  (if (endp alist-list) (mv res state)
    (let ((alist (car alist-list)))
      (met ((new-alist-list state) (maximal-match-pattern hints quant vars pattern goal alist state))
	   (met ((res state) (keep-pattern-instances hints pattern new-alist-list goal res state))
		(maximal-match-pattern-alist-list hints quant vars pattern goal (cdr alist-list) res state))))))

(defun maximal-match-pattern-list (hints quant plist goal alist-list state)
  (declare (xargs :mode :program))
  (if (endp plist) (mv alist-list state)
    (let ((pattern (car plist)))
      (let ((vars (term-vars pattern)))
	(met ((alist-list state) (maximal-match-pattern-alist-list hints quant vars pattern goal alist-list nil state))
	     (maximal-match-pattern-list hints quant (cdr plist) goal alist-list state))))))

(defun maximal-match-pattern-list-list (hints quant plist-list goal alist res state)
  (declare (xargs :mode :program))
  (if (endp plist-list) (mv res state)
    (met ((alist-list state) (maximal-match-pattern-list hints quant (car plist-list) goal (list alist) state))
	 (let ((res (merge-alist-list alist-list res)))
	   (maximal-match-pattern-list-list hints quant (cdr plist-list) goal alist res state)))))


(defun simple-pattern-match-predicate-in-goal (not fn args goal res)
  (if (endp goal) res
    (let ((term (car goal)))
      (let ((negated (and (consp term) (equal (car term) 'not))))
	(let ((term (if negated (cadr term) term)))
	  (if (and (iff not negated)
		   (consp term)
		   (equal (car term) fn))
	      (let ((alist (pairlis$ args (cdr term))))
		(let ((res (add-new-alist alist res)))
		  (simple-pattern-match-predicate-in-goal not fn args (cdr goal) res)))
	    (simple-pattern-match-predicate-in-goal not fn args (cdr goal) res)))))))

(defun maximal-instance-matching (hints type quant goal state)
  (declare (xargs :mode :program))
  (let ((body (quant-instance-body type quant)))
    (met ((err plist-list state) (bash-term-to-dnf body hints nil nil state))
	 (declare (ignore err))
	 (met ((res state) (maximal-match-pattern-list-list hints quant plist-list goal nil nil state))
	   ;;
	   ;; Match on unopened quantified formulae
	   ;;
	   (let ((res (simple-pattern-match-predicate-in-goal (equal type (quant-type quant))
							      (quant-name quant)
							      (quant-bound quant)
							      goal
							      res)))
	     (mv res state))))))


;; The -1 versions ..

(defun maximal-match-1-pattern-alist-list (hints quant vars pattern goal alist-list res state)
  (declare (xargs :mode :program))
  (if (endp alist-list) (mv res state)
    (let ((alist (car alist-list)))
      (met ((new-alist-list state) (maximal-match-pattern hints quant vars pattern goal alist state))
	   (let ((res (merge-alist-list new-alist-list res)))
	     (maximal-match-1-pattern-alist-list hints quant vars pattern goal (cdr alist-list) res state))))))

(defun maximal-match-1-pattern-list-rec (hints quant pattern top bottom goal alist res state)
  (declare (xargs :mode :program))
  (met ((alist-list state)
	(maximal-match-pattern-list hints quant (append top bottom) goal (list alist) state))
       (met ((new-alists state)
	     (maximal-match-1-pattern-alist-list hints quant (term-vars pattern) pattern goal alist-list nil state))
	     (let ((new-alists (filter-negations new-alists (negate-term pattern) goal)))
	       (let ((res (merge-alist-list new-alists res)))
		 (if (endp bottom) (mv res state)
		   (maximal-match-1-pattern-list-rec hints quant (car bottom) (cons pattern top) (cdr bottom)
						     goal alist res state)))))))

(defun maximal-match-1-pattern-list (hints quant plist goal alist state)
  (declare (xargs :mode :program))
  (if (consp plist)
      (maximal-match-1-pattern-list-rec hints quant (car plist) nil (cdr plist) goal alist nil state)
    (mv (list alist) state)))

(defun maximal-match-1-pattern-list-list (hints quant plist-list goal alist res state)
  (declare (xargs :mode :program))
  (if (endp plist-list) (mv res state)
    (met ((alist-list state) (maximal-match-1-pattern-list hints quant (car plist-list) goal alist state))
	 (let ((res (merge-alist-list alist-list res)))
	   (maximal-match-1-pattern-list-list hints quant (cdr plist-list) goal alist res state)))))

(defun maximal-match-1-pattern-list-alist-list (hints quant plist-list goal alist-list res state)
  (declare (xargs :mode :program))
  (if (endp alist-list) (mv res state)
    (let ((alist (car alist-list)))
      (met ((res state) (maximal-match-1-pattern-list-list hints quant plist-list goal alist res state))
	   (maximal-match-1-pattern-list-alist-list hints quant plist-list goal (cdr alist-list) res state)))))

(defun keep-keys (keys alist)
  (if (consp keys)
      (cons (assoc (car keys) alist)
	    (keep-keys (cdr keys) alist))
    nil))

(defun alist-list-to-use-hints (quant alist-list use-hints)
  (if (consp alist-list)
      (let ((alist (car alist-list)))
	(let ((alist (keep-keys (append (quant-vars quant) (quant-bound quant)) alist)))
	  (let ((use-hints (cons `(:instance ,(quant-instantiate quant) ,@(soft-alistify alist)) use-hints)))
	    (alist-list-to-use-hints quant (cdr alist-list) use-hints))))
    use-hints))

(defun maximal-instantiation-matching (hints quant alists goal state)
  (declare (xargs :mode :program))
  (let ((body (quant-instantiation-body quant)))
    (met ((err plist-list state) (bash-term-to-dnf body hints nil nil state))
	 (declare (ignore err))
	 (maximal-match-1-pattern-list-alist-list hints quant plist-list goal alists nil state))))

;; Find every match for the first pattern.  Then find every match for
;; every subsequent pattern under the binding(s) of the first pattern.
;; The subterm version will be slightly more complicated.

;; - If the instantiation matches the goal exactly, the proof is done.
;; - If the instantiation produces one new term .. that is good.
;; - If the negation of the new term produced by the instantiation appears
;;   in the goal, the instantiation is useless.

;; => this third rule may suggest that we are not searching for the
;;    right thing.
#|
(defun-sk forall-example (a)
  (forall (x y) (implies (and (boo a x) (hoo a y)) (pred a))))

((thm (forall-example a)) -> `(
			       ((not (BOO A (VAL 0 (FORALL-EXAMPLE-WITNESS A))))
				(not (HOO A (VAL 1 (FORALL-EXAMPLE-WITNESS A))))
				(pred a))
			       ))

((thm (not (forall-example a)) :otf-flg t)
 ->
 (
  ((BOO A (VAL 0 (FORALL-EXAMPLE-WITNESS A))))

  ((HOO A (VAL 1 (FORALL-EXAMPLE-WITNESS A))))

  (not (PRED A))
  ))
|#

;; try-drops will attempt to match a pattern completely up to a final
;; element.  It does this for every possible final element.  It will
;; then allow that final element to be matched a lazily as possible
;; .. allowing for the introduction of "new" information from the
;; quantification.  The "pattern-choices" are the various (minimal)
;; ways in which the final pattern can be matched and still fulfill
;; the instantiation obligations.

;; The patterns passed in to try-drops should be ordered in such a way
;; as to always try the harder patterns first. (they should appear
;; first in the list)


(encapsulate
    (
     ((boo * *) => *)
     ((hoo * *) => *)
     ((pred *) => *)
     )

  (local
   (defun boo (x y) (list x y)))
  (local
   (defun hoo (x y) (list x y)))
  (local (defun pred (x) (or x (not x))))

  (defthm pred-hoo
    (pred (hoo x y)))

  (defthmd skolemization-axiom
    (IMPLIES
     (and
      (BOO Q x)
      (syntaxp (and (symbolp x)
		    (symbolp y))))
     (HOO Q y)))

  )

(defun inc-assoc (key alist)
  (if (consp alist)
      (if (equal key (caar alist))
	  (acons+ key (1+ (nfix (cdar alist))) (cdr alist))
	(cons (car alist) (inc-assoc key (cdr alist))))
    (acons+ key 1 nil)))

(defun quantified-formula-information-rec (quant inst alists)
  (declare (ignorable inst quant))
  (if (consp alists)
      (let ((alist (car alists)))
	(let ((sub-alist (sub-alist (quant-bound quant) alist)))
	  (let ((term (quant-body quant)))
	    (let ((term (instantiate-term sub-alist term)))
	      ;;
	      ;; Name appears in brackets if term appears negated ..
	      ;;
	      (let ((zed (if (iff (quant-forall? quant) inst)
			     (cw "   ~p0 :" (quant-name quant))
			   (cw "  [~p0]:" (quant-name quant)))))
		(declare (ignore zed))
		(let ((zed (if inst
			       (cw " (FORALL ")
			     (cw " (EXISTS "))))
		  (declare (ignore zed))
		  (let ((zed (if (iff (quant-forall? quant) inst)
				 (cw "~p0 ~p1)~%" (quant-vars quant) term)
			       (cw "~p0 ~p1)~%" (quant-vars quant) (negate-term term)))))
		    (declare (ignore zed))
		    (quantified-formula-information-rec quant inst (cdr alists)))))))))
    nil))

(defun instantiable-formula-information (quant alists)
  (declare (ignorable quant alists))
  (let ((zed (cw "~%Instantiable Formula In Goal:~%")))
    (declare (ignore zed))
    (let ((zed (quantified-formula-information-rec quant t alists)))
      (declare (ignore zed))
      (cw "~%"))))

(defun skolemizable-formula-information (quant alists)
  (declare (ignorable quant alists))
  (let ((zed (cw "~%Skolemizable Formula In Goal:~%")))
    (declare (ignore zed))
    (let ((zed (quantified-formula-information-rec quant nil alists)))
      (declare (ignore zed))
      (cw "~%"))))

(defun instance-hint (hints rec formulae use-hints)
  (if (consp use-hints)
      (let ((hint (car use-hints)))
	(let ((hint `(:use ,hint)))
	  (let ((zed (cw "Computed Hint: ~p0" hint)))
	    (declare (ignore zed))
	    (if (or rec (consp (cdr use-hints)))
		`(:computed-hint-replacement
		  ((instantiate-quantified-formulae-fn world stable-under-simplificationp
						       clause ',(cdr use-hints) ',rec ',hints ',formulae acl2::pspv state))
		  ,@hint)
	      hint))))
    nil))

(defun instantiate-quantified-formulae-rec (hints qlist rec formulae use-hints goal state)
  (declare (xargs :mode :program))
  (if (endp qlist) (let ((hint (instance-hint hints rec formulae use-hints)))
		     (mv nil hint state))
    (let ((quant (car qlist)))
      (met ((alists state) (maximal-instance-matching hints :forall quant goal state))
	(let ((zed (and alists (instantiable-formula-information quant alists))))
	  (declare (ignore zed))
	  (met ((alists state) (maximal-instantiation-matching hints quant alists goal state))
	    (let ((use-hints (alist-list-to-use-hints quant alists use-hints)))
	      (instantiate-quantified-formulae-rec hints (cdr qlist) rec formulae use-hints goal state))))))))

(defun filter-formulae-rec (fns qlist)
  (if (endp qlist) nil
    (let ((q (car qlist)))
      (if (member (quant-name q) fns)
	  (cons q (filter-formulae-rec fns (cdr qlist)))
	(filter-formulae-rec fns (cdr qlist))))))

(defun filter-formulae (fns qlist)
  (if (null fns) qlist
    (let ((fns (if (atom fns) (list fns) fns)))
      (filter-formulae-rec fns qlist))))

(defun instantiate-quantified-formulae-fn (world stable goal use-hints rec hints formulae pspv state)
  (declare (xargs :mode :program)
	   (acl2::ignorable pspv))
  (if (not stable) (mv nil nil state)
    (if (consp use-hints)
	(let ((hint (instance-hint hints rec formulae use-hints)))
	  (mv nil hint state))
      (let ((qlist (filter-formulae formulae (table::get 'quant-list))))
	(acl2::preserve-pspv (instantiate-quantified-formulae-rec hints qlist rec formulae nil goal state)
			     :pspv pspv)))))

(defmacro instantiate-quantified-formulae (&key (rec 't) (hints 'nil) (formulae 'nil))
  `(instantiate-quantified-formulae-fn world stable-under-simplificationp clause nil ',rec ',hints ',formulae acl2::pspv state))

(defmacro inst? (&key (rec 't) (hints 'nil) (formulae 'nil) (when 'nil))
  (if when
      `(if ,when (instantiate-quantified-formulae :rec ,rec :hints ,hints :formulae ,formulae)
	 (mv nil nil state))
    `(instantiate-quantified-formulae :rec ,rec :hints ,hints :formulae ,formulae)))

; Matt K. addition: Avoid ACL2(p) failure due to INST calls below.
(local (include-book "std/system/non-parallel-book" :dir :system))
(local (acl2::non-parallel-book))

;; skolemization

(defun restrict-all-instances (quant list-alist)
  (if (consp list-alist)
      (let ((alist (car list-alist)))
	(if (consp alist)
	    `((,(quant-skolemize quant) (,@(soft-alistify alist)))
	      ,@(restrict-all-instances quant (cdr list-alist)))
	  (restrict-all-instances quant (cdr list-alist))))
    nil))

(defun skolemize-quantified-formulae-rec (hints qlist enable restrict goal state)
  (declare (xargs :mode :program))

  ;; DAG -- I'm concerned that :restrict hints aren't working the
  ;; way I would like ..

  (if (endp qlist) (let ((hints (and (or enable restrict)
				     `(:do-not '(preprocess)
				       :in-theory (enable ,@enable)
				       ,@(and restrict `(:restrict ,restrict))))))
		     (let ((zed (and hints (cw "Computed Hint: ~p0" hints))))
		       (declare (ignore zed))
		       (mv nil hints state)))
    (let ((quant (car qlist)))
      (met ((alists state) (maximal-instance-matching hints :exists quant goal state))
	   (let ((zed (and alists (skolemizable-formula-information quant alists))))
	     (declare (ignore zed))
	     (let ((restrictions (restrict-all-instances quant alists)))
	       (let ((enable   (if alists (cons (quant-skolemize quant) enable) enable))
		     (restrict (append restrictions restrict)))
		 (skolemize-quantified-formulae-rec hints (cdr qlist) enable restrict goal state))))))))

(defun skolemize-quantified-formulae-fn (world stable goal hints pspv state)
  (declare (xargs :mode :program)
	   (acl2::ignorable pspv))
  (if (not stable) (mv nil nil state)
    (let ((qlist (table::get 'quant-list)))
      (acl2::preserve-pspv (skolemize-quantified-formulae-rec hints qlist nil nil goal state)
			   :pspv pspv))))

(defmacro skolemize-quantified-formulae (&key (hints 'nil))
  `(skolemize-quantified-formulae-fn world stable-under-simplificationp clause ',hints acl2::pspv state))

(defmacro skosimp (&key (hints 'nil) (when 'nil))
  (if when
      `(if ,when (skolemize-quantified-formulae :hints ,hints)
	 (mv nil nil state))
    `(skolemize-quantified-formulae :hints ,hints)))

(local-events

 (def::un-sk forall-zen (a)
   (forall (x y) (implies (boo a x) (hoo a y))))

 (def::un-sk exists-zen (a)
   (exists (x y) (not (implies (boo a x) (hoo a y)))))

 (defthmd forall-zen-instantiation-test
   (implies
    (forall-zen q)
    (implies (boo q x1) (hoo q y1)))
   :hints ((inst?)))

 (defthmd exists-zen-instantiation-test
   (implies
    (not (exists-zen q))
    (implies (boo q x1) (hoo q y1)))
   :hints ((inst?)))

 (local (in-theory (enable skolemization-axiom)))

 ;; Note that the instantiation and skolemization hints do not interfere.

 (defthmd forall-zen-skolemization-test
   (forall-zen q)
   :hints ((skosimp)
	   (inst?)
	   ))

 (defthmd exists-zen-skolemization-test
   (not (exists-zen q))
   :hints ((skosimp)
	   (inst?)
	   ))

 ;; This is kind of a cool theorem

 (defthmd forall-implies-not-exists
   (iff (forall-zen q)
	(not (exists-zen q)))
   :hints ((skosimp)
	   (inst?)))

 )

(local-events

 #|

 This is the example from the ACL2 documentation.  It is challenging
 because is requires that an instantiated term be simplified before a
 complete match would work.  It does prove, however, in PVS using only
 skosimp and inst? and the member-append rule provided.

 |#

 (defstub p (x) t)

 (def::un-sk forall-p (x)
   (forall (a) (implies (member a x) (p a))))

 #+joe
 (defthmd forall-p-skolemization
   (equal (forall-p-witness a)
	  (gensym::generalize (hide (forall-p-witness a))))
   :hints (("Goal" :in-theory (enable gensym::generalize)
	    :expand (:free (x) (hide x)))))

 #+joe
 (add-generalization-pattern (hide (forall-p-witness a)))

 #+joe
 (table::set 'quant-list
	     (list
	      (new-quant :name 'forall-p
			 :type :forall
			 :vars `(a)
			 :bound `(x)
			 :instantiate 'forall-p-necc
			 :skolemize 'forall-p-skolemization
			 :body  `(implies (member a x) (p a))
			 :witness `(forall-p-witness x)
			 )))

 #+joe
 (in-theory (disable FORALL-P-NECC))

#|
(trace$
 maximal-instance-matching
 maximal-match-pattern-list-list
 maximal-match-pattern-list
 maximal-match-pattern-alist-list
 keep-pattern-instances
 contains-subclause
 maximal-match-pattern
 greedy-match-pattern-list-list
 greedy-match-pattern-list
 greedy-match-pattern-alist-list
 greedy-match-pattern
 pattern-match-list-list-goal-subterm
 pattern-match-list-goal-subterm
 map-pattern-match-goal-subterm
 pattern-match-goal-subterm )

(thm
 (forall-p a)
 :hints (("Goal" :do-not-induct t)
	 (inst?)))
|#

 (defthm member-of-append
   (iff (member a (append x y))
	(or (member a x)
	    (member a y))))

 (defthm forall-p-append
   (equal (forall-p (append x1 x2))
	  (and (forall-p x1) (forall-p x2)))
   :otf-flg t
   :hints (("Goal" :do-not-induct t)
	   (skosimp) ;; this messes up the proof .. why?
           ;; See my DAG comment in skolemize-quantified-formulae-rec
	   (inst?)))

 )

#|
;; You will want this, too
(defun if-to-and (term)
  (if (consp term)
      (if (equal (car term) 'if)
	  (cond
	   ((equal (cadddr term) *nil*)
	    (cons (cadr term)
		  (if-to-and (caddr term))))
	   ((equal (caddr term) *nil*)
	    (cons (negate-term (cadr term))
		  (if-to-and (cadddr term))))
	   (t
	    (list term)))
	(list term))
    (list term)))


(defun unwrap-term (term)
  (if (consp term)
      (let ((term (cond
		   ((equal (car term) 'if)
		    term)
		   ((equal (car term) 'equal)
		    (cond
		     ((equal (caddr term) *nil*)
		      `(not ,(cadr term)))
		     ((equal (caddr term) *t*)
		      (cadr term))
		     (t term)))
		   (t term))))
	(negate-term term))
    `(not ,term)))

(defun if-term (term)
  (and (consp term)
       (equal (car term) 'if)))

(defun type-alist-to-clause (type-alist res state)
  (declare (xargs :mode :program))
  (if (consp type-alist)
      (let ((typeset (car type-alist)))
	(let ((expr (car typeset))
	      (type (cadr typeset)))
	  (met ((term zed) (convert-type-set-to-term expr type (ens state) (w state) nil))
	       (declare (ignore zed))
	       (let ((term (unwrap-term term)))
		 (let ((res (if (if-term term) res (cons term res))))
		   (type-alist-to-clause (cdr type-alist) res state))))))
    res))

;; (type-alist-clause `(list (consp x) (natp x)) ttree-lst force-flg type-alist ens world pot-lst pt)
;; (type-alist-clause `(list (consp y) (natp x)) nil       nil       nil        (ens state) (w state) nil nil)
#+joe
(mv-let (x type-alist z)
	(type-alist-clause `((pred z) (consp y) (natp x)) nil  nil nil (ens state) (w state) nil nil)
	(declare (ignore x z))
	(type-alist-to-clause type-alist nil state))
|#

(local-events

 (def::un-sk rewrite-boo ()
   (forall  (x y) (equal (boo x y) (hoo x y))))

 ;; Here we show that we can pattern match on an "equal" term
 ;; in the quantification.

 (defthm rewrite-implies-pred-boo
   (implies
    (rewrite-boo)
    (pred (boo x y)))
   :hints ((inst?)))

 )

#|
;; We expect to use "bash-term-to-dnf" inside of a make-event
;; to produce the p-list and np-list values.

ACL2 !>(bash-term-to-dnf
	'(implies (true-listp x) (equal (append x y) zzz))
	'(("Goal" :expand ((true-listp x)
			   (true-listp (cdr x))
			   (append x y))))
	nil nil state)
 (((EQUAL Y ZZZ))
  ((NOT (CONSP X))
   (NOT (CONSP (CDR X)))
   (NOT (TRUE-LISTP (CDDR X)))
   (EQUAL (LIST* (CAR X)
                 (CADR X)
                 (APPEND (CDDR X) Y))
          ZZZ))
  ((NOT (CONSP X))
   (CDR X)
   (EQUAL (CONS (CAR X) Y) ZZZ)))
ACL2 !>

|#


#|
;; The pick-a-point/quantification connection.
;;
;; I was recently mulling over the difficulty of doing congruence
;; proofs .. and what a blessing pick-a-point often is for such
;; proofs.  In particular, I was frustrated that I wasn't able to use
;; a "pick-a-point" like strategy to leverage terms from my hypothesis.
;; (chaining from equal to equiv can be very hard).
;;
;; What I had failed to fully grasp was that pick-a-point is merely
;; leveraging a form of quantification.  In particular, pick-a-point
;; relies on your ability to reduce some term into an assertion about
;; some arbitrary element.
;;
;; Which is to say: it relies on the fact that your predicate is just
;; a form of quantification in disguise.
;;
;; Realizing that, we understand that the reason it doesn't really
;; work to use pick-a-point in the hypothesis is because pick-a-point
;; is skolemization .. and from the hypothesis we need instantiation.
;;
;; Thus, It should be possible to use quantification directly to do
;; the same thing (in some sense: more) than we can do with pick-a-
;; point.  Pick-a-point itself is then merely quant::skosimp and we
;; can also "pick-a-point" from terms in the hypothesis via
;; quant::inst? to help complete our proofs.
;;
;; Curiously, now that I understand better how :forward-chaining rules
;; are used, I'm not sure that they don't work better than inst? in
;; similar circumstances.  In particular, a big problem with inst? is
;; that it doesn't have access to the type-alist.  Perhaps a good
;; thing to do would be to define equivalences using quantification
;; and then use forward chaining rules (rather than inst?) to dispatch
;; proofs.  Although, of course, inst? would always be available if
;; it turned out we did need it.

;; One other observation about the best way to do congruence proofs.
;; So you have a new function.  You hope that this function satisfies
;; some congruence.  Consider how the function might decompose into
;; the operators used in describing the equivalences .. memberp,
;; count, assoc, keys, len, etc.  You must then proof theorems about
;; how those primitives interace with your new function.  If the
;; results of those theorems satisfy the congruences, then so will
;; your new function.
;;
;; to decompose the expression:
;;
;; (equiv-conc (fn a b c) z)
;;
;; Well, presumably equiv-conc reduces to the equality of some number
;; of accessors over each term.  Prove a theorem relating each of
;; those accessors to your function. Once this is done, the congruence
;; proof should be easy.  Note that this will hopefully allow you to
;; induct in a nice way over simple accessors rather than over an
;; equivalence relation (which sucks).

;; equality for lists reduces to the following:

(equal (equal x y)
       (and
	(equal (len x) (len y))
	(equal (lastcdr x) (lastcdr y))
	(forall (a) (equal (nth a x) (nth a y)))))

;; equivalence for lists:

(equal (equiv x y)
       (and
	(equal (len x) (len y))
	(forall (a) (equal (nth a x) (nth a y)))))

;; bag equivalence:

(equal (perm x y)
       (forall (a) (equal (count a x) (count a y))))

;; set equivalence

(equal (setequiv x y)
       (forall (a) (equal (memberp a x) (memberp a y))))
|#

;; So here we demonstrate the trick .. rather than doing pick-a-point
;; proofs about things .. we simply *define* our equivalence relations
;; using quantification.  The result is not executable, but it may be
;; easier to reason about.

(local
 (encapsulate
     ()

   (def::un-sk assox-equiv (x y)
     (forall (a) (equal (assoc a x) (assoc a y))))

   ;; I have added skosimp hints now .. just because I can :O

   (defequiv assox-equiv
     :hints ((quant::skosimp)
	     (quant::inst?)))

   ;; Hey .. don't we match against the skolem predicate, too?
   ;; I should fix that .. see TODO at top.
   ;;
   ;; (in-theory (disable assox-equiv))

   (defcong assox-equiv equal (assoc a x) 2
     :hints ((quant::skosimp)
	     (quant::inst?)))

   (defcong assox-equiv assox-equiv (cons pair y) 2
     :hints ((quant::skosimp)
	     (quant::inst?)))

   (defcong assox-equiv assox-equiv (acons key value y) 3
     :hints ((quant::skosimp)
	     (quant::inst?)))

   ))

(acl2::defxdoc def::un-sk
  :short "An extension of defun-sk that supports automated skolemization and instantiation of quantified formulae"
  :parents (defun-sk)
  :long "<p> 
The @('def::un-sk') macro is an extension of @(tsee defun-sk) that supports
automated skolemization and instantiation of quantified formulae via the
computed hints @('quant::inst?') and @('quant::skosimp').
</p>
<p>Usage:</p> @({
  (include-book \"coi/quantification/quantification\" :dir :system)
               
  (def::un-sk forall-zen (a)
    (forall (x y) (implies (boo a x) (hoo a y))))

  (def::un-sk exists-zen (a)
    (exists (x y) (not (implies (boo a x) (hoo a y)))))

  (defthmd forall-zen-instantiation-test
    (implies
     (forall-zen q)
     (implies (boo q x1) (hoo q y1)))
    :hints ((quant::inst?)))

  (defthmd exists-zen-instantiation-test
    (implies
     (not (exists-zen q))
     (implies (boo q x1) (hoo q y1)))
    :hints ((quant::inst?)))

  ;; This is kind of a cool theorem

  (defthmd forall-is-not-exists
    (iff (forall-zen q) 
         (not (exists-zen q)))
    :hints ((quant::skosimp)
 	    (quant::inst?)))

  ;; Here we use it to do \"pick-a-point\" proofs

  (def::un-sk assox-equiv (x y)
    (forall (a) (equal (assoc a x) (assoc a y))))

  (defequiv assox-equiv
    :hints ((quant::skosimp)
            (quant::inst?)))

  (defcong assox-equiv equal (assoc a x) 2
    :hints ((quant::skosimp)
            (quant::inst?)))

  (defcong assox-equiv assox-equiv (cons pair y) 2
    :hints ((quant::skosimp)
            (quant::inst?)))

  (defcong assox-equiv assox-equiv (acons key value y) 3
    :hints ((quant::skosimp)
  	    (quant::inst?)))
 })

")

(acl2::defxdoc quant::inst?
  :short "A hint that attempts automated instantiation of quantified formulae"
  :parents (def::un-sk)
  :long "<p> See @(tsee def::un-sk) </p>")

(acl2::defxdoc quant::skosimp
  :short "A hint for performing automated skolemization of quantified formulae"
  :parents (def::un-sk)
  :long "<p> See @(tsee def::un-sk) </p>")

