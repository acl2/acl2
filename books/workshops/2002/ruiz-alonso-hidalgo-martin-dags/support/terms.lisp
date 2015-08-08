;;; terms.lisp
;;; Properties about terms, substitutions, and system of equations.
;;; Created: 7-10-99 Last revison: 15-02-2001
;;; =============================================================================


#| To certify this book:

(in-package "ACL2")

(certify-book "terms")

|#


(in-package "ACL2")
(include-book "basic")

;;; *******************************************************************
;;; BASIC PROPERTIES ABOUT FIRST-ORDER TERMS, SUBSTITUTIONS AND SYSTEM
;;; OF EQUATIONS.
;;; *******************************************************************


;;; ============================================================================
;;; 1. Terms
;;; ============================================================================



;;; ----------------------------------------------------------------------------
;;; 1.1 Representation of terms
;;; ----------------------------------------------------------------------------

;;; We will represent first-order terms in prefix notation, using
;;; lists. For example, the term f(x h(a) g(x y b)), where x, y are
;;; variables and a, b are constants is represented as
;;; (f x (h (a) (g x y (b)).
;;; Note that constants are considered as 0-ary functions.


;;; The following functions define the set of well-formed terms (and
;;; list of terms) in a given signature We will prove later that our
;;; main functions acting on terms are closed in the set of terms of a
;;; given signature (the closure theorems).

;;; A signature is defined to be a function of two arguments. The
;;; intended meaning is that receiving as input a symbol function and a
;;; natural number, we return t if the arity of the symbol is n, and nil
;;; otherwise. This will allows to represent infinite signatures and
;;; variadic symbol functions.

;;; A general signature:

(defstub signat (* *) => *)


;;; EXAMPLE:
;;; This is for example, the signature of group theory
; (defun signat (symb n)
;   (let* ((sig '((* 2) (i 1) (e 0)))
; 	 (found (assoc symb sig))
; 	 (arity (cdr found)))
;     (and found (member n arity))))


;;; The variables of terms in a given signature, will be restricted to
;;; eqlablep ACL2 objects. This is due to two reasons:
;;; - First we restrict the kind objects that can be considered as
;;;   variables in a given language, to discard "strange" cases.

;;; - Second, in this way well-formed terms (as defined by term-p below)
;;;   can be seen as terms in a particular signature. This will allow to
;;;   export the closure theorems to guard theorems, as we will see.

;;; Thus we define variable-s-p as eqlablep, a predicate for recognizing
;;; variables of terms in a given signature.

(defmacro variable-s-p (x) `(eqlablep ,x))

;;; ====== TERM-S-P, TERM-S-P-AUX


;;; term-s-p-aux define terms and lists of terms in a given
;;; signature. We define at the same time terms and lists of terms,
;;; using a standard trick for mutual recursion. (term-s-p-aux flg x) is
;;; t if flg=nil and x is a list of terms in a signature or flg /= nil
;;; and x is a term in a signature. Nil otherwise.

(defun term-s-p-aux (flg x)
  (if flg
      (if (atom x)
	  (variable-s-p x)
	(if (signat (car x) (len (cdr x)))
	    (term-s-p-aux nil (cdr x))
	  nil))
    (if (atom x)
	(equal x nil)
      (and (term-s-p-aux t (car x))
	   (term-s-p-aux nil (cdr x))))))

(defmacro term-s-p (x)
  `(term-s-p-aux t ,x))


;;; ====== TERM-P, TERM-P-AUX


;;; For guard verification purposes, we will define a function term-p
;;; defining "proper" representation of first-order terms, i.e., the
;;; kind of Common Lisp objects that our functions are expected to
;;; receive as input when executed. As for terms in a signature, this is
;;; done for terms and for lists of terms.  Note that we require that
;;; variables and function symbols have to be eqlablep objects. This
;;; will allow us to use eql instead of equal in executable functions,
;;; making them more efficient.


(defun term-p-aux (flg x)
  (declare (xargs :guard t))
  (if flg
      (if (atom x)
	  (eqlablep x)
	(and (eqlablep (car x))
	     (term-p-aux nil (cdr x))))
    (if (atom x)
	(equal x nil)
      (and (term-p-aux t (car x))
	   (term-p-aux nil (cdr x))))))

(defmacro term-p (x)
  (declare (xargs :guard t))
  `(term-p-aux t ,x))




;;; VERY IMPORTANT REMARK: NON-PROPER TERMS
;;; ***************************************

;;; Having defined the above functions, nevertheless, since ACL2 is a
;;; logic of total functions, our functions acting on terms are defined
;;; for every object, even for those not representing "proper" terms, as
;;; defined by term-s-p and term-p. Our definitions will deal
;;; with the "non-proper" case in such a way that our theorems do not
;;; need hypothesis of the form "(term-p term)" or "(term-s-p term)"
;;; (except those concerning guard verification or closure properties,
;;; as we will see later).

;;; Thus, we can see any ACL2 object as a representation of a term, in
;;; the following way:

;;; - Variables are atomic objects.
;;; - Every consp object can be seen as the term with the top function
;;;   symbol in its car. The cdr is the list of its arguments.


;;; ====== VARIABLE-P
;;; x is a variable (in a wide sense)
;;; Similar to variable-s-p, we define variable-p, recognizing those
;;; ACL2 objects that can be considered as variables with this wide
;;; point of view.

(defun variable-p (x)
  (declare (xargs :guard t))
  (atom x))

;;; REMARKS:
;;; --------

;;; - Note that this function variable-p is not strictly needed (we
;;;   could use atom), but it improves readability of the proofs
;;;   developed by the prover.
;;; - This could be optimized if we used a macro definition instead of
;;;   defun. But we prefer to disable variable-p after proving its main
;;;   properties, for the sake of readability of theorems and proofs
;;;   (maybe we will modify it later).
;;; - Note that variable-s-p implies variable-p. The reverse implication
;;;   is not true.


;;; Before disabling variable-p, we prove its main property:

(defthm non-variables-are-consp
  (equal (variable-p x)
	 (not (consp x)))
  :rule-classes :compound-recognizer)

(in-theory (disable variable-p))


;;; IMPORTANT REMARK: from the discussions above, note that we are
;;; guided by the following principle:

;;; - To reason, it is better not to restrict the kind of objects we are
;;; deling with, since the theorems are more general, and often easier
;;; to prove (in addition, we will prove the corresponding closure
;;; theorems).
;;; - For execution (i.e., for guard verification), it is better to restrict
;;; if we can improve eficiency. For example, restricting variables and
;;; function symbols to be eqlablep objects allows us to replace eql by
;;; equal (when comparing variables or function symbols).

;;; ----------------------------------------------------------------------------
;;; 1.2 Some functions on terms.
;;; ----------------------------------------------------------------------------

;;; REMARK: Note that the following functions are defined for terms and
;;; for list of terms, using mutual recursion. If the flag flg is not nil,
;;; then we refer to terms and if flg is nil, we refer to lists of terms.

;;; ====== VARIABLES
;;; The list of variables of a term


(defun variables (flg term)
  (declare (xargs :guard (term-p-aux flg term)
		  :verify-guards nil))
  (if flg
      (if (variable-p term)
	  (list term)
	(variables nil (cdr term)))
    (if (endp term)
	nil
      (append (variables t (car term))
	      (variables nil (cdr term))))))

;;; Needed for guard verification:
(defthm variables-true-listp
  (true-listp (variables flg term)))

(verify-guards variables)


;;; ======= LIST-OF-VARIABLES-P
(defun list-of-variables-p (l)
  (if (endp l)
      t
    (and (variable-p (car l))
	 (list-of-variables-p (cdr l)))))


(defthm variables-is-a-list-of-variables
  (list-of-variables-p (variables flg term)))


(encapsulate
 ()

 (local
  (defthm list-of-variables-p-subsetp
    (implies (and (list-of-variables-p l)
		  (subsetp m l))
	     (list-of-variables-p m))))

 (defcong equal-set iff (list-of-variables-p l) 1))


;;; ======= MAKE-VAR and related macros


(defmacro make-var (t1 t2) `(list 'var ,t1 ,t2))

(defmacro compound-var (x) `(equal (car ,x) 'var))

(defmacro first-of-var (x)  `(second ,x))

(defmacro second-of-var (x)  `(third ,x))


;;; ======= VARIABLES-SET
;;; The set of variables of a term.

(defmacro variables-set (flg term)
  `(make-set (variables ,flg ,term)))



;;; ======= N-VARIABLES
;;; Number of distinct variables

(defmacro n-variables (flg term)
  `(len (variables-set ,flg ,term)))

;;; ======= SIZE
;;; Number of function symbols of a term

(defun size (flg term)
  (if flg
      (if (variable-p term)
	  0
	(+ 1 (size nil (cdr term))))
    (if (endp term)
	0
      (+ (size t (car term))
	 (size nil (cdr term))))))


;;; ======= LENGTH
;;; Number of symbols of a term (including variables)

(defun length-term (flg term)
  (if flg
      (if (variable-p term)
	  1
	(1+ (length-term nil (cdr term))))
    (if (endp term)
	0
      (+ (length-term t (car term))
	 (length-term nil (cdr term))))))

(defthm length-term-positive
  (< 0 (length-term t term))
  :rule-classes :linear)

;;; ========== SUBTERM

(defun subterm (flg t1 t2)
  (if flg
      (if (equal t1 t2)
	  t
	(if (variable-p t2)
	    nil
	  (subterm nil t1 (cdr t2))))
    (if (endp t2)
	nil
      (or (subterm t t1 (car t2))
	  (subterm nil t1 (cdr t2))))))





;;; ============================================================================
;;; 2. Substitutions.
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 2.1 Representation of substitutions.
;;; ----------------------------------------------------------------------------


;;; We represent substitutions as lists of pairs of the form
;;; (variable . term). As with terms, we can view every object as a
;;; substitution. See section 4 of basic.lisp.
;;; Anyway, we define substitution-p for guard verification purposes,
;;; and substitution-s-p to define substitutions in a given signature.


;;; ====== SUBSTITUTION-P

(defun substitution-p (l)
  (declare (xargs :guard t))
  (if (atom l)
      (equal l nil)
    (and (consp (car l))
	 (eqlablep (caar l))
	 (term-p (cdar l))
	 (substitution-p (cdr l)))))

;;; ====== SUBSTITUTION-S-P

(defun substitution-s-p (l)
  (if (atom l)
      (equal l nil)
    (and (consp (car l))
	 (variable-s-p (caar l))
	 (term-s-p (cdar l))
	 (substitution-s-p (cdr l)))))


;;; ----------------------------------------------------------------------------
;;; 2.2 Applying substitutions to terms (and lists of terms)
;;; ----------------------------------------------------------------------------

;;; ==== APPLY-SUBST

(defun apply-subst (flg sigma term)
  (declare (xargs :guard (and (alistp sigma)
			      (term-p-aux flg term))))
  (if flg
      (if (variable-p term)
	  (val term sigma)
	(cons (car term)
	      (apply-subst nil sigma (cdr term))))
    (if (endp term)
	term
      (cons (apply-subst t sigma (car term))
	    (apply-subst nil sigma (cdr term))))))

;;; REMARK: the substitution does not change the final tail of the lists
;;; (this is essential for having the same properties for proper and
;;; non-proper terms)

(defmacro instance (term sigma)
  `(apply-subst t ,sigma ,term))

;;; Some useful lemmas:

(defthm apply-consp-is-consp-list-of-terms
  (equal (consp (apply-subst nil sigma l))
	 (consp l)))

(defthm apply-returns-variable-implies-variable
  (implies (and flg (not (variable-p term)))
	   (not (variable-p (apply-subst flg sigma term)))))


(defthm equal-len-apply-subst-nil
  (equal (len (apply-subst nil sigma term))
	 (len term)))


(defthm apply-atom
  (implies (atom sigma)
	   (equal (apply-subst flg sigma term) term)))

(defthm one-identity-substitution
  (equal (apply-subst flg nil term) term))


(in-theory (disable apply-atom))




;;; The following lemmas proves closure properties w.r.t a given
;;; signature and they are needed for guard verification.

(defthm val-substitution-s-p-term-s-p
  (implies (and (substitution-s-p sigma)
		(variable-s-p  x))
	   (term-s-p (val x sigma))))

(defthm apply-subst-term-s-p-aux
  (implies (and (term-s-p-aux flg term)
		(substitution-s-p sigma))
	   (term-s-p-aux flg (apply-subst flg sigma term))))

(defthm apply-subst-term-p-aux
  (implies (and (term-p-aux flg term)
		(substitution-p sigma))
	   (term-p-aux flg (apply-subst flg sigma term)))
  :hints (("Goal" :use (:functional-instance
			apply-subst-term-s-p-aux
			(signat (lambda (x n) (eqlablep x)))
			(term-s-p-aux term-p-aux)
			(substitution-s-p substitution-p)))))

;;; IMPORTANT REMARK: It can be proved without the hint. But this a good
;;; example of how the concept of well-formed term is a particular case
;;; of the general concept of term in a given signature. We will use
;;; this technique very often.


;;; ==== SUBSTITUTE-VAR
;;; Replace every occurrence of a given variable x by a given term t1.

(defun substitute-var (x t1 flg term)
  (declare (xargs :guard (term-p-aux flg term)))
  (if flg
      (if (variable-p term)
	  (if (eql x term)
	      t1
	    term)
	(cons (car term)
	      (substitute-var x t1 nil (cdr term))))
    (if (endp term)
	term
      (cons (substitute-var x t1 t (car term))
	    (substitute-var x t1 nil (cdr term))))))



;;; ----------------------------------------------------------------------------
;;; 2.3 Functional aspects of substitutions.
;;; ----------------------------------------------------------------------------


;;; ====== COMPOSITION
;;; Composition of two substitutions

(defun composition (sigma1 sigma2)
  (declare (xargs :guard (and (alistp sigma1)
			      (substitution-p sigma2))))
  (if (endp sigma2)
      sigma1
    (cons (cons (caar sigma2) (apply-subst t sigma1 (cdar sigma2)))
	  (composition sigma1 (cdr sigma2)))))

;;; Lemmas:

(defthm value-composition
  (implies (variable-p x)
	   (equal (val x (composition sigma1 sigma2))
		  (apply-subst t sigma1 (val x sigma2)))))


(defthm composition-of-substitutions-apply
  (equal (apply-subst flg (composition sigma1 sigma2) term)
	 (apply-subst flg sigma1 (apply-subst flg sigma2 term))))

;;; Closure property

(defthm composition-substitution-s-p
  (implies (and (substitution-s-p sigma1)
		(substitution-s-p sigma2))
	   (substitution-s-p (composition sigma1 sigma2))))

;;; ========= RESTRICTION (see basic.lisp)

(defthm subsetp-restriction
  (implies (subsetp (variables flg term) l)
	   (equal (apply-subst flg (restriction sigma l) term)
		  (apply-subst flg sigma term))))

;;; ========= DOMAIN (see basic.lisp)

(defthm  x-not-in-domain-remains-the-same
  (implies (not (member x (domain sigma)))
	   (equal (val x sigma) x)))

(in-theory (disable x-not-in-domain-remains-the-same))


(defthm substitution-does-not-change-term
  (implies (disjointp (domain sigma) (variables flg term))
	   (equal (apply-subst flg sigma term) term))
  :hints (("Goal"
	   :in-theory (enable x-not-in-domain-remains-the-same))))


(in-theory (disable substitution-does-not-change-term))

;;; ========= UNION OF SUBSTITUTIONS

;;; Lemmas about union of substitutions of disjoint domains
;;; They will be used in mg-instance.lisp and in
;;; critical-pairs.lisp

(defthm only-the-first-bind-is-important-append
  (implies (subsetp (variables flg term) (domain sigma1))
	   (equal (apply-subst flg (append sigma1 sigma2) term)
		  (apply-subst flg sigma1 term))))

(local
 (defthm domains-disjointp-do-not-interfere-lemma
   (implies (and (disjointp (domain sigma1)
			    (domain sigma2))
		 (member term (domain sigma2)))
	    (equal (val term (append sigma1 sigma2))
		   (val term sigma2)))))

(defthm domains-disjointp-do-not-interfere
  (implies (and (disjointp (domain sigma1) (domain sigma2))
		(subsetp (variables flg term) (domain sigma2)))
	   (equal (apply-subst flg (append sigma1 sigma2) term)
		  (apply-subst flg sigma2 term))))


;;; ====== COINCIDE

;;; This will be our predicate for testing the equality
;;; of substitutions. sigma1 and sigma2 coincide in l if their
;;; restriction to l are equal.

(defun coincide (sigma1 sigma2 l)
  (if (atom l)
      T
    (and (equal (val (car l) sigma1)
		(val (car l) sigma2))
	 (coincide sigma1 sigma2 (cdr l)))))


;;; Properties of coincide


(encapsulate
 ()
 (local
  (defthm coincide-main-property
   (implies (and (coincide sigma1 sigma2 l)
		 (member x l))
	    (equal (equal (val x sigma1) (val x sigma2)) t))))
;;; Note: this form of the rule avoids cycles.


 (defthm coincide-in-term
   (implies (and
	     (subsetp (variables flg term) l)
	     (coincide sigma1 sigma2 l))
	   (equal (apply-subst flg sigma1 term)
		  (apply-subst flg sigma2 term)))
   :rule-classes nil))

(defthm coincide-reflexive
  (coincide sigma sigma l))

(defthm coincide-append
  (equal (coincide sigma sigma1 (append l m))
	 (and (coincide sigma sigma1 l)
		(coincide sigma sigma1 m))))


;;; ======== EXTENSION

;;; sigma1 "extends" sigma

(defmacro extension (sigma1 sigma)
  `(coincide ,sigma ,sigma1 (domain ,sigma)))

;;; ======== NORMAL-FORM-SUBST

;;; Given a term (or a list of terms), there are an infinite number of
;;; substitutions acting in the same way on the term. Sometimes, it will
;;; be useful to take a representative of all those functions.

(defmacro normal-form-subst (flg sigma term)
  `(restriction ,sigma (make-set (variables ,flg ,term))))

(defthm equal-normal-form-subst-wrt-term
  (equal (apply-subst flg (normal-form-subst flg sigma term) term)
	 (apply-subst flg sigma term))
  :rule-classes nil)


;;; ============================================================================
;;; 3. Systems of equations.
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 3.1 Representation
;;; ----------------------------------------------------------------------------


;;; Every object ecu can be seen as an equation,
;;; being its left side (car ecu) and its right side (cdr ecu).

;;; ========== LHS and RHS
;;; The left-hand side and right-hand side of
;;; an equation or rule:

(defmacro lhs (equ)
  `(car ,equ))

(defmacro rhs (equ)
  `(cdr ,equ))



;;; Note that atomic objects are equivalent to '(nil . nil). Every
;;; object can be interpreted as a system of equations: a list of
;;; equations. Note that atomic objects are empty systems.  It is
;;; interesting to note that we use the same representation for systems
;;; and for substitutions.
;;; Nevertheless, we define system-p for guard verification:

;;; ========= SYSTEM-P

(defun system-p (S)
  (declare (xargs :guard t))
  (if (atom S)
      (equal S nil)
    (and (consp (car S))
	 (term-p (caar S)) (term-p (cdar S))
	 (system-p (cdr S)))))

;;; And we define the concept of system of terms in a given signature

;;; ========= SYSTEM-P

(defun system-s-p (S)
  (if (atom S)
      (equal S nil)
    (and (consp (car S))
	 (term-s-p (caar S)) (term-s-p (cdar S))
	 (system-s-p (cdr S)))))


;;; The following lemmas are needed for guard verification:

;;; REMARK: Note that the following lemmas state a result for terms and
;;; substitutions in given signature and there are also the same results
;;; for well-formed terms and substitutitions. Since well-formed terms
;;; are a particular case of terms of a signature (the signature that
;;; returns t for every eqlablep object and natural number), we could
;;; have proved the results for well-formed terms by functional
;;; instantiation of the corresponding results for signatures. But the
;;; results are so simple that they are proved anyway in a very easily
;;; without functional instantiation.

(defthm system-p-implies-alistp
   (implies (system-p S) (alistp S))
   :rule-classes :forward-chaining)

(defthm system-p-append
   (implies (and (system-p S1) (system-p S2))
 	   (system-p (append S1 S2))))

(defthm system-s-p-append
  (implies (and (system-s-p S1) (system-s-p S2))
	   (system-s-p (append S1 S2))))


(defthm system-p-eliminate
   (implies (system-p S)
 	   (system-p (eliminate equ S))))

(defthm system-s-p-eliminate
   (implies (system-s-p S)
 	   (system-s-p (eliminate equ S))))

(defthm system-p-pair-args
   (implies
    (and (term-p-aux nil t1)
 	(term-p-aux nil t2))
    (system-p (first (pair-args t1 t2)))))

(defthm system-s-p-pair-args
  (implies
    (and (term-s-p-aux nil t1)
 	(term-s-p-aux nil t2))
    (system-s-p (first (pair-args t1 t2)))))


(defthm system-p-term-p-aux-arguments
   (implies (and (system-p S)
 		(member ecu S)
 		(not (variable-p (car ecu)))
 		(not (variable-p (cdr ecu))))
 	   (and (term-p-aux nil (cdar ecu))
 		(term-p-aux nil (cddr ecu)))))

(defthm system-s-p-term-p-aux-arguments
   (implies (and (system-s-p S)
 		(member ecu S)
 		(not (variable-p (car ecu)))
 		(not (variable-p (cdr ecu))))
 	   (and (term-s-p-aux nil (cdar ecu))
 		(term-s-p-aux nil (cddr ecu)))))


;;; ----------------------------------------------------------------------------
;;; 3.2 Some related function definitions.
;;; ----------------------------------------------------------------------------


;;; ===== DOMAIN and CO-DOMAIN
;;; already defined (see basic.lisp, section 4)

;;; ===== SYSTEM-VAR
;;; Variables of the system:

(defun system-var (S)
  (if (endp S)
      nil
    (append (variables t (caar S))
	    (append (variables t (cdar S))
		    (system-var (cdr S))))))


;;; ===== APPLY-SIST:
;;; Apply sigma to every term in system S.

(defun apply-syst (sigma S)
  (if (endp S)
      nil
    (cons (cons (apply-subst t sigma (caar S))
		(apply-subst t sigma (cdar S)))
	  (apply-syst sigma (cdr S)))))

;;; REMARK: After applying apply-syst, every element of the system is
;;; listp.


;;; ====== APPLY-RANGE:
;;; Apply sigma only to the right-hand sides of equations in system S.

(defun apply-range (sigma S)
  (if (endp S)
      nil
    (cons (cons (caar S) (apply-subst t sigma (cdar S)))
	  (apply-range sigma (cdr S)))))


;;; ===== SUBSTITUTE-SYST:
;;; Apply sigma= '((x . t1)) to every term in system S.

(defun substitute-syst (x t1 S)
  (declare (xargs :guard (system-p S)))
  (if (endp S)
      nil
    (cons (cons (substitute-var x t1 t (caar S))
		(substitute-var x t1 t (cdar S)))
	  (substitute-syst x t1 (cdr S)))))


;;; ===== SUBSTITUTE-RANGE:
;;; Apply sigma = '((x . t1)) to every term in system S.

(defun substitute-range (x t1 S)
  (declare (xargs :guard (system-p S)))
  (if (endp S)
      nil
    (cons (cons (caar S)
		(substitute-var x t1 t (cdar S)))
	  (substitute-range x t1 (cdr S)))))



;;; ======= UNION-SYSTEMS

(defun union-systems (S-T) (append (car S-T) (cdr S-T)))


;;; ======= NORMAL-FORM-SYST
;;; Pair of system in normal form

(defun normal-form-syst (S-sol)
  (declare (xargs :guard t))
  (not (and  (consp S-sol) (consp (car S-sol)))))



;;; ======= LENGTH-SYSTEM

(defun length-system (S)
  (if (endp S)
      0
    (+ (length-term t (caar S)) (length-term t (cdar S))
       (length-system (cdr S)))))



;;; ======= MATCHER
;;; Matcher of a system of equations

(defun matcher (sigma S)
  (if (endp S)
      t
    (and (equal (apply-subst t sigma (caar S))
		(cdar S))
	 (matcher sigma (cdr S)))))


;;; ====== SYSTEM-SUBSTITUTION
;;; The kind of substitutions that are matchers of themselves.

(defun system-substitution (S)
  (if (endp S)
      t
    (and
     (consp (car S))
     (variable-p (caar S))
     (not (member (caar S) (domain (cdr S))))
     (system-substitution (cdr S)))))



;;; ===== N-SYSTEM-VAR

(defun n-system-var (S)
  (len (make-set (system-var S))))


;;; ====== SIZE-SYSTEM


(defun size-system (S)
  (if (endp S)
      0
    (+ (size t (caar s))
       (size t (cdar s))
       (size-system (cdr s)))))


;;; ====== N-VARIABLES-RIGHT-HAND-SIDE



(defun n-variables-right-hand-side (S)
  (cond ((endp S) 0)
	((variable-p (cdar S)) (1+ (n-variables-right-hand-side (cdr S))))
	(t (n-variables-right-hand-side (cdr S)))))




;;; ======= UNIFICATION-MEASURE

(defun unification-measure (S-sol)
  (cons  (cons (1+ (n-system-var (first S-sol)))
	       (size-system (first S-sol)))
	 (n-variables-right-hand-side (first S-sol))))


;;; ----------------------------------------------------------------------------
;;; 3.3 Solutions of systems. Idempotent substitutions.
;;; ----------------------------------------------------------------------------



;;; ==== SOLUTION
;;; Solution of system of equations.
;;; A substitution is a solution of a system if its a solution of every
;;; member of the system. A substitution sigma is a solution of an
;;; equation ecu if sigma(car(ecu)) = sigma (cdr (ecu)). Two systems are
;;; equivalent if they have the same set of solutions.


(defun solution (sigma S)
  (if (endp S)
      t
    (and (equal (apply-subst t sigma (caar S))
		(apply-subst t sigma (cdar S)))
	 (solution sigma (cdr S)))))


;;; ===== IDEMPOTENT SYSTEMS/SUBSTITUTIONS

;;; Some substitutions are solution
;;; of themselves. We then call that substitution idempotent.
;;; Its domain is a set of variables and the variables of its
;;; co-domain are disjoint with its domain.

(defun idempotent (S)
  (and (system-substitution S)
       (disjointp (variables nil (co-domain S)) (domain S))))

;;; REMARK: In the literature, idempotent substitutions are defined as
;;; substitutions sigma such that sigma·sigma = sigma. But this
;;; definition involves functional equality. We will see that the above
;;; definition implies this property (see main-property-mgs in the book
;;; unification-definition.lisp) Nevertheless, the definition does not
;;; characterize the property. For example, the substitution represented
;;; by ((x . y) (x . z)) verify that property but is not idempotent in
;;; our sense. Fortunately, it can be proved that there exists a
;;; functionally equivalent idempotent (in our sense) substitution, ((x
;;; . y)) in this case.

;;; ············································································
;;; 3.3.1 The main property of idempotent substitutions.
;;; ············································································

;;; .... PROOF PLAN:

; We want to prove idempotence-main-lemma (see below)
; idempotence-main-lemma fails in:

;          (IMPLIES (AND (SOLUTION S X)
;                        (SYSTEM-SUBSTITUTION S)
;                        (DISJOINT (VARIABLES F (CO-DOMAIN S)) (DOMAIN S))
;                        (SETP (DOMAIN S))
;                        (MEMBER (CONS V W) S)
;                        (SUBSETP X S))
;                   (EQUAL (APPLY T S V)
;                          (APPLY T S W))).


; Strategy to prove this:

; 1) (apply-subst t sigma v) is (val v sigma) if sigma is
; system-substitution and (v . w) is in sigma
; 2) (val v sigma) is w si (v . w) is in s and (domain s) is setp
; 3) (apply-subst t sigma w) is w if (domain s) is disjoint with
; variables of w (this has been proved before, in terms.lisp)
; 4)  if (disjointp (variables nil (co-domain s)) l), and (v . w) is a
; member of s, the variables of w is disjoint with l.
;;; We compile these properties in the following encapsulate:


(local
 (encapsulate
  ()
  (local
   (defthm system-substitution-properties
     (implies (and (system-substitution sigma)
		   (member (cons v w) sigma))
	      (and (variable-p v) (equal (val v sigma) w)))))

  (local
   (defthm co-domain-disjoint-lemma
     (implies (and (disjointp (variables nil (co-domain s)) l)
		   (member (cons v w) s))
	      (disjointp (variables t w) l))
  :rule-classes nil
  :hints (("Goal" :induct (len s)))))

  (local
   (defthm co-domain-disjoint
     (implies (and (disjointp (variables nil (co-domain s)) (domain s))
		   (member (cons v w) s))
	      (equal (apply-subst t s w) w))
     :hints (("Goal" :use
	      (:instance co-domain-disjoint-lemma
			  (l (domain s)))
	      :in-theory (enable substitution-does-not-change-term )))))

  (defthm idempotence-main-lemma
    (implies (and (idempotent S)
		  (subsetp sol S))
	     (solution S sol)))))

;;; And the main property of idempotent substitutions.

(defthm idempotence
  (implies (idempotent S)
	   (solution S S)))


;;; ============================================================================
;;; 4. The tree structure of a term
;;; ============================================================================


;;; ----------------------------------------------------------------------------
;;; 4.1 Positions, occurrences and replacements.
;;; ----------------------------------------------------------------------------

;;; ============ POSITIONS OF A TERM

(defun position-p (pos term)
  (declare (xargs :guard (term-p term)
		  :verify-guards nil))
  (cond ((atom pos) (equal pos nil))
	((variable-p term) nil)
	(t
	 (and (integerp (car pos)) (< 0 (car pos))
	      (<= (car pos) (len (cdr term)))
	      (position-p (cdr pos)
			 (nth (- (car pos) 1) (cdr term)))))))



;;; ====== OCURRENCE IN A TERM AT A POSITION

(defun occurrence (term pos)
  (declare (xargs :guard
		  (and (term-p term)
		       (position-p pos term))
		  :verify-guards nil))
  (if (endp pos)
      term
    (occurrence (nth (- (car pos) 1) (cdr term))
		(cdr pos))))


;;; ====== REPLACING A OCCURRENCE IN A TERM FOR OTHER TERM

(defun replace-term (term1 pos term2)
  (declare (xargs :guard
		  (and  (term-p term1)
			(position-p pos term1))
		  :verify-guards nil))
  (if (endp pos)
      term2
    (cons (car term1)
	  (replace-list (cdr term1)
			(- (car pos) 1)
			(replace-term (nth (- (car pos) 1) (cdr term1))
				      (cdr pos)
				      term2)))))

;;; Guard verification

(encapsulate
 ()

 (local
  (defthm term-p-aux-true-listp
    (implies (and (term-p-aux flg term)
		  (implies flg (not (variable-p term))))
	     (true-listp term))))

 (local
  (defthm term-p-aux-true-listp
    (implies (and (term-p-aux flg term)
		  (implies flg (not (variable-p term))))
	     (true-listp term))))


 (local
  (defthm term-p-aux-nth
    (implies (term-p-aux nil term)
	     (term-p-aux t (nth i term)))))

 (verify-guards position-p)
 (verify-guards occurrence)
 (verify-guards replace-term))

;;; ----------------------------------------------------------------------------
;;; 4.2 Some results concerning the tree structure of a term
;;; ----------------------------------------------------------------------------

;;; ············································································
;;; 4.2.1 Concatenation of positions
;;; ············································································

(defthm position-p-append
  (implies (position-p p1 term)
	   (iff (position-p (append p1 p2) term)
		(position-p p2 (occurrence term p1)))))


(defthm occurrence-append
  (implies (and (position-p p1 term)
		(position-p p2 (occurrence term p1)))
	   (equal (occurrence term (append p1 p2))
		  (occurrence (occurrence term p1) p2))))


(defthm replace-term-append
  (implies (position-p (append pos1 q) term)
	   (equal (replace-term term (append pos1 q) x)
		  (replace-term term pos1
				(replace-term (occurrence term pos1)
					      q x)))))


;;; ············································································
;;; 4.2.2 Substitutions and positions
;;; ············································································

(defthm nth-apply-subst
  (implies (and (integerp i)
		(<= 0 i)
		(< i (len l)))
	   (equal (nth i (apply-subst nil sigma l))
		  (apply-subst t sigma (nth i l)))))


(defthm position-p-instance
  (implies (position-p pos term)
	   (position-p pos (instance term sigma))))

(defthm occurrence-instance
  (implies (position-p pos term)
	   (equal
	    (occurrence (instance term sigma) pos)
	    (instance (occurrence term pos) sigma))))

(local
 (defthm replace-list-instance
   (equal
    (apply-subst nil sigma (replace-list l i x))
    (replace-list (apply-subst nil sigma l) i (apply-subst t sigma x)))))


(defthm replace-term-instance
  (implies (position-p pos term)
	   (equal
	    (replace-term (instance term sigma) pos
			  (instance t1 sigma))
	    (instance (replace-term term pos t1) sigma))))


;;; ············································································
;;; 4.2.3 Prefix positions
;;; ············································································

(local
 (defthm equal-len-replace-list
   (equal (len (replace-list l i x))
	  (len l))))

(defthm position-p-prefix
  (implies (position-p pos1 term1)
	   (iff (position-p (append pos1 pos2)
			    (replace-term term1 pos1 term2))
		(position-p pos2 term2))))

(defthm occurrence-prefix
  (implies (and (position-p pos1 term1)
		(position-p pos2 term2))
	   (equal (occurrence
		   (replace-term term1 pos1 term2)
		   (append pos1 pos2))
		  (occurrence term2 pos2))))

(defthm replace-term-prefix
   (implies (and (position-p pos1 term1)
		 (position-p pos2 term2))
	    (equal (replace-term
		    (replace-term
		     term1 pos1 term2)
		    (append pos1 pos2)
		    term3)
		   (replace-term
		    term1 pos1
		    (replace-term term2 pos2 term3)))))



;;; ············································································
;;; 4.2.4 Disjoint positions
;;; ············································································

(local
 (defun induct-position-p-disjoint (pos1 pos2 term)
   (cond ((variable-p term) t)
	 ((and (consp pos1) (consp pos2))
	  (if (equal (car pos1) (car pos2))
	      (induct-position-p-disjoint
	       (cdr pos1)
	       (cdr pos2)
	       (nth (- (car pos1) 1) (cdr term)))
	    t))
	 (t t))))

(local
 (defthm equality-of-predecesor
   (implies (and (integerp i) (integerp j))
	    (iff (equal (+ -1 i) (+ -1 j))
		 (equal i j))))) ;;; I don't like this rule.

(defthm position-p-disjoint-positions
  (implies (and (position-p pos1 term)
		(position-p pos2 term)
		(disjoint-positions pos1 pos2))
	   (position-p pos1 (replace-term term pos2 x)))
  :hints (("Goal"
	   :induct (induct-position-p-disjoint pos1 pos2 term)
	   :expand ((:free (term i pos x)
			   (replace-term term (cons i pos) x))
		    (:free (i pos fn args)
			   (position-p (cons i pos)
				       (cons fn args)))))))

(defthm occurrence-disjoint-positions
  (implies (and (position-p pos1 term)
		(position-p pos2 term)
		(disjoint-positions pos1 pos2))
	   (equal (occurrence (replace-term term pos1 x) pos2)
		  (occurrence term pos2)))
  :hints (("Goal"
	   :induct (induct-position-p-disjoint
		    pos1 pos2 term)
	   :expand ((:free (term i pos x)
			   (replace-term term (cons i pos) x))
		    (:free (i pos fn args)
			   (occurrence (cons fn args)
				       (cons i pos)))))))


(defthm replace-term-disjoint-positions
  (implies (and
	    (position-p pos1 term)
	    (position-p pos2 term)
	    (disjoint-positions pos1 pos2))
	   (equal (replace-term (replace-term term pos1 x) pos2 y)
		  (replace-term (replace-term term pos2 y) pos1 x)))
  :hints (("Goal" :induct (induct-position-p-disjoint pos1 pos2 term)
	   :expand ((:free (term i pos x)
			   (replace-term term (cons i pos) x))
		    (:free (i pos fn args)
			   (position-p (cons i pos) (cons fn args)))))))


;;; ············································································
;;; 4.2.5 Disabling the theory
;;; ············································································

(defconst *tree-structure-of-terms*
  '(position-p-append occurrence-append replace-term-append
    position-p-instance occurrence-instance replace-term-instance
    position-p-prefix occurrence-prefix replace-term-prefix
    position-p-disjoint-positions occurrence-disjoint-positions
    replace-term-disjoint-positions))

(in-theory
 (set-difference-theories (current-theory :here) *tree-structure-of-terms*))

;;; ----------------------------------------------------------------------------
;;; 4.3 Recursive versions of position-p, occurrence and replace-term
;;; ----------------------------------------------------------------------------

;;; The definition of position-p, occurrence and replace-term is done
;;; following the classical definition in the literature. Sometimes,
;;; this kind of definition does not provide a good induction scheme
;;; when proving properties relating this functions with other functions
;;; defined in a mutually recursive way, for terms and for lists of
;;; terms. For that reason we will give and alternative definition of
;;; position-p, occurrence and replace-term, in a mutually recursive
;;; style, and we prove that both definitions are equivalente for
;;; terms.

;;; POSITION-P-REC

(defun position-p-rec (flg pos term)
  (declare (xargs :guard t))
  (if flg
      (cond ((atom pos) (equal pos nil))
	    ((variable-p term) nil)
	    (t (position-p-rec nil pos (cdr term))))
    (cond ((or (atom term) (atom pos)) nil)
	  ((eql 1 (car pos))
	   (position-p-rec t (cdr pos) (car term)))
	  ((and (integerp (car pos)) (<= 2 (car pos)))
	   (position-p-rec nil (cons (- (car pos ) 1) (cdr pos)) (cdr
								 term)))
	  (t nil))))

;;; The two definitions are the same, as stated in the following
;;; rewrite rule

(encapsulate
 ()
 (defthm equal-position-p-position-p-rec-lemma
   (if flg
       (equal (position-p-rec flg pos term)
	      (position-p pos term))
     (equal (position-p-rec flg pos term)
	    (and (consp pos) (consp term)
		 (integerp (car pos)) (<= 1 (car pos))
		 (<= (car pos) (len term))
		 (position-p (cdr pos) (nth (- (car pos) 1) term)))))
  :rule-classes nil)

 (defthm equal-position-p-position-p-rec
   (equal (position-p pos term)
	  (position-p-rec t pos term))
   :hints (("Goal" :use (:instance
			 equal-position-p-position-p-rec-lemma
			 (flg t))))))




;;; OCCURRENCE-REC

(defun occurrence-rec (flg term pos)
  (if flg
      (cond ((endp pos) term)
	    ((variable-p term) nil)
	    (t (occurrence-rec nil (cdr term) pos)))
    (cond ((or (endp term) (endp pos)) nil)
	  ((equal (car pos) 1)
	   (occurrence-rec t (car term) (cdr pos)))
	  ((and (integerp (car pos)) (<= 2 (car pos)))
	   (occurrence-rec nil (cdr term) (cons (- (car pos ) 1) (cdr pos))))
	  (t nil))))

;;; The two definitions are the same, as stated in the following
;;; rewrite rule

(encapsulate
 ()
 (local
  (defthm equal-occurrence-occurrence-rec-lemma
    (implies (position-p-rec flg pos term)
	     (if flg
		 (equal (occurrence-rec flg term pos)
			(occurrence term pos))
	       (equal (occurrence-rec flg term pos)
		      (occurrence (nth (- (car pos) 1) term) (cdr pos)))))
    :rule-classes nil))


 (defthm equal-occurrence-occurrence-rec
   (implies (position-p-rec t pos term)
	    (equal (occurrence term pos)
		   (occurrence-rec t term pos)))
   :hints (("Goal" :use (:instance
			 equal-occurrence-occurrence-rec-lemma (flg t))))))





;;; REPLACE-TERM-REC

(defun replace-term-rec (flg term1 pos term2)
  (if flg
      (cond ((endp pos) term2)
	    ((variable-p term1) nil)
	    (t (cons (car term1)
		     (replace-term-rec nil (cdr term1) pos term2))))
    (cond ((or (endp term1) (endp pos)) nil)
	  ((equal (car pos) 1)
	   (cons (replace-term-rec t (car term1) (cdr pos) term2)
		 (cdr term1)))
	  ((and (integerp (car pos)) (<= 2 (car pos)))
	   (cons (car term1)
		 (replace-term-rec nil (cdr term1)
				(cons (- (car pos ) 1) (cdr pos)) term2)))
	  (t nil))))


(encapsulate
 ()
 (local
  (defthm equal-replace-term-replace-term-rec-lemma
    (implies (position-p-rec flg pos term1)
	     (if flg
		 (equal (replace-term-rec flg term1 pos term2)
			(replace-term term1 pos term2))
	       (equal (replace-term-rec flg term1 pos term2)
		      (replace-list
		       term1
		       (- (car pos) 1)
		       (replace-term (nth (- (car pos) 1) term1)
				     (cdr pos) term2)))))
    :rule-classes nil))


  (defthm equal-replace-term-replace-term-rec
    (implies (position-p-rec t pos term1)
	     (equal (replace-term term1 pos term2)
		    (replace-term-rec t term1 pos term2)))
    :hints (("Goal" :use (:instance
			 equal-replace-term-replace-term-rec-lemma
			 (flg t))))))




;;; ----------------------------------------------------------------------------
;;; 4.2 Related closure theorems
;;; ----------------------------------------------------------------------------

;;; The following is a good example of how these "-aux" versions can
;;; help to prove properties. Recall that term-s-p and term-p are
;;; defined by mutual recursion (functions term-s-p-aux and
;;; term-p-aux). If we want to prove that occurrence and replace-term
;;; are closed in the set of terms of a given signature, then it is much
;;; easier to prove first the analogous theorems for occurrence-rec, and
;;; replace-term-rec (i.e. the theorem for terms and for lists of terms
;;; at the same time), and then to export those properties to the
;;; original definitions of position-p, occurrence and replace-term.

;;; The "-aux" versions
(defthm occurrence-term-s-p-aux
  (implies (and (term-s-p-aux flg term)
		(position-p-rec flg pos term))
	   (term-s-p (occurrence-rec flg term pos))))

(encapsulate
 ()

 (local
  (defthm replace-term-rec-equal-len
    (implies (position-p-rec nil pos term)
	     (equal (len (replace-term-rec nil term pos t1))
		    (len term)))))

 (defthm replace-term-rec-term-s-p-aux
   (implies (and (term-s-p-aux flg term)
		 (position-p-rec flg pos term)
		 (term-s-p t1))
	    (term-s-p-aux flg (replace-term-rec flg term pos t1)))))



;;; The intended theorems are now an easy consequence of the
;;; equivalence lemmas between the original definitions and its "-aux"
;;; versions

(defthm occurrence-term-s-p
  (implies (and (term-s-p term)
		(position-p pos term))
	   (term-s-p (occurrence term pos))))

(defthm replace-term-term-s-p
  (implies (and (term-s-p term)
		(position-p pos term)
		(term-s-p t1))
	   (term-s-p (replace-term term pos t1))))


;;; Theorems needed for guard verification:


(defthm occurrence-term-p
  (implies (and (term-p term)
		(position-p pos term))
	   (term-p (occurrence term pos)))
  :hints (("Goal" :use (:functional-instance
			occurrence-term-s-p
			(signat (lambda (x n) (eqlablep x)))
			(term-s-p-aux term-p-aux)))))



(defthm replace-term-term-p
  (implies (and (term-p term)
		(position-p pos term)
		(term-p t1))
	   (term-p (replace-term term pos t1)))
  :hints (("Goal" :use (:functional-instance
			replace-term-term-s-p
			(signat (lambda (x n) (eqlablep x)))
			(term-s-p-aux term-p-aux)))))


;;; ----------------------------------------------------------------------------
;;; 4.3 Another useful rules
;;; ----------------------------------------------------------------------------

;;; Here we list some additional rules which more easily proved using
;;; the "-aux" versions of position-p, occurrence and replace-term.

(local
 (defthm occurrence-position-p-rec-relation
   (implies (position-p-rec flg pos term)
            (iff (equal t1 (occurrence-rec flg term pos))
                 (equal (replace-term-rec flg term pos t1)
                        term)))))

(defthm occurrence-position-relation
  (implies (position-p pos term)
           (iff (equal t1 (occurrence term pos))
                (equal (replace-term term pos t1)
                       term))))

;;; REMARK: very useful rule!!! (take care with it)
(in-theory (disable occurrence-position-relation))


;;; Now we disable the theorems of equivalence between the "-aux"
;;; versions and the original functions. We will enable locally when
;;; needed:



(defconst *position-rec-versions*
  '(equal-position-p-position-p-rec
    equal-occurrence-occurrence-rec
    equal-replace-term-replace-term-rec))

(in-theory
 (set-difference-theories (current-theory :here) *position-rec-versions*))





