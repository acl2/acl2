;;; ============================================================================;;; list-unification-rules.lisp
;;; Título: Unification as transformation rules
;;;         (using a  prefix representation of terms)
;;; ============================================================================


#| To certify this book:

(in-package "ACL2")

(certify-book "list-unification-rules")

|#

(in-package "ACL2")
(include-book "subsumption-subst")

;;; ============================================================================
;;;
;;; 0) Introducción
;;;
;;; ============================================================================

;;; In this book we specify a set of transformation rules acting on
;;; systems of equations,. This transformation rules, due to Martelli
;;; and Montanari, applied non--deterministically, can be used to obtain
;;; most general solutions of system of equations; that is, solutions of
;;; systems of equations that subsume every other solution (whenever
;;; they exist).

;;; In this book we specify a set of transformation rules acting on
;;; systems of equations,. This transformation rules, due to Martelli
;;; and Montanari, applied non--deterministically, can be used to obtain
;;; most general solutions of system of equations; that is, solutions of
;;; systems of equations that subsume every other solution (whenever
;;; they exist).

;;; In this book we consider terms, equations and systems of equations
;;; represented as lists, in prefix notation. The concepts and results
;;; needed about first--order terms and substitutions are taken from the
;;; following books:

;;; *)
;;;   {\tt basic.lisp}: some basic results about lists, association
;;;   lists, etc.
;;; *)
;;;   {\tt terms.lisp}: basic concepts about terms and substitutions.
;;; *)
;;;   {\tt matching.lisp}: a pattern for a rule--based matching
;;;   algorithm.
;;; *)
;;;   {\tt subsumption.lisp}: the subsumption relation between terms.
;;; *)
;;;  {\tt subsumption-subst.lisp}: the subsumption relation between
;;;  substitutions.
;;; -)

;;; A substitution $\sigma$ is a {\em solution} of an equation $t_1 =
;;; t_2$ if $\sigma(t_1)=\sigma(t_2)$, and is a solution of a system of
;;; equations $S$ if it is a solution of every member of $S$.  A solution of
;;; $S$ is a {\em most general solution
;;; (mgs)} if it subsumes every other solution of $S$.

;;; The relation we are going to formalize in this book is usually noted
;;; as $\Rightarrow_u$, and defined by the following set of
;;; transformation rules, acting of pair of systems of equations. The
;;; first system contains the equations to be solved and the second
;;; system contains the solution partially computed. Here $\bot$
;;; represents failure.

;;; $$\begin{array}{lll}
;;; \mbox{{\bf Delete}:} & \{t= t\}\cup R;U & \Rightarrow_u R;U \\
;;; \mbox{{\bf Check}:} & \{x= t\}\cup R;U & \Rightarrow_u \bot\\
;;;  & &\mbox{{\small if $x\in var(t)$ and $x\not=t$}}\\
;;; \mbox{{\bf Eliminate}:} & \{x= t\}\cup R;U & \Rightarrow_u
;;; \theta(R); \{x= t\}\cup \theta(U) \\
;;;  & &\mbox{{\small if $x\in X$, $x\notin var(t)$ and
;;;  $\theta=\{x\mapsto t\}$}}\\
;;; \mbox{{\bf Decompose}:} & \{f(s_1,\ldots,s_n)=
;;;        f(t_1,\ldots,t_n)\}\cup R;U & \Rightarrow_u \{s_1=
;;; t_1,\ldots,s_n= t_n\}\cup R;U\\
;;; \mbox{{\bf Clash }:} & \{f(s_1,\ldots,s_n)=
;;;        g(t_1,\ldots,t_m)\}\cup R;U & \Rightarrow_s \bot \mbox{, {\small
;;; if $n\not= m$ or $f\not= g$}}\\
;;; \mbox{{\bf Orient}:} & \{t= x\}\cup R;U & \Rightarrow_u \{x= t\}\cup R;U \\
;;;  & &\mbox{{\small if $x\in X$, $t\notin X$}}\\
;;; \end{array}$$

;;; To obtain a most general solution of a system of equations $S$ (or
;;; detect its unsolvability), we can apply this rules
;;; non--deterministically, starting in the pair of systems
;;; $S;\emptyset$, until $\bot$ is obtained or a pair of systems
;;; $\emptyset;\sigma$ is obtained. In the first case, the system $S$ is
;;; unsolvable. In the second case $\sigma$ is most general solution of
;;; $S$.

;;; In this book we formalize in ACL2 this result. Note that we are not
;;; going to define an {\em algorithm} to apply the rules. We only
;;; describe the formal properties of application of sequences of the
;;; rules of transformations. From these properties it is easy to
;;; conclude that every algorithm that applies the rules until a
;;; solution or failure is obtained, is an algorithm that computes most
;;; general solutions.

;;; So in this book:

;;; *)
;;;   Definition of the relation $\Rightarrow_u$. We represent the
;;;   relation $\Rightarrow_u$ as a reduction relation. That is, we
;;;   consider a set of {\em operators} that can be applied to a set of
;;;   objects ({\em pairs of systems of equations}). To specify this
;;;   reduction relation we define the {\em applicability test} of the
;;;   operators and the {\em one--reduction step} (the result of
;;;   applying an operator to an object). See \cite{amai-jruiz} for more
;;;   details about the formalization of abstract reductions.
;;; *)
;;;   The transformation relation preserves the set of solutions and
;;;   idempotency of the second system (under certain conditions).
;;; *)
;;;   The transformation relation is terminating.
;;; *)
;;;   A finite sequence of transformation steps (until there is no
;;;   applicable rule), ends with a most general solution of the
;;;   original system, or failure, if there is no solution.
;;; -)


;;; ============================================================================
;;;
;;; 1) Definition of $\Rightarrow_u$ as a reduction relation
;;;
;;; ============================================================================

;;; Our goal in this section is to define the transformation relation of
;;; Martelli and Montanari. We consider that every transformation rule
;;; can be represented as an {\em operator}, indicating the equation to
;;; be transformed and the specific transformation to be performed. With
;;; this idea, the transformation relation can be defined by means of
;;; two ACL2 functions. A function {\tt unif-legal-s}, checking if it is
;;; {\em legal} to apply a given operator to a pair of systems of
;;; equations. And a second function {\tt unif-reduce-one-step-s} that
;;; computes the result of applying a given (legal) operator to a pair
;;; of systems of equations.

;;; Pairs of systems of equations will be represented as lists of the
;;; form {\tt (S sol)}, where {\tt S} is a system of equations and {\tt
;;; sol} is a substitution. Failure will be represented as {\tt
;;; nil}. See {\tt terms.lisp} for a description of how we represent
;;; systems and substitutions.

;;; Operators are represented by lists of two elements: the name of the
;;; rule to be applied and a natural number indicating the equation of
;;; the first system (the system of equations to be solved) that will be
;;; considered. That is, we have seven types of operators:

;;; 1)
;;; {\tt (delete $N$)}: delete  equation $N$.
;;; 2)
;;; {\tt (decompose $N$)}: decompose equation $N$.
;;; 3)
;;; {\tt (orient $N$)}: orient equation $N$.
;;; 4)
;;; {\tt (eliminate $N$)}: eliminate equation N.
;;; 5)
;;; {\tt (clash1 $N$)}: clash for different top function symbol
;;; (equation $N$).
;;; 6)
;;; {\tt (clash2 $N$)}: clash for different number of arguments
;;; (equation $N$).
;;; 7)
;;; {\tt (occur-check $N$)}: detect occur-check (equation $N$).
;;; -)

;;; Definition of the function {\tt unif-legal-s} (the applicability
;;; test). Note the auxiliary functions for every type of operator.


(defun unif-legal-s-delete (t1 t2)
  (equal t1 t2))

(defun unif-legal-s-decompose (t1 t2)
  (and (not (variable-p t1))
       (not (variable-p t2))
       (equal (car t1) (car t2))
       (mv-let (pair-args bool)
	       (pair-args (cdr t1) (cdr t2))
	       (declare (ignore pair-args))
	       bool)))

(defun unif-legal-s-clash1 (t1 t2)
  (and (not (variable-p t1))
       (not (variable-p t2))
       (not (equal (car t1) (car t2)))))

(defun unif-legal-s-clash2 (t1 t2)
  (and (not (variable-p t1))
       (not (variable-p t2))
       (mv-let (pair-args bool)
	       (pair-args (cdr t1) (cdr t2))
	       (declare (ignore pair-args))
	       (not bool))))

(defun unif-legal-s-orient (t1 t2)
  (and (not (variable-p t1))
       (variable-p t2)))

(defun unif-legal-s-eliminate (t1 t2)
  (and (variable-p t1)
       (not (member t1 (variables t t2)))))


(defun unif-legal-s-occur-check (t1 t2)
  (and (variable-p t1)
       (not (equal t1 t2))
       (member t1 (variables t t2))))

(defun unif-legal-s (S-sol op)
  (let ((name (first op))
	(equ-n (second op))
	(tbs-s (car S-sol)))
    (and (natp equ-n)
	 (< equ-n (len tbs-s))
	 (let* ((equ (nth equ-n tbs-s))
		(t1 (car equ))
		(t2 (cdr equ)))
	   (case name
		 (delete (unif-legal-s-delete t1 t2))
		 (decompose (unif-legal-s-decompose t1 t2))
		 (orient (unif-legal-s-orient t1 t2))
		 (eliminate (unif-legal-s-eliminate t1 t2))
		 (clash1 (unif-legal-s-clash1 t1 t2))
		 (clash2 (unif-legal-s-clash2 t1 t2))
		 (occur-check (unif-legal-s-occur-check t1 t2))
		 (t nil))))))


;;; Definition of the function {\tt unif\--reduce\--one\--step\--s},
;;; implementing the application of one step of transformation. Note
;;; again the auxiliary functions for every type of operator.

(defun unif-reduce-one-step-s-delete (equ R sol)
  (declare (ignore equ))
  (list R sol))

(defun unif-reduce-one-step-s-decompose (equ R sol)
  (let ((t1 (car equ)) (t2 (cdr equ)))
    (mv-let (pair-args bool)
	    (pair-args (cdr t1) (cdr t2))
	    (declare (ignore bool))
	    (list (append pair-args R) sol))))


(defun unif-reduce-one-step-s-clash1 (equ R sol)
  (declare (ignore equ R sol))
  nil)

(defun unif-reduce-one-step-s-clash2 (equ R sol)
  (declare (ignore equ R sol))
  nil)

(defun unif-reduce-one-step-s-orient (equ R sol)
  (let ((t1 (car equ)) (t2 (cdr equ)))
    (list (cons (cons t2 t1) R) sol)))


(defun unif-reduce-one-step-s-eliminate (equ R sol)
  (let ((sigma (list equ)))
    (list  (apply-syst sigma  R)
	   (cons  equ (apply-range sigma sol)))))


(defun unif-reduce-one-step-s-occur-check (equ R sol)
  (declare (ignore equ R sol))
  nil)



(defun eliminate-n (n l)
  (if (zp n)
      (cdr l)
    (cons (car l) (eliminate-n (1- n) (cdr l)))))

(defun unif-reduce-one-step-s (S-sol op)
  (let* ((name (first op))
	 (equ-n (second op))
	 (S (first S-sol))
	 (R (eliminate-n equ-n S))
	 (sol (second S-sol))
	 (equ (nth equ-n S)))
    (case name
      (delete (unif-reduce-one-step-s-delete equ R sol))
      (decompose (unif-reduce-one-step-s-decompose equ R sol))
      (orient (unif-reduce-one-step-s-orient equ R sol))
      (eliminate (unif-reduce-one-step-s-eliminate equ R sol))
      (clash1 (unif-reduce-one-step-s-clash1 equ R sol))
      (clash2 (unif-reduce-one-step-s-clash2 equ R sol))
      (occur-check (unif-reduce-one-step-s-occur-check equ R sol))
      (t nil))))

;;; ============================================================================
;;;
;;; 2) The transformations preserve the set of solutions
;;;
;;; ============================================================================

;;; We prove now that the rules of transformation preserve the
;;; solutions of the pair of systems of equations. That is, we want to
;;; prove the following theorems:

; (defthm mm-preserves-solutions-1
;   (implies (and (unif-legal-s S-sol op)
; 		  (solution sigma (both-systems S-sol)))
; 	   (solution sigma (both-systems (unif-reduce-one-step-s S-sol op)))))



; (defthm mm-preserves-solutions-2
;   (implies (and (unif-legal-s S-sol op)
; 		  (unif-reduce-one-step-s S-sol op)
; 		  (solution sigma (both-systems (unif-reduce-one-step-s S-sol
; 			 					  op))))
; 	     (solution sigma (both-systems S-sol))))

; (defthm mm-preserves-solutions-3
;   (implies (and (unif-legal-s S-sol op)
; 		  (not (unif-reduce-one-step-s S-sol op)))
; 	     (not (solution sigma (both-systems S-sol)))))



;;; First, let us define a congruence that will be useful to deal with
;;; selection of arbitrary equations. The following proves that @perm@
;;; is a congruence with respect to the second argument of @solution@.

(local
 (encapsulate
  ()

  (local
   (defthm member-solution
     (implies (and
	       (member ecu S)
	       (solution sigma S))
	      (equal (instance (car ecu) sigma)
		     (instance (cdr ecu) sigma)))))

  (local
   (defthm solution-delete-one
     (implies (solution sigma S)
	      (solution sigma (delete-one x S)))))

  (local
   (defthm solution-delete-one-2
    (implies (and (solution sigma (delete-one x S))
		  (equal (instance (car x) sigma)
			 (instance (cdr x) sigma)))
	     (solution sigma S))))

  (defcong perm iff (solution sigma s) 2)))


;;; And the following defines a rewriting rule that will be useful to
;;; rewrite system of equations (when reasoning about them) in such a
;;; way that the seleceted equation comes in front of the system.

(local
 (encapsulate
  ()
  (local
   (defthm perm-nth-eliminate-n
     (implies (and (natp n)
		   (< n (len l)))
	      (perm l (cons (nth n l) (eliminate-n n l))))
     :rule-classes nil))

  (defthm perm-nth-eliminate-n-instance
    (let ((S (car S-sol)))
      (implies (and (< n (len S)) (natp n)) ;;; The order of the
					    ;;; hypothesis is
					    ;;; important (free vars)
	       (perm S (cons (nth n S) (eliminate-n n S)))))
    :hints (("Goal" :use (:instance perm-nth-eliminate-n
				    (l (car S-sol))))))))



;;; And also some general rules that will be useful:


(local
 (defthm solution-append
   (equal (solution sigma (append S1 S2))
	  (and (solution sigma S1) (solution sigma S2)))))


(local
 (defthm solution-eliminate-n
   (implies (solution sigma S)
	    (solution sigma (eliminate-n n S)))))


;;; To prove the intended theorems, we need some lemmas for some of the
;;; transformation rules. The following lists those lemmas classified by
;;; type of rules (some type of rules do not need specific lemmas):

;;; -----------------------------------
;;;
;;; 2.1)  Rule {\tt DECOMPOSE}
;;;
;;; -----------------------------------

;;; See the definition of {\tt pair-args} in {\tt basic.lisp}.

(local
 (defun induction-transform-sel-decompose-rule (l1 l2)
   (if (or (atom l1) (atom l2))
       t
     (induction-transform-sel-decompose-rule (cdr l1) (cdr l2)))))

(local
 (defthm transform-sel-rule-decompose
   (implies (second (pair-args l1 l2))
	    (equal (solution sigma (first (pair-args l1 l2)))
		   (equal (apply-subst nil sigma l1)
			  (apply-subst nil sigma l2))))
   :hints (("Goal" :induct
	    (induction-transform-sel-decompose-rule l1 l2)))))


;;; -----------------------------------
;;;
;;; 2.2)  Rule {\tt ELIMINATE}
;;;
;;; -----------------------------------


;;; For this rule, we need to prove that if $\sigma$ ia a solution of the
;;; system $sol$ and $x$ is a variable, then $\sigma(sol(x)) =
;;; sol(x)$. More generally, we prove that if $\sigma$ is a solution of
;;; $S$, then $\sigma=\sigma\cdot S$:


(local
 (encapsulate
  ()
  (local
   (defthm main-property-eliminate-lemma
     (implies (and (solution sigma sol) (variable-p x) flg)
	      (equal
	       (apply-subst flg sigma (val x sol))
	       (val x sigma)))))


  (defthm substitutions-solution-system
    (implies (solution sigma S)
	     (equal
	      (apply-subst flg sigma (apply-subst flg S term))
	      (apply-subst flg sigma term))))))

;;; IMPORTANT: this is a key rule in the proof of the generality of the
;;; solutions obtained applying the transformations.

;;; Two corollaries:

(local
 (defthm main-property-eliminate
   (implies (solution sigma sol)
	    (equal
	     (solution sigma (apply-syst sol S))
	     (solution sigma S)))))


(local
  (defthm main-property-eliminate-corollary
    (implies (solution sigma sol)
 	    (equal
 	     (solution sigma (apply-range sol S))
 	     (solution sigma S)))))

;;; -----------------------------------
;;;
;;; 2.3)  Rule {\tt CHECK}
;;;
;;; -----------------------------------

;;; Our goal here is to prove that the equation $x=t$ when $x$ is a
;;; variable (different from $t$) in the set of variables of $t$, has no
;;; solution.

;;; Our proof plan is the following. The idea is to show that
;;; $\sigma(x)\not=\sigma(t)$, for all $\sigma$, and we prove it by
;;; means of the following steps:

;;; 1)
;;;  $t$ is of the form  $f(t_1,\ldots,t_n)$, and $x$ is in some  $t_i$.
;;; 2)
;;;  $\sigma(x)$ is a subterm of $\sigma(t_i)$.
;;; 3)
;;;  $\sigma(t_i)$ is a descendant of $\sigma(t)$.
;;; 4)
;;;  Every subterm has size less or equal than its superterm.
;;; 5)
;;; Every descendant has a size strictly less than its superterm.
;;; 6)
;;; Thus, $size(\sigma(x)) < size(\sigma(t)))$ (that is, they are
;;; different).
;;; -)

(local
 (encapsulate
  ()

  (local
   (defthm if-x-in-term-sigma-x-subterm-of-sigma-term
     (implies (and (variable-p x)
		   (member x (variables flg term)))
	      (subterm flg (val x sigma) (apply-subst flg sigma term)))))

  (local
   (defthm
     if-x-is-not-term-and-is-in-term-then-is-in-some-argument
     (implies (and (member x (variables t term))
		   (not (equal x term)))
	      (member x (variables nil (cdr term))))))

  (local
   (defthm size-subterm
     (implies (subterm flg t1 t2)
	      (>= (size flg t2) (size t t1)))
     :rule-classes nil))

  (local
   (defthm
     size-of-sigma-x-leq-than-the-size-of-sigma-of-arguments
     (implies (and
	       (variable-p x)
	       (member x (variables t term))
	       (not (equal x term)))
	      (>= (size nil (apply-subst nil sigma (cdr term)))
		  (size t (val x sigma))))
     :rule-classes nil
     :hints (("Goal" :use
	      ((:instance size-subterm (flg nil)
			  (t1 (val x sigma))
			  (t2 (apply-subst nil sigma (cdr term)))))))))

  (defthm
    transform-sel-check-rule-not-equal-size
    (implies (and
	      (variable-p x)
	      (member x (variables t term))
	      (not (equal x term)))
	     (not (equal (size t (val x sigma))
			 (size t (apply-subst t sigma term)))))
    :rule-classes nil
    :hints (("Goal"
	     :use (:instance
		   size-of-sigma-x-leq-than-the-size-of-sigma-of-arguments))))))

;;; REMARK: It can be proved with @<@, but it is not necessary here.


;;; And finally, the equation $x=t$ has no solution (when $x$ is in
;;; $var(t)$ and is different from $t$).

(local
 (defthm transform-sel-check-rule
   (implies (and
	     (variable-p x)
	     (member x (variables t term))
	     (not (equal x term)))
	    (not (equal  (val x sigma)
			 (apply-subst t sigma term))))
   :hints (("Goal"
	    :use ((:instance
		   transform-sel-check-rule-not-equal-size))))))


;;; -----------------------------------
;;;
;;; 2.4)  Rule {\tt CLASH1}
;;;
;;; -----------------------------------

;;; The equation $f(t_1,\ldots,t_n)=g(s_1,\ldots,s_n)$ has no solution
;;; if $f\not=g$.

(local
 (defthm transform-mm-sel-conflict-rule
   (implies (and (not (variable-p t1))
		 (not (variable-p t2))
		 (not (equal (car t1) (car t2))))
	    (not (equal (apply-subst t sigma t1)
			(apply-subst t sigma t2))))))



;;; -----------------------------------
;;;
;;; 2.5)  Rule {\tt CLASH2}
;;;
;;; -----------------------------------

;;; If $\sigma(t_1,\ldots,t_n . a)=\sigma(s_1,\ldots,s_m . b)$, then
;;; $n=m$ and $a=b$. That is the equation $f(t_1,\ldots,t_n
;;; . a)=g(s_1,\ldots,s_m . b)$ has no solution when $n\not= m$ or
;;; $a\not= b$. Note that the function @pair-args@ (see {\tt basic.lisp})
;;; checks this property).

(local
 (encapsulate
  ()
  (local
   (defthm transform-sel-not-pair-rule-lemma
     (implies (equal (apply-subst nil sigma l)
		     (apply-subst nil sigma m))
	      (second (pair-args l m)))))

  (defthm transform-sel-not-pair-rule
    (implies (and (not (variable-p t1))
		  (not (variable-p t2))
		  (not (second (pair-args (cdr t1) (cdr t2)))))
	     (not (equal (apply-subst t sigma t1)
			 (apply-subst t sigma t2)))))))



;;; -----------------------------------
;;;
;;; 2.6)  The intended properties
;;;
;;; -----------------------------------

;;; The following function computes the union of the pair of the system:

(defun both-systems (S-T)
  (append (first S-T) (second S-T)))

;;; And these are the theorems proving that the transformations preserve
;;; the set of solutions of the pair of systems:

(defthm mm-preserves-solutions-1
  (implies (and (unif-legal-s S-sol op)
		(solution sigma (both-systems S-sol)))
	   (solution sigma (both-systems (unif-reduce-one-step-s S-sol op)))))



(defthm mm-preserves-solutions-2
  (implies (and (unif-legal-s S-sol op)
		(unif-reduce-one-step-s S-sol op)
		(solution sigma (both-systems (unif-reduce-one-step-s S-sol
								  op))))
	   (solution sigma (both-systems S-sol))))

(defthm mm-preserves-solutions-3
  (implies (and (unif-legal-s S-sol op)
		(not (unif-reduce-one-step-s S-sol op)))
	   (not (solution sigma (both-systems S-sol)))))


;;; ============================================================================
;;;
;;; 3) The transformation rules preserve idempotency (under certain conditions)
;;;
;;; ============================================================================

;;; Our goal in this section is to prove the following:

;  (defthm transform-mm-sel-preserves-idempotency
;    (let* ((S (first S-sol)) (sol (second S-sol))
; 	    (transformado (unif-reduce-one-step-s S-sol op))
; 	    (St (first transformado)) (solt (second transformado)))
;      (implies (and (unif-legal-s S-sol op)
; 		     (idempotent sol)
; 		     (disjointp (system-var S) (domain sol)))
; 	      (and (idempotent solt)
; 		   (disjointp (system-var St) (domain solt))))))


;;; That is, idempotence of the second system is preserved in
;;; transformation steps (whenever the variables of the first system are
;;; disjoint with the variables of the domain of the second system).

;;; First, we use again a congruence with respect to @system-var@ and
;;; @equal-set@, that will be useful again to reason about selection of
;;; equations:

(local
 (encapsulate

  ()

  (local (defthm subsetp-variables-lemma-1
	   (implies (member ecu s2)
		    (subsetp (variables t (car ecu))
			     (system-var s2)))))

  (local (defthm subsetp-variables-lemma-2
	   (implies (member ecu s2)
		    (subsetp (variables t (cdr ecu))
			     (system-var s2)))))

  (local (defthm subsetp-system-var
		       (implies (subsetp S1 S2)
				(subsetp (system-var S1) (system-var S2)))))


  (defcong equal-set equal-set (system-var S) 1)))

;;; REMARK: Recall that @perm@ is a refinement of @equal-set@, and
;;; therefore the rule {\tt perm\--nth\--eliminate\--n\--instance} will
;;; also act in the context of @system-var@.

;;; An useful lemma:

(local
 (defthm system-var-append
   (equal (system-var (append x y))
	  (append (system-var x) (system-var y)))))


;;; Again, we need some specific lemmas for some of the transformation
;;; rules. Let us see.


;;; -----------------------------------
;;;
;;; 3.1)  Rule {\tt DECOMPOSE}
;;;
;;; -----------------------------------

(local
 (encapsulate
  ()
  (defthm pair-args-system-var-lemma-1  ;;it will be used later
    (subsetp (system-var (first (pair-args l1 l2)))
	     (append (variables nil l1) (variables nil l2))))

  (local (defthm pair-args-system-var-lemma-2
	   (implies (second (pair-args l1 l2))
		    (subsetp (append (variables nil l1)
				     (variables nil l2))
			     (system-var (first (pair-args l1 l2)))))
	   :hints (("Goal" :induct
		    (induction-transform-sel-decompose-rule l1 l2)))))

  (defthm pair-args-system-var
    (implies (second (pair-args l1 l2))
	     (equal-set (system-var (first (pair-args l1 l2)))
			(append (variables nil l1)
				(variables nil l2)))))))



;;; -----------------------------------
;;;
;;; 3.2)  Rule {\tt ELIMINATE}
;;;
;;; -----------------------------------


(local
 (defthm apply-range-preserves-domain
   (equal (domain (apply-range sigma S)) (domain S))))


(local
 (defthm co-domain-de-apply-range
  (equal (co-domain (apply-range sigma s))
	 (apply-subst nil sigma (co-domain s)))))


(local
 (defthm apply-range-preserves-system-substitution
  (implies (system-substitution S)
	   (system-substitution (apply-range sigma S)))))

(local
 (defthm eliminate-variables-in-co-domain
  (implies (not (member (car ecu) (variables t (cdr ecu))))
	   (not (member (car ecu)
			(variables flg (apply-subst flg (list ecu) s)))))))


(local
 (defthm variables-apply-subsetp-lemma
  (implies (and (not (member x (variables flg term)))
		(not (member x (variables nil (co-domain sigma)))))
	   (not (member x (variables flg (apply-subst flg sigma term)))))))


(local
 (defthm variables-apply-subsetp
  (subsetp (variables flg (apply-subst flg sigma term))
	   (append (variables flg term) (variables nil (co-domain sigma))))
  :hints (("Goal" :in-theory (enable not-subsetp-witness-lemma)))))

(local
 (defthm subsetp-disjoint
   (implies (and (subsetp a b)
		 (disjointp m b))
	    (disjointp m a))
   :rule-classes nil))

(local
 (defthm
   domain-disjoint-co-domain-eliminate-bridge-lemma
  (implies (disjointp m
		      (append (variables flg term)
			      (variables nil (co-domain sigma))))
	   (disjointp m (variables flg (apply-subst flg sigma term))))
  :hints (("Goal" :use
	   ((:instance
	     subsetp-disjoint
	     (b (append (variables flg term) (variables nil (co-domain sigma))))
	     (a (variables flg (apply-subst flg sigma term)))))))))

(local
 (defthm eliminate-eliminate-variables
  (implies (not (member (car ecu) (variables t (cdr ecu))))
	   (not (member (car ecu) (system-var
				   (apply-syst (list ecu) s)))))
  :hints (("Goal" :induct (len s)))))



(local
 (encapsulate
  ()
  (local
   (defthm eliminate-eliminate-variables-2
     (implies (and (not (member x (variables nil (co-domain sigma))))
		   (not (member x (system-var s))))
	      (not (member x (system-var
			      (apply-syst sigma s)))))))

  (defthm subsetp-system-var-co-domain
    (subsetp (system-var (apply-syst sigma s))
	     (append (variables nil (co-domain sigma))
		     (system-var s)))
    :hints (("Goal" :in-theory
	     (enable not-subsetp-witness-lemma))))))


(local
 (defthm
   domain-disjoint-system-eliminate-bridge-lemma
   (implies (disjointp m
		       (append (variables nil (co-domain sigma))
			       (system-var S)))
	   (disjointp m
		      (system-var (apply-syst sigma S))))
   :hints (("Goal"
	    :use ((:instance
		   subsetp-disjoint
		   (b (append (variables nil (co-domain sigma)) (system-var S)))
		   (a (system-var (apply-syst sigma S)))))))))



;;; -----------------------------------
;;;
;;; 3.3)  The intended property
;;;
;;; -----------------------------------

(local
 (defthm transform-mm-sel-preserves-idempotency
   (let* ((S (first S-sol)) (sol (second S-sol))
	  (transformado (unif-reduce-one-step-s S-sol op))
	  (St (first transformado)) (solt (second transformado)))
     (implies (and (unif-legal-s S-sol op)
		   (idempotent sol)
		   (disjointp (system-var S) (domain sol)))
	      (and (idempotent solt)
		   (disjointp (system-var St) (domain solt)))))))

;;; We disable @idempotent@

(local (in-theory (disable idempotent)))


;;; ============================================================================
;;;
;;; 4) The transformation rules describe a noetherian relation
;;;
;;; ============================================================================

;;; We show now that we can define an ordinal measure on pair of systems
;;; of equations and prove that this measure decreases in every single
;;; step of transformation. The measure is defined in {\tt terms.lisp}
;;; and is given by the function {\tt unification\--measure}:

;(defun unification-measure (S-sol)
;  (list* (cons 2 (1+ (n-system-var (first S-sol))))
;	 (cons 1 (1+ (size-system (first S-sol))))
;	 (n-variables-right-hand-side (first S-sol))))


;;; where @n-system-var@ defines the the number of (different) variables
;;; of the system, @size-system@ is the total number of function symbols
;;; of the system and {\tt n\--variables\--right\--hand\--side} is the
;;; number of equations in a system with a variable right hand side.

;;; Our goal is to prove the following theorems:

; (defthm ordinalp-unification-measure
;   (o-p (unification-measure S-sol)))

; (defthm unification-measure-decreases
;   (implies (unif-legal-s S-sol op)
; 	     (o< (unification-measure (unif-reduce-one-step-s S-sol op))
; 		 (unification-measure S-sol))))

;;; The first theorem is easy. For the second, we need to prove the
;;; following:

;;; 1)
;;;  Every transformation step does not add new variables to the first
;;;  system.
;;; 2)
;;;  The ELIMINATE rule eliminates one variable of the first system.
;;; 3)
;;;  If the number of variables stays the same, then the size of the
;;;  first system does not increase.
;;; 4)
;;;  If the number of variables and the size is equal, then the number
;;;  of variables in the right hand side of equations stay the same.
;;; -)

;;; Let us see in detail every of the above items:


;;; -----------------------------------
;;;
;;; 4.1)  The transformation does not add new variables to the first system
;;;
;;; -----------------------------------

;;; We will prove that the variables of the first system are a subset of
;;; the subset of transformed system.

;;; First, some lemmas about @eliminate-n@:


(local
  (defthm subsetp-variables-eliminate-n
    (implies (< n (len S))
	     (subsetp (system-var (eliminate-n n S))
		      (system-var S)))))

(local
  (defthm subsetp-variables-eliminate-lemma
    (implies (and (natp n) (< n (len S)))
	     (subsetp (append (system-var (list (nth n S)))
			      (system-var (eliminate-n n S)))
		      (system-var S)))
    :rule-classes nil))


(local
  (defthm subsetp-variables-eliminate
   (implies (and (natp n) (< n (len S))
		 (variable-p (car (nth n S))))
	    (subsetp (system-var (apply-syst (list (nth n S)) (eliminate-n n S)))
		     (system-var S)))
   :hints (("Goal"
 	   :in-theory (disable subsetp-system-var-co-domain)
 	   :use ((:instance subsetp-variables-eliminate-lemma)
 		 (:instance subsetp-system-var-co-domain
 			    (sigma (list (nth n S)))
 			    (S (eliminate-n n S))))))))

;;; Two lemmas about @len@, @setp@ and @subsetp@.

(local
 (defthm len-subsetp-setp
   (implies (and (setp l) (setp m) (subsetp l m))
	   (<= (len l) (len m)))
   :hints (("Goal" :induct (subset-induction l m)))))

(local
 (defthm subsetp-make-set
   (implies (subsetp l m)
	    (subsetp (make-set l) (make-set m)))))


;;; And the intended result in this subsection:

(local
 (encapsulate
  ()

;; First, established in terms of @subsetp@:

  (defthm unif-reduce-one-step-s-does-not-add-new-variables
    (implies (unif-legal-s S-sol op)
	     (subsetp (system-var (car (unif-reduce-one-step-s S-sol op)))
		      (system-var (car S-sol))))
    :hints (("Subgoal 2"
	     :use (:instance subsetp-variables-eliminate
			     (n (cadr op))
			     (S (car S-sol))))))

;; And finally, in terms of @n-system-var@:

  (defthm
    transform-does-not-increases-n-variables
    (implies (unif-legal-s S-sol op)
	     (>= (n-system-var (first S-sol))
		 (n-system-var (first (unif-reduce-one-step-s S-sol op)))))
    :rule-classes :linear
    :hints (("Goal" :in-theory
	     (disable system-var unif-reduce-one-step-s unif-legal-s))))))


;;; -----------------------------------
;;;
;;; 4.2)  The {\tt ELIMINATE} rule eliminates variables
;;;
;;; -----------------------------------

;;; We are going to prove that when @n-system-var@ stays the same, then
;;; the ELIMINATE rule has not been applied.

;;; For that purpose, we will use the lemma {\tt
;;; len\--subsetp\--setp\--strict} (see below) where @x@ is {\tt (car
;;; ecu)}.

(local
 (encapsulate
  ()

  (local
   (defthm positive-length-member
     (implies (member x l)
	      (< 0 (len l)))
     :rule-classes (:rewrite :linear)))

  (local
   (defthm member-eliminate
     (implies (and (member x l)
		   (not (equal x y)))
	      (member x (eliminate y l)))))

  (defthm len-subsetp-setp-strict
    (implies (and
	      (setp l)
	      (setp m)
	      (subsetp l m)
	      (member x m)
	      (not (member x l)))
	     (< (len l) (len m)))
    :hints (("Goal" :induct (subset-induction l m)))
    :rule-classes nil)))


;;; Technical lemma:

(local
 (defthm subsetp-variables-orient-2
   (let ((ecu (nth n S)))
     (implies (and (natp n) (< n (len S)) (variable-p (car ecu)))
	      (member (car ecu) (system-var S))))))

;;; REMARK: This lemma is trivial, but we need it because we disable
;;; {\tt system-var} in the next lemma.

;;; And the intended result in this subsection:

(local
  (defthm eliminate-variables-strict
    (let ((ecu (nth n S)))
      (implies (and (< n (len S)) (natp n)
		    (variable-p (car ecu))
		    (not (member (car ecu) (variables t (cdr ecu)))))
	       (> (n-system-var S)
		  (n-system-var (apply-syst (list ecu)
					    (eliminate-n n S))))))
    :rule-classes :linear
    :hints (("Goal" :use
	     ((:instance len-subsetp-setp-strict
			 (l (make-set
			     (system-var (apply-syst (list (nth n S))
						     (eliminate-n n S)))))
			 (m (make-set (system-var S)))
			 (x (car (nth n S)))))
	     :in-theory (disable system-var)))))


;;; -----------------------------------
;;;
;;; 4.3)  The size of the system does not increase
;;;
;;; -----------------------------------

;;; We show now that the size of the system does not increase (whenever
;;; the number of variables stays the same).

;;; First, two useful congruences, to deal with selection of equations:

(local
 (encapsulate
  ()

  (local (defthm perm-equal-size-system-defcong-lemma
	   (implies (member x S)
		    (equal (size-system S)
			   (+ (size t (car x)) (size t (cdr x))
			      (size-system (delete-one x S)))))))

  (defcong perm equal (size-system S) 1)))




(local
 (encapsulate
  ()

  (local (defthm perm-equal-size-system-defcong-lemma
	   (implies (member x S)
		    (equal (n-variables-right-hand-side S)
			   (if (variable-p (cdr x))
			       (1+ (n-variables-right-hand-side (delete-one x S)))
			     (n-variables-right-hand-side (delete-one x S)))))))

  (defcong perm equal (n-variables-right-hand-side S) 1)))


;;; A technical lemma:

(local
  (defthm size-system-append
    (equal (size-system (append x y))
 	  (+ (size-system x) (size-system y)))))


;;; This lemma is needed to deal with the DECOMPOSE rule:

(local
 (defthm size-systems-decompose-lemma
   (implies (second (pair-args l1 l2))
 	    (equal (size-system (first (pair-args l1 l2)))
 		   (+ (size nil l1) (size nil l2))))))


;;; And the intended result in this subsection:


(local
 (defthm
   si-permanece-system-var-al-transformar-decrece-size-system
   (implies (and (unif-legal-s S-sol op)
		 (equal (n-system-var (first S-sol))
			(n-system-var (first (unif-reduce-one-step-s S-sol op)))))
	    (>= (size-system (first S-sol))
		(size-system (first (unif-reduce-one-step-s S-sol op)))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable n-system-var)))))


;;; We disable @n-system-var@:

(local (in-theory (disable n-system-var)))

;;; REMARK: This @disable@ is needed here, because we want to prove
;;; later  {\tt
;;; if\--n\--variables\--and\--size\--are\--equal\--reduction\--decrease\--n\--variables\--r-h-s}


;;; -----------------------------------
;;;
;;; 4.4)  The number of right--hand side variables
;;;
;;; -----------------------------------

;;; A technical lemma:

(local
 (defthm size-t->-0
  (implies (not (variable-p term)) (< 0 (size t term)))
  :rule-classes :linear))


;;; And the intended result in this subsection:

(local
 (defthm
   if-n-variables-and-size-are-equal-reduction-decrease-n-variables-r-h-s
   (implies (and (unif-legal-s S-sol op)
		 (equal (n-system-var (first S-sol))
			(n-system-var (first (unif-reduce-one-step-s S-sol op))))
		 (equal (size-system (first S-sol))
			(size-system (first (unif-reduce-one-step-s S-sol op)))))
	    (< (n-variables-right-hand-side
		(first (unif-reduce-one-step-s S-sol op)))
	       (n-variables-right-hand-side (first S-sol))))
  :rule-classes :linear))


;;; -----------------------------------
;;;
;;; 4.5)  The termination results
;;;
;;; -----------------------------------


;;; We disable the components of {\tt unification\--measure} and the
;;; components of the reduction relation. In this way, the above lemmas
;;; can be applied:

(local (in-theory (disable n-system-var
		    size-system
		    n-variables-right-hand-side)))

(local (in-theory (disable unif-legal-s unif-reduce-one-step-s)))

;;; And finally:

(defthm ordinalp-unification-measure
  (o-p (unification-measure S-sol)))

(defthm unification-measure-decreases
  (implies (unif-legal-s S-sol op)
	   (o< (unification-measure (unif-reduce-one-step-s S-sol op))
	       (unification-measure S-sol))))



;;; ============================================================================
;;;
;;; 5) Sequences of transformation steps
;;;
;;; ============================================================================

;;; Since the properties described in sections 2 and 3 are preserved in each
;;; transformation step, they are also preserved in every finite
;;; sequence of transformation steps.  We prove this in this section.

;;; -----------------------------------
;;;
;;; 5.1)  Defining sequences of transformations
;;;
;;; -----------------------------------

;;; A sequence of transformations can be represented as the sequence of
;;; operators applied. The following function check thta every of these
;;; operators is legal:

(defun unif-seq-s-p (S-sol unif-seq)
  (declare (xargs :measure (acl2-count unif-seq)))
  (if (endp unif-seq)
      t
    (let ((op (car unif-seq)))
      (and (unif-legal-s S-sol op)
	   (unif-seq-s-p
	    (unif-reduce-one-step-s S-sol op)
	    (cdr unif-seq))))))

;;; The following function obtains the last pair of systems obtained by
;;; a sequence of transformations (given by the sequence of operators):

(defun unif-seq-s-last (S-sol unif-seq)
  (if (endp unif-seq)
      S-sol
    (unif-seq-s-last (unif-reduce-one-step-s S-sol (car unif-seq))
		     (cdr unif-seq))))



;;; -----------------------------------
;;;
;;; 5.2) Properties preserved by sequences of transformations
;;;
;;; -----------------------------------

;;; First, a technical lemma:

(local
 (defthm if-solvable-transform-sel-success
   (implies (and (consp seq)
		 (unif-seq-s-p S-sol seq)
		 (unif-seq-s-last S-sol seq))
	    (unif-reduce-one-step-s S-sol (car seq)))
   :hints (("Goal" :in-theory (enable unif-legal-s)))))


(local (in-theory (disable both-systems)))

;;; The set of solutions is preserved:


(local
 (defthm
   unif-seq-s-equivalent-1
   (implies (and (solution sigma (both-systems S-sol))
		 (unif-seq-s-p S-sol unif-seq))
	    (solution sigma (both-systems (unif-seq-s-last S-sol unif-seq))))
   :rule-classes nil))



(local
 (defthm unif-seq-s-equivalent-2
  (implies (and  (unif-seq-s-p S-sol unif-seq)
		 (unif-seq-s-last S-sol unif-seq)
		 (solution sigma (both-systems (unif-seq-s-last S-sol unif-seq))))
	   (solution sigma (both-systems S-sol)))
  :rule-classes nil))

(local
 (defthm unif-seq-s-unsolvable
  (implies (and (consp S-sol) ;;; esto es necesario
		(unif-seq-s-p S-sol unif-seq)
		(not (unif-seq-s-last S-sol unif-seq)))
	   (not (solution sigma (both-systems S-sol))))
  :rule-classes nil))



(local (in-theory (enable both-systems)))


;;; Idempotence of the second system is preserved:

(local
 (defthm unif-seq-s-preserves-idempotency
   (let* ((S (first S-sol))  (sol (second S-sol))
	  (unif-seq-s-last (unif-seq-s-last S-sol unif-seq))
	  (solution (second unif-seq-s-last)))
      (implies (and (unif-seq-s-p S-sol unif-seq)
		    (idempotent sol)
		    (disjointp (system-var S) (domain sol)))
	       (idempotent solution)))
   :hints (("Goal" :induct (unif-seq-s-last S-sol unif-seq)
	    :in-theory (disable disjointp-conmutative)))))


;;; ============================================================================
;;;
;;; 6) A particular case of transformation sequences
;;;
;;; ============================================================================


;;; We are interested in a particular case of sequences. Those beginning
;;; in pair of systems of the form $S;\emptyset$ and ending in pair of
;;; systems of the form $\emptyset;\sigma$ or in $\bot$ (failure).
;;; From the above properties it is easy to prove
;;; that $S$ is solvable if and only if failure is not
;;; obtained, and in that case $\sigma$ is a most general solution of
;;; $S$.

;;; This the definition of these type of sequences of operators, and the
;;; pair of system finally obtained by the sequence of transformations:


(defun mgs-seq-p (S seq)
  (and (unif-seq-s-p (list S nil) seq)
       (normal-form-syst (unif-seq-s-last (list S nil) seq))))

(defun mgs-seq (S seq)
  (unif-seq-s-last (list S nil) seq))


;;; Example:

;;; The constant @*S0*@ stores the initial system of equations:

; ACL2 !>(defconst *S0* (list (cons '(f x (g v) (a)) '(f (h y z) y v))))

;;; The function @mgs-seq-p@ checks if a given sequence of operators is
;;; legal:

; ACL2 !>(mgs-seq-p *S0* '((decompose 0) (eliminate 0)
;                          (orient 0) (eliminate 0) (orient 0) (eliminate 0)))
; T

;;; The function @mgs-seq@ obtains the final pair of system obtained
;;; applying the sequence of opertors:

; ACL2 !>(mgs-seq *S0* '((decompose 0) (eliminate 0) (orient 0)
;                        (eliminate 0) (orient 0) (eliminate 0)))
; (NIL (V A) (Y G (A)) (X H (G (A)) Z))

;;; The second system contains a most genarl solution of @*S0*@:

; ACL2 !>(second (mgs-seq *S0* '((decompose 0) (eliminate 0) (orient 0)
;                                (eliminate 0) (orient 0) (eliminate 0))))
; ((V A) (Y G (A)) (X H (G (A)) Z))

;;; The following properties prove the intended properties, an easy
;;; consequence of the properties of the previous section:

(defthm mgs-seq-completeness
  (implies (and (solution sigma S)
		(mgs-seq-p S unif-seq))
	   (mgs-seq S unif-seq))
  :rule-classes nil
  :hints
  (("Goal" :use
    ((:instance unif-seq-s-unsolvable (S-sol (list S nil)))))))


(defthm mgs-seq-soundness
  (implies (and (mgs-seq-p S unif-seq)
		(mgs-seq S unif-seq))
	   (solution (second (mgs-seq S unif-seq)) S))
  :rule-classes nil
  :hints (("Goal" :use
	   ((:instance unif-seq-s-equivalent-2
		       (S-sol (list S nil))
		       (sigma (second (mgs-seq S unif-seq))))))))


(defthm mgs-seq-idempotent
  (implies (mgs-seq-p S unif-seq)
	   (idempotent (second (mgs-seq S unif-seq)))))

;;; REMARK: This is true even if (mgs-seq S unif-seq) fails

(defthm mgs-seq-most-general-solution-main-lemma
  (implies (and (solution sigma S)
		(mgs-seq-p S unif-seq))
	   (equal (instance (instance term (second (mgs-seq S unif-seq)))
			    sigma)
		  (instance term sigma)))
  :hints (("Goal" :use
	   (:instance
	    unif-seq-s-equivalent-1  (S-sol (list S nil))))))

;;; We disable mgs-seq and megs-seq-p

(in-theory (disable mgs-seq mgs-seq-p))

(defthm mgs-sel-most-general-solution
  (implies (and (solution sigma S) (mgs-seq-p S unif-seq))
	   (subs-subst (second (mgs-seq S unif-seq)) sigma))
  :hints (("Goal"
	   :use
	   ((:functional-instance
	     subs-subst-completeness
	     (sigma-w (lambda ()
			(if (and (solution sigma S) (mgs-seq-p S unif-seq))
			    (second (mgs-seq S unif-seq)) nil)))
	     (gamma-w (lambda ()
			(if (and (solution sigma S) (mgs-seq-p S unif-seq))
			    sigma nil)))
	     (delta-w (lambda ()
			(if (and (solution sigma S) (mgs-seq-p S unif-seq))
			    sigma nil))))))))


;;; Note that the above four properties provide a form to compute most
;;; general solutions of systems of equations: apply transformations
;;; (starting in $S;\emptyset$) until $\emptyset;\sigma$ or failure is
;;; obtained. Then the system $S$ is solvable if and only if failure is
;;; not obtained and in that case $\sigma$ is a most general idempotent
;;; solution of $S$. Thus, to verify a given unification algorithm, we
;;; simply has to show that the result obtained is the result obtained
;;; by a sequence of legal operators.



;;; ===============================================================


