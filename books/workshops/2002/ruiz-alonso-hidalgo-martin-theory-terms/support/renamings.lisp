;;; renamings.lisp
;;; Renamings variables of a term. Renamings substitutions. Properties.
;;; Created 24-10-99. Last modified: 15-02-2001
;;; =============================================================================


#| To certify this book:

(in-package "ACL2")

(certify-book "renamings")

|#

(in-package "ACL2")
(include-book "subsumption")


;;; ******************************************************
;;; RENAMING SUBSTITUTIONS. THE "RENAMED" EQUIVALENCE.
;;; A PARTICULAR RENAMING: NUMBER-RENAME
;;; ******************************************************

;;; In this book:
;;; - The equivalence relation "renamed": one term t1 is a renamed version
;;;   of t2 if (subs t1 t2) and (subs t2 t1).
;;; - Definition of the concept of renaming substitutions and the main
;;;   property of renamings with respect to the renamed equivalence: t2 is
;;;   a renamed version of t1 iff there exists a renaming s.t. its
;;;   domain contains the variables of t1 and applied to t1 is equal to
;;;   t2.
;;; - Definition and properties of a particular kind of renaming
;;;   (number-renaming) and guard verification. This "number-renaming"
;;;   will be defined for terms and for lists of terms.


;;; ============================================================================
;;; 1. The "renamed" equivalence
;;; ============================================================================

;;; ====== RENAMED

(defun renamed (t1 t2)
  (if (subs t1 t2)
      (if (subs t2 t1) t nil)
    nil))

(defequiv renamed
  :hints (("Goal" :in-theory
	   (enable subsumption-transitive))))

;;; And congruences:

(defcong renamed iff (subs t1 t2) 1
    :hints (("Goal" :in-theory
	   (enable subsumption-transitive))))

(defcong renamed iff (subs t1 t2) 2
    :hints (("Goal" :in-theory
	   (enable subsumption-transitive))))



;;; ============================================================================
;;; 2. Renaming variables: definition and properties.
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 2.1 Definition
;;; ----------------------------------------------------------------------------

;;; ======= VARIABLE-SUBSTITUTION

(defun variable-substitution (sigma)
  (if (atom sigma)
      t
    (and (variable-p (cdar sigma))
	 (variable-substitution (cdr sigma)))))

(local
 (defthm variable-substitution-value-variable-p
   (implies (and (variable-substitution sigma)
		 (variable-p term))
	    (variable-p (val term sigma)))))

;;; ======= RENAMING

(defun renaming (sigma)
  (and (variable-substitution sigma)
       (setp (co-domain sigma))))


;;; In the following, we will prove the main property of renamings: "t2
;;; is a renamed version of t1 iff there exists a renaming sigma
;;; s.t. its domain is a set containing the variables of t1 and that
;;; applied to t1 is equal to t2"


;;; ----------------------------------------------------------------------------
;;; 2.2 Renaming implies renamed
;;; ----------------------------------------------------------------------------


;;; ············································································
;;; 2.2.1 An important lemma
;;; ············································································

;;; We will show that the inverse substitution of a renaming is its
;;; inverse function, in some sense.

(encapsulate
 ()

 (local
  (defthm val-val-inverse-lemma
    (implies (and
	      (member x (domain sigma))
	      (equal (val x sigma) y))
	     (member y (co-domain sigma)))))

;;; If sigma is a substitution such that its co-domain is a set of
;;; variables, then sigma^{-1}(sigma(x)) = x, for all x in
;;; domain(sigma). Remeber that a renaming is a substitution such that
;;; its co-domain are sets of variables (no duplicated
;;; elements)

 (local
  (defthm val-val-inverse-renaming
    (implies (and (renaming sigma)
		  (member x (domain sigma)))
	     (equal (val (val x sigma) (inverse sigma)) x))))

;;; The main theorem:
;;; If the variables of t1 are in the domain of sigma, then
;;; sigma^{-1}(sigma(t1)) = t1, whenever sigma is a substitution with a
;;; set of variables as its co-domain. This theorema will be needed also
;;; in subsumption-well-founded.lisp

  (defthm renaming-inverse
    (implies (and
	      (renaming sigma)
	      (subsetp (variables flg term) (domain sigma)))
	     (equal
	      (apply-subst flg (inverse sigma) (apply-subst flg sigma term))
	      term))))


;;; ············································································
;;; 2.2.2 And the intended property
;;; ············································································


(defthm renaming-implies-renamed
  (implies (and
	    (renaming sigma)
	    (subsetp (variables t term) (domain sigma)))
	   (renamed (instance term sigma) term))
  :hints (("Goal" :use (:instance subs-completeness
				  (t1 (instance term sigma))
				  (t2 term)
				  (sigma (inverse sigma))))))

;;; ----------------------------------------------------------------------------
;;; 2.3 Renamed implies renaming
;;; ----------------------------------------------------------------------------

;;; We will show that when (subs t1 t2) and (subs t2 t1), then
;;; (normal-form-subst t (matching t1 t2) t1) is a renaming s.t.
;;; applied to t1 is equal to t2.

;;; Note that the condition (subs term t2) and (subs t2 term) can be
;;; stated in terms of apply-subst: that is the same to say that
;;; there exists two substitutions sigma and delta such that:
;;;  (equal (apply-subst flg delta (apply-subst flg sigma term))
;;;		   term)

;;; Let sigmar = (normal-form-subst flg sigma term). We have to prove
;;; the two following properties:
;;;  * (variable-substitution sigmar)
;;;  * (co-domain sigmar) is a setp.


;;; ············································································
;;; 2.3.1 sigmar is a variable-substitution
;;; ············································································

(local
 (encapsulate
  ()

  (local
   (defthm renamed-implies-variable-val-lemma
     (implies (and flg (variable-p (apply-subst flg delta (val term sigma))))
	      (variable-p (val term sigma)))
     :rule-classes nil))


  (local
   (defthm renamed-implies-variable-val
     (implies (and
	       (equal (apply-subst flg delta (apply-subst flg sigma term))
		      term)
	       (member x (variables flg term)))
	      (variable-p (val x sigma)))
     :hints (("Subgoal *1/1"
	      :use renamed-implies-variable-val-lemma))))

  (local
   (defthm renamed-implies-variable-substitution-main-lemma
     (implies (and
	       (equal (apply-subst flg delta (apply-subst flg sigma term))
		      term)
	       (subsetp l (variables flg term)))
	      (variable-substitution (restriction sigma l)))
     :hints (("Goal" :induct (len l)))))

  (defthm renamed-implies-variable-substitution
    (implies
     (equal (apply-subst flg delta (apply-subst flg sigma term)) term)
     (variable-substitution (normal-form-subst flg sigma term)))
    :hints (("Goal" :use
	     (:instance renamed-implies-variable-substitution-main-lemma
			(l (make-set (variables flg term)))))))))

;;; ············································································
;;; 2.3.2 An important lemma
;;; ············································································

;;; When (equal (apply-subst flg delta (apply-subst flg sigma term))
;;; term) then two different variables of term cannot have the the value
;;; with respect to sigma


(local
 (encapsulate
  ()

  (local
   (defthm renamed-implies-injective-val-lemma
     (implies (and
	       (equal (instance (val x sigma) delta) x)
	       (equal (instance (val y sigma) delta) y)
	       (not (equal x y)))
	      (not (equal (val x sigma) (val y sigma))))
     :rule-classes nil))

  (local
   (defthm identity-on-term-identity-val
     (implies (and
	       (equal (apply-subst flg delta (apply-subst flg sigma term))
		      term)
	       (member x (variables flg term)))
	      (equal (instance (val x sigma) delta) x))
     :rule-classes nil))

  (defthm  renamed-implies-injective-val
    (implies (and
	      (equal (apply-subst flg delta (apply-subst flg sigma term))
		     term)
	      (member x (variables flg term))
	      (member y (variables flg term))
	      (not (equal x y)))
	     (not (equal (val x sigma) (val y sigma))))
    :hints (("Goal" :use ((:instance renamed-implies-injective-val-lemma)
			  (:instance identity-on-term-identity-val)
			  (:instance identity-on-term-identity-val
				     (x y))))))))


;;; ············································································
;;; 2.3.2 co-domain of sigmar is a setp
;;; ············································································



(local
 (encapsulate

  ()

  (local
   (defthm  renamed-implies-setp-codomain-main-lemma
     (implies (and
	       (equal (apply-subst flg delta (apply-subst flg sigma term))
		      term)
	       (setp l)
	       (subsetp l (variables flg term)))
	      (setp (co-domain (restriction sigma l))))
     :hints (("Goal" :induct (setp l))
	     ("Subgoal *1/2'4'" :induct (len l2)))))


 (defthm renamed-implies-setp-codomain
    (implies
     (equal (apply-subst flg delta (apply-subst flg sigma term)) term)
     (setp (co-domain (normal-form-subst flg sigma term))))
    :hints (("Goal" :use
	     (:instance renamed-implies-setp-codomain-main-lemma
			(l (make-set (variables flg term)))))))))

;;; ············································································
;;; 2.3.3 sigmar is a renaming
;;; ············································································

(local
 (defthm renamed-implies-renaming-main-lemma
   (implies
    (equal (apply-subst flg delta (apply-subst flg sigma term)) term)
    (renaming (normal-form-subst flg sigma term)))
   :rule-classes nil))


(defthm renamed-implies-renaming
  (let ((ren (normal-form-subst t (matching t1 t2) t1)))
    (implies (renamed t1 t2)
	     (and (renaming ren)
		  (equal (instance t1 ren) t2))))
  :hints (("Goal" :use
	   (:instance renamed-implies-renaming-main-lemma
		      (term t1) (sigma (matching t1 t2))
		      (delta (matching t2 t1))
		      (flg t)))))


;;; ============================================================================
;;; 3. Number renamings: a special kind of renaming.
;;; ============================================================================

;;; We will define number-renaming. We rename the term enumerating the
;;; variables, starting from a given number x and incrementing by y.


;;; ----------------------------------------------------------------------------
;;; 3.1 Number renaming.
;;; ----------------------------------------------------------------------------


;;; As we said before, this is a special kind of renaming. Every
;;; variable is substituted in a sound way for a number. This could be
;;; done very easiliy in two rounds. First compute the renaming
;;; substitution and then apply the renaming to obtain the renamed
;;; version of the term. Since this will be a procedure to apply very
;;; often, we implement here in a more eficcient way: the renaming and
;;; the renamed term are computed at the same time.

;;; The definition:

(defun number-rename-aux (flg term sigma x y)
  (declare (xargs :guard (and (term-p-aux flg term)
			      (acl2-numberp x)
			      (acl2-numberp y)
			      (alistp-acl2-numberp sigma))
		  :verify-guards nil))
  (if flg
      (if (variable-p term)
	  (let ((find-term (assoc term sigma)))
	    (if find-term
		(mv (cdr find-term) sigma)
	      (let ((z (if (endp sigma) x (+ y (cdar sigma)))))
		(mv z (cons (cons term z) sigma)))))
	(mv-let (renamed-args renaming-args)
		(number-rename-aux nil (cdr term) sigma x y)
		(mv (cons (car term) renamed-args) renaming-args)))
    (if (endp term)
	(mv term sigma)
      (mv-let (renamed-car renaming-car)
	      (number-rename-aux t (car term) sigma x y)
	      (mv-let (renamed-cdr renaming-cdr)
		      (number-rename-aux nil (cdr term) renaming-car x y)
		      (mv (cons renamed-car renamed-cdr)
			  renaming-cdr))))))
;;; REMARK : x is only needed when sigma is endp and no
;;; longer. It can be considered as a constant.




;;; Guard verification

(local
 (defthm alistp-acl2-numberp-alistp
   (implies (alistp-acl2-numberp l)
	    (alistp l))
   :rule-classes :forward-chaining))

(local
 (defthm alistp-acl2-numberp-second-number-rename-aux
   (implies (and (alistp-acl2-numberp sigma)
		 (acl2-numberp x))
	    (alistp-acl2-numberp
	     (second (number-rename-aux flg term sigma x y))))))


(verify-guards number-rename-aux)

;;; ----------------------------------------------------------------------------
;;; 3.2 Number-rename-aux: closure properties
;;; ----------------------------------------------------------------------------
;;; The results in this subsection are needed for further guard
;;; verification of functions using number-rename-aux and for the proof
;;; of closure properties of number-rename



(local
 (defthm number-rename-aux-substitution-s-p
   (implies (and (acl2-numberp x)
		 (term-s-p-aux flg term)
		 (substitution-s-p sigma))
	    (substitution-s-p
	     (second (number-rename-aux flg term sigma x y))))))

;;; Needed for closure property:


(local
 (encapsulate
  ()

  (local
   (defthm number-rename-aux-equal-len
     (equal (len (first (number-rename-aux nil term sigma x y)))
	    (len term))))

  (defthm number-rename-aux-term-s-p-aux
    (implies (and (acl2-numberp x)
		  (term-s-p-aux flg term)
		  (alistp-acl2-numberp sigma))
	     (term-s-p-aux
	      flg (first (number-rename-aux flg term sigma x y)))))))




;;; ----------------------------------------------------------------------------
;;; 3.3 Number-rename-aux: main properties.
;;; ----------------------------------------------------------------------------

;;; ············································································
;;; 3.3.1 Previous (local) lemmas about coincide.
;;; ············································································

;;; We will need these lemmas because we are going to talk about
;;; extensions (see the definition in terms.lisp, subsection 2.3)

;;; ====== COINCIDE. See definition and properties in terms.lisp

(local
 (encapsulate
  ()

  (local
   (defthm coincide-main-property
     (implies (and (coincide sigma1 sigma2 l)
		   (member x l))
	      (equal (equal (val x sigma1) (val x sigma2)) t))))

;;; REMARK: The form of the rule avoids non-termination
;;; This rule is also local in terms.lisp. We don't want terms.lisp to
;;; export everywhere. That's the reason why we repeat here the rule.


  (defthm coincide-conmutative
    (implies (coincide a b l)
	     (coincide b a l)))


  (in-theory (disable coincide-conmutative))

  (defthm coincide-cons
    (implies (and
	      (not (member x l))
	      (coincide sigma sigma1 l))
	     (coincide (cons (cons x y) sigma) sigma1 l)))


  (defthm coincide-subsetp-transitive
    (implies (and (coincide sigma sigma1 l)
		  (coincide sigma1 sigma2 m)
		  (subsetp  l m))
	     (coincide sigma sigma2 l)))

  (in-theory (disable coincide-subsetp-transitive))))


;;; ············································································
;;; 3.3.2 Previous (local) lemmas about acl2-numberp-list-increment
;;; ············································································

;;; We will define and prove some local properties of the concept of
;;; being a list of numbers l such that each of its elements is obtained
;;; incrementing the previous one by a constant y.

;;; ====== ACL2-NUMBERP-LIST-INCREMENT

(local
 (defun acl2-numberp-list-increment (l y)
   (cond ((endp l) t)
	 ((endp (cdr l)) (acl2-numberp (first l)))
	 (t (and (acl2-numberp (first l))
		 (= y (- (first l) (second l)))
		 (acl2-numberp-list-increment (cdr l) y))))))

(local
 (encapsulate
  ()

  (local
   (defthm acl2-numberp-list-increment-setp-1-lema
     (implies (and (acl2-numberp-list-increment l y)
		   (consp l)
		   (> y 0)
		   (> x (first l)))
	      (not (member x l)))))

  (local
   (defthm acl2-numberp-list-increment-setp-1
     (implies (and (acl2-numberp-list-increment l y)
		   (> y 0))
	      (setp l))))

  (local
   (defthm acl2-numberp-list-increment-setp-2-lema
     (implies (and (acl2-numberp-list-increment l y)
		   (consp l)
		   (< y 0)
		   (< x (first l)))
	      (not (member x l)))))

  (local
   (defthm acl2-numberp-list-increment-setp-2
     (implies (and (acl2-numberp-list-increment l y)
		   (< y 0))
	      (setp l))))


  (defthm acl2-numberp-list-increment-setp
    (implies (and (acl2-numberp-list-increment l y)
		  (not (=  y 0)))
	     (setp l))
    :hints (("Goal" :cases ((> y 0) (< y 0)))))))



;;; ············································································
;;; 3.3.3 number-rename-aux: properties of the variables of the returned term
;;; ············································································

;;; We will prove that (first (number-rename-aux flg term sigma x y) is a
;;; term having numeric variables, and:
;;; * if y>0, they are greater than x
;;; * if y<0, they are smaller than x

;;; ===== ACL2-NUMBERP-LIST-SMALLER-THAN

(defun acl2-numberp-list-smaller-than (l x)
  (if (endp l)
      t
    (and (acl2-numberp (first l))
	 (<= (first l) x) (acl2-numberp-list-smaller-than (cdr l) x))))

;;; ===== ACL2-NUMBERP-LIST-BIGGER-THAN

(defun acl2-numberp-list-bigger-than (l x)
  (if (endp l)
      t
    (and
     (acl2-numberp (first l))
     (>= (first l) x) (acl2-numberp-list-bigger-than (cdr l) x))))


(local
 (encapsulate
  ()

  (local
   (defthm acl2-numberp-list-bigger-than-append
     (iff (acl2-numberp-list-bigger-than (append l1 l2) x)
	  (and (acl2-numberp-list-bigger-than l1 x)
	       (acl2-numberp-list-bigger-than l2 x)))))

  (defthm number-renamed-aux-variables->=-x
    (implies (and (acl2-numberp-list-bigger-than (co-domain sigma) x)
		  (> y 0)
		  (acl2-numberp x))
	     (and
	      (acl2-numberp-list-bigger-than
	       (variables
		flg (first (number-rename-aux flg term sigma x y))) x)
	      (acl2-numberp-list-bigger-than
	       (co-domain
		(second (number-rename-aux flg term sigma x y))) x))))


  (local
   (defthm acl2-numberp-list-smaller-than-append
     (iff (acl2-numberp-list-smaller-than (append l1 l2) x)
	  (and (acl2-numberp-list-smaller-than l1 x)
	       (acl2-numberp-list-smaller-than l2 x)))))

  (defthm number-renamed-aux-variables-<=-x
    (implies (and (acl2-numberp-list-smaller-than (co-domain sigma) x)
		  (< y 0)
		  (acl2-numberp x))
	     (and
	      (acl2-numberp-list-smaller-than
	       (variables
		flg (first (number-rename-aux flg term sigma x y))) x)
	      (acl2-numberp-list-smaller-than
	       (co-domain
		(second (number-rename-aux flg term sigma x y))) x))))))


;;; ············································································
;;; 3.3.4 number-rename-aux: Main property of the co-domain of the
;;; returned substitution.
;;; ············································································


(local
 (defthm number-rename-co-domain-acl2-numberp-list-increment
   (implies (and (acl2-numberp-list-increment (co-domain sigma) y)
		 (acl2-numberp x)
		 (acl2-numberp y))
	    (acl2-numberp-list-increment
	     (co-domain (second (number-rename-aux flg term sigma x y))) y))))

;;; ············································································
;;; 3.3.5 number-rename-aux: the substitution returned is a renaming
;;; ············································································


(local
 (encapsulate
  ()

  (local
   (defthm acl2-numberp-list-increment-implies-variable-substitution
     (implies (acl2-numberp-list-increment (co-domain sigma) y)
	      (variable-substitution sigma))))

  (local
   (defthm acl2-numberp-list-increment-implies-renaming
     (implies (and
	       (acl2-numberp-list-increment (co-domain sigma) y)
	       (acl2-numberp y)
	       (not (= y 0)))
	      (renaming sigma))))


  (defthm number-rename-renaming
    (implies (and (acl2-numberp x) (acl2-numberp y) (not (= y 0)))
	     (renaming (second (number-rename-aux flg term nil x y))))
    :hints (("Goal" :use (:instance
			  acl2-numberp-list-increment-implies-renaming
			  (sigma
			   (second
			    (number-rename-aux flg term nil x y)))))))))



;;; ············································································
;;; 3.3.3 Subsumption properties of number-rename-aux
;;; ············································································


;;; 3.3.3.1
;;; The substituion returned by  number-rename-aux, applied to the input
;;; term returns the returned term (i.e term subsumes the
;;; number-rename-aux term)
;;; ··········································································

;;; Two previos lemmas:


(local
 (defthm number-rename-invariants
   (let ((number-renaming-aux
	  (second (number-rename-aux flg t1 sigma x y))))
     (implies (alistp sigma)
	      (and
	       (alistp number-renaming-aux)
	       (subsetp (domain sigma) (domain number-renaming-aux))
	       (extension number-renaming-aux sigma)
	       (subsetp (variables flg t1) (domain number-renaming-aux)))))
   :hints (("Goal"
	    :in-theory (enable
			subsetp-transitive
			coincide-conmutative
			coincide-subsetp-transitive)))))

(local
 (defthm number-rename-incremental
   (implies (alistp sigma)
	    (equal (apply-subst
		    flg1
		    (second (number-rename-aux
			     flg2 t2
			     (second (number-rename-aux
				      flg1 t1 sigma x1 y1)) x2 y2))
		    t1)
		   (apply-subst
		    flg1
		    (second (number-rename-aux flg1 t1 sigma x1 y1))
		    t1)))
   :hints (("Goal" :use
	    (:instance coincide-in-term
		       (flg flg1)
		       (sigma2
			(second
			 (number-rename-aux
			  flg2 t2
			  (second (number-rename-aux flg1 t1 sigma x1 y1))
			  x2 y2)))
		       (term t1)
		       (sigma1
			(second (number-rename-aux flg1 t1 sigma x1 y1)))
		       (l
			(domain
			 (second
			  (number-rename-aux flg1 t1 sigma x1 y1)))))))))


;;; And the main result:
(local
 (defthm term-subsumes-number-renamed-aux-term
   (implies (alistp sigma)
	    (equal
	     (apply-subst flg (second (number-rename-aux flg term sigma
							 x y))
			  term)
	     (first (number-rename-aux flg term sigma x y))))))



;;; 3.3.3.2
;;; The term returned by number-rename-aux subsumes the input term
;;; ···································································

(local
 (encapsulate
  ()
  (local
   (defthm number-renamed-aux-term-subsumes-term-lemma
     (implies (and (acl2-numberp x) (acl2-numberp y) (not (= y 0)))
	      (equal
	       (apply-subst
		flg
		(inverse (second (number-rename-aux flg term nil x y)))
		(apply-subst flg (second (number-rename-aux flg term nil
							    x y))
			     term))
	       term))
     :hints (("Goal"
	      :in-theory (disable renaming
				  term-subsumes-number-renamed-aux-term)))
     :rule-classes nil))

  (defthm number-renamed-aux-term-subsumes-term
    (implies (and (acl2-numberp x) (acl2-numberp y) (not (= y 0)))
	     (equal
	      (apply-subst
	       flg
	       (inverse (second (number-rename-aux flg term nil x y)))
	       (first (number-rename-aux flg term nil x y)))
	      term))
    :hints (("Goal"
	     :use (:instance number-renamed-aux-term-subsumes-term-lemma))))))


;;; ----------------------------------------------------------------------------
;;; 3.4 Number-rename: definition and main (non-local) properties
;;; ----------------------------------------------------------------------------

;;; Here we compile the results of section 3.

(defun number-rename (term x y)
  (declare (xargs :guard (and (term-p term)
			      (acl2-numberp x)
			      (acl2-numberp y))))
  (mv-let (renamed renaming)
	  (number-rename-aux t term nil x y)
	  (declare (ignore renaming))
	  renamed))


;;; The following lemma can be useful: number-rename never returns the
;;; term nil (instead, it could return the number x). So there are no
;;; confussion between nil as fail and nil as term.

(defthm number-rename-not-nil
  (implies (acl2-numberp x)
	   (number-rename term x y)))

;;; Subsumption properties:

(defthm term-subsumes-number-renamed-term
  (subs term (number-rename term x y))

  :hints (("Goal" :use
	   (:instance subs-completeness
		       (t1 term)
		       (t2 (number-rename term x y))
		       (sigma
			(second (number-rename-aux t term nil x y)))))))

(defthm number-renamed-term-subsumes-term
  (implies (and (acl2-numberp x) (acl2-numberp y) (not (= y 0)))
	   (subs (number-rename term x y) term))

  :hints (("Goal" :use
	   (:instance subs-completeness
		       (t2 term)
		       (t1 (number-rename term x y))
		       (sigma
			(inverse
			 (second (number-rename-aux t term nil x y))))))))


;;; Variables of (number-rename term x y) are:
;;; * if y>0, they are all bigger than x
;;; * if y<0, they are all smaller than x

(defthm number-renamed-variables->=-x
   (implies (and (acl2-numberp x) (> y 0))
	    (acl2-numberp-list-bigger-than
	     (variables t (number-rename term x y))
	     x)))


(defthm number-renamed-variables-<=-x
   (implies (and (acl2-numberp x) (< y 0))
	    (acl2-numberp-list-smaller-than
	     (variables t (number-rename term x y))
	     x)))

;;; An useful property for standardization apart:
(encapsulate
 ()

 (local
  (defthm smaller-bigger-disjointp
    (implies (and
	      (< x1 x2)
	      (acl2-numberp-list-smaller-than l1 x1)
	      (acl2-numberp-list-bigger-than l2 x2))
	     (disjointp l1 l2))))

 (defthm number-rename-standardization-apart
   (implies (and (acl2-numberp x1)
		 (acl2-numberp x2)
		 (< x1 x2)
		 (< y1 0)
		 (< 0 y2))
	    (disjointp (variables t (number-rename t1 x1 y1))
		       (variables t (number-rename t2 x2 y2))))
   :hints (("Goal" :use
	    (:instance
	     smaller-bigger-disjointp
	     (l1 (variables t (number-rename t1 x1 y1)))
	     (l2 (variables t (number-rename t2 x2 y2))))))))


;;; Closure property:


(defthm number-rename-term-s-p
  (implies (and (acl2-numberp x) (term-s-p term))
	   (term-s-p (number-rename term x y))))


;;; Needed for guard verification:

(defthm number-rename-term-p
  (implies (and (acl2-numberp x) (term-p term))
	   (term-p (number-rename term x y)))
  :hints (("Goal" :use (:functional-instance
			number-rename-term-s-p
			(signat (lambda (x n) (eqlablep x)))
			(term-s-p-aux term-p-aux)))))

;;; We have extracted the main properties of number-rename, so we now
;;; disable its definition:
(in-theory (disable number-rename))


;;; A rewriting congruence rule:

(defthm number-renamed-term-renamed-term
  (implies (and (acl2-numberp x) (acl2-numberp y) (not (= y 0)))
	   (renamed (number-rename term x y) term)))


;;; ----------------------------------------------------------------------------
;;; 3.5 Number-rename-list: definition and main (non-local) properties
;;; ----------------------------------------------------------------------------

;;; Renaming lists of terms
;;; Although we are going just to repeat the above development, now for
;;; lists of terms, we think it is convinient to define separately
;;; number-rename from number-rename-list, although they are diferent
;;; particular cases of the same function: number-rename-aux.

;;; Sometimes (see for example critical-pairs.lisp) we will need to
;;; rename several terms at the same time (for example, both terms of a
;;; rewriting rule). In such cases we want the same variable to be
;;; replaced for the same number, wherever that variable occurs in the
;;; list (even in diferent terms of the list). That's the reason why we
;;; define number-rename-list and its properties as non-local in this
;;; book.

(defun number-rename-list (l x y)
  (declare (xargs :guard (and (term-p-aux nil l)
			      (acl2-numberp x)
			      (acl2-numberp y))))
  (mv-let (renamed renaming)
	  (number-rename-aux nil l nil x y)
	  (declare (ignore renaming))
	  renamed))


;;; Subsumption properties:

(defthm list-subsumes-number-renamed-list-
  (subs-list l (number-rename-list l x y))

  :hints (("Goal" :use
	   (:instance subs-list-completeness
		       (l1 l)
		       (l2 (number-rename-list l x y))
		       (sigma
			(second (number-rename-aux nil l nil x y)))))))

(defthm number-renamed-list-subsumes-list
  (implies (and (acl2-numberp x) (acl2-numberp y) (not (= y 0)))
	   (subs-list (number-rename-list l x y) l))

  :hints (("Goal" :use
	   (:instance subs-list-completeness
		       (l2 l)
		       (l1 (number-rename-list l x y))
		       (sigma
			(inverse
			 (second (number-rename-aux nil l nil x y))))))))


;;; Variables of (number-rename term x y) are:
;;; * if y>0, they are all bigger than x
;;; * if y<0, they are all smaller than x

(defthm number-renamed-list-variables->=-x
   (implies (and (acl2-numberp x) (> y 0))
	    (acl2-numberp-list-bigger-than
	     (variables nil (number-rename-list term x y))
	     x)))


(defthm number-renamed-list-variables-<=-x
   (implies (and (acl2-numberp x) (< y 0))
	    (acl2-numberp-list-smaller-than
	     (variables nil (number-rename-list term x y))
	     x)))

;;; An useful property for standardization apart:
(encapsulate
 ()

 (local
  (defthm smaller-bigger-disjointp
    (implies (and
	      (< x1 x2)
	      (acl2-numberp-list-smaller-than l1 x1)
	      (acl2-numberp-list-bigger-than l2 x2))
	     (disjointp l1 l2))))

 (defthm number-rename-list-standardization-apart
   (implies (and (acl2-numberp x1)
		 (acl2-numberp x2)
		 (< x1 x2)
		 (< y1 0)
		 (< 0 y2))
	    (disjointp (variables nil (number-rename-list l1 x1 y1))
		       (variables nil (number-rename-list l2 x2 y2))))
   :hints (("Goal" :use
	    (:instance
	     smaller-bigger-disjointp
	     (l1 (variables nil (number-rename-list l1 x1 y1)))
	     (l2 (variables nil (number-rename-list l2 x2 y2))))))))


;;; Closure property:


(defthm number-rename-list-term-s-p-aux-nil
  (implies (and (acl2-numberp x) (term-s-p-aux nil l))
	   (term-s-p-aux nil (number-rename-list l x y))))


;;; Needed for guard verification:

(defthm number-rename-list-term-p-aux-nil
  (implies (and (acl2-numberp x) (term-p-aux nil l))
	   (term-p-aux nil (number-rename-list l x y)))
  :hints (("Goal" :use (:functional-instance
			number-rename-list-term-s-p-aux-nil
			(signat (lambda (x n) (eqlablep x)))
			(term-s-p-aux term-p-aux)))))

;;; We have extracted the main properties of number-rename-list, so we now
;;; disable its definition:
(in-theory (disable number-rename-list))





