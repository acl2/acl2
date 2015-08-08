;;; =================================================================
;;; subsumption-definition-v0.lisp
;;; Definition and correctness of a subsumption
;;; algorithm between terms. Definition of the subsumption relation.
;;; Created 7-10-99.
;;; This is a translated version of an .events file for nqthm
;;; WARNING: Although this book is correct, there an improved version,
;;; based on rules of transformation, subsumption.lisp
;;; =================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "subsumption-definition-v0")

|#

(in-package "ACL2")
(include-book "terms")

;;; **********************************
;;; DEFINITION: SUBSUMPTION ALGORITHM
;;; **********************************

;;; NOTE:
;;; 1) Definition by mutual recursion on terms and list of terms.
;;; 2) sigma is a substitutions of computed bindings for the moment.

(defun subsumption-alg (flg t1 t2 sigma)
  (if flg
      (if (variable-p t1)
	  (if (member t1 (domain sigma))
	      (if (equal (val t1 sigma) t2)
		  sigma			                    ; *11*
		nil)                                        ; *10*
	    (cons (cons t1 t2) sigma))                      ; *9*
	(if (variable-p t2)
	    nil                                             ; *8*
	  (if (equal (car t1) (car t2))
	      (subsumption-alg nil (cdr t1) (cdr t2) sigma) ; *7*
	    nil)))                                          ; *6*
    (if (atom t1)
	(if (equal t1 t2) sigma nil)                        ; *5* y *4*
      (if (atom t2)
	  nil                                               ; *3*
	(let ((subs-primeros (subsumption-alg t (car t1) (car t2) sigma)))
	  (if subs-primeros
	      (subsumption-alg nil                          ; *2*
			      (cdr t1)
			      (cdr t2)
			      subs-primeros)
	    nil))))))                                       ; *1*

;;; DESCRIPTION:
;;; Input:   t1 and t2 are terms or list of terms (depending on flg).
;;;          sigma is a substitution (initial bindings)
;;;          flg is a boolean value:
;;;          - If flg is nil, t1 and t2 are list of terms
;;;          - If flg is not nil, t1 and t2 are terms.
;;; Output:
;;; *11* If t1 and t2 are terms, t1 is a variable alrady bound in sigma,
;;;      and its value in sigma is t2, returns sigma.
;;; *10* As in *1*, but the value of t1 in sigma iis not t2, returns nil
;;; *9* If t1 and t2 are terms, t1 is a variable not bound in sigma,
;;;     return sigma adding the binding (t1 . t2)
;;; *8* If t1 is not a variable and t2 is a variable, returns nil.
;;; *7* If t1 and t2 are non-variable terms, with the same top function
;;;     symbol, recursively call to subsumption-alg applied to the lists
;;;     of the respective arguments.
;;; *6* If t1 and t2 are non-variable terms, with different top function
;;;     symbol, return nil.
;;; *5* If t1 and t2 are lists of terms and t1 is an empty list,
;;;     the same as t2, returns sigma.
;;; *4* If t1 and t2 are lists of terms and t1 is an empty list,
;;;     different from t2, returns nil.
;;; *3* If t1 and t2 are lists of terms, t1 is not an empty list,
;;;     and t2 is an empty list, returns nil.
;;; *2* If t1 and t2 are non-empty lists of terms and the the first
;;;     elements of t1 subsumes the first element of t2, recursively
;;;     call subsumption-alg with the list of the rest of respective
;;;     arguments, with initial bindings the substitution obtained when
;;;     applying the algorithm to the first arguments.
;;; *1* If t1 and t2 are non-empty lists of terms and the the first
;;;     elements of t1 does not subsume the first element of t2, returns
;;;     nil.


;;; ******************************
;;; PREVIOUS LEMMAS ABOUT COINCIDE
;;; ******************************
;;; ====== COINCIDE. See definition and properties in terms.lisp
(local
(defthm coincide-main-property
   (implies (and (coincide sigma1 sigma2 l)
		 (member x l))
	    (equal (equal (val x sigma1) (val x sigma2)) t))))

;;; The form of the rule avoids non-termination
;;; This rule is also local in terms.lisp. We don't want terms.lisp to
;;; export everywhere. That's the reason why we repeat here the rule.
(local
(defthm coincide-conmutative
  (implies (coincide a b l)
	   (coincide b a l))))


(local (in-theory (disable coincide-conmutative)))
(local
(defthm coincide-cons
  (implies (and
	    (not (member x l))
	    (coincide sigma sigma1 l))
	   (coincide (cons (cons x y) sigma) sigma1 l))))

(local
(defthm coincide-subsetp-transitive
  (implies (and (coincide sigma sigma1 l)
		(coincide sigma1 sigma2 m)
		(subsetp m l))
	   (coincide sigma sigma2 m))))

(local
(in-theory (disable coincide-subsetp-transitive)))



;;; *************************************************
;;; LEMMAS FOR PROVING SOUNDNESS OF SUBSUMPTION-ALG
;;; *************************************************

;;; ========================  LEMA  ================
;;; If subsumption suceeds, the result extends sigma
;;; ================================================

(local (defthm soundness-main-lemma-1
  (let ((result-subsumption (subsumption-alg flg t1 t2 sigma)))
    (implies result-subsumption
	     (and
	      (subsetp (domain sigma) (domain result-subsumption))
	      (extension result-subsumption sigma)
	      (subsetp (variables flg t1) (domain result-subsumption)))))
  :hints (("Goal"
	   :in-theory (enable
		       subsetp-transitive
		       coincide-conmutative
		       coincide-subsetp-transitive)))))



(local (defthm soundness-main-lemma-2
  (implies (and (subsumption-alg flg1 t1 t2 sigma)
		(subsumption-alg flg2 t3 t4 (subsumption-alg flg1 t1 t2 sigma)))
	   (equal (apply-subst
		   flg1
		   (subsumption-alg flg2 t3 t4 (subsumption-alg flg1 t1 t2
						      sigma))
		   t1)
		  (apply-subst flg1 (subsumption-alg flg1 t1 t2 sigma) t1)))
  :hints (("Goal" :use
	   (:instance coincide-in-term
		      (flg flg1)
		      (sigma2 (subsumption-alg flg2 t3 t4
					       (subsumption-alg flg1 t1 t2 sigma)))
		      (term t1)
		      (sigma1 (subsumption-alg flg1 t1 t2 sigma))
		      (l (domain (subsumption-alg flg1 t1 t2 sigma))))))))



;;; ****************************
;;; SOUNDNESS OF SUBSUMPTION-ALG
;;; ****************************

;;; ==============================  LEMMA  ==============================
;;; If subsumption suceeds, the result is a matching susbtitution for t1
;;; and t2
;;; =====================================================================


(local (defthm soudness-subsumption-alg
    (implies (subsumption-alg flg t1 t2 sigma)
	     (equal (apply-subst flg (subsumption-alg flg t1 t2 sigma) t1)
		    t2))))


;;; ******************************
;;; COMPLETENESS OF SUBSUMPTION-ALG
;;; ******************************

;;; ============================  LEMMA ===============================
;;; If sigma1 is a matching substitution for t1 and t2, our subsumption
;;; algorithm succeeds and sigma1 is an extension of the substitution
;;; returned.
;;; ===================================================================

(local (defthm completeness-subsumption-alg-general
  (let ((result-subsumption (subsumption-alg flg t1 t2 sigma1)))
    (implies (and (equal (apply-subst flg sigma t1) t2)
		  sigma1
		  (extension sigma sigma1))
	     (and result-subsumption
		  (extension sigma result-subsumption))))
  :rule-classes nil))
;;; REMARKS:
;;;    The free variables in the lemma make it useless as rewriting
;;;    rule.


;;; ******************************************************************
;;; DEFINITION: A SUBSUMPTION RELATION BETWEEN TERMS OR LISTS OF TERMS
;;; ******************************************************************


(defun subs (t1 t2)
  (subsumption-alg t t1 t2 0))


;;; REMARK: In ACL2, nil and the empty list are the same thing. To
;;; distinguish fail from the empty list, we apply subsumption with an
;;; non-nil atom (0 in this case) and at teh end we fix the final tail.

;;; =================
;;; SOUNDNESS OF SUBS
;;; =================

(defthm soudness-subs
  (implies (subs t1 t2)
	   (equal (instance t1 (subs t1 t2))
		  t2))
  :rule-classes (:rewrite :elim))

;;; ============================
;;; COMPLETENESS OF SUBS-WITNESS
;;; ============================

(defthm completeness-subs
  (implies (equal (instance t1 sigma) t2)
	   (subs t1 t2))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
			 completeness-subsumption-alg-general
			 (flg t)
			 (sigma1 0))))))


(in-theory (disable subsumption-alg))
(in-theory (disable subs))
















