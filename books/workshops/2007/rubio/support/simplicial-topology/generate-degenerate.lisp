;;; ==========================================================
;;; An elementary example about simplicial topology
;;; Supporting material for the paper "Formalizing simplicial topology
;;; in ACL2"
;;; Authors: J.L. Ruiz-Reina, J. Rubio, M. Andrés, L. Lambán
;;; Created: July, 2007
;;; Last modified: July 9th, 2007
;;; ==========================================================



#| To certify this book:

(in-package "ACL2")

(defconst *abstract-proofs-exports*
  '(last-elt r-step direct operator elt1 elt2 r-step-p make-r-step
    first-of-proof last-of-proof steps-up steps-down steps-valley
    proof-before-valley proof-after-valley inverse-r-step inverse-proof
    local-peak-p proof-measure proof-before-peak proof-after-peak
    local-peak peak-element))

(defconst *cnf-package-exports*
  (union-eq *acl2-exports*
	    (union-eq
	     *common-lisp-symbols-from-main-lisp-package*
	     *abstract-proofs-exports*)))

(defpkg "CNV" (cons 'multiset-diff *cnf-package-exports*))


(certify-book "generate-degenerate" 3)

|#

(in-package "ACL2")



;;; We prove the following elementary result in simplicial topology:

;;; Theorem 1: Let $K$ be a simplicial set. Any degenerate $n$-simplex
;;; $x\in K_n$ can be expressed in a unique way as a (possibly) iterated
;;; degeneracy of a non-degenerate simplex $y$ in the following way:
;;; $$x=\eta_{j_k}\ldots \eta_{j_1}y$$ with $y\in K_r, \ k=n-r>0, \ 0 \leq
;;; j_1 < \cdots < j_k < n$.


;;; In our ACL2 model, this is simply stated as follows:

;;; Theorem 2: Any ACL2 list $l$ can be expressed in a unique way as a
;;; pair $(dl,l')$ such that: $$l=degenerate(dl,l')$$
;;; with $l'$ without two consecutive elements equal and $dl$ an
;;; strictly increasingdegeneracy list.


;;; We present an alternative proof, based on defining a reduction
;;; relation and reducing the intended result to proving that the
;;; relation is noetherian and locally confluent.

;;; We will need a previously developed theory about abstract
;;; reductions. In  Partcular, we need an ACL2 proof of Newman's lemma
;;; (every noetherian and locally confluent reduction relation is
;;; convergent and thus has the property of unique normal forms)

(include-book "../abstract-reductions/convergent")
(include-book "arithmetic/top-with-meta" :dir :system)




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART I: Definition of the S-reduction relation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The reduction will be defined following the ideas of a previous
;;; formalization of abstract reduction systemas reported in reference
;;; [9] of the paper. This will allow us to functionally instantiate the
;;; properties proved in that library of results.

;;; Domain of the reduction (we do not need to be more specific):

(defun simplex (x)
  (declare (ignore x))
  t)

;;; Operators are of the form (<TYPE> . <I>) where <TYPE> is 'O or 'R
;;; and <I> is the position of the list where the reduction takes place

;;; The function checking when it is valid to apply an operator to an
;;; element:

(defun s-legal (x op)
  (let ((l1 (car x))
	(l2 (cdr x))
	(op-type (car op))
	(op-index (cdr op)))
    (if (equal 'o op-type)
	(and (natp op-index)
	     (< op-index (1- (len l1)))
	     (>= (nth op-index l1)
		 (nth (1+ op-index) l1)))
      (and (natp op-index)
	   (< op-index (1- (len l2)))
	   (equal (nth op-index l2)
		  (nth (1+ op-index) l2))))))


(defun interchange1+ (i l)
  (if (zp i)
      (list* (second l) (1+ (first l)) (cddr l))
    (cons (first l) (interchange1+ (1- i) (cdr l)))))

(defun del-nth (i l)
  (if (zp i)
      (cdr l)
    (cons (car l) (del-nth (1- i) (cdr l)))))

;;; The function that applies on step of reduction

(defun s-reduce-one-step (x op)
  (let ((l1 (car x))
	(l2 (cdr x))
	(op-type (car op))
	(op-index (cdr op)))
    (if (equal 'o op-type)
	(cons (interchange1+ op-index l1) l2)
      (cons (cons op-index l1) (del-nth op-index l2)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART II: Noetherianity
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; First, a well-founded relation s-rel is defined; it will be used for
;;; justifying noetherianity of the S-reduction

(defun consecutive-repetitions (l)
  (cond ((or (endp l) (endp (cdr l))) 0)
	((equal (first l) (second l))
	 (1+ (consecutive-repetitions (cdr l))))
	(t (consecutive-repetitions (cdr l)))))

(defun disorders-aux (x l)
  (cond ((endp l) 0)
	((>= x (car l)) (1+ (disorders-aux (1+ x) (cdr l))))
	(t (disorders-aux x (cdr l)))))


(defun disorders (l)
  (if (endp l)
      0
    (+ (disorders-aux (car l) (cdr l))
       (disorders (cdr l)))))

(defun s-rel (p1 p2)
  (let ((l1 (car p1))
	(l2 (cdr p1))
	(l3 (car p2))
	(l4 (cdr p2)))
    (cond  ((< (consecutive-repetitions l2)
	       (consecutive-repetitions l4))
	    t)
	   ((= (consecutive-repetitions l2)
	       (consecutive-repetitions l4))
	    (< (disorders l1) (disorders l3)))
	   (t nil))))


(defun s-ordinal-embedding (p)
  (let ((l1 (car p))
	(l2 (cdr p)))
    (cons (cons 1 (1+ (consecutive-repetitions l2)))
	  (disorders l1))))


(defthm s-rel-well-founded-relation
  (and (o-p (s-ordinal-embedding x))
       (implies (s-rel x y)
		(o< (s-ordinal-embedding x)
		    (s-ordinal-embedding y))))
  :rule-classes :well-founded-relation)




;;; Second, notherianity of the reduction is justified proving that
;;; every application of a "legal" operator returns an smaller element
;;; (w.r.t.  the well-founded relation s-rel)

;;; previous lemmas

(defthm interchange-1+-disorders-aux-lemma
  (implies (and (natp i) (< i (1- (len l)))
		(<= (NTH (1+ I) L) (NTH I L)))
	   (<= (disorders-aux x (interchange1+ i l))
	       (disorders-aux x l)))
  :rule-classes :linear)


(defthm interchange-1+-reduces-disorders
  (implies (and (natp i)
		(< i (1- (len l)))
		(<= (nth (1+ i) l) (nth i l)))
	   (< (disorders (interchange1+ i l))
	      (disorders l)))
  :rule-classes :linear)


(defthm car-del-nth
  (implies (and (natp i)
		(< i (1- (len l)))
		(equal (nth i l) (nth (1+ i) l)))
	   (equal (car (del-nth i l)) (car l))))

(defthm del-nth-reduces-consecutive-repetitions
  (implies (and (natp i)
		(< i (1- (len l)))
		(equal (nth i l)
		       (nth (1+ i) l)))
	   (< (consecutive-repetitions (del-nth i l))
	      (consecutive-repetitions l)))
  :rule-classes :linear)



;;; FInally, noetherianity:
(defthm s-reduction-noetherian
   (implies (s-legal p op)
	    (s-rel (s-reduce-one-step p op) p)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART III: A function checking reducibility (and properties)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We define a function s-reducible, returning a legal operator
;;; whenever it exists, NIL otherwise

(defun find-disorder (l)
  (cond ((or (endp l) (endp (cdr l))) nil)
	((>= (first l) (second l)) 0)
	(t (let ((fd-cdr (find-disorder (cdr l))))
	     (if fd-cdr (1+ fd-cdr) nil)))))

(defun find-consecutive-repetition (l)
  (cond ((or (endp l) (endp (cdr l))) nil)
	((equal (first l) (second l)) 0)
	(t (let ((fcr-cdr (find-consecutive-repetition (cdr l))))
	     (if fcr-cdr (1+ fcr-cdr) nil)))))


(defun s-reducible (p)
  (let ((l1 (car p))
	(l2 (cdr p)))
    (let ((i1 (find-disorder l1)))
      (if i1
	  (cons 'o i1)
	(let ((i2 (find-consecutive-repetition l2)))
	  (if i2
	      (cons 'r i2)
	    nil))))))

;;; After a number of needed lemmas, we prove the main properties of
;;; s-reducible:


;;; Some lemmas

(defthm find-disorder-main-property-1
  (implies (and (not (find-disorder l))
	        (natp i)
		(< i (1- (len l))))
	   (< (nth i l) (nth i (cdr l))))
  :rule-classes :linear)


(defthm find-disorder-main-property-2
  (let ((index-fd (find-disorder l)))
    (implies index-fd
	     (>= (nth index-fd l) (nth (1+ index-fd) l))))
  :hints (("Goal" :induct (find-disorder l)))
  :rule-classes nil)

(defthm find-disorder-corollary
  (let ((index-fd (find-disorder l)))
    (implies (and index-fd
		  (consp l))
	     (<= (nth index-fd (cdr l)) (nth index-fd l))))
  :hints (("Goal" :use (:instance find-disorder-main-property-2
				  (l (cdr l))))))


(defthm find-consecutive-repetition-main-property-1
  (implies (and (not (find-consecutive-repetition l))
	        (natp i)
		(< i (1- (len l))))
	   (equal (equal (nth i l) (nth i (cdr l)))
		  nil)))


(defthm find-consecutive-repetition-main-property-2
  (let ((index-fcr (find-consecutive-repetition l)))
    (implies index-fcr
	     (equal (nth index-fcr l) (nth (1+ index-fcr) l))))
  :hints (("Goal" :induct (find-consecutive-repetition l)))
  :rule-classes nil)


(defthm find-consecutive-repetition-corollary
  (let ((index-fcr (find-consecutive-repetition l)))
    (implies (and index-fcr
		  (consp l))
	     (equal (nth index-fcr (cdr l)) (nth index-fcr l))))
  :hints (("Goal" :use (:instance find-consecutive-repetition-main-property-2
				  (l (cdr l))))))



(defthm find-disorder-less-than-1--len
  (implies (find-disorder l)
	   (< (find-disorder l) (1- (len l))))
  :rule-classes :linear)

(defthm find-consecutive-repetition-less-than-1--len
  (implies (find-consecutive-repetition l)
	   (< (find-consecutive-repetition l) (1- (len l))))
  :rule-classes :linear)




;;; The two main properties of s-reducible


(defthm s-reducible-legal-1
  (implies (not (s-reducible p))
	   (not (s-legal p op))))




(defthm s-reducible-legal-2
  (implies (s-reducible p)
	   (s-legal p (s-reducible p))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART IV: Normal-form computation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun s-normal-form (p)
  (declare (xargs :measure (if (simplex p) p (cons nil nil))
		  :well-founded-relation s-rel
		  :hints (("Goal" :in-theory
			   (disable s-reducible s-legal s-reduce-one-step s-rel)))))
  (if (simplex p)
      (let ((red (s-reducible p)))
	(if red
	    (s-normal-form (s-reduce-one-step p red))
	    p))
    p))


;;; One important property of s-normal-form:

(defthm s-normal-form-main-property
  (not (s-reducible (s-normal-form p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART V: Definition of the equivalence closure =_S
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; A proof step

(defun s-proof-step-p (s)
   (let ((elt1 (elt1 s)) (elt2 (elt2 s))
	 (operator (operator s)) (direct (direct s)))
     (and (r-step-p s)
	  (implies direct (and (s-legal elt1  operator)
			       (equal (s-reduce-one-step elt1 operator)
				      elt2)))
	  (implies (not direct) (and (s-legal elt2 operator)
				     (equal (s-reduce-one-step elt2 operator)
					    elt1))))))

;;; The equivalence closure s-equiv-p. Note that we need an extra
;;; argument P representing the sequence of reduction steps (either from
;;; direct or inverse) connecting the elements related (this sequence is
;;; usually called a "proof")

(defun s-equiv-p (x y p)
   (if (endp p)
       (and (equal x y) (simplex x))
       (and
	(simplex x)
	(s-proof-step-p (car p))
	(equal x (elt1 (car p)))
	(s-equiv-p (elt2 (car p)) y (cdr p)))))



;;; Now we list a number of useful properties about proofs and s-equiv-p
;;; (taken from confluence.lisp and specialized for the particular case
;;; of s-equiv-p )

(encapsulate
 ()

 (local
  (defthm first-element-of-equivalence
    (implies (and (s-equiv-p x y p) (consp p))
	     (equal (elt1 (car p)) x))))

 (local
  (defthm last-elt-of-equivalence
    (implies (and (s-equiv-p x y p) (consp p))
	     (equal (elt2 (last-elt p)) y))))

 (local
  (defthm proof-append
    (implies (equal z (last-of-proof x p1))
	     (equal (s-equiv-p x y (append p1 p2))
		  (and (s-equiv-p x z p1)
		       (s-equiv-p z y p2))))))

 (local
  (defthm consp-inverse-proof
    (iff (consp (inverse-proof p))
	 (consp p))))

 (local
  (defthm last-elt-append
    (implies (consp p2)
	     (equal (last-elt (append p1 p2)) (last-elt p2)))))

 (local
  (defthm last-elt-inverse-proof
    (implies (consp p)
	     (equal (last-elt (inverse-proof p))
		    (inverse-r-step (car p))))))


 (defthm s-equiv-p-symmetric
   (implies (s-equiv-p x y p)
	    (s-equiv-p y x (inverse-proof p))))

 (defthm s-equiv-p-transitive
   (implies (and (s-equiv-p x y p1)
		 (s-equiv-p y z p2))
	    (s-equiv-p x z (append p1 p2)))
   :rule-classes nil))

;;; Note: In abstract-proofs.lisp (included by this book) we have the
;;; following definitions, checking "proof shapes":


;; (defun steps-valley (p)
;;    (cond ((endp p) t)
;; 	 ((direct (car p)) (steps-valley (cdr p)))
;; 	 (t (steps-up (cdr p)))))

;; (defun local-peak-p (p)
;;    (and (consp p)
;; 	(consp (cdr p))
;; 	(atom (cddr p))
;; 	(not (direct (car p)))
;; 	(direct (cadr p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART VI: Local confluence of S-reductions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; In this context, a reduction is locally confluent if every local
;;; peak proof can be transformed in an equivalent valley proof.

;;; The following auxiliary definitions lead us to the definition of a
;;; function s-transform-local-peak. Each of these auxiliary definitions
;;; deal with one possibility of combination of two rules in a local
;;; peak of S-reductions. Please, read it "top-down"


(defun s-transform-disjoint-o-o-local-peak  (i j l1 l2 l3 l4)
    (list (make-r-step :direct t
		       :operator (cons 'o j)
		       :elt1 (cons l1 l2)
		       :elt2 (cons (interchange1+ j l1) l2))
	  (make-r-step :direct nil
		       :operator (cons 'o i)
		       :elt1 (cons (interchange1+ i l3) l4)
		       :elt2 (cons l3 l4))))



(defun s-transform-contiguous-o-o-local-peak
  (i j l1 l2 l3 l4)
    (list (make-r-step :direct t
		       :operator (cons 'o j)
		       :elt1 (cons l1 l2)
		       :elt2 (cons (interchange1+ j l1) l2))
	  (make-r-step :direct t
		       :operator (cons 'o i)
		       :elt1 (cons (interchange1+ j l1) l2)
		       :elt2 (cons
			      (interchange1+ i
					     (interchange1+ j l1))
			      l2))
	  (make-r-step :direct nil
		       :operator (cons 'o j)
		       :elt1 (cons
			      (interchange1+ j
					     (interchange1+ i l3))
			      l4)
		       :elt2 (cons (interchange1+ i l3) l4))
	  (make-r-step :direct nil
		       :operator (cons 'o i)
		       :elt1 (cons (interchange1+ i l3) l4)
		       :elt2 (cons l3 l4))))



(defun s-transform-o-r-local-peak (i j l1 l2 l3 l4)
  (list (make-r-step :direct t
		     :operator (cons 'r j)
		     :elt1 (cons l1 l2)
		     :elt2 (cons (cons j l1) (del-nth j l2)))
	(make-r-step :direct nil
		     :operator (cons 'o (1+ i))
		     :elt1 (cons (interchange1+ (1+ i) l3) l4)
		     :elt2 (cons l3 l4))))


(defun s-transform-r-o-local-peak (i j l1 l2 l3 l4)
  (list (make-r-step :direct t
		     :operator (cons 'o (1+ j))
		     :elt1 (cons l1 l2)
		     :elt2 (cons (interchange1+ (1+ j) l1) l2))
	(make-r-step :direct nil
		     :operator (cons 'r i)
		     :elt1 (cons (cons i l3)  (del-nth i l4))
		     :elt2 (cons l3 l4))))


(defun s-transform-r-r-i-<-j-local-peak
  (i j l1 l2 l3 l4)
  (list (make-r-step :direct t
		     :operator (cons 'r (1- j))
		     :elt1 (cons l1 l2)
		     :elt2 (cons (cons (1- j) l1) (del-nth (1- j) l2)))
	(make-r-step :direct t
		     :operator (cons 'o 0)
		     :elt1 (cons (cons (1- j) l1) (del-nth (1- j) l2))
		     :elt2 (cons (interchange1+ 0 (cons (1- j) l1))
				 (del-nth (1- j) l2)))
	(make-r-step :direct nil
		     :operator (cons 'r i)
		     :elt1 (cons (cons i l3) (del-nth i l4))
		     :elt2 (cons l3 l4))))



(defun s-transform-r-r-i->-j-local-peak
  (i j l1 l2 l3 l4)
  (list (make-r-step :direct t
		     :operator (cons 'r j)
		     :elt1 (cons l1 l2)
		     :elt2 (cons (cons j l1) (del-nth j l2)))
	(make-r-step :direct nil
		     :operator (cons 'o 0)
		     :elt1 (cons (interchange1+ 0 (cons (1- i) l3))
				 (del-nth (1- i) l4))
		     :elt2 (cons (cons (1- i) l3) (del-nth (1- i) l4)))
	(make-r-step :direct nil
		     :operator (cons 'r (1- i))
		     :elt1 (cons (cons (1- i) l3) (del-nth (1- i) l4))
		     :elt2 (cons l3 l4))))




(defun s-transform-local-peak (p)
  (let* ((step1 (first p))
         (step2 (second p))
	 (px (elt1 step1))
	 (py (elt2 step2))
	 (l1 (car px))
	 (l2 (cdr px))
	 (l3 (car py))
	 (l4 (cdr py))
         (operator1 (operator step1))
         (operator2 (operator step2))
         (type1 (car operator1))
         (type2 (car operator2))
	 (i (cdr operator1))
	 (j (cdr operator2)))
    (cond ((and (equal type1 'o) (equal type2 'o))
	   (cond ((= i j) nil)
		 ((or (< (+ i 1) j) (< (+ j 1) i))
		  (s-transform-disjoint-o-o-local-peak i j l1 l2 l3 l4))
		 (t (s-transform-contiguous-o-o-local-peak i j l1 l2 l3
							 l4))))
	  ((and (equal type1 'o) (not (equal type2 'o)))
	   (s-transform-o-r-local-peak i j l1 l2 l3 l4))

	  ((and (not (equal type1 'o)) (equal type2 'o))
	   (s-transform-r-o-local-peak i j l1 l2 l3 l4))

	  (t (cond ((= i j) nil)
		   ((< i j)
		    (s-transform-r-r-i-<-j-local-peak i j l1 l2 l3 l4))
		   (t (s-transform-r-r-i->-j-local-peak i j l1 l2 l3 l4)))))))


;;; ----------------------------------------------------------

;;; Once defined, s-transform-local-peak, we prove the following two
;;; results, establishing local confleunce of S-reductions

;; (defthm local-confluence-1
;;   (implies (and (s-equiv-p x y p)
;; 		(local-peak-p p))
;; 	   (steps-valley (s-transform-local-peak p))))



;; (defthm local-confluence-2
;;   (implies (and (s-equiv-p x y p)
;; 		(local-peak-p p))
;; 	   (s-equiv-p x y (s-transform-local-peak p))))



;;; local-confluence-1 is very easy:

(defthm local-confluence-1
  (implies (and (s-equiv-p x y p)
		(local-peak-p p))
	   (steps-valley (s-transform-local-peak p))))

;;; For local-confluence-2, we need to deal with any of the auxiliary
;;; functions


;;; s-transform-o-r-local-peak



(defthm s-transform-o-r-local-peak-s-equiv-p
  (implies (and (natp i)
		(< i (1- (len l)))
		(>= (nth i l) (nth (1+ i) l))
		(natp j)
		(< j (1- (len m)))
		(equal (nth j m) (nth (1+ j) m)))
	   (s-equiv-p (cons (interchange1+ i l) m)
		      (cons (cons j l) (del-nth j m))
		      (s-transform-o-r-local-peak
		       i j
		       (interchange1+ i l) m
		       (cons j l)
		       (del-nth j m)))))


;;; s-transform-disjoint-r-o

(defthm s-transform-r-o-local-peak-s-equiv-p
  (implies (and (natp i)
		(< i (1- (len m)))
		(equal (nth i m) (nth (1+ i) m))
		(natp j)
		(< j (1- (len l)))
		(>= (nth j l) (nth (1+ j) l)))
	   (s-equiv-p (cons (cons i l) (del-nth i m))
		      (cons (interchange1+ j l) m)
		      (s-transform-r-o-local-peak
		       i j
		       (cons i l) (del-nth i m)
		       (interchange1+ j l) m))))



;;; s-transform-disjoint-o-o

(defthm len-interchange1+
  (implies (and (natp i)
		(< i (1- (len l))))
	   (equal (len (interchange1+ i l)) (len l))))

(defthm nth-interchange1+-case-1
  (implies (and (natp i)
		(< i (1- (len l)))
		(natp j)
		(< j (len l))
		(< i j))
	   (equal (nth i (interchange1+ j l))
		  (nth i l))))

(defthm nth-bigger-than-1-cons
  (implies (posp j)
	   (equal (nth j (cons x l)) (nth (1- j) l))))


(defthm nth-interchange1+-case-2
  (implies (and (natp i)
		(< i (1- (len l)))
		(natp j)
		(< j (len l))
		(< (+ i 1) j))
	   (equal (nth j (interchange1+ i l))
		  (nth j l))))

(defthm nth-interchange1+-case-3
  (implies (and (natp i)
		(< i (1- (len l)))
		(natp j)
		(< j (1- (len l)))
		(< (+ i 1) j))
	   (equal (nth (1+ j) (interchange1+ i l))
		  (nth (1+ j) l))))


(defthm nth-interchange1+-case-4
  (implies (and (natp i)
		(< i (1- (len l)))
		(natp j)
		(< j (len l))
		(< (+ i 1) j))
	   (equal (nth (1+ i) (interchange1+ j l))
		  (nth (1+ i) l))))


(defthm car-interchange
  (implies (posp i)
	   (equal (car (interchange1+ i l)) (car l))))

(defthm interchange1+-disjoint
  (implies (and (natp i)
		(< i (1- (len l)))
		(natp j)
		(< j (1- (len l)))
		(< (+ i 1) j))
	   (and (equal (interchange1+ i (interchange1+ j l))
		       (interchange1+ j (interchange1+ i l)))
		(equal (interchange1+ j (interchange1+ i l))
		       (interchange1+ i (interchange1+ j l))))))


(defthm s-transform-disjoint-o-o-local-peak-s-equiv-p
  (implies (and (natp i)
		(< i (1- (len l)))
		(>= (nth i l) (nth (1+ i) l))
		(natp j)
		(< j (1- (len l)))
		(>= (nth j l) (nth (1+ j) l))
		(or (< (+ i 1) j) (< (+ j 1) i)))
	   (s-equiv-p (cons (interchange1+ i l) m)
		      (cons (interchange1+ j l) m)
		      (s-transform-disjoint-o-o-local-peak
		       i j
		       (interchange1+ i l) m
		       (interchange1+ j l) m))))


;;; s-transform-contiguous-o-o-local-peak

(defthm nth-i-interchange1+-i
  (implies (and (natp i) (< i (1- (len l))))
	   (equal (nth i (interchange1+ i l))
		  (nth (1+ i) l))))


(defthm nth-1+i-interchange1+-i
  (implies (and (natp i) (< i (1- (len l))))
	   (equal (nth (1+ i) (interchange1+ i l))
		  (1+ (nth i l)))))

(defthm nth-2+i-interchange1+-i
  (implies (and (natp i)
		(< (1+ i) (1- (len l))))
	   (equal (nth (+ 2 i) (interchange1+ (+ 1 i) l))
		  (1+ (nth (1+ i) l))))
  :hints (("Goal" :use (:instance nth-1+i-interchange1+-i (i (1+ i))))))



(defthm interchange1+-contiguous-composition
  (implies
     (and (natp i)
          (< (+ 1 i) (+ -1 (len l))))
     (equal (interchange1+ i
                           (interchange1+ (+ 1 i)
                                          (interchange1+ i l)))
            (interchange1+ (+ 1 i)
                           (interchange1+ i (interchange1+ (+ 1 i) l))))))

(encapsulate
 ()

 (local
  (defthm s-transform-contiguous-o-o-local-peak-s-equiv-p-case-1
    (implies (and (natp i)
		  (< (1+ i) (1- (len l)))
		  (>= (nth i l) (nth (1+ i) l))
		  (>= (nth (1+ i) l) (nth (+ 2 i) l)))
	     (s-equiv-p (cons (interchange1+ i l) m)
			(cons (interchange1+ (1+ i) l) m)
			(s-transform-contiguous-o-o-local-peak
			 i (1+ i)
			 (interchange1+ i l) m
			 (interchange1+ (1+ i) l) m)))
    :hints (("Goal" :in-theory (disable nth interchange1+)))))

 (local
  (defthm s-transform-contiguous-o-o-local-peak-s-equiv-p-case-2
    (implies (and (natp j)
		  (< (1+ j) (1- (len l)))
		  (>= (nth (1+ j) l) (nth (+ 2 j) l))
		  (>= (nth j l) (nth (1+ j) l)))
	     (s-equiv-p (cons (interchange1+ (1+ j) l) m)
			(cons (interchange1+ j l) m)
			(s-transform-contiguous-o-o-local-peak
			 (1+ j) j
			 (interchange1+ (1+ j) l) m
			 (interchange1+ j l) m)))
    :hints (("Goal" :in-theory (disable nth interchange1+)))))



 (defthm s-transform-contiguous-o-o-local-peak-s-equiv-p
   (implies (and (natp i)
		 (< i (1- (len l)))
		 (>= (nth i l) (nth (1+ i) l))
		 (natp j)
		 (< j (1- (len l)))
		 (>= (nth j l) (nth (1+ j) l))
		 (not (= i j))
		 (>= (+ i 1) j)
		 (>= (+ j 1) i))
	    (s-equiv-p (cons (interchange1+ i l) m)
		       (cons (interchange1+ j l) m)
		       (s-transform-contiguous-o-o-local-peak
			i j
			(interchange1+ i l) m
			(interchange1+ j l) m)))
   :hints (("Goal" :cases ((= j (1+ i)) (= i (1+ j)))))))



;;; s-transform-r-r-i-<-j-local-peak

(defthm len-del-nth
  (implies (and (< i (len l))
		(natp i))
	   (equal (len (del-nth i l)) (1- (len l)))))

(defthm s-transform-r-r-i-<-j-local-peak-s-equiv-p
  (implies (and (natp i)
		(< i (1- (len m)))
		(equal (nth i m) (nth (1+ i) m))
		(natp j)
		(< j (1- (len m)))
		(equal (nth j m) (nth (1+ j) m))
		(< i j))
	   (s-equiv-p (cons (cons i l) (del-nth i m))
		      (cons (cons j l) (del-nth j m))
		      (s-transform-r-r-i-<-j-local-peak
		       i j
		       (cons i l) (del-nth i m)
		       (cons j l) (del-nth j m)))))


;;; s-transform-r-r-i-<-j-local-peak


(defthm s-transform-r-r-i->-j-local-peak-s-equiv-p
  (implies (and (natp i)
		(< i (1- (len m)))
		(equal (nth i m) (nth (1+ i) m))
		(natp j)
		(< j (1- (len m)))
		(equal (nth j m) (nth (1+ j) m))
		(< j i))
	   (s-equiv-p (cons (cons i l) (del-nth i m))
		      (cons (cons j l) (del-nth j m))
		      (s-transform-r-r-i->-j-local-peak
		       i j
		       (cons i l) (del-nth i m)
		       (cons j l) (del-nth j m)))))


;;; We disable and finally prove the intended result:

(in-theory (disable s-transform-disjoint-o-o-local-peak
		    s-transform-contiguous-o-o-local-peak
		    s-transform-o-r-local-peak
                    s-transform-r-o-local-peak
		    s-transform-r-r-i-<-j-local-peak
		    s-transform-r-r-i->-j-local-peak))

(defthm local-confluence-2
  (implies (and (s-equiv-p x y p)
		(local-peak-p p))
	   (s-equiv-p x y (s-transform-local-peak p))))




;;; Once proved, we disable s-transform-local-peak

(in-theory (disable s-transform-local-peak ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART VII: S-reduction is convergent
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We prove now that S-reduction is convergent. That is every
;;; S-equivalent elements have a common normal form.

;;; This result is not trivial (it needs a proof of Newman's lemma, see
;;; reference [5] in the paper). But we can obtain this result simply by
;;; functionally instantiating from a previous formalization of abstract
;;; reduction systems:

(defthm s-reduction-convergent

  (implies (s-equiv-p p1 p2 proof)
	   (equal (s-normal-form p1) (s-normal-form p2)))

  :hints (("Goal"
	   :use (:functional-instance
		 (:instance CNV::r-equivalent-complete
			    (CNV::x p1) (CNV::y p2) (CNV::p proof))
		 (CNV::q simplex)
		 (CNV::q-w (lambda () (cons nil nil)))
		 (CNV::equiv-p s-equiv-p)
		 (CNV::proof-step-p s-proof-step-p)
		 (CNV::r-equivalent
		  (lambda (p1 p2)
		    (equal (s-normal-form p1) (s-normal-form p2))))
		 (CNV::normal-form s-normal-form)
		 (CNV::reducible s-reducible)
		 (CNV::reduce-one-step s-reduce-one-step)
		 (CNV::legal s-legal)
		 (CNV::rel s-rel)
		 (CNV::fn s-ordinal-embedding)
		 (CNV::transform-local-peak s-transform-local-peak)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART VIII: Face an degeneracy operators in Simplicial Topology
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We prove the relation between S-reduction and degeneracy. See the
;;; paper for an explanation of this concept and its role in Simplicial
;;; Topology

;;; Degenerate

(defun deg (i l)
  (if (zp i)
      (cons (car l) l)
    (cons (car l) (deg (1- i) (cdr l)))))

(defun degenerate (l1 l2)
  (if (endp l1)
      l2
    (degenerate (cdr l1) (deg (car l1) l2))))

(defun degeneration-true-listp (l n)
  (if (endp l)
      (equal l nil)
    (and
     (natp (car l))
     (< (car l) n)
     (degeneration-true-listp (cdr l) (1+ n)))))


;;; The following lemmas are needed for proving that degeneration is
;;; preserved under S-reductions. That is, if $(l_1, l_2) \rightarrow_S
;;; (l_3, l_4$) is a reduction in $S$, then $degenerate(l_1,l_2)
;;; =degenerate (l_3, l_4)$.


(defthm deg-composition-main-lemma
  (implies (and
	    (natp i)
	    (< i (len m))
	    (natp j)
	    (< j (len (deg i m)))
	    (<= j i))
	   (equal (deg (1+ i) (deg j m))
		  (deg j (deg i m)))))


(defthm len-deg
  (implies (and (natp i)
		(< i (len l)))
	   (equal (len (deg i l)) (1+ (len l)))))


(defthm degenerate-interchange-base-case-lemma
  (implies (and (consp l)
		(consp (cdr l))
		(degeneration-true-listp l (len m))
		(<= (second l) (first l)))
	   (equal (degenerate (interchange1+ 0 l) m)
		  (degenerate l m)))
  :hints (("Goal" :in-theory (disable deg)))
  :rule-classes nil)


(defthm degenerate-interchange
  (implies (and
	    (degeneration-true-listp l (len m))
	    (natp i)
	    (< i (1- (len l)))
	    (>= (nth i l) (nth (1+ i) l)))
	   (equal (degenerate (interchange1+ i l) m)
		  (degenerate l m)))
  :hints (("Subgoal *1/2" :use degenerate-interchange-base-case-lemma)))



(defthm deg-del-nth
  (implies (and (natp i)
		(< i (1- (len l)))
		(equal (nth i l) (nth (1+ i) l)))
	   (equal (deg i (del-nth i l)) l)))


;;; The intended theroem:

(defthm degenerate-preserved-under-S-reductions
  (implies (and (degeneration-true-listp (car p) (len (cdr p)))
		(s-legal p op))
	   (let ((p1 (s-reduce-one-step p op)))
	     (equal (degenerate (car p1) (cdr p1))
		    (degenerate (car p) (cdr p))))))


;;; Now we prove other important property: If
;;; $degenerate(l_1,l_2)=l$, then $(nil,l) =_S (l_1, l_2)$


(defun degenerate-steps (l1 l2)
  (if (endp l1)
      nil
    (cons (make-r-step :direct nil
		       :operator (cons 'r (car l1))
		       :elt1 (cons l1 l2)
		       :elt2 (cons (cdr l1) (deg (car l1) l2)))
	  (degenerate-steps (cdr l1) (deg (car l1) l2)))))


(defthm nth-deg-repetition
  (implies (and (natp i)
		(< i (len l)))
	   (equal (nth (1+ i) (deg i l))
		  (nth i (deg i l)))))

(defthm del-nth-deg
  (implies (and (natp i)
		(< i (len l)))
	   (equal (del-nth i (deg i l)) l)))




;;; The intended result

(defthm degenerate-s-equivalent
  (implies (degeneration-true-listp l (len m))
	   (s-equiv-p (cons l m) (cons nil (degenerate l m))
		      (degenerate-steps l m))))

(defthm degenerate-s-equivalent-bis
  (implies (and (consp p) (degeneration-true-listp (car p) (len (cdr p))))
	   (s-equiv-p p (cons nil (degenerate (car p) (cdr p)))
		      (degenerate-steps (car p) (cdr p)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PART IX: Putting the pieces together and proving THEOREM 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; Strictly increasing:

(defun increasing (l)
  (if (or (endp l) (endp (cdr l)))
      t
    (and (< (first l) (second l))
	 (increasing (cdr l)))))

;;; Without repetitions:

(defun non-degenerated (l)
  (if (or (endp l) (endp (cdr l)))
      t
     (and (not (equal (first l) (second l)))
	  (non-degenerated (cdr l)))))

;;; Simplices in canonical form:

(defun canonical (p)
  (and
   (consp p)
   (degeneration-true-listp (car p) (len (cdr p)))
   (increasing (car p))
   (non-degenerated (cdr p))))


;;; Lemmas

(defthm not-find-disorder-iff-increasing
  (iff (find-disorder l) (not (increasing l))))

(defthm s-irreducible-implies-increasing
  (implies (not (s-reducible p))
	   (increasing (car p))))

(defthm not-find-disorder-implies-non-degenerated
  (iff (find-consecutive-repetition l)
       (not (non-degenerated l))))


(defthm s-irreducible-implies-non-degenerated
  (implies (not (s-reducible p))
	   (non-degenerated (cdr p))))



(defthm increasing-and-non-degenerated-implies-s-reducible
  (implies (and (increasing (car p))
		(non-degenerated (cdr p)))
	   (not (s-reducible p))))


(defthm degeneration-true-listp-interchange-1+
  (implies (and (natp i)
                (< i (1- (len l1)))
		(>= (nth i l1) (nth (1+ i) l1))
		(degeneration-true-listp l1 n))
         (degeneration-true-listp (interchange1+ i l1) n)))

(defthm degeneration-true-listp-preserved-by-reduction
  (implies (and (degeneration-true-listp (car p) (len (cdr p)))
		(s-legal p  op))
	   (let ((pr (s-reduce-one-step p op)))
	     (degeneration-true-listp (car pr) (len (cdr pr))))))



;;; It is time to disable

(in-theory (disable s-legal s-reduce-one-step s-reducible))

;;; Properties of s-normal-form

(defthm degeneration-true-listp-s-normal-form
  (implies (degeneration-true-listp (car p) (len (cdr p)))
	   (let ((snf (s-normal-form p)))
	     (degeneration-true-listp (car snf) (len (cdr snf))))))



(defthm s-normal-form-increasing-and-non-degenerated
  (let ((snf (s-normal-form p)))
    (and (increasing (car snf))
	 (non-degenerated (cdr snf)))))

(defthm s-normal-form-degenerates
  (let* ((snf (s-normal-form p))
	 (snf1 (car snf))
	 (snf2 (cdr snf)))
    (implies (degeneration-true-listp (car p) (len (cdr p)))
	     (equal (degenerate snf1 snf2)
		    (degenerate (car p) (cdr p))))))


(defthm s-normal-form-of-increasing-and-non-degenerated
  (implies (and (increasing (car p))
		(non-degenerated (cdr p)))
	   (equal (s-normal-form p) p)))


;;; Uniqueness main lemma

(defthm uniqueness-main-lemma
  (let ((dl1 (car p1))
	(l1 (cdr p1))
	(dl2 (car p2))
	(l2 (cdr p2)))
  (implies
    (and (canonical p1) (canonical p2)
	 (equal (degenerate dl1 l1) l)
	 (equal (degenerate dl2 l2) l))
    (s-equiv-p p1 p2
	       (append (degenerate-steps dl1 l1)
		       (inverse-proof (degenerate-steps dl2 l2))))))
  :hints (("Goal" :use
	   ((:instance s-equiv-p-transitive
		       (x p1) (z p2) (y (cons nil l))
		       (p1 (degenerate-steps (car p1) (cdr p1)))
		       (p2 (inverse-proof (degenerate-steps (car p2)
							    (cdr p2)))))))))


;;;;;;;;;;;;;;;;;; FINAL THEOREMS ;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Finally, (s-normal-form (cons nil l)) is a witness


(defun generate (l)
  (s-normal-form (cons nil l)))

(defthm existence

   (let ((gen (generate l)))
     (and (canonical gen)
          (equal (degenerate (car gen) (cdr gen)) l))))




(defthm uniqueness

  (implies
    (and (canonical p1) (canonical p2)
	 (equal (degenerate (car p1) (cdr p1)) l)
	 (equal (degenerate (car p2) (cdr p2)) l))
   (equal p1 p2))

  :rule-classes nil
  :hints (("Goal" :use
	    ((:instance
	     s-reduction-convergent
	     (proof (append (degenerate-steps (car p1) (cdr p1))
			    (inverse-proof (degenerate-steps (car p2)
							     (cdr p2))))))))))


