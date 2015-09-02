;;; multiset.lisp
;;; - Useful lemmas about multisets
;;; - Multiset extension of a well-founded relation is a well-founded relation.
;;; Created: 10-6-99 Last Revision: 19-09-00
;;; ============================================================================

#| To certify this book:

(in-package "ACL2")

(defpkg "MUL" (union-eq *acl2-exports*
			(union-eq
			 *common-lisp-symbols-from-main-lisp-package*
			 '(remove-one multiset-diff ctoa atoc))))
;;; Con la nueva representación, añadimos ctoa y atoc al paquete MUL

(certify-book "multiset" 1)

|#

(in-package "MUL")
(include-book "ordinals/e0-ordinal" :dir :system)

(ACL2::set-verify-guards-eagerness 2)

;;; *****************************************************
;;; PART I: DEFINITIONS AND USEFUL LEMMAS ABOUT MULTISETS
;;; *****************************************************

;;; ============================================================================
;;; 1. Multisets (unordered lists).
;;; ============================================================================


;;; ----------------------------------------------------------------------------
;;; 1.1 equal-set and properties.
;;; ----------------------------------------------------------------------------

(defun equal-set (x y)
  (declare (xargs :guard
		  (if (acl2::eqlable-listp y)
		      (true-listp x)
		      (if (acl2::eqlable-listp x)
			  (true-listp y)
			  nil))))
  (and (subsetp x y) (subsetp y x)))

(local
 (defthm subsetp-cons
   (implies (subsetp l m)
	    (subsetp l (cons x m)))))

(local
 (defthm subsetp-reflexive
   (subsetp l l)))

(local
 (defthm subsetp-transitive
   (implies (and (subsetp l m)
		 (subsetp m n))
	    (subsetp l n))))

(acl2::defequiv equal-set)

(acl2::defcong equal-set equal (consp l) 1)

;;; ----------------------------------------------------------------------------
;;; 1.2 remove-one and properties.
;;; ----------------------------------------------------------------------------

(defun remove-one (x l)
  (cond ((atom l) l)
	((equal x (car l)) (cdr l))
	(t (cons (car l) (remove-one x (cdr l))))))

(defthm remove-one-true-listp
  (implies (true-listp l)
	   (true-listp (remove-one x l))))

(local
 (defthm member-remove-one
   (implies (and (member x l) (not (equal x y)))
	    (member x (remove-one y l)))))

(local
 (defthm remove-one-conmute
   (equal (remove-one x (remove-one y l))
	  (remove-one y (remove-one x l)))))

(local
 (defthm remove-one-member
   (implies (not (member x l))
	    (not (member x (remove-one y l))))))

(local
 (defthm remove-one-subsetp
   (subsetp (remove-one x l) l)))

;;; ----------------------------------------------------------------------------
;;; 1.3 Multiset difference and properties.
;;; ----------------------------------------------------------------------------

(defun multiset-diff (m n)
  (if (atom n)
      m
      (multiset-diff (remove-one (car n) m) (cdr n))))

(defthm multiset-diff-true-listp
  (implies (and (true-listp m)
		(true-listp n))
	   (true-listp (multiset-diff m n))))

(local
 (defthm multiset-diff-member
   (implies (and (member x n) (not (member x m)))
	    (member x (multiset-diff n m)))))

(local
 (defthm multiset-diff-removing-the-same-element
   (implies (and (member x n) (member x m))
	    (equal (multiset-diff (remove-one x m)
				  (remove-one x n))
		   (multiset-diff m n)))))

(local
 (defthm multiset-diff-nil
   (not (consp (multiset-diff nil l)))))

(local
 (defthm subsetp-multiset-diff
   (subsetp (multiset-diff n m) n)))

(defthm multiset-diff-remove-one-not-consp
  (not (consp (multiset-diff (remove-one x l) l)))
  :hints (("Goal" :induct (acl2::len l))))

(defthm list-multiset-diff-1
  (implies (not (member x l))
	   (equal (multiset-diff (list x) l)
		  (list x))))

(defthm list-multiset-diff-2
  (implies (not (member x l))
	   (equal (multiset-diff l (list x))
		  l)))

(defthm multiset-diff-append-1
  (equal (multiset-diff (append m1 m2)
			(append m1 m3))
	 (multiset-diff m2 m3)))

;;; REMARK: An analogue property is not true for (multiset-diff (append
;;; m1 m2) (append m3 m2)) (take for example '(3 2 1 3) and '(1
;;; 3)). Nevertheless, we prove below that (multiset-diff (append m1 m2)
;;; (append m3 m2)) is exactly the same set (although not the same list
;;; in general) as (multiset-diff m1 m3). This rewrite rule will be used
;;; together with two congruence rules relating forall-exists-rel-bigger
;;; and equal-se (see 2.3 in this file). Furthermore, using functional
;;; instantiation, these two congruence rules are generated for every
;;; particular relation "rel" by defmul (see defmul.lisp).



(encapsulate
 ()

 (local
  (defun my-occur (x l)
    (cond ((atom l) 0)
	  ((equal x (car l)) (1+ (my-occur x (cdr l))))
	  (t (my-occur x (cdr l))))))

 (local
  (defthm my-occur-append
    (equal (my-occur x (append l m))
	   (+ (my-occur x l) (my-occur x m)))))

 (local
  (defthm my-occur-remove-one
    (equal (my-occur x (remove-one y l))
	   (if (and (equal x y) (member x l))
	       (1- (my-occur x l))
	       (my-occur x l)))))

 (local
  (defthm subsetp-multiset-diff-member
    (implies (not (member x l))
	     (not (member x (multiset-diff l m))))))

 (local
  (defthm multiset-diff-my-occur
    (iff (member x (multiset-diff l m))
	 (> (my-occur x l) (my-occur x m)))))

 (local
  (defthm multiset-diff-append-2-lemma
    (iff (member x (multiset-diff (append m1 m2)
				  (append m3 m2)))
	 (member x (multiset-diff m1 m3)))))

 (local
  (defun not-subsetp-witness (m1 m2)
    (declare (xargs :verify-guards nil))
    (if (atom m1)
	nil
	(if (member (car m1) m2)
	    (not-subsetp-witness (cdr m1) m2)
	    (car m1)))))

 (local
  (defthm not-subsetp-witness-lemma
    (equal (subsetp m1 m2)
	   (implies (member (not-subsetp-witness m1 m2) m1)
		    (member (not-subsetp-witness m1 m2) m2)))))

 (defthm multiset-diff-append-2
   (equal-set (multiset-diff (append m1 m2)
			     (append m3 m2))
	      (multiset-diff m1 m3))))

;;; ----------------------------------------------------------------------------
;;; 1.4 A useful meta rule about "multiset-diff"
;;; ----------------------------------------------------------------------------

;;; This rule rewrites expressions of the form:

;;; (multiset-diff (list* x1 ... xm l)
;;; 	           (list* y1 ... yk l))

;;; to the equivalent (w.r.t. equal-set):

;;; (multiset-diff (list x1 ... xm)
;;;    	           (list y1 ... yk))



(defun initial-cars (l)
  (if (and (consp l)
	   (eq (car l) 'cons)
	   (consp (cdr l))
	   (consp (cddr l))
	   (eq (cdddr l) 'nil))
      (list 'cons (cadr l) (initial-cars (caddr l)))
      ''nil))

(defun last-cdr (l)
  (if (and (consp l)
	   (eq (car l) 'cons)
	   (consp (cdr l))
	   (consp (cddr l))
	   (eq (cdddr l) 'nil))
      (last-cdr (caddr l))
      l))

(defun exclude-last-cdr-multiset-diff (x)
  (if (and (consp x)
	   (eq (car x) 'multiset-diff)
	   (consp (cdr x))
	   (consp (cddr x))
	   (eq (cdddr x) 'nil))
      (list 'multiset-diff
	    (initial-cars (cadr x))
	    (initial-cars (caddr x)))
      x))

(acl2::defevaluator ev-multiset-diff ev-multiset-diff-list
		    ((cons x l)
		     (multiset-diff l1 l2)
		     (equal l1 l2)))

(local
 (defthm ev-multiset-diff-append-initial-cars-last-cdr
   (equal (append (ev-multiset-diff (initial-cars l) a)
		  (ev-multiset-diff (last-cdr l) a))
	  (ev-multiset-diff l a))))

(defun hypothesis-multiset-diff-meta (x)
  (if (and (consp x)
	   (consp (cdr x))
	   (consp (cddr x))
	   (eq (cdddr x) 'nil))
      (list 'equal
	    (last-cdr (cadr x))
	    (last-cdr (caddr x)))
      ''nil))

(defthm multiset-diff-meta
  (implies
   (ev-multiset-diff (hypothesis-multiset-diff-meta x) a)
   (equal-set (ev-multiset-diff x a)
	      (ev-multiset-diff (exclude-last-cdr-multiset-diff x) a)))
  :rule-classes ((:meta :trigger-fns (multiset-diff)))
  :hints (("Goal"
	   :use ((:instance
		  multiset-diff-append-2
		  (m1 (ev-multiset-diff (initial-cars (cadr x)) a))
		  (m2 (ev-multiset-diff (last-cdr (cadr x)) a))
		  (m3 (ev-multiset-diff (initial-cars (caddr x)) a))))
	   :in-theory (disable initial-cars))))




;;; **********************************************
;;; PART II: WELL-FOUNDEDNES OF MULTISET RELATIONS
;;; **********************************************


;;; ============================================================================
;;; 2. Multiset extension of a well-founded relation is a well-founded
;;;    relation.
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 2.1 A general well-founded relation
;;; ----------------------------------------------------------------------------

;;; Definition of a general well-founded relation on a set:
;;; - mp:  the measure property defining the set.
;;; - rel: the well-founded relation defined on elements satisfying mp.
;;; - fn:  the embedding justifying the well-foundedness of rel.


(encapsulate
 ((mp (x) booleanp)
  (rel (x y) booleanp)
  (fn (x) o-p))

 (local (defun mp (x) (declare (ignore x)) nil))
 (local (defun rel (x y) (declare (ignore x y)) nil))
 (local (defun fn (x) (declare (ignore x)) 1))

 (defthm rel-well-founded-relation-on-mp
   (and (implies (mp x) (o-p (fn x)))
	(implies (and (mp x)
		      (mp y)
		      (rel x y))
		 (o< (fn x) (fn y))))
   :rule-classes (:well-founded-relation :rewrite)))


;;; Conviene tenerlo separado, por que hace falta. PERO NO DENTRO DEL
;;; ENCAPSULADO. Como alternativa, yo la he puesto además como regla de
;;; reescritura. Preguntar a CK si esto afecta a defmul.


;;; REMARK: For our purpouses, we need another property about "fn", its
;;; values must be greater than 0.  Thus, we define a new measure
;;; function "fn1" equal to "fn" except for integers, where 1 is added.

;;; Nota: hace falta probar que la relación es b.f. "respecto" a
;;; e0-ordinalp, porque la prueba esta hecha para los ordinales
;;; antiguos. Así que ahora también introducimos "ctoa"

(defun add1-if-integer (x)
  (if (integerp x) (1+ x) x))

(defmacro fn1 (x)
  `(add1-if-integer (ctoa (fn ,x))))

;;; We prove now that fn1 is also an embedding, with the aditional
;;; property that never returns zero

(local
 (defthm e0-ord-<-add1-if-integer
   (implies (and (e0-ordinalp x) (e0-ordinalp y) )
	    (iff (e0-ord-< (add1-if-integer x) (add1-if-integer y))
		 (e0-ord-< x y)))))

(local
 (defthm add1-if-integer-e0-ordinalp-not-equal-0
   (implies (e0-ordinalp x)
	    (not (equal (add1-if-integer x) 0)))))

(local
 (defthm add1-if-integer-e0-ordinalp
   (implies (e0-ordinalp x)
	    (e0-ordinalp (add1-if-integer x)))))

(local (in-theory (disable add1-if-integer)))

(local
 (defthm fn-e0-ordinalp
   (implies (mp x)
	    (e0-ordinalp (ctoa (fn x))))
   :hints (("Goal" :use rel-well-founded-relation-on-mp))))

;;; Here they are:

(local
 (defthm fn1-e0-ordinalp
   (implies (mp x)
	    (and (e0-ordinalp (fn1 x))
		 (not (equal (fn1 x) 0))))))


(local
 (defthm rel-well-founded-relation-on-mp-rewrite
   (implies (and (mp x)
                 (mp y)
                 (rel x y))
	    (e0-ord-< (fn1 x) (fn1 y)))))


;;; ----------------------------------------------------------------------------
;;; 2.2 Induced multiset relation
;;; ----------------------------------------------------------------------------

;;; Now we define the multiset extension on multisets of elements with
;;; the MP-property.  We need to define:
;;; - The measure property defining multisets of elements:
;;;   mp-true-listp.
;;; - The well-founded relation: mul-rel.
;;; - The embedding justifying well-foundedness: mp-fn-o-p.

;;; Como originalmente hicimos la prueba con e0-ordinal, habiamos construido una
;;; inmersión en los ordinales, llamada map-fn-e0-ordinal y toda la
;;; prueba la habíamos hecho probando que era una inmersión en los
;;; e0 ordinales. Para aprovechar eso en la 2-8, definimos map-fn-o-p
;;; simplemente aplicando atoc en un último paso.

;;; Measure property

(defun mp-true-listp (l)
  (if (atom l)
      (equal l nil)
      (and (mp (car l)) (mp-true-listp (cdr l)))))

;;; Multiset relation

(defun exists-rel-bigger (x l)
  (cond ((atom l) nil)
	((rel x (car l)) t)
	(t (exists-rel-bigger x (cdr l)))))

(defun forall-exists-rel-bigger (l m)
  (if (atom l)
      t
      (and (exists-rel-bigger (car l) m)
	   (forall-exists-rel-bigger (cdr l) m))))

(defun mul-rel (n m)
  (let ((m-n (multiset-diff m n))
	(n-m (multiset-diff n m)))
    (and (consp m-n) (forall-exists-rel-bigger n-m m-n))))
;;; Embedding

(defun insert-e0-ord-< (x l)
  (cond ((atom l) (cons x l))
	((not (e0-ord-< x (car l)))  (cons x l))
	(t (cons (car l) (insert-e0-ord-< x (cdr l))))))

(defun map-fn-e0-ord (l)
  (declare (xargs :guard (mp-true-listp l)))
  (if (consp l)
      (insert-e0-ord-< (fn1 (car l))
		       (map-fn-e0-ord (cdr l)))
      0))

;;; Nuevo para la 2.8: má adelante tendremos que definir esto y
;;; demostrar que se trata de una inmersion en los nuevos ordinales de
;;; la versión 2.8:
;; (defun map-fn-o-p (x)
;;   (declare (xargs :guard (mp-true-listp x)))
;;   (atoc (map-fn-e0-ord x)))


;;; ----------------------------------------------------------------------------
;;; 2.3 An interesting congruence.
;;; ----------------------------------------------------------------------------

;;; These rules are used in conjuction with rewite rules that simplify
;;; multiset differences (w.r.t equal or equal-set)

;;; REMARK: These two congruence rules will be instantiated by every
;;; defmul macro to prove the analogues for every particular rel.


(encapsulate
 ()

 (local (defthm exists-rel-bigger-subsetp
	  (implies (and
		    (exists-rel-bigger x a)
		    (subsetp a b))
		   (exists-rel-bigger x b))))

 (acl2::defcong equal-set iff (forall-exists-rel-bigger l m) 2))


(encapsulate
 ()

 (local
  (defthm forall-exists-rel-bigger-subsetp
    (implies (and
	      (forall-exists-rel-bigger b l)
	      (subsetp a b))
	     (forall-exists-rel-bigger a l))))

 (acl2::defcong equal-set iff (forall-exists-rel-bigger l m) 1))


(in-theory
 (disable
  equal-set-implies-iff-forall-exists-rel-bigger-2
  equal-set-implies-iff-forall-exists-rel-bigger-1))


;;; ----------------------------------------------------------------------------
;;; 2.4 Some ad hoc lemmas about ordinals.
;;; ----------------------------------------------------------------------------


(local
 (defthm weak-e0-ord-<-trichotomy
   (implies (e0-ord-< o1 o2)
	    (not (e0-ord-< o2 o1)))))

(local (in-theory (disable weak-e0-ord-<-trichotomy)))

(local
 (defthm e0-ord-<-trichotomy
   (implies (and (e0-ordinalp o1)
		 (e0-ordinalp o2)
		 (not (equal o1 o2))
		 (not (e0-ord-< o1 o2)))
	    (e0-ord-< o2 o1))
   :rule-classes :type-prescription))

(defthm e0-ord-<-irreflexive
  (not (e0-ord-< x x)))

(local (in-theory (disable e0-ord-<-irreflexive)))

(local
 (defthm e0-ord-<-transitive-corollary
   (implies (and (e0-ordinalp o1)
		 (e0-ordinalp o3)
		 (e0-ord-< o3 o2)
		 (not (e0-ord-< o1 o2)))
	    (e0-ord-< o3 o1))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable e0-ord-<-trichotomy)))))


;;; ----------------------------------------------------------------------------
;;; 2.5 Well-foundedness of mul-rel
;;; ----------------------------------------------------------------------------


;;; Our goal is to prove that mul-rel is a well-founded relation ("with
;;; respecto to e0-ordinals") on elements
;;;   satisfying mp-true-listp. We have to prove:
;;; 1) If (mp-true-listp m), the (map-fn-e0-ord m) is an ordinal.
;;; 2) If l and m are mp-true-listp and (mul-rel n m), then
;;;    (e0-ord-< (map-fn-e0-ord n) (map-fn-e0-ord m))


;;; ············································································
;;; 2.5.1 The measure is an e0-ordinal.
;;; ············································································

(local
 (defthm e0-ordinalp-insert-e0-ord-<
   (implies (and (e0-ordinalp l)
		 (e0-ordinalp o)
		 (not (equal o 0)))
	    (e0-ordinalp (insert-e0-ord-< o l)))
   :hints (("Goal" :in-theory (enable weak-e0-ord-<-trichotomy)))))

(local
 (defthm e0-ordinalp-map-fn-e0-ord
   (implies (mp-true-listp m)
	    (e0-ordinalp (map-fn-e0-ord m)))))


;;; ············································································
;;; 2.5.2 The measure is an embedding
;;; ············································································



;;; SKETCH OF THE PROOF:
;;; Let N and M such that (mul-rel N M). We have to prove that
;;;      (e0-ord-< (map-fn-e0-ord N) (map-fn-e0-ord M))
;;;  Suppose (fn x) and (fn y) are the biggest
;;; (w.r.t. e0-ord-<) elements of fn[N] and fn[M], respectively. Since
;;; they are ordinals, three cases are possible:

;;; 1) (fn x) < (fn y). Done.

;;; 2) (fn x) > (fn y). This is not possible: in that case x is in N-M
;;; and by the multiset order definition, exists z in M-N such that (rel
;;; x z) and consequently (fn z) > (fn x) >= (fn y). This is a
;;; contradiction with the fact that (fn y) is the biggest element of
;;; fn[M].

;;; 3) (fn x) = (fn y). In that case, x is in M, since otherwise it
;;; would exist z in M-N such that (rel z x) and the same contradiction
;;; as in case 2) appears. So N-{x} and M-{x} are multisets and N-{x}
;;; bigger than M-{x} w.r.t. multiset relation with the property that
;;; the ordinal mesures of these two multisets are respectively the
;;; cdr's of the ordinal measures of N and M. Induction hypothesis can
;;; be applied here.
;;;
;;; We must define an induction scheme to mimic this proof sketch.
;;; This will be done later by induction-multiset
;;; But we previously prove some lemmas...



;;; max-fn1-list (an element in l with maximal (fn1 ..)) and properties.
;;; ······································································

(local
 (defun max-fn1-list (l)
   (declare (xargs :guard (mp-true-listp l)))
   (cond ((atom l) nil)
	 ((atom (cdr l)) (car l))
	 (t (let ((max-cdr (max-fn1-list (cdr l))))
	      (if (e0-ord-< (fn1 max-cdr) (fn1 (car l)))
		  (car l)
		  max-cdr))))))

(local
 (defthm max-fn1-list-member
   (implies (consp l)
	    (member (max-fn1-list l) l))))

(local
 (defthm mp-member-true-listp
   (implies (and (mp-true-listp l)
		 (member x l))
	    (mp x))
   :rule-classes :type-prescription))

(local
 (defthm max-fn1-listp-mp
   (implies (and (consp l) (mp-true-listp l))
	    (mp (max-fn1-list l)))))

(local
 (defthm max-fn1-list-maximal
   (implies (member x l)
	    (not (e0-ord-< (fn1 (max-fn1-list l)) (fn1 x))))
   :hints (("Goal" :in-theory (enable e0-ord-<-irreflexive)))))




;;; An "alternative definition" of "map-fn-e0-ord".
;;; ···············································

(local
 (encapsulate
  ()

  (local
   (defthm insert-e0-ord-<-conmute
     (implies (and (e0-ordinalp x) (e0-ordinalp y))
	      (equal (insert-e0-ord-< x (insert-e0-ord-< y l))
		     (insert-e0-ord-< y (insert-e0-ord-< x l))))
     :hints (("Goal" :in-theory (enable
				 weak-e0-ord-<-trichotomy
				 e0-ord-<-trichotomy
				 e0-ord-<-transitive-corollary)))))

  (local
   (defthm another-definition-of-map-fn-e0-ord-lemma
     (implies (and (mp-true-listp l) (member x l))
	      (equal (map-fn-e0-ord l)
		     (insert-e0-ord-< (fn1 x)
				      (map-fn-e0-ord (remove-one x l)))))
     :rule-classes nil))

  (local
   (defun bigger-than-list (x l)
     (declare (xargs :verify-guards nil))
     (cond ((atom l) t)
	   ((e0-ord-< x (car l)) nil)
	   (t (bigger-than-list x (cdr l))))))

  (local
   (defthm bigger-than-list-insert
     (implies (and (bigger-than-list x l)
		   (not (e0-ord-< x y)))
	      (bigger-than-list x (insert-e0-ord-< y l)))))

  (local
   (defthm bigger-than-list-max-fn1-map-fn-e0-ord-subsetp
     (implies (subsetp m l)
	      (bigger-than-list (fn1 (max-fn1-list l))
				(map-fn-e0-ord m)))
     :rule-classes nil))

  (local
   (defthm bigger-than-list-max-fn1-map-fn-e0-ord-remove-one
     (implies (equal (fn1 x) (fn1 (max-fn1-list l)))
	      (bigger-than-list (fn1 x) (map-fn-e0-ord (remove-one x l))))
     :hints (("Goal"
	      :use (:instance bigger-than-list-max-fn1-map-fn-e0-ord-subsetp
			      (m (remove-one x l)))))))

  (local
   (defthm bigger-than-list-insert-e0-ord-<-cons
     (implies (bigger-than-list (fn1 x) l)
	      (equal (insert-e0-ord-< (fn1 x) l)
		     (cons (fn1 x) l)))))

  (defthm another-definition-of-map-fn-e0-ord
    (implies (and (equal (fn1 x) (fn1 (max-fn1-list l)))
		  (mp-true-listp l)
		  (member x l))
	     (equal (map-fn-e0-ord l)
		    (cons (fn1 x) (map-fn-e0-ord (remove-one x l)))))
    :hints (("Goal" :use another-definition-of-map-fn-e0-ord-lemma))
    :rule-classes ((:definition :install-body nil :controller-alist ((map-fn-e0-ord t)))))))

;;; REMARK:
;;; It's very interesting the use of this definition rule and
;;; the free variables in it, essential for expanding in an adequate
;;; manner for the induction scheme in map-fn-e0-ord-measure. Note that
;;; this rule has "x" as a free variable. We put the first hypotesis
;;; (equal (fn1 x) (fn1 (max-fn1-list l))), and the rule will only be
;;; used (and "x" conveniently instantiated) if such condition is among
;;; the assumptions. Contrary to most of cases, this is pretty good for
;;; our purpouses. (see "Subgoal *1/6" (where it is used) and "Subgoal
;;; *1/4" (where it is not used) of
;;; map-fn-e0-ord-measure, in the expansion of (map-fn-e0-ord m))

;;; Once we used the following commented rule, but with that rule
;;; definition of map-fn-e0-ord is expanded. This is convenient for
;;; Subgoal *1/6 but not for Subgoal *1/4 where we need
;;;  (map-fn-e0-ord m) to be expanded to the expression :
;;;  (cons (max-fn-list l) (map-fn-e0-ord (remove-one (max-fn-list l) m)))
;;;  and not to the expression:
;;;  (cons (max-fn-list l) (map-fn-e0-ord (remove-one (max-fn-list m) m)))
;;;  Such expression would be obtained if the following rewrite rule
;;;  were used:
;;; (defthm another-definition-of-map-fn-e0-ord-rewrite-rule
;;;   (implies (and (mp-true-listp l) (consp l))
;;;     (equal (map-fn-e0-ord l)
;;; 	   (cons (fn1 (max-fn1-list l))
;;; 		 (map-fn-e0-ord
;;; 		  (remove-one (max-fn1-list l) l)))))
;;;   :hints (("Goal"
;;; 	   :use ((:instance
;;; 		  another-definition-of-map-fn-e0-ord
;;; 		  (x (max-fn1-list l)))))))

;;; Solution: The rule another-definition-of-map-fn-e0-ord-rewrite-rules
;;; (see below) rewrites car and cdr of map-fn-e0-ord and the criteria
;;; of expanding definitions, when applied to e0-ord-<, determines that
;;; those rules are applied in (map-fn-e0-ord l) and NOT in
;;; (map-fn-e0-ord m). In this case, the role of the free variables is
;;; essential.


(local
 (defthm another-definition-of-map-fn-e0-ord-rewrite-rules
   (implies (and (mp-true-listp l)
		 (consp l))
	    (and (equal (car (map-fn-e0-ord l)) (fn1 (max-fn1-list l)))
		 (equal (cdr (map-fn-e0-ord l))
			(map-fn-e0-ord (remove-one (max-fn1-list l) l)))))
   :hints (("Goal" :use (:instance
			 another-definition-of-map-fn-e0-ord
			 (x (max-fn1-list l)))))))

;;; Expansion of the definition of (map-fn-e0-ord l) and (map-fn-e0-ord
;;; m) is always tried. The above rules help the system to satisfy the
;;; criteria for function expansion in the cases where it is really
;;; needed.  (see "Subgoal *1/6" or "Subgoal *1/4" of
;;; map-fn-e0-ord-measure)



;;; Needed for forall-exists-rel-bigger-max-fn1-list
;;; ················································

;;; We prove forall-exists-rel-bigger-max-fn1-list-lemma, establishing
;;; that if (mul-rel n m), and x is in n and not in m, then (fn1 x) is
;;; strictly smaller than (fn1 (max-fn1-list m)). This property will be
;;; used to show forall-exists-rel-bigger-max-fn1-list, essential for
;;; handling cases *1/7 and *1/6 of our map-fn-e0-ord-measure. And also
;;; is used to show
;;; forall-exists-rel-bigger-max-fn1-list-lemma-corollary, for handling
;;; case *1/5

(local
 (defthm member-fn1-ordinal
   (implies (and (member x l) (mp-true-listp l))
	    (e0-ordinalp (fn1 x)))))

(local
 (defthm mp-true-listp-remove-one
   (implies (mp-true-listp l)
	    (mp-true-listp (remove-one x l)))))


(defthm mp-true-listp-multiset-diff
  (implies (mp-true-listp m)
	   (mp-true-listp (multiset-diff m n))))

(local
 (encapsulate
  ()

  (local
   (defun exists-rel-bigger-witness (x l)
     (declare (xargs :verify-guards nil))
     (cond ((atom l) nil)
	   ((rel x (car l)) (car l))
	   (t (exists-rel-bigger-witness x (cdr l))))))

  (local
   (defthm exists-rel-bigger-witness-main-property-lemma
     (implies (and (mp-true-listp l) (exists-rel-bigger x l))
	      (mp (exists-rel-bigger-witness x l)))))

  (local
   (defthm exists-rel-bigger-witness-main-property
     (implies (exists-rel-bigger x l)
	      (rel x (exists-rel-bigger-witness x l)))))

  (local
   (defthm forall-exists-rel-bigger-lemma
     (implies (and
	       (forall-exists-rel-bigger l1 l2)
	       (member x l1)
	       (mp-true-listp l1)
	       (mp-true-listp l2))
	      (e0-ord-< (fn1 x) (fn1 (exists-rel-bigger-witness x l2))))))

  (local
   (defthm member-multiset-diff-exists-rel-bigger-witness-lemma
     (implies (and
	       (forall-exists-rel-bigger l1 l2)
	       (member x l1)
	       (subsetp l2 l3))
	      (member (exists-rel-bigger-witness x l2) l3))))

  (local
   (defthm member-multiset-diff-exists-rel-bigger-witness
     (implies (and
	       (member x n)
	       (not (member x m))
	       (forall-exists-rel-bigger (multiset-diff n m)
					 (multiset-diff m n)))
	      (member (exists-rel-bigger-witness x (multiset-diff m n)) m))))

  (defthm forall-exists-rel-bigger-max-fn1-list-lemma
    (implies (and
	      (consp m)
	      (mp-true-listp n)
	      (mp-true-listp m)
	      (member x n)
	      (not (member x m))
	      (forall-exists-rel-bigger (multiset-diff n m)
					(multiset-diff m n)))
	     (e0-ord-< (fn1 x) (fn1 (max-fn1-list m))))
    :hints (("Goal" :use ((:instance
			   e0-ord-<-transitive-corollary
			   (o3 (fn1 x))
			   (o2 (fn1
				(exists-rel-bigger-witness
				 x
				 (multiset-diff m n))))
			   (o1 (fn1 (max-fn1-list m))))))))))




;;; Previous lemmas to map-fn-e0-ord-measure, handling every subgoal
;;; ································································

;;; Needed for "Subgoal *1/8":

(local
 (defthm max-fn1-e0-ordinalp
   (implies (and (consp l) (mp-true-listp l))
	    (e0-ordinalp (fn1 (max-fn1-list l))))))

(local
 (defthm max-fn1-e0-ord-trichotomy-<
   (implies (and
	     (mp-true-listp n) (mp-true-listp m) (consp n) (consp m)
	     (not (equal (fn1 (max-fn1-list n))
			 (fn1 (max-fn1-list m))))
	     (not (e0-ord-< (fn1 (max-fn1-list n))
			    (fn1 (max-fn1-list m)))))
	    (e0-ord-< (fn1 (max-fn1-list m))
		      (fn1 (max-fn1-list n))))
   :hints (("Goal"
	    :use (:instance e0-ord-<-trichotomy
			    (o1 (fn1 (max-fn1-list n)))
			    (o2 (fn1 (max-fn1-list m))))))))

;;; Needed for "Subgoal *1/7":
;;; - another-definition-of-map-fn-e0-ord-rewrite-rules
;;; - max-fn1-e0-ord-trichotomy-< and

(local
 (defthm forall-exists-rel-bigger-max-fn1-list
   (implies (and (consp n)
		 (consp m)
		 (mp-true-listp n)
		 (mp-true-listp m)
		 (forall-exists-rel-bigger (multiset-diff n m)
					   (multiset-diff m n)))
	    (not (e0-ord-< (fn1 (max-fn1-list m)) (fn1 (max-fn1-list n)))))
   :hints (("Goal"
	    :use (:instance forall-exists-rel-bigger-max-fn1-list-lemma
			    (x (max-fn1-list n)))
	    :in-theory (enable weak-e0-ord-<-trichotomy)))))


;;; Needed for "Subgoal *1/6":
;;; - another-definition-of-map-fn-e0-ord-rewrite-rules and

(local
 (defthm consp-map-fn1
   (implies (consp l) (consp (map-fn-e0-ord l)))
   :rule-classes :type-prescription))

;;; Needed for "Subgoal *1/5":

(local
 (defthm forall-exists-rel-bigger-max-fn1-list-lemma-corollary
   (implies (and (consp n)
		 (consp m)
		 (mp-true-listp n)
		 (mp-true-listp m)
		 (equal (fn1 (max-fn1-list n))
			(fn1 (max-fn1-list m)))
		 (forall-exists-rel-bigger (multiset-diff n m)
					   (multiset-diff m n)))
	    (member (max-fn1-list n) m))
   :hints (("Goal" :use ((:instance forall-exists-rel-bigger-max-fn1-list-lemma
				    (x (max-fn1-list n))))))))

;;; Needed for "Subgoal *1/4":
;;;   - another-definition-of-map-fn-e0-ord
;;;   - another-definition-of-map-fn-e0-ord-rewrite-rules
;;;   - max-fn1-list-member
;;;   - mp-true-listp-remove-one
;;;   - multiset-diff-removing-the-same-element and


;;; Needed for "Subgoal *1/3" and "Subgoal *1/2":
;;;   - multiset-diff-nil

;;; Subgoal *1/1 is solved simply expanding definitions


;;; At last: map-fn-e0-ord-measure.
;;; ·······························

(local
 (encapsulate
  ()

  ;;; Induction scheme.

  (local
   (defun induction-multiset (n m)
     (declare (xargs :measure (acl2::len n)
		     :verify-guards nil))
     (cond ((atom n) (if (atom m) 1 2))
	   ((atom m) 3)
	   (t (let* ((max-m (max-fn1-list m))
		     (max-n (max-fn1-list n))
		     (fn1-max-m (fn1 max-m))
		     (fn1-max-n (fn1 max-n)))
		(cond ((equal fn1-max-m fn1-max-n)
		       (if (member max-n m)
			   (induction-multiset
			    (remove-one max-n n)
			    (remove-one max-n m))
			   5))
		      ((e0-ord-< fn1-max-n fn1-max-m) 6)
		      ((e0-ord-< fn1-max-m fn1-max-n) 7)
		      (t 8)))))))

  (defthm map-fn-e0-ord-measure
    (implies (and (mp-true-listp n)
		  (mp-true-listp m)
		  (mul-rel n m))
	     (e0-ord-< (map-fn-e0-ord n)
		       (map-fn-e0-ord m)))
    :hints (("Goal" :induct (induction-multiset n m))))))


;;; ########################################################################
;;; THE MAIN THEOREM OF THIS BOOK:
;;; The multiset relation induced by a well-founded relation is well-founded
;;; ########################################################################

;;; The main theorem of this book:

(local
 (defthm multiset-extension-of-rel-well-founded-wrt-e0-ordinals
   (and (implies (mp-true-listp x) (e0-ordinalp (map-fn-e0-ord x)))
	(implies (and (mp-true-listp x)
		      (mp-true-listp y)
		      (mul-rel x y))
		 (e0-ord-< (map-fn-e0-ord x) (map-fn-e0-ord y))))
   :rule-classes nil))


;;; Pero con los nuevos ordinales no nos basta con esto, hay que demostrar
;;; una inmersión en los ordinales con la nueva representación. Esta
;;; inmersión la dá map-fn-o-p, definida simplemente
;;; como la aplicación de atoc a map-fn-e0-ord


(defun map-fn-o-p (x)
  (declare (xargs :guard (mp-true-listp x)))
  (atoc (map-fn-e0-ord x)))


(defthm multiset-extension-of-rel-well-founded
  (and (implies (mp-true-listp x) (o-p (map-fn-o-p x)))
       (implies (and (mp-true-listp x)
		     (mp-true-listp y)
		     (mul-rel x y))
		(o< (map-fn-o-p x) (map-fn-o-p y))))
  :hints (("Goal"
	   :use ((:instance  ACL2::e0-ordinal-well-founded-cnf
			    (ACL2::x (map-fn-e0-ord x))
			    (ACL2::y (map-fn-e0-ord y))))))
  :rule-classes :well-founded-relation)
