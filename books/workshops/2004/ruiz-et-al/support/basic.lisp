;;; basic.lisp
;;; Some stuff about lists, sets, etc.
;;; Created: 6-8-99 Last revison: 05-9-2002
;;; =============================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "basic")

|#


(in-package "ACL2")

;;; Replace the path if needed:

;;; Arithmetic:
(include-book "arithmetic/top-with-meta" :dir :system)





;;; **************************************
;;; BASIC PROPERTIES ABOUT LISTS, SETS,...
;;; **************************************

;;; REMARK: This is book is not intended to be a complete tratement of
;;; such data structures, but and "ad hoc" collection of definition and
;;; properties, needed for further development of the theory of first
;;; order terms.

;;; ============================================================================
;;; 1. Lists
;;; ============================================================================


;;; ======= APPEND

(defthm append-associative
  (equal (append (append x y) z)
	 (append x (append y z))))

(defthm member-append
  (iff (member x (append a b))
       (or (member x a) (member x b))))


(defthm append-nil
  (implies (true-listp l)
	   (equal (append l nil) l)))


;;; ======= REVLIST

(defun revlist (l)
  (declare (xargs :guard (true-listp l)))
  (if (endp l)
      nil
    (append (revlist (cdr l)) (list (car l)))))

(defthm revlist-true-listp
  (true-listp (revlist l)))

(local
 (defthm revappend-revlist
   (equal (revappend l m) (append (revlist l) m))))

(defthm reverse-revlist
  (implies (true-listp l)
	   (equal (reverse l) (revlist l))))

;;; ===== TRUE-LISTP

(defthm true-listp-append-rewrite
  (equal (true-listp (append a b))
	 (true-listp b)))

(defthm true-listp-rev
  (true-listp (revlist x)))


;;; ====== LAST


(defthm last-append
  (implies (consp m)
	   (equal (last (append l m)) (last m))))


;;; ====== REVERSE


(defthm car-last-rev
  (equal (car (last (revlist l))) (car l)))

(defthm rev-append
  (equal (revlist (append l m)) (append (revlist m) (revlist l))))

(defthm revlist-revlist
  (implies (true-listp l)
	   (equal (revlist (revlist l)) l)))


(defthm consp-revlist
  (iff (consp (revlist l))
       (consp l)))


(defthm member-revlist
  (iff (member x (revlist l))
       (member x l)))


;;; ====== DELETE-ONE

(defun delete-one (x l)
  (cond ((atom l) l)
	((equal x (car l)) (cdr l))
	(t (cons (car l) (delete-one x (cdr l))))))

(defthm delete-one-less-length
  (implies (member x m)
	   (< (len (delete-one x m)) (len m))))

(defthm member-delete-one
  (implies (and (member x m) (not (equal x y)))
	   (member x (delete-one y m))))

(defthm delete-one-conmute
  (equal (delete-one x (delete-one y l))
	 (delete-one y (delete-one x l))))

(defthm subsetp-delete-one
  (implies (not (member x l))
	   (not (member x (delete-one y l)))))

;;; ======= ELIMINATE (like remove, but different guard, using equal)

(defun eliminate (x l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l) nil)
	((equal x (car l)) (eliminate x (cdr l)))
	(t (cons (car l) (eliminate x (cdr l))))))


(defthm eliminate-len
  (implies (member x l)
	   (< (len (eliminate x l)) (len l)))
  :rule-classes :linear)

;;; ====== NATURAL-TRUE-LISTP
(defun positive-integer-true-listp (l)
  (declare (xargs :guard t))
  (if (atom l)
      (equal l nil)
    (and (integerp (car l)) (> (car l) 0)
	 (positive-integer-true-listp (cdr l)))))

;;; ====== REPLACE-LIST

(defun replace-list (l n x)
  (declare (xargs :guard
		  (and (true-listp l) (integerp n) (>= n 0))))
  (if (endp l)
      nil
    (if (zp n)
	(cons x (cdr l))
      (cons (car l) (replace-list (cdr l) (- n 1) x)))))


(defthm nth-replace-list-same-position
  (implies (and (integerp i)
		(<= 0 i)
		(< i (len l)))
	   (equal (nth i (replace-list l i x)) x)))


(defthm replace-list-same-length
  (equal (len (replace-list l i x)) (len l)))


(defthm nth-replace-list-different-position
  (implies (and (integerp i) (integerp k)
		(<= 0 i) (<= 0 k)
		(< i (len l)) (< k (len l))
		(not (equal i k)))
	   (equal (nth i (replace-list l k x)) (nth i l))))




(defthm replace-list-different-position
  (implies (and (integerp i) (integerp k)
		(<= 0 i) (<= 0 k)
		(< i (len l)) (< k (len l))
		(not (equal i k)))
	   (equal
	    (replace-list (replace-list l i x) k y)
	    (replace-list (replace-list l k y) i x))))



(defthm replace-list-same-position
  (implies (and (integerp i)
		(<= 0 i)
		(< i (len term)))
	   (equal
	    (replace-list (replace-list term i x) i y)
	    (replace-list term i y))))





;;; ====== PAIR-ARGS

(defun pair-args (l1 l2)
  (declare (xargs :guard (and (true-listp l1) (true-listp l2))))
  (cond ((endp l1) (if (equal l1 l2) (mv nil t) (mv nil nil)))
	((endp l2) (mv nil nil))
	(t (mv-let (pair-rest bool)
		   (pair-args (cdr l1) (cdr l2))
		   (if bool
		       (mv (cons (cons (car l1) (car l2))
				 pair-rest)
			   t)
		     (mv nil nil))))))

;;; **** Guard verification
(defthm pair-args-true-listp
  (true-listp (car (pair-args l1 l2))))


;;; ======= MV-NTH

;;; REMARK: I prefer to deal with first,second, third, etc... than with
;;; mv-nth.

(defthm mv-nth-0-first
  (equal (mv-nth 0 l) (first l)))

(defthm mv-nth-1-second
  (equal (mv-nth 1 l) (second l)))

(defthm mv-nth-2-third
  (equal (mv-nth 2 l) (third l)))

(defthm mv-nth-3-fourth
  (equal (mv-nth 3 l) (fourth l)))

(defthm mv-nth-4-fifth
  (equal (mv-nth 4 l) (fifth l)))

;;; and so on...


;;; ============================================================================
;;; 2. Sets
;;; ============================================================================

;;; ====== SETP
;;; A true-list without repeated elements.

(defun setp (l)
  (if (atom l)
      t
    (and (not (member (car l) (cdr l)))
	 (setp (cdr l)))))

(encapsulate
 ()
 (local (defthm member-eliminate
	  (implies (member y (eliminate x l))
		   (member y l))))

 (defthm eliminate-preserves-setp
  (implies (setp l)
	   (setp (eliminate x l)))))




;;; ====== SUBSETP

(defun not-subsetp-witness (l1 l2)
  (if (atom l1)
      nil
      (if (member (car l1) l2)
          (not-subsetp-witness (cdr l1) l2)
        (car l1))))

(defthm not-subsetp-witness-lemma
  (equal (subsetp l1 l2)
         (implies  (member (not-subsetp-witness l1 l2) l1)
                   (member (not-subsetp-witness l1 l2) l2))))


(in-theory (disable not-subsetp-witness-lemma))

(defthm subsetp-append-1
  (equal (subsetp (append x y) z)
         (and (subsetp x z) (subsetp y z))))

(defthm subsetp-append-2
  (implies (subsetp c a)
	   (subsetp c (append b a))))

(defthm subsetp-append-3
  (implies (subsetp b c)
	   (subsetp b (append c a))))


(defthm subsetp-cons
  (implies (subsetp l m)
	   (subsetp l (cons x m))))

(defthm subsetp-reflexive
  (subsetp l l))

(defthm delete-one-subsetp
  (subsetp (delete-one x l) l))

(defun subset-induction (l m)
  (if (or (atom l) (atom m) (not (member (car l) m)))
      t
    (subset-induction (cdr l) (eliminate (car l) m))))

(defthm
   substp-preserved-when-deleting-a-non-member
   (implies (and (subsetp z m) (not (member x z)))
	    (subsetp z (eliminate x m))))


;;; ====== DISJOINTP

;;; No common elements

(defun disjointp (l1 l2)
  (if (endp l1)
      t
    (and (not (member (car l1) l2))
	 (disjointp (cdr l1) l2))))


(defthm disjointp-cons
  (equal (disjointp l (cons x m))
	 (and (not (member x l))
	      (disjointp l m))))

(defthm disjointp-append-1
  (equal (disjointp (append l m) n)
	 (and (disjointp l n)
	      (disjointp m n))))

(defthm disjointp-append-2
  (equal (disjointp m (append l n))
	 (and (disjointp m l)
	      (disjointp m n))))

(defthm disjointp-conmutative
  (equal (disjointp l1 l2) (disjointp l2 l1)))

(defthm disjointp-nil
  (disjointp x nil))

;;; ====== NO-DUPLICATESP



(defthm no-duplicatesp-append
  (iff (no-duplicatesp (append l1 l2))
       (and (no-duplicatesp l1)
	    (no-duplicatesp l2)
	    (disjointp l1 l2))))


(defthm no-duplicatesp-revlist
  (iff (no-duplicatesp (revlist l))
       (no-duplicatesp l)))


;;; ======= MAKE-SET
;;; Eliminate duplicates.

(defun make-set (l)
  (if (atom l)
      nil
    (if (member (car l) (cdr l))
	(make-set (cdr l))
      (cons (car l) (make-set (cdr l))))))

(defthm member-make-set
  (iff (member x (make-set l)) (member x l)))

(defthm setp-make-set
  (setp (make-set x)))

(defthm make-set-of-a-setp-is-the-same
  (implies (setp l)
	   (equal (make-set l) (fix-true-list l))))

(defthm len-fix-true-list
  (equal (len (fix-true-list l)) (len l)))

(defthm make-set-lessp-length-if-not-setp
  (implies (not (setp l))
	   (< (len (make-set l))
	      (len l)))
  :rule-classes :linear)


(defthm length-make-set-leq
  (>= (len l)
      (len (make-set l)))
  :rule-classes :linear)

(defthm make-set-fix-true-list
  (equal (fix-true-list (make-set l)) (make-set l)))


;;; ============ EQUAL-SET: CONGRUENCE AND REWRITE RULES

(defun equal-set (x y)
  (and (subsetp x y) (subsetp y x)))


(defthm subsetp-transitive
  (implies (and (subsetp l m)
		(subsetp m n))
	   (subsetp l n)))


(defequiv equal-set)


(defcong equal-set iff (subsetp x y) 1)
(defcong equal-set iff (subsetp x y) 2)
(defcong equal-set equal (consp l) 1)

(encapsulate
 ()
 (local
  (defthm subsetp-disjoint-1
    (implies (and (subsetp x x-equiv)
		  (disjointp x-equiv y))
	     (disjointp x y))))

 (defcong equal-set iff (disjointp x y) 1))

(encapsulate
 ()
 (local
  (defthm subsetp-disjoint-2
    (implies (and (subsetp y y-equiv)
		  (disjointp x y-equiv))
	     (disjointp x y))))

 (defcong equal-set iff (disjointp x y) 2))


(encapsulate
 ()
 (local (defthm equal-set-member-cong-lemma-1
	  (implies (and (not (member x y))
			(subsetp y-equiv y))
		   (not (member x y-equiv)))))

 (local (defthm equal-set-member-cong-lemma-2
	  (implies (and (member x y)
			(subsetp y y-equiv))
		   (member x y-equiv))))
 (defcong equal-set iff (member x y) 2))


(defthm equal-set-make-set
  (equal-set (make-set l) l))

;;; REMARK: The following rule is needed in
;;; equal-size-and-not-inverse-subsumption-implies-not-renaming-almost
;;; I don't know why the previous rule is not used (monitoring is not
;;; possible, because it is a "simple"(?) rule). So I think I need the
;;; following rule, which is redundant (?)


(defthm subsetp-make-set-provisional
  (iff (subsetp a (make-set b)) (subsetp a b)))




;;; ====== PERM: CONGRUENCE AND REWRITE RULES


(defun perm (lst1 lst2)
  (cond ((atom lst1) (atom lst2))
        ((member (car lst1) lst2)
         (perm (cdr lst1) (delete-one (car lst1) lst2)))
        (t nil)))


(encapsulate
 ()

 (defthm perm-reflexive
  (perm x x))

 (local
  (defthm perm-main-lemma
    (implies (and (member x a)
		  (member x b)
		  (perm (delete-one x a) (delete-one x b)))
	     (perm a b))))

 (local
  (defthm perm-symmetric
    (implies (perm x y) (perm y x))))


 (local
  (defthm perm-transitive-reverse
    (implies (and (perm a b)
		  (perm a c))
	     (perm b c))
    :rule-classes nil))

 (local
  (defthm perm-transitive
    (implies (and (perm a b)
		  (perm b c))
	     (perm a c))
  :hints (("Goal" :use
	   ((:instance perm-symmetric
		       (x a) (y b))
	    (:instance perm-transitive-reverse
		       (a b) (b a)))))))
 (defequiv perm))



(local (defthm perm-implies-subsetp
	 (implies (perm x y) (subsetp x y))
	 :hints (("Goal" :induct (perm x y)))))


(defrefinement perm equal-set)

;;; Rewriting rules

(defthm perm-fix-true-list
  (perm (fix-true-list l) l))


;;; ============================================================================
;;; 3. Sequences
;;; ============================================================================

;;; Sequences of natural numbers will be used to represent positions of
;;; terms.

;;; ===== PREFIX

(defun prefix (p1 p2)
  (cond ((endp p1) t)
	((endp p2) nil)
	((equal (car p1) (car p2))
	 (prefix (cdr p1) (cdr p2)))
	(t nil)))

;;; ===== DIFFERENCE-POS

(defun difference-pos (p q)
  (if (atom p)
      q
    (difference-pos (cdr p) (cdr q))))


(defthm difference-the-same
  (implies (true-listp l)
	   (equal (difference-pos l l) nil)))

(defthm difference-pos-common-prefix
  (equal (difference-pos l (append l m))
	 m))

(defthm difference-pos-common-prefix-append
  (equal (difference-pos (append l m) (append l n))
	 (difference-pos m n)))


;;; ===== DISJOINT-POSITIONS

(defun disjoint-positions (p1 p2)
  (cond
   ((or (endp p1) (endp p2)) nil)
   ((equal (car p1) (car p2))
    (disjoint-positions (cdr p1) (cdr p2)))
   (t t)))



;;; ============================================================================
;;; 4. Association lists
;;; ============================================================================


;;; REMARK: Association lists represent finite domain functions in the
;;; following way:
;;; - Every atom object represents the identity function.
;;; - If an atom object is member of an association list will be
;;; considered as (nil . nil).
;;; - If several pairs (x . t1), (x . t2),... are member of an
;;; association list only the first one is considered.
;;; As a consecuence of this representation, different objects represent
;;; the same finite domain function. Thus, we cannot use equal as a
;;; predicate to talk about equality of finite domain functions.

;;; REMARK: We do not use the book alist-theory.list
;;; provided by the distribution because we need our own version of
;;; assoc (see the function val). We want the association list to behave
;;; like identity outside its domain.

;;; ======= VAL
;;; (i.e., sigma(x))

(defun val (x sigma)
  (declare (xargs :guard (if (eqlablep x)
			     (alistp sigma)
			     (eqlable-alistp sigma))))
  (if (endp sigma)
      x
    (if (eql x (caar sigma)) (cdar sigma) (val x (cdr sigma)))))


#||
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]

;;; REMARK: For execution, I will use assoc when the variable is in the
;;; domain. Sometimes, I have to use assoc-equal (see renamings.lisp).
;;; The following rule rewrites assoc-equal to assoc. In this way, we
;;; can build one set of rules about assoc.  WARNING: this is different
;;; rewriting strategy than the one given in the book alist-defthms.lisp
;;; in the ACL2 distribution.

(defthm assoc-equal-assoc-equal
  (equal (assoc-equal x a) (assoc x a)))
||#


;;; This relation between val and assoc is expressed
;;; here. For reasonig, I prefer to use val (that's the explanation for
;;; the orientation of the following rule):
(defthm assoc-val
	 (implies (assoc x l)
		  (equal (cdr (assoc x l)) (val x l))))

;;; ====== RESTRICTION
;;; The list of pairs (x. sigma(x)), for all x in l.

(defun restriction (sigma l)
  (if (atom l)
      l
    (cons (cons (car l) (val (car l) sigma))
	  (restriction sigma (cdr l)))))

;;; ====== DOMAIN
;;; domain of association lists (the list of first components of sigma).
;;; Note: as we said above, the atom elements of sigma are considered
;;; as (nil . nil). This remark also applies to the following definitions.

(defun domain (sigma)
  (declare (xargs :guard (alistp sigma)))
  (if (endp sigma)
      nil
    (cons (caar sigma) (domain (cdr sigma)))))


(defthm domain-restriction
  (equal (domain (restriction sigma l)) (fix-true-list l)))


(defthm domain-append
  (equal (domain (append l1 l2))
	 (append (domain l1) (domain l2))))

(defthm consp-domain
   (equal (consp (domain sigma))
	  (consp sigma)))


(defthm assoc-member-domain
  (implies (alistp sigma)
	   (iff (member x (domain sigma))
		(assoc x sigma))))


;;; ====== CO-DOMAIN
;;; co-domain of association lists (the list of first components of sigma).

(defun co-domain (sigma)
  (if (atom sigma)
      nil
    (cons (cdar sigma) (co-domain (cdr sigma)))))



;;; ====== INVERSE
;;; The association list obtained reversing the pairs.

(defun inverse (sigma)
  (if (atom sigma)
      nil
    (cons (cons (cdar sigma) (caar sigma))
	  (inverse (cdr sigma)))))


(defthm domain-of-inverse-is-co-domain
  (equal (domain (inverse sigma)) (co-domain sigma)))

(defthm co-domain-of-inverse-is-domain
  (equal (co-domain (inverse sigma)) (domain sigma)))

(defthm same-length-co-domain-and-domain
  (equal (len (domain sigma))
	 (len (co-domain sigma))))

(in-theory (disable same-length-co-domain-and-domain))



;;; ====== ALISTP (for guard verification)

(defthm assoc-consp-or-nil
  (implies (alistp a)
	   (or (consp (assoc x a))
	       (equal (assoc x a) nil)))
  :rule-classes :type-prescription)


(defun alistp-acl2-numberp (l)
  (declare (xargs :guard t))
  (if (atom l)
      (equal l nil)
    (and (consp (car l)) (acl2-numberp (cdar l))
	 (alistp-acl2-numberp (cdr l)))))


;;;============================================================================
;;;
;;; 5. Misecelanea
;;;
;;;============================================================================

;; Ya incluido en la versión 2-8
;; (defun natp (n)
;;   (declare (xargs :guard t))
;;   (and (integerp n)
;;        (<= 0 n)))

;;; The following function define true lists of indices bounded by a
;;; given natural number:

(defun bounded-nat-true-listp (l n)
  (declare (xargs :guard (natp n)))
  (if (atom l)
      (equal l nil)
    (and (natp (car l))
	 (< (car l) n)
	 (bounded-nat-true-listp (cdr l) n))))

;;; And a function for true lists of natural numbers:

(defun nat-true-listp (l)
  (declare (xargs :guard t))
  (if (atom l)
      (equal l nil)
    (and (natp (car l))
	 (nat-true-listp (cdr l)))))

;;; Both concepts are related:

(defthm bounded-nat-true-listp-nat-true-listp
  (implies (bounded-nat-true-listp l n)
	   (nat-true-listp l)))

;;;============================================================================




