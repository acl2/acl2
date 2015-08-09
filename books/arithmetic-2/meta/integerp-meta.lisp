; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; integerp-meta.lisp
;;;
;;;
;;; This book contains a meta rule which attempts to determine
;;; whether a sum or product is or is not an integer.
;;;
;;; Organization of file:
;;; 0. Introduction to meta functions.
;;; 1. Setup.
;;; 2. Overview.
;;; 3. Functions called by the meta function.
;;; 4. The meta function.
;;; 5. An encapsulate containing the meta theorem.
;;; 6. Cleanup.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 0. Introduction to meta functions.

#|
A meta function is a user-written, custom simplifier.  Like a Common
Lisp macro, it takes an s-expression and returns another one which
replaces the original.  In particular, a meta function takes
an ACL2 term and returns another, equivalent, ACL2 term.  If
the returned value is different than the input one, the input term is
replaced with the output one.

Here is a schematic example of a meta function and its associated meta
rule:

(defun meta-fn (acl2-term)
  <If acl2-term is an equality between two sums with
    an addend in common, return a new term with this
    common addend removed.  Otherwise return acl2-term
    unchanged.>)

Example:
(meta-fn '(equal (+ a b c)
                 (+ b d e)))
==>
'(equal (+ a c)
  (+ d e))

(defthm meta-fn-correct
  (equal (eval-under-alist acl2-term alist)
         (eval-under-alist (meta-fn acl2-term) alist))
  :rule-classes ((:meta :trigger-fns ((EQUAL)))))

Note that, unlike a macro, a regular meta function has no
introspective abilities --- it can only ``see'' the acl2 term and
so must act on a purely syntactic level.  For some examples of
regular meta functions see the book ../arithmetic/meta.  Also, see
the user documentation.

In these books we use the newly developed extended meta functions.
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 1. Setup.

(in-package "ACL2")

(local (include-book "../pass1/top"))

(table acl2-defaults-table :state-ok t)
#|
(defun fn-symb (x)

; Returns the function-symbol of x. or nil if x is a variable or constant.
; A handy function to have around when defining meta-functions.

  (cond ((variablep x)
         nil)
        ((fquotep x)
         nil)
        (t
         (car x))))
|#
(defun ts-fix (x)

; We "fix" x to be a valid type-set.  This function is needed because mfc-ts
; is not axiomatized to return a valid type-set. This seems, to me, to be a
; bug in our specification and it may change with the next release.

  (let ((int-x (ifix x)))
    (if (and (<= *min-type-set* int-x)
	     (<= int-x *max-type-set*))
	int-x
    0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 2. Overview.

; We wish to determine whether a sum or product is or is not an integer.
; What is the difficulty?  Consider (+ a b c).  If ACL2 knows that
; each of a, b, and c are integers, type reasoning is sufficient to
; determine that the sum, (+ a b c) is also an integer.  Similarly,
; if a and (+ b c) are both know to be an integer, type reasoning
; can determine that (+ a b c) is an integer.
;
; But what about the following: c is known to be an integer, as is
; (+ a b).  Recall that (+ a b c) is "actually"
; (BINARY-+ a (BINARY-+ b c)).  Type reasoning will not help us much here.
; It will try to determine the types of a and (BINARY-+ b c), which
; are not known to be integers;  but does not any other combinations.
;
; The meta rule that we define here does try other combinations.

; We start by defining two "dummy" functions.  We use these functions
; to control subsequent rewriting.  This is discussed further below.

(defun intp-+ (x y)
  (+ x y))

(defun intp-* (x y)
  (* x y))

(defevaluator intp-eva intp-eva-lst ((intp-+ x y)
				     (intp-* x y)
				     (binary-+ x y)
				     (binary-* x y)
                                     (integerp x)
				     (if x y z)
				     (equal x y)
				     (fix x)))

; Our meta rule will, hopefully, massage the terms into a form such that
; these rules can do their work.

(defthm intp-1
  (implies (and (integerp x)
		(integerp y))
	   (integerp (intp-* x y))))

(defthm intp-2
  (implies (and (integerp x)
		(integerp y))
	   (integerp (intp-+ x y))))

(defthm nintp-1
  (implies (and (acl2-numberp x)
		(not (integerp x))
		(integerp y))
	   (not (integerp (intp-+ x y)))))

(defthm nintp-2
  (implies (and (integerp x)
		(acl2-numberp y)
		(not (integerp y)))
	   (not (integerp (intp-+ x y)))))

; Let us now look at a simple example.
;
; (thm
;   (implies (and (integerp a)
;                 (integerp (+ a c))
;                 (integerp (+ d f))
;                 (integerp (+ b d e))
;                 (real/rationalp f)
;                 (not (integerp f)))
;            (not (integerp (+ a b c d e f)))))
;
; The meta function will rewrite the term
; (integerp (+ a b c d e f))
; to
; (integerp (intp-+ (+ a c)
;                   (intp-+ (+ c d e))
;                           (fix f))))
; At which point the four rules above should finish the job.
;
; Why do we do it this way? It was easy to write and prove correct.
; The meta rule produces a term which is easily shown to be
; equivalent to the original one, and regular rewrite rules perform
; the actual work.  We use a set of dummy functions so that we can
; control subsequent rewriting.  Without them, the sum would be
; rewritten back to the original term before we got to the
; integerp test.  This is an artifact of the fact that ACL2
; rewrites from the inside out, and that all of the term returned
; by a meta function is rewritten.  Perhaps it would be better
; if a meta function could return a term and a substitution alist
; as a regular rewrite rule does.
;
; This separation of concerns makes a meta rule much easier to
; design or modify.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 3. Functions called by the meta function.

; In the example just above, we partitioned the summands into three
; parts.  This section of the book defines the functions that will
; do this partitioning for us.

; We start off with three simple functions.  The first one strips
; the summands or factors out of a sum or product, and the next two
; reconstruct a sum or product.

(defun leaves (term bin-op)

; Term is an ACL2 term, and bin-op is one of 'BINARY-+ and
; BINARY-*.  We return a list of summands or factors as appropriate.

; The first branch of the cond is not needed for the correct
; operation of the meta rule, but does make the proof easier.  We
; believe that part of the difficulty lies in the fact that
; defevaluator does not axiomatize the number of arguments an ACL2
; function takes.  Note that we ``fix'' term in the first branch of
; the cond.

  (cond ((atom term)
	 (if (eq bin-op 'BINARY-+)
	     ''0
	   ''1))
	((eq (fn-symb term) bin-op)
	 (if (eq (fn-symb (fargn term 2)) bin-op)
	     (cons (fargn term 1)
		   (leaves (fargn term 2) bin-op))
	   (list (fargn term 1)
		 (fargn term 2))))
	(t
	 (list term))))

(defun tree (leaves bin-op)

; We assume that bin-op is either 'BINARY-+ or 'BINARY-*.  We
; return a bin-op tree representing the sum or product of the
; leaves as appropriate.

  (cond ((endp leaves)
	 (if (eq bin-op 'BINARY-+)
	     ''0
	   ''1))
	((endp (cdr leaves))
	 (list 'fix (car leaves)))
	((endp (cddr leaves))
	 (list bin-op (car leaves) (cadr leaves)))
	(t
	 (list bin-op (car leaves) (tree (cdr leaves) bin-op)))))

(defun big-tree (bags big-bin-op bin-op)

; Bags is a list of lists of leaves.  We assume that big-bin-op
; and bin-op are either 'INTP-+ and 'BINARY-+ or 'INTP-* and
; 'BINARY-*.  We form a big-bin-op tree whose 'leaves' are bin-op
; trees of the bagged leaves.
;
; Pseudo-example:
; (big-tree '((a b) (c d e) (f)) 'big-bin-op 'bin-op)
; ==>
; (big-bin-op (bin-op a b)
;             (big-bin-op (bin-op c (bin-op d e))
;                         (fix f)))

  (cond ((endp bags)
	 (if (eq bin-op 'BINARY-+)
	     ''0
	   ''1))
	((endp (cdr bags))
	 (tree (car bags) bin-op))
	((endp (cddr bags))
	 (list big-bin-op
	       (tree (car bags) bin-op)
	       (tree (cadr bags) bin-op)))
	(t
	 (list big-bin-op
	       (tree (car bags) bin-op)
	       (big-tree (cdr bags) big-bin-op bin-op)))))

; The next two functions extract the information we use
; to partition the summands or factors.  We wish to constuct two
; lists.  One will contain bags of terms know to be an integer, and the
; other will contain bags of terms known to be numeric but non-integers.
; A bag is a list of leaves.
;
; We look in two places for information.  We call type-set,
; (via mfc-ts), on each of the individual leaves we are concerned
; with; and we scan through the type-alist.  Calling type-set
; is the more powerful procedure and so we use it on the individual
; leaves, but there are too many other possibilities to use it
; for other terms.

; Note that each bag contains a list of leaves.  Example:
; Assume that we are working with a sum.
; If the type-alist reveals that (+ a b (* c d)) is an integer, we
; would add '(a b (* c d)) to the intp-bags.
; However, if (* a b (+ c d)) is known to be an integer, we would
; add '(* a b (+ c d)) to the intp-bags.

(defun bag-leaves (leaves mfc state
			  intp-bags non-intp-bags)

; Leaves is a list of leaves from a sum or product; intp-bags and
; non-intp-bags are initially nil.  We scan through the leaves,
; getting their type from mfc-ts, and accumulate the known integers
; (non-integers) into intp-bags (non-intp-bags).  Note that we "bag"
; each leaf individually, and so return two lists of lists of leaves.

  (if (endp leaves)
      (mv intp-bags non-intp-bags)
    (let ((leaf-type (ts-fix (mfc-ts (car leaves) mfc state))))
      (cond ((ts-subsetp leaf-type *ts-integer*)
	     (bag-leaves (cdr leaves) mfc state
			  (cons (list (car leaves)) intp-bags)
			  non-intp-bags))
	    ((and (ts-subsetp leaf-type *ts-acl2-number*)
		  (ts-subsetp leaf-type
			      (ts-complement *ts-integer*)))
	     (bag-leaves (cdr leaves) mfc state
			  intp-bags
			  (cons (list (car leaves)) non-intp-bags)))
	    (t
	     (bag-leaves (cdr leaves) mfc state
			  intp-bags non-intp-bags))))))

(defun bag-terms (type-alist bin-op intp-bags non-intp-bags)

; We scan through the type-alist and "bag" those terms known to be an
; integer or a non-integer, accumulating the result into intp-bags
; and non-intp-bags.

; Note: The type-alist consists of a list of triples of the form:
; (term numeric-type-set . ttree).
; See the ACL2 documentation topic ``type-set'' for details on
; how type knowledge is encoded in a numeric-type-set.

  (cond ((endp type-alist)
	 (mv intp-bags non-intp-bags))
	((variablep (caar type-alist))
	 (bag-terms (cdr type-alist) bin-op
		    intp-bags non-intp-bags))
	((ts-subsetp (cadr (car type-alist))
		     *ts-integer*)
	 (bag-terms (cdr type-alist) bin-op
		    (cons (leaves (caar type-alist) bin-op)
			  intp-bags)
		    non-intp-bags))
	((and (ts-subsetp (cadr (car type-alist))
			  *ts-acl2-number*)
	      (ts-subsetp (cadr (car type-alist))
			  (ts-complement *ts-integer*)))
	 (bag-terms (cdr type-alist) bin-op
		    intp-bags
		    (cons (leaves (caar type-alist) bin-op)
			  non-intp-bags)))
	(t
	 (bag-terms (cdr type-alist) bin-op
		    intp-bags non-intp-bags))))

(defun subtract-leaf (leaf leaves)

; Leaf is a term and leaves is a list of terms.  We return two
; values.  The first is a boolean flag indicating whether we
; found an occurence of leaf.  The second is the list leaves with
; the first occurance of leaf, if there is one, removed.

  (cond ((endp leaves)
	 (mv nil nil))
	((equal leaf (car leaves))
	 (mv t (cdr leaves)))
	(t
	 (mv-let (flag new-leaves)
	   (subtract-leaf leaf (cdr leaves))
	   (if flag
	       (mv t (cons (car leaves)
			   new-leaves))
	     (mv nil leaves))))))

(defun subtract-bag (bag leaves)

; Bag and leaves are both lists of terms.  We return two values.
; The first is a boolean flag indicating whether bag is a
; sub-bag of leaves.  If the flag is t, the second value is the
; the list leaves with each element of bag removed.

  (cond ((endp bag)
	 (mv t leaves))
	((endp (cdr bag))
	 (subtract-leaf (car bag) leaves))
	(t
	 (mv-let (flag new-leaves)
	   (subtract-bag (cdr bag) leaves)
	   (if flag
	       (subtract-leaf (car bag) new-leaves)
	     (mv nil leaves))))))

; These next three functions attempt to partition the leaves of
; our original term in a useful way.  There are two possibilities
; of interest.
; 1. We can partition leaves such that each part is known to be
;    an integer.  In this case our original term is an integer.
; 2. We can partition leaves such that all but one part is known
;    to be an integer, and the reamaining one is know to be a
;    non-integer.  In this case, out original term is not an
;    integer.
; We use the information gathered by bag-leaves and bag-terms
; to determine potential partitions.

(defun collect-bags-intp (leaves intp-bags)

; We try to partition leaves such that each part is an intp-bag.

  (cond ((endp leaves)
	 (mv t nil))
	((endp intp-bags)
	 (mv nil nil))
	(t
	 (mv-let (flag new-leaves)
	   (subtract-bag (car intp-bags) leaves)
	   (if flag
	       (mv-let (flag new-bags)
		 (collect-bags-intp new-leaves (cdr intp-bags))
		 (if flag
		     (mv t (cons (car intp-bags)
				 new-bags))
		   (collect-bags-intp leaves (cdr intp-bags))))
	     (collect-bags-intp leaves (cdr intp-bags)))))))

(defun collect-bags-non-intp (leaves intp-bags non-intp-bags)

; We try to partition leaves such that exactly one part is a non-intp-bag
; and all the rest are each an intp-bag.

  (cond ((endp non-intp-bags)
	 (mv nil nil))
	(t
	 (mv-let (flag new-leaves)
	   (subtract-bag (car non-intp-bags) leaves)
	   (if (and flag
		    (consp new-leaves))
	       (mv-let (flag bag-list)
		 (collect-bags-intp new-leaves intp-bags)
		 (if flag
		     (mv t
			 (cons (car non-intp-bags)
			       bag-list))
		   (collect-bags-non-intp leaves
					  intp-bags
					  (cdr non-intp-bags))))
	     (collect-bags-non-intp leaves
				    intp-bags
				    (cdr non-intp-bags)))))))

(defun collect-bags (leaves intp-bags non-intp-bags bin-op)

; We try to partition leaves in a way that lets us determine that the
; original term is or is not an integerp.

  (mv-let (flag bag-list)
    (if (eq bin-op 'BINARY-+)
	(collect-bags-non-intp leaves intp-bags non-intp-bags)
      (mv nil nil))
    (if flag
	(mv flag bag-list)  ;; non-intp
      (collect-bags-intp leaves intp-bags))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 4. The meta function.

(defun meta-integerp (term mfc state)

; Assumptions: 1. Term is right-associated.  2. Not all leaves
; are known to be integers by type-set.
;
; Pseudo-Example:
; (integerp (+ a (+ b (+ c d))))
;  ==> (integerp (intp-+ (+ a c) (+ b d)))

  (if (consp term)
      (let ((bin-op (fn-symb (fargn term 1))))
	(if (and (member-eq bin-op '(BINARY-+ BINARY-*))
		 (eq (fn-symb term) 'INTEGERP)
		 (eq (fn-symb (fargn (fargn term 1) 2)) bin-op))

	    ;; We have a term of the form:
	    ;; (integerp (bin-op x (bin-op y z))).

	    (let ((leaves (leaves (fargn term 1) bin-op)))
	      (mv-let (intp-leaves non-intp-leaves)
		(bag-leaves leaves mfc state nil nil)
		(mv-let (intp-bags non-intp-bags)
		  (bag-terms (mfc-type-alist mfc) bin-op
			     intp-leaves non-intp-leaves)
		  (mv-let (flag bag-list)
		    (collect-bags leaves intp-bags non-intp-bags bin-op)
		    (if flag
			`(INTEGERP ,(big-tree bag-list
					      (if (eq bin-op 'BINARY-+)
						  'INTP-+
						'INTP-*)
					      bin-op))
		      term)))))
	  term))
    term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 5. An encapsulate containing the meta theorem.

(encapsulate
 ()

 (local
  (defun tree-2 (leaves bin-op)
    (cond ((endp leaves)
	   (if (eq bin-op 'BINARY-+)
	       ''0
	     ''1))
	  (t
	   (list bin-op (car leaves) (tree-2 (cdr leaves) bin-op))))))

 (local
  (defthm trees
    (implies (or (eq bin-op 'BINARY-+)
		 (eq bin-op 'BINARY-*))
	     (equal (intp-eva (tree leaves bin-op) a)
		    (intp-eva (tree-2 leaves bin-op) a)))))

 (local
  (in-theory (disable tree)))

 (local
  (defun big-tree-2 (bags big-bin-op bin-op)
    (cond ((endp bags)
	   (if (eq bin-op 'BINARY-+)
	       ''0
	     ''1))
	  (t
	   (list big-bin-op
		 (tree (car bags) bin-op)
		 (big-tree-2 (cdr bags) big-bin-op bin-op))))))

 (local
  (defthm big-tree-big-tree-2
    (and
     (equal (intp-eva (big-tree bags 'INTP-+ 'BINARY-+) a)
	    (intp-eva (big-tree-2 bags 'BINARY-+ 'BINARY-+) a))
     (equal (intp-eva (big-tree bags 'INTP-* 'BINARY-*) a)
	    (intp-eva (big-tree-2 bags 'BINARY-* 'BINARY-*) a)))))

 (local
  (in-theory (disable big-tree)))

 (local
  (defthm tree-2-leaves
    (implies (and (or (eq bin-op 'BINARY-+)
		      (eq bin-op 'BINARY-*))
		  (eq (fn-symb term) bin-op))
	     (equal (intp-eva (tree-2 (leaves term bin-op) bin-op) a)
		    (intp-eva term a)))
    :hints (("Subgoal 2" :induct t)
	    ("Subgoal 1" :induct t))))

 (local
  (defthm acl2-numberp-tree-2
    (implies (or (eq bin-op 'BINARY-+)
		 (eq bin-op 'BINARY-*))
	     (acl2-numberp (intp-eva (tree-2 x bin-op) a)))
    :rule-classes :type-prescription))

 (local
  (defthm subtract-leaf-good-+
    (mv-let (flag new-leaves)
      (subtract-leaf leaf leaves)
      (implies flag
	       (equal (+ (intp-eva leaf a)
			 (intp-eva (tree-2 new-leaves 'BINARY-+) a))
		      (intp-eva (tree-2 leaves 'BINARY-+) a))))))

 (local
  (defthm subtract-leaf-good-*
    (mv-let (flag new-leaves)
      (subtract-leaf leaf leaves)
      (implies flag
	       (equal (* (intp-eva leaf a)
			 (intp-eva (tree-2 new-leaves 'BINARY-*) a))
		      (intp-eva (tree-2 leaves 'BINARY-*) a))))))

 (local
  (defthm subtract-bag-good-+
    (mv-let (flag new-leaves)
      (subtract-bag bag leaves)
      (implies flag
	       (equal (+ (intp-eva (tree-2 bag 'BINARY-+) a)
			 (intp-eva (tree-2 new-leaves 'BINARY-+) a))
		      (intp-eva (tree-2 leaves 'BINARY-+) a))))
    :hints (("Subgoal *1/3"
	     :use
	     ((:instance subtract-leaf-good-+
			 (leaf (CAR BAG))
			 (leaves (MV-NTH 1 (SUBTRACT-BAG (CDR BAG) LEAVES)))))
	     :in-theory (disable subtract-leaf-good-+ tree)))))

 (local
  (defthm subtract-bag-good-*
    (mv-let (flag new-leaves)
      (subtract-bag bag leaves)
      (implies flag
	       (equal (* (intp-eva (tree-2 bag 'BINARY-*) a)
			 (intp-eva (tree-2 new-leaves 'BINARY-*) a))
		      (intp-eva (tree-2 leaves 'BINARY-*) a))))
    :hints (("Subgoal *1/3"
	     :use
	     ((:instance subtract-leaf-good-*
			 (leaf (CAR BAG))
			 (leaves (MV-NTH 1 (SUBTRACT-BAG (CDR BAG) LEAVES)))))
	     :in-theory (disable subtract-leaf-good-* tree)))))

 (local
  (defthm collect-bags-intp-good-+
    (mv-let (flag bags)
      (collect-bags-intp leaves intp-bags)
      (implies (and flag
		    (consp leaves))
	       (equal (intp-eva (big-tree-2 bags 'BINARY-+ 'BINARY-+) a)
		      (intp-eva (tree-2 leaves 'BINARY-+) a))))
    :hints (("Subgoal *1/4'5'" :use ((:instance subtract-bag-good-+
						(bag INTP-BAGS1)))
	     :in-theory (disable subtract-bag-good-+)))))

 (local
  (defthm collect-bags-intp-good-*
    (mv-let (flag bags)
      (collect-bags-intp leaves intp-bags)
      (implies (and flag
		    (consp leaves))
	       (equal (intp-eva (big-tree-2 bags 'BINARY-* 'BINARY-*) a)
		      (intp-eva (tree-2 leaves 'BINARY-*) a))))
    :hints (("Subgoal *1/4'5'" :use ((:instance subtract-bag-good-*
						(bag INTP-BAGS1)))
	     :in-theory (disable subtract-bag-good-*)))))

 (local
  (defthm collect-bags-good
    (mv-let (flag bags)
      (collect-bags leaves intp-bags non-intp-bags bin-op)
      (implies (and flag
		    (member-eq bin-op '(BINARY-+ BINARY-*))
		    (consp leaves))
	       (equal (intp-eva (big-tree-2 bags bin-op bin-op) a)
		      (intp-eva (tree-2 leaves bin-op) a))))))

 (local
  (defthm big-tree-term
    (mv-let (flag bags)
      (collect-bags (leaves term bin-op)
		    intp-bags non-intp-bags bin-op)
      (implies (and flag
		    (or (and (eq intp-bin-op 'INTP-+)
			     (eq bin-op 'BINARY-+))
		        (and (eq intp-bin-op 'INTP-*)
			     (eq bin-op 'BINARY-*)))
		    (eq (fn-symb term) bin-op))
	       (equal (intp-eva (big-tree bags intp-bin-op bin-op) a)
		      (intp-eva term a))))
    :hints (("Goal" :in-theory (disable leaves collect-bags tree-2)))))

 (local
  (in-theory (disable leaves bag-leaves bag-terms collect-bags big-tree
		      intp-+ intp-*)))

; We export only this.

 (defthm meta-integerp-correct
   (equal (intp-eva term a)
	  (intp-eva (meta-integerp term mfc state) a))
   :rule-classes ((:meta :trigger-fns (INTEGERP))))

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 6. Cleanup

(in-theory (disable leaves tree big-tree bag-leaves bag-terms
		    subtract-leaf subtract-bag
		    collect-bags-intp collect-bags-non-intp
		    collect-bags meta-integerp))

(in-theory (disable intp-+ intp-*))
