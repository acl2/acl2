; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; integerp-meta.lisp
;;;
;;;
;;; This book contains a meta rule about when a sum or
;;; product is or is not an integer.
;;;
;;; NOTE: I have now generalized the book to include
;;; meta-rationalp-correct also.  Some of the function and variable
;;; names are, therefore, misleading.
;;;
;;; Pseudo-Example: (See code for an explanation)
;;; If we know that (+ a c) and (+ b d) are integers:
;;; (integerp (+ a (+ b (+ c d))))
;;;  ===>
;;; (integerp (intp-+ (+ a c) (+ b d)))
;;;
;;; The basic idea here is that we attempt to partition the addends
;;; (or factors) into ``bags'' such that:
;;; 1. The union of the contents of the bags are the addends (factors)
;;; 2. Either all the bags are known to be integerp
;;;    or
;;;    (in the case of a sum) all the bags except one are know to be
;;;    integerp and the exception is know to not be an integerp.
;;; Given this we can determine that the original sum or product is
;;; or is not an integerp.  We preserve this bagging by the use of
;;; intp-+ and intp-* so that ACL2 does not re-distribute and
;;; re-associate the bags apart.  The rules intp-[12] and nintp-[12]
;;; then allow us to prove the desired result.
;;;
;;; The only theorem we export from this book is meta-integerp-correct.
;;;
;;; I would really like to get something like this into type-set, so
;;; that this book in not needed anymore, but initial efforts have
;;; slowed ACL2 down by three or four percent, which seems like too
;;; much to me.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

(local
 (include-book "../../support/top"))

(local
 (include-book "default-hint"))

(local
 (set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
					       hist pspv))))

(table acl2-defaults-table :state-ok t)

(table acl2-defaults-table :verify-guards-eagerness 0)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun intp-+ (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (+ x y))

(defun intp-* (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (* x y))

(defun meta-integerp-unhide (x)
  (declare (xargs :guard t))
  x)

(defthm meta-integerp-unhide-hide
  (equal (meta-integerp-unhide (hide x))
	 x)
  :hints (("Goal" :expand ((hide x)))))

(in-theory (disable meta-integerp-unhide
		    (:executable-counterpart meta-integerp-unhide)))

(defevaluator intp-eva intp-eva-lst ((intp-+ x y)
				     (intp-* x y)
				     (binary-+ x y)
				     (binary-* x y)
                                     (integerp x)
				     (rationalp x)
				     #+non-standard-analysis
				     (realp x)
				     (hide x)
				     (meta-integerp-unhide x)
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

(defthm intp-3
  (implies (and (rationalp x)
		(rationalp y))
	   (rationalp (intp-* x y))))

(defthm intp-4
  (implies (and (rationalp x)
		(rationalp y))
	   (rationalp (intp-+ x y))))

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

(defthm nintp-3
  (implies (and (acl2-numberp x)
		(not (rationalp x))
		(rationalp y))
	   (not (rationalp (intp-+ x y)))))

(defthm nintp-4
  (implies (and (rationalp x)
		(acl2-numberp y)
		(not (rationalp y)))
	   (not (rationalp (intp-+ x y)))))

#+non-standard-analysis
(defthm nintp-5
  (implies (and (real/rationalp x)
		(acl2-numberp y)
		(not (real/rationalp y)))
	   (not (real/rationalp (intp-+ x y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun leaves (term bin-op)
  (declare (xargs :guard (symbolp bin-op)))
  (cond ((atom term)
	 (if (eq bin-op 'BINARY-+)
	     (list ''0)
	   (list ''1)))
	((eq (fn-symb term) bin-op)
	 (if (eq (fn-symb (arg2 term)) bin-op)
	     (cons (arg1 term)
		   (leaves (arg2 term) bin-op))
	   (list (arg1 term)
		 (arg2 term))))
	(t
	 (list term))))

(defun tree (leaves bin-op)
  (declare (xargs :guard (symbolp bin-op)))
  (cond ((atom leaves)
	 (if (eq bin-op 'BINARY-+)
	     ''0
	   ''1))
	((atom (cdr leaves))
	 (list 'fix (car leaves)))
	((atom (cddr leaves))
	 (list bin-op (car leaves) (cadr leaves)))
	(t
	 (list bin-op (car leaves) (tree (cdr leaves) bin-op)))))

(defun big-tree (bags big-bin-op bin-op)
  (declare (xargs :guard (and (symbolp big-bin-op)
                              (symbolp bin-op))))

; We form a big-bin-op tree whose 'leaves' are bin-op trees of the
; bagged leaves.
; Pseudo-example:
; (big-tree '((a b) (c d e) (f)) 'big-bin-op 'bin-op)
; ==> (big-bin-op (bin-op a b)
;                 (big-bin-op (bin-op c (bin-op d e))
;                             (fix f)))

  (cond ((atom bags)
	 (if (eq bin-op 'BINARY-+)
	     ''0
	   ''1))
	((atom (cdr bags))
	 (tree (car bags) bin-op))
	((atom (cddr bags))
	 (list big-bin-op
	       (tree (car bags) bin-op)
	       (tree (cadr bags) bin-op)))
	(t
	 (list big-bin-op
	       (tree (car bags) bin-op)
	       (big-tree (cdr bags) big-bin-op bin-op)))))

;;; I leave the following two defuns here in case we ever want to go
;;; back to them.  At present, we use mfc-rw to determine whether an
;;; addend is an integer or not.  The following code would allow us to
;;; use mfc-ts instead.
#|
(defun ts-fix (x)
  (declare (xargs :guard t))
  (let ((int-x (ifix x)))
    (if (and (<= *min-type-set* int-x)
	     (<= int-x *max-type-set*))
	int-x
    0)))

(defun bag-leaves (leaves mfc state
			  intp-bags non-intp-bags)
  (declare (xargs :guard t))

; Leaves is a list of leaves from a sum or product; intp-bags and
; non-intp-bags are initially nil.  We scan through the leaves,
; getting their type from mfc-ts, and accumulate the known integers
; (non-integers) into intp-bags (non-intp-bags).  Note that we "bag"
; each leaf individually, and so return two lists of lists of leaves.

  (if (atom leaves)
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
|#

(defun bag-leaves (leaves mfc state
			  intp-bags non-intp-bags
			  intp-flag)
  (declare (xargs :guard t))

; Leaves is a list of leaves from a sum or product; intp-bags and
; non-intp-bags are initially nil.  We scan through the leaves,
; getting their type from mfc-ts, and accumulate the known integers
; (non-integers) into intp-bags (non-intp-bags).  Note that we "bag"
; each leaf individually, and so return two lists of lists of leaves.

  (if (atom leaves)
      (mv intp-bags non-intp-bags)
    (let ((rewriting-result (if intp-flag
				(mfc-rw+ '(INTEGERP x)
					 `((x . ,(car leaves)))
					 t t mfc state)
			      (mfc-rw+ #-non-standard-analysis '(RATIONALP x)
				       #+non-standard-analysis '(REALP x)
					 `((x . ,(car leaves)))
					 t t mfc state))))
      (cond ((equal rewriting-result *t*)
	     (bag-leaves (cdr leaves) mfc state
			  (cons (list (car leaves)) intp-bags)
			  non-intp-bags
			  intp-flag))
            ((equal rewriting-result *nil*)
	     (bag-leaves (cdr leaves) mfc state
			 intp-bags
			 (cons (list (car leaves)) non-intp-bags)
			 intp-flag))
            (t
             (bag-leaves (cdr leaves) mfc state
                         intp-bags non-intp-bags
			 intp-flag))))))

(defun bag-terms (type-alist bin-op
			     intp-bags non-intp-bags
			     intp-flag)
  (declare (xargs :guard (and (type-alistp type-alist)
                              (or (equal bin-op 'BINARY-+)
                                  (equal bin-op 'BINARY-*)))))

; We scan through the type-alist and "bag" those terms known to be an
; integer or a non-integer, accumulating the result into intp-bags
; and non-intp-bags.

  (cond ((atom type-alist)
	 (mv intp-bags non-intp-bags))
	((variablep (caar type-alist))
	 (bag-terms (cdr type-alist) bin-op
		    intp-bags non-intp-bags
		    intp-flag))
	((ts-subsetp (cadr (car type-alist))
		     (if intp-flag
			 *ts-integer*
		       #-non-standard-analysis *ts-rational*
		       #+non-standard-analysis *ts-real*
		       ))
	 (bag-terms (cdr type-alist) bin-op
		    (cons (leaves (caar type-alist) bin-op)
			  intp-bags)
		    non-intp-bags
		    intp-flag))
	((and (ts-subsetp (cadr (car type-alist))
			  *ts-acl2-number*)
	      (ts-subsetp (cadr (car type-alist))
			  (ts-complement (if intp-flag
					     *ts-integer*
					   #-non-standard-analysis *ts-rational*
					   #+non-standard-analysis *ts-real*
					   ))))
	 (bag-terms (cdr type-alist) bin-op
		    intp-bags
		    (cons (leaves (caar type-alist) bin-op)
			  non-intp-bags)
		    intp-flag))
	(t
	 (bag-terms (cdr type-alist) bin-op
		    intp-bags non-intp-bags
		    intp-flag))))

(defun subtract-leaf (leaf leaves)
  (declare (xargs :guard (true-listp leaves)))
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
  (declare (xargs :guard (and (true-listp bag)
                              (true-listp leaves))))
  (cond ((endp bag)
	 (mv t leaves))
	((endp (cdr bag))
	 (subtract-leaf (car bag) leaves))
	(t
	 (mv-let (flag new-leaves)
	   (subtract-bag (cdr bag) leaves)
	   (if flag
	       (subtract-leaf (car bag) new-leaves)
	     (mv nil nil))))))

(defun collect-bags-intp (leaves intp-bags)
  (declare (xargs :guard (and (true-listp leaves)
                              (true-list-listp intp-bags))))

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
  (declare (xargs :guard (and (true-listp leaves)
                              (true-list-listp intp-bags)
                              (true-list-listp non-intp-bags))))

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
  (declare (xargs :guard (and (true-listp leaves)
                              (true-list-listp intp-bags)
                              (true-list-listp non-intp-bags))))

; We try to partition leaves in a way that lets us determine that the
; original term is or is not an integerp.

  (mv-let (flag bag-list)
    (if (eq bin-op 'BINARY-+)
	(collect-bags-non-intp leaves intp-bags non-intp-bags)
      (mv nil nil))
    (if flag
	(mv flag bag-list)  ;; non-intp
      (collect-bags-intp leaves intp-bags))))

(defun meta-integerp (term mfc state)
  (declare (xargs :guard (pseudo-termp term)))

; Assumptions: 1. Term is right-associated.  2. Not all leaves
; are known to be integers by type-set.
;
; Pseudo-Example:
; (integerp (+ a (+ b (+ c d))))
;  ==> (integerp (intp-+ (+ a c) (+ b d)))

; We use meta-integerp-unhide and hide to prevent re-arrangement
; of factors/addends.  This may happen before rewriting has had a
; chance to normalize expressions --- most commonly at Goal.
; Consider, for example, that we know (integerp (* 1/2 Y X)) from,
; the type-alist and that we are asked about (integerp (* 1/2 X Y)).
; This meta-integerp would return (integerp (* 1/2 Y X)), which
; would then be permuted to (integerp (* 1/2 X Y)), and we would
; loop.

  (if (eq (fn-symb term) 'INTEGERP)

      (let ((bin-op (fn-symb (fargn term 1))))
	(if (and (member-eq bin-op '(BINARY-+ BINARY-*))
		 (eq (fn-symb (fargn (fargn term 1) 2)) bin-op))

	    ;; We have a term of the form:
	    ;; (integerp (bin-op x (bin-op y z))).

	    (let ((leaves (leaves (fargn term 1) bin-op)))
	      (mv-let (intp-leaves non-intp-leaves)
		(bag-leaves leaves mfc state nil nil t)
		(mv-let (intp-bags non-intp-bags)
		  (bag-terms (mfc-type-alist mfc) bin-op
			     intp-leaves non-intp-leaves
			     t)
		  (mv-let (flag bag-list)
		    (collect-bags leaves intp-bags non-intp-bags bin-op)
		    (if flag
			`(INTEGERP (META-INTEGERP-UNHIDE
				    (HIDE
				     ,(big-tree bag-list
						(if (eq bin-op 'BINARY-+)
						    'INTP-+
						  'INTP-*)
						bin-op))))
		      term)))))
	  term))
    term))

(defun meta-rationalp (term mfc state)
  (declare (xargs :guard (pseudo-termp term)))

; Assumptions: 1. Term is right-associated.  2. Not all leaves
; are known to be integers by type-set.
;
; Pseudo-Example:
; (integerp (+ a (+ b (+ c d))))
;  ==> (integerp (intp-+ (+ a c) (+ b d)))

  (if (eq (fn-symb term) 'RATIONALP)

      (let ((bin-op (fn-symb (fargn term 1))))
	(if (and (member-eq bin-op '(BINARY-+ BINARY-*))
		 (eq (fn-symb (fargn (fargn term 1) 2)) bin-op))

	    ;; We have a term of the form:
	    ;; (integerp (bin-op x (bin-op y z))).

	    (let ((leaves (leaves (fargn term 1) bin-op)))
	      (mv-let (intp-leaves non-intp-leaves)
		(bag-leaves leaves mfc state nil nil nil)
		(mv-let (intp-bags non-intp-bags)
		  (bag-terms (mfc-type-alist mfc) bin-op
			     intp-leaves non-intp-leaves
			     nil)
		  (mv-let (flag bag-list)
		    (collect-bags leaves intp-bags non-intp-bags bin-op)
		    (if flag
			`(RATIONALP (META-INTEGERP-UNHIDE
				     (HIDE
				      ,(big-tree bag-list
						 (if (eq bin-op 'BINARY-+)
						     'INTP-+
						   'INTP-*)
						 bin-op))))
		      term)))))
	  term))
    term))

#+non-standard-analysis
(defun meta-realp (term mfc state)
  (declare (xargs :guard (pseudo-termp term)))

; Assumptions: 1. Term is right-associated.  2. Not all leaves
; are known to be integers by type-set.
;
; Pseudo-Example:
; (integerp (+ a (+ b (+ c d))))
;  ==> (integerp (intp-+ (+ a c) (+ b d)))

  (if (eq (fn-symb term) 'REALP)

      (let ((bin-op (fn-symb (fargn term 1))))
	(if (and (member-eq bin-op '(BINARY-+ BINARY-*))
		 (eq (fn-symb (fargn (fargn term 1) 2)) bin-op))

	    ;; We have a term of the form:
	    ;; (integerp (bin-op x (bin-op y z))).

	    (let ((leaves (leaves (fargn term 1) bin-op)))
	      (mv-let (intp-leaves non-intp-leaves)
		(bag-leaves leaves mfc state nil nil nil)
		(mv-let (intp-bags non-intp-bags)
		  (bag-terms (mfc-type-alist mfc) bin-op
			     intp-leaves non-intp-leaves
			     nil)
		  (mv-let (flag bag-list)
		    (collect-bags leaves intp-bags non-intp-bags bin-op)
		    (if flag
			`(REALP (META-INTEGERP-UNHIDE
				     (HIDE
				      ,(big-tree bag-list
						 (if (eq bin-op 'BINARY-+)
						     'INTP-+
						   'INTP-*)
						 bin-op))))
		      term)))))
	  term))
    term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Everything below here is
;;; 1. A verification of our guards.
;;; 2. A proof of:
#|
 (defthm meta-integerp-correct
   (equal (intp-eva term a)
	  (intp-eva (meta-integerp term mfc state) a))
   :rule-classes ((:meta :trigger-fns (INTEGERP))))

 (defthm meta-rationalp-correct
   (equal (intp-eva term a)
	  (intp-eva (meta-integerp term mfc state) a))
   :rule-classes ((:meta :trigger-fns (RATIONALP))))
|#
;;; These latter two theorems are all that are exported from the rest
;;; of this book.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Do not read past this comment unless you have a good reason for
;;; doing so.  See comment immediately above.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We verify our guards

(encapsulate
 ()

 (local
  (encapsulate
   ()

   (local
    (defthm niq-bounds
        (implies (and (integerp i)
                      (<= 0 i)
                      (integerp j)
                      (< 0 j))
                 (and (<= (nonnegative-integer-quotient i j)
                          (/ i j))
                      (< (+ (/ i j) -1)
                         (nonnegative-integer-quotient i j))))
      :hints (("Subgoal *1/1''" :use (:instance NORMALIZE-<-/-TO-*-3-3
				  (x 1)
				  (y i)
				  (z j))))
      :rule-classes ((:linear
                      :trigger-terms ((nonnegative-integer-quotient i j))))))

   (local
    (defthm floor-bounds-1
        (implies (and (real/rationalp x)
                      (real/rationalp y))
                 (and (< (+ (/ x y) -1)
                         (floor x y))
                      (<= (floor x y)
                          (/ x y))))
      :rule-classes ((:generalize)
                     (:linear :trigger-terms ((floor x y))))))

   (local
    (defthm floor-bounds-2
        (implies (and (real/rationalp x)
                      (real/rationalp y)
                      (integerp (/ x y)))
                 (equal (floor x y)
                        (/ x y)))
      :rule-classes ((:generalize)
                     (:linear :trigger-terms ((floor x y))))))

   (local
    (defthm floor-bounds-3
        (implies (and (real/rationalp x)
                      (real/rationalp y)
                      (not (integerp (/ x y))))
                 (< (floor x y)
                    (/ x y)))
      :rule-classes ((:generalize)
                     (:linear :trigger-terms ((floor x y))))))

   (local
    (in-theory (disable floor)))

   (local
    (defun ind-hint (x y n)
      (declare (xargs :measure (abs (ifix x))))
      (cond ((or (zip x) (zip y) (zp n))
             t)
            ((equal x -1)
             t)
            (t
             (ind-hint (floor x 2) (floor y 2) (+ -1 n))))))

   (local
    (defthm one
        (implies (and (integerp x)
                      (integerp n)
                      (< 0 n)
                      (<= (- (EXPT 2 N)) X))
                 (equal (< (FLOOR X 2) (- (* 1/2 (EXPT 2 N))))
                        nil))))

   (local
    (defthm two-x
        (implies (and (< x 4)
                      (<= -4 x)
                      (integerp x))
                 (or (equal x -4)
                     (equal x -3)
                     (equal x -2)
                     (equal x -1)
                     (equal x 0)
                     (equal x 1)
                     (equal x 2)
                     (equal x 3)))
      :rule-classes nil))

   (local
    (defthm two-y
        (implies (and (< y 4)
                      (<= -4 y)
                      (integerp y))
                 (or (equal y -4)
                     (equal y -3)
                     (equal y -2)
                     (equal y -1)
                     (equal y 0)
                     (equal y 1)
                     (equal y 2)
                     (equal y 3)))
      :rule-classes nil))

   (local
   (defthm foo
       (implies (and (integerp x)
                     (integerp n)
                     (< 1 n)
                     (< x (* 1/2 (EXPT 2 N))))
                (< (+ 1 (* 2 x)) (expt 2 n)))))


   (local
    (defthm logand-bounds
        (implies (and (integerp x)
                      (<= (- (expt 2 n)) x)
                      (< x (expt 2 n))
                      (integerp y)
                      (<= (- (expt 2 n)) y)
                      (< y (expt 2 n))
                      (integerp n)
                      (< 1 n))
                 (and (<= (- (expt 2 n)) (logand x y))
                      (< (logand x y) (expt 2 n))))
      :hints (("Goal" :in-theory (disable floor expt)
                      :induct (ind-hint x y n)
                      :do-not '(generalize))
              ("Subgoal *1/3.18" :use (two-x two-y))
              ("Subgoal *1/3.17" :use (two-x two-y))
              ("Subgoal *1/3.16" :use (two-x two-y))
              ("Subgoal *1/3.15" :use (two-x two-y))
              ("Subgoal *1/3.14" :use (two-x two-y))
              ("Subgoal *1/3.13" :use (two-x two-y))
              )))

   (defthm logand-thm
       (implies (and (integerp x)
                     (<= *min-type-set* x)
                     (<= x *max-type-set*)
                     (integerp y)
                     (<= *min-type-set* y)
                     (<= y *max-type-set*))
                (and (<= *min-type-set* (logand x y))
                     (<= (logand x y) *max-type-set*)))
     :hints (("Goal" :use ((:instance logand-bounds
                                      (n (length *actual-primitive-types*)))))))

   ))
#|
 (local
  (encapsulate
   ()

   (local
    (include-book
     "../../ihs/logops-lemmas"))

   (defthm logand-thm
       (implies (and (integerp x)
                     (<= *min-type-set* x)
                     (<= x *max-type-set*)
                     (integerp y)
                     (<= *min-type-set* y)
                     (<= y *max-type-set*))
                (and (<= *min-type-set* (logand x y))
                     (<= (logand x y) *max-type-set*)))
     :hints (("Goal" :use ((:instance signed-byte-p-logops
                                      (size (1+ (length *actual-primitive-types*)))
                                      (i x)
                                      (j y)))
                     :in-theory (disable logand signed-byte-p-logops))))

   ))|#

 (verify-guards intp-+)

 (verify-guards intp-*)

 (verify-guards leaves)

 (local
  (defthm pseudo-term-listp-leaves
      (implies (and (pseudo-termp x)
                    (or (equal bin-op 'binary-+)
                        (equal bin-op 'binary-*)))
               (pseudo-term-listp (leaves x bin-op)))))

 (verify-guards tree)

 (verify-guards big-tree)

 (verify-guards bag-leaves)

 (local
  (defthm pseudo-term-list-listp-bag-leaves
      (implies (and (pseudo-term-listp x)
                    (pseudo-term-list-listp y)
                    (pseudo-term-list-listp z))
               (and (pseudo-term-list-listp
                     (car (bag-leaves x mfc state y z flag)))
                    (pseudo-term-list-listp
                     (mv-nth 1 (bag-leaves x mfc state y z flag)))))))

 (verify-guards bag-terms)

 (local
  (defthm pseudo-term-list-listp-bag-terms
      (implies (and (type-alistp type-alist)
                    (or (equal bin-op 'binary-+)
                        (equal bin-op 'binary-*))
                    (pseudo-term-list-listp intp-bags)
                    (pseudo-term-list-listp non-intp-bags))
               (and (pseudo-term-list-listp
                     (car (bag-terms type-alist bin-op
                                     intp-bags non-intp-bags
				     flag)))
                    (pseudo-term-list-listp
                     (mv-nth 1 (bag-terms type-alist bin-op
                                          intp-bags non-intp-bags
					  flag)))))))

 (verify-guards subtract-leaf)

 (local
  (defthm true-listp-subtract-leaf
      (implies (true-listp leaves)
               (true-listp (mv-nth 1 (subtract-leaf leaf leaves))))))

 ;; It is odd that I did not need this hint when I was verifying guards
 ;; as I introduced the functions.

 (verify-guards subtract-bag
                :otf-flg t)

 (local
  (defthm true-listp-subtract-bag
      (implies (true-listp leaves)
               (true-listp (mv-nth 1 (subtract-bag leaf leaves))))))

 (verify-guards collect-bags-intp)

 (verify-guards collect-bags-non-intp)

 (verify-guards collect-bags)

 (local
  (encapsulate
   ()

   (local
    (defthm pseudo-term-list-listp-collect-bags-intp
        (implies (and (true-listp leaves)
                      (pseudo-term-list-listp intp-bags))
                 (pseudo-term-list-listp
                  (mv-nth 1 (collect-bags-intp leaves intp-bags))))))

   (local
    (defthm pseudo-term-list-listp-collect-bags-non-intp
        (implies (and (true-listp leaves)
                      (pseudo-term-list-listp intp-bags)
                      (pseudo-term-list-listp non-intp-bags))
                 (pseudo-term-list-listp
                  (mv-nth 1 (collect-bags-non-intp leaves intp-bags non-intp-bags))))))

   (defthm pseudo-term-list-listp-collect-bags
       (implies (and (true-listp leaves)
                     (pseudo-term-list-listp intp-bags)
                     (pseudo-term-list-listp non-intp-bags)
                     (or (equal bin-op 'binary-+)
                         (equal bin-op 'binary-*)))
                (pseudo-term-list-listp
                 (mv-nth 1 (collect-bags leaves intp-bags non-intp-bags bin-op)))))

   ))

 (local
  (defthm pseudo-term-list-listp-implies-true-list-listp
      (implies (pseudo-term-list-listp x)
               (true-list-listp x))))

 (verify-guards meta-integerp
                  :hints (("Goal" :in-theory (disable bag-leaves
                                                      bag-terms
                                                      collect-bags))))

 (verify-guards meta-rationalp
                  :hints (("Goal" :in-theory (disable bag-leaves
                                                      bag-terms
                                                      collect-bags))))

 #+non-standard-analysis
 (verify-guards meta-realp
                  :hints (("Goal" :in-theory (disable bag-leaves
                                                      bag-terms
                                                      collect-bags))))

 )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We prove the meta rule

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

; We export only these.

 (defthm meta-integerp-correct
   (equal (intp-eva term a)
	  (intp-eva (meta-integerp term mfc state) a))
   :rule-classes ((:meta :trigger-fns (INTEGERP))))

 (defthm meta-rationalp-correct
   (equal (intp-eva term a)
	  (intp-eva (meta-rationalp term mfc state) a))
   :rule-classes ((:meta :trigger-fns (RATIONALP))))

 #+non-standard-analysis
 (defthm meta-realp-correct
   (equal (intp-eva term a)
	  (intp-eva (meta-realp term mfc state) a))
   :rule-classes ((:meta :trigger-fns (REALP))))

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable leaves tree big-tree bag-leaves bag-terms
		    subtract-leaf subtract-bag
		    collect-bags-intp collect-bags-non-intp
		    collect-bags meta-integerp meta-rationalp
		    #+non-standard-analysis
		    meta-realp
		    ))

(in-theory (disable intp-+ intp-*))
