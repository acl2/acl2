; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; integerp-meta.lisp
;;;
;;;
;;; This book contains a meta rule about when a sum or
;;; product is or is not an integer.
;;;
;;; Pseudo-Example: (See code for an explanation)
;;; (integerp (+ a (+ b (+ c d))))
;;;  ===>
;;; (integerp (intp-+ (+ a c) (+ b d)))
;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")


(local
 (include-book "../pass1/top"))

(include-book "default-hint")

(set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                              hist pspv)))

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

(defevaluator intp-eva intp-eva-lst ((intp-+ x y)
				     (intp-* x y)
				     (binary-+ x y)
				     (binary-* x y)
                                     (integerp x)
				     (hide x)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun leaves (term bin-op)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp bin-op))))
  (cond ((atom term)
	 (if (eq bin-op 'BINARY-+)
	     (list ''0)
	   (list ''1)))
	((eq (fn-symb term) bin-op)
	 (if (eq (fn-symb (fargn term 2)) bin-op)
	     (cons (fargn term 1)
		   (leaves (fargn term 2) bin-op))
	   (list (fargn term 1)
		 (fargn term 2))))
	(t
	 (list term))))

(defun tree (leaves bin-op)
  (declare (xargs :guard (and (pseudo-term-listp leaves)
                              (symbolp bin-op))))
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
  (declare (xargs :guard (and (pseudo-term-list-listp bags)
                              (symbolp big-bin-op)
                              (symbolp bin-op))))

; We form a big-bin-op tree whose 'leaves' are bin-op trees of the
; bagged leaves.
; Pseudo-example:
; (big-tree '((a b) (c d e) (f)) 'big-bin-op 'bin-op)
; ==> (big-bin-op (bin-op a b)
;                 (big-bin-op (bin-op c (bin-op d e))
;                             (fix f)))

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
  (declare (xargs :guard (and (pseudo-term-listp leaves)
                              (pseudo-term-list-listp intp-bags)
                              (pseudo-term-list-listp non-intp-bags))))

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
	    ((and (ts-subsetp leaf-type *ts-rational-acl2-number*)
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
			  intp-bags non-intp-bags)
  (declare (xargs :guard (and (pseudo-term-listp leaves)
                              (pseudo-term-list-listp intp-bags)
                              (pseudo-term-list-listp non-intp-bags))))

; Leaves is a list of leaves from a sum or product; intp-bags and
; non-intp-bags are initially nil.  We scan through the leaves,
; getting their type from mfc-ts, and accumulate the known integers
; (non-integers) into intp-bags (non-intp-bags).  Note that we "bag"
; each leaf individually, and so return two lists of lists of leaves.

  (if (endp leaves)
      (mv intp-bags non-intp-bags)
    (let ((rewriting-result (mfc-rw `(INTEGERP ,(car leaves)) t t mfc state)))
      (cond ((equal rewriting-result *t*)
	     (bag-leaves (cdr leaves) mfc state
			  (cons (list (car leaves)) intp-bags)
			  non-intp-bags))
            ((equal rewriting-result *nil*)
	     (bag-leaves (cdr leaves) mfc state
			  intp-bags
			  (cons (list (car leaves)) non-intp-bags)))
            (t
             (bag-leaves (cdr leaves) mfc state
                         intp-bags non-intp-bags))))))

(defun bag-terms (type-alist bin-op intp-bags non-intp-bags)
  (declare (xargs :guard (and (type-alistp type-alist)
                              (or (equal bin-op 'BINARY-+)
                                  (equal bin-op 'BINARY-*))
                              (pseudo-term-list-listp intp-bags)
                              (pseudo-term-list-listp non-intp-bags))))

; We scan through the type-alist and "bag" those terms known to be an
; integer or a non-integer, accumulating the result into intp-bags
; and non-intp-bags.

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
			  *ts-rational-acl2-number*)
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

  (if (eq (fn-symb term) 'INTEGERP)

      (let ((bin-op (fn-symb (fargn term 1))))
	(if (and (member-eq bin-op '(BINARY-+ BINARY-*))
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
      :rule-classes ((:linear
                      :trigger-terms ((nonnegative-integer-quotient i j))))))

   (local
    (defthm floor-bounds-1
        (implies (and (rationalp x)
                      (rationalp y))
                 (and (< (+ (/ x y) -1)
                         (floor x y))
                      (<= (floor x y)
                          (/ x y))))
      :rule-classes ((:generalize)
                     (:linear :trigger-terms ((floor x y))))))

   (local
    (defthm floor-bounds-2
        (implies (and (rationalp x)
                      (rationalp y)
                      (integerp (/ x y)))
                 (equal (floor x y)
                        (/ x y)))
      :rule-classes ((:generalize)
                     (:linear :trigger-terms ((floor x y))))))

   (local
    (defthm floor-bounds-3
        (implies (and (rationalp x)
                      (rationalp y)
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
                                      (size (1+ (length *actual-primitive-types*))
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
                     (car (bag-leaves x mfc state y z)))
                    (pseudo-term-list-listp
                     (mv-nth 1 (bag-leaves x mfc state y z)))))))

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
                                     intp-bags non-intp-bags)))
                    (pseudo-term-list-listp
                     (mv-nth 1 (bag-terms type-alist bin-op
                                          intp-bags non-intp-bags)))))))

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

 )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(in-theory (disable leaves tree big-tree bag-leaves bag-terms
		    subtract-leaf subtract-bag
		    collect-bags-intp collect-bags-non-intp
		    collect-bags meta-integerp))

(in-theory (disable intp-+ intp-*))
