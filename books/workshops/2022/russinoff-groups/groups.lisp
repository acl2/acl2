(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "projects/quadratic-reciprocity/euclid" :dir :system)

(local (include-book "support"))

;;---------------------------------------------------------------------------------------------------
;; Properties of Lists
;;---------------------------------------------------------------------------------------------------

;; Proper list of distinct non-nil elements:

(defun dlistp (l)
  (if (consp l)
      (and (not (member-equal (car l) (cdr l)))
           (dlistp (cdr l)))
    (null l)))

(defthm dlistp-true-listp
  (implies (dlistp l)
           (true-listp l)))

;; Sublists:

(defun sublistp (l m)
  (if (consp l)
      (and (member-equal (car l) m)
           (sublistp (cdr l) m))
    t))

(defthm member-sublist
  (implies (and (member-equal x l)
                (sublistp l m))
	   (member-equal x m)))

(defthm sublistp-cons
  (implies (sublistp l m)
           (sublistp l (cons x m))))

(defthm sublistp-self
  (sublistp l l))

(defthm sublistp-append
  (implies (and (sublistp l g)
                (sublistp m g))
	   (sublistp (append l m) g)))

(defthmd sublistp-<=-len
  (implies (and (dlistp l)
		(sublistp l m))
	   (<= (len l) (len m))))

(defthmd sublistp-equal-len
  (implies (and (dlistp l)
                (dlistp m)
		(sublistp l m)
		(sublistp m l))
	   (equal (len l) (len m))))

(defthmd len-proper-sublist
  (implies (and (sublistp l m)
                (dlistp l)
		(member-equal x m)
		(not (member-equal x l)))
	   (< (len l) (len m))))

(defthm sublistp-remove1
  (implies (and (sublistp l m)
                (not (member x l)))
	   (sublistp l (remove1-equal x m))))

;; remove1-equal:

(defthm remove1-sublistp
  (sublistp (remove1-equal x l) l))

(defthm dlistp-remove1
  (implies (dlistp l)
           (and (dlistp (remove1-equal x l))
	        (not (member-equal x (remove1-equal x l))))))

(defthm remove1-member
  (implies (not (member-equal x l))
	   (not (member-equal x (remove1 y l)))))

(defthm member-remove1
  (implies (and (member-equal x l)
                (not (equal x y)))
	   (member-equal x (remove1-equal y l))))

(defthm len-remove1-equal
  (implies (member x l)
           (equal (len (remove1-equal x l))
	          (1- (len l)))))

;; Index of x in l:

(defun index (x l)
  (if (consp l)
      (if (equal x (car l))
          0
	(1+ (index x (cdr l))))
    0))

(verify-guards index)

(defthmd index-1-to-1
  (implies (and (member x l)
                (member y l)
		(not (equal x y)))
           (not (= (index x l) (index y l)))))

(defthm nth-ind
  (implies (member x l)
	   (equal (nth (index x l) l)
	          x)))

(defthm ind<len
  (implies (member x l)
           (and (natp (index x l))
	        (< (index x l) (len l)))))

(defthm member-nth
  (implies (and (natp n)
                (< n (len l)))
	   (member (nth n l) l)))

(defthm ind-nth
  (implies (and (dlistp l)
                (natp i)
                (< i (len l)))
	   (equal (index (nth i l) l)
	          i)))

;; Append a list of lists:

(defun append-list (l)
  (if (consp l)
      (append (car l) (append-list (cdr l)))
    ()))

(defthmd member-append-list
  (implies (and (member-equal x l) (member l m))
           (member x (append-list m))))

;; Disjoint lists:
		  
(defun disjointp (l m)
  (if (consp l)
      (and (not (member-equal (car l) m))
           (disjointp (cdr l) m))
    t))

(defthm disjointp-disjoint
  (implies (and (disjointp l m)
                (member-equal x l))
	   (not (member-equal x m))))

(defthm disjointp-cons
  (implies (and (disjointp m l)
                (not (member-equal x m)))
	   (disjointp m (cons x l))))

(defthmd disjointp-symmetric
  (implies (disjointp l m)
           (disjointp m l)))

(defthm dlistp-append
  (implies (and (dlistp l)
                (dlistp m)
		(disjointp l m))
	   (dlistp (append l m))))

(defun disjointp-list (l m)
  (if (consp m)
      (and (disjointp l (car m))
	   (disjointp-list l (cdr m)))
    t))

(defthm disjointp-append-list
  (implies (disjointp-list l m)
           (disjointp l (append-list m))))

(defun disjointp-pairwise (l)
  (if (consp l)
      (and (disjointp-list (car l) (cdr l))
	   (disjointp-pairwise (cdr l)))
    t))

(defun dlistp-list (l)
  (if (consp l)
      (and (dlistp (car l))
           (dlistp-list (cdr l)))
    t))

(defthm dlistp-append-list
  (implies (and (dlistp-list l)
                (disjointp-pairwise l))
	   (dlistp (append-list l))))

;; If two lists are not disjoint, then they have a common member:

(defun common-member (l m)
  (if (consp l)
      (if (member-equal (car l) m)
          (car l)
	(common-member (cdr l) m))
    ()))

(defthm common-member-shared
  (implies (not (disjointp l m))
           (and (member-equal (common-member l m) l)
	        (member-equal (common-member l m) m))))

;; The lemma len-1-1-equal may be functionally instantiated to show that two list have the same length:

(encapsulate (((x) => *) ((y) => *) ((xy *) => *) ((yx *) => *))
  (local (defun x () '(0)))
  (local (defun y () '(0)))
  (local (defun xy (a) (declare (ignore a)) 0))
  (local (defun yx (a) (declare (ignore a)) 0))
  (defthm dlistp-x (dlistp (x)))
  (defthm dlistp-y (dlistp (y)))
  (defthm yx-xy
    (implies (member-equal a (x))
             (and (member-equal (xy a) (y))
	          (equal (yx (xy a)) a))))
  (defthm xy-yx
    (implies (member-equal a (y))
             (and (member-equal (yx a) (x))
	          (equal (xy (yx a)) a)))))

(defthmd len-1-1-equal
  (equal (len (x)) (len (y))))

;; An mxn matrix is a proper list of m proper lists of length n:

(defun matrixp (l m n)
  (declare (xargs :guard (and (natp m) (natp n))))
  (if (consp l)
      (and (posp m)
           (true-listp (car l))
	   (= (len (car l)) n)
	   (matrixp (cdr l) (1- m) n))
    (and (zerop m) (null l))))


;;---------------------------------------------------------------------------------------------------
;; Fimite Groups
;;---------------------------------------------------------------------------------------------------

;; A group of g order n is represented by its operation table, an nxn matrix.  The first row of g,
;; car(g), is a list of the elements of g, beginning with its identity element e = x0:

;;   (x0 x1 x2 ... x(n-1))

;; For 0 <= k < n, the kth row, (nth k g), is

;;   (xkx0 xkx1 xkx2 ... xkx(n-1)).

;; The elements of a group:

(defmacro elts (g) `(car ,g))

;; Group membership:

(defmacro in (x g)
  `(member-equal ,x (elts ,g)))

;; Order of a group:

(defun order (g) (len (elts g)))

;; Left identity element:

(defun e (g) (caar g))

;; index of a group element:

(defmacro ind (x g) `(index ,x (elts ,g)))

;; Group operation:

(defun op-guard (g)
  (declare (xargs :guard t))
  (and (true-listp g) (matrixp g (len (car g)) (len (car g)))))

(defun op (x y g)
  (declare (xargs :guard (op-guard g)))
  (nth (ind y g)
       (nth (ind x g) g)))

;; Note that the left-identity property is immediate:

(defthm group-left-identity
  (implies (in x g)
	   (equal (op (e g) x g)
		  x)))

;; Closure is established by checking every pair of group elements in search of a counterexample:

(defun cy (x l g)
  (if (consp l)
      (if (in (op x (car l) g) g)
	  (cy x (cdr l) g)
	(list (car l)))
    ()))

(defun cxy (l g)
  (if (consp l)
      (let ((cy (cy (car l) (elts g) g)))
        (if cy
	    (cons (car l) cy)
	  (cxy (cdr l) g)))
    ()))

(defun closedp-cex (g) (cxy (elts g) g))

(defun closedp (g) (null (closedp-cex g)))

;; Associativity is established by checking every triple of group elements:

(defun az (x y l g)
  (if (consp l)
      (if (equal (op x (op y (car l) g) g)
                 (op (op x y g) (car l) g))
	  (az x y (cdr l) g)
	(list (car l)))
    ()))

(defun ayz (x l g)
  (if (consp l)
      (let ((az (az x (car l) (elts g) g)))
        (if az
	    (cons (car l) az)
	  (ayz x (cdr l) g)))
    ()))

(defun axyz (l g)
  (if (consp l)
      (let ((ayz (ayz (car l) (elts g) g)))
        (if ayz
	    (cons (car l) ayz)
	  (axyz (cdr l) g)))
    ()))

(defun assocp-cex (g) (axyz (elts g) g))

(defun assocp (g) (null (assocp-cex g)))

;; Left inverse:

(defun inv-aux (x l g)
  (if (consp l)
      (if (equal (op (car l) x g) (e g))
          (car l)
	(inv-aux x (cdr l) g))
    ()))

(defun inv (x g)
  (inv-aux x (elts g) g))

;; The inverse property is checked by a search of (elts g), returning a counterexample or NIL.
;; Thus, we are assuming that NIL is never an element of a group:

(defun check-inverses (l g)
  (if (consp l)
      (if (inv (car l) g)
          (check-inverses (cdr l) g)
	(car l))
    ()))

(defun inv-cex (g) (check-inverses (elts g) g))

(defun inversesp (g) (null (inv-cex g)))

;; The group properties:

(defund groupp (g)
  (and (posp (order g))
       (matrixp g (order g) (order g))
       (dlistp (elts g))
       (not (in () g))
       (closedp g)
       (assocp g)
       (inversesp g)))

(defthm dlistp-elts
  (implies (groupp g)
           (dlistp (elts g))))

(defthm non-nil-elts
  (implies (groupp g)
           (not (in () g))))

(defthm in-e-g
  (implies (groupp g)
           (in (e g) g)))

(defthmd order-pos
  (implies (groupp g)
           (posp (order g))))

;; Commutativity is established by checking every pair of group elements:

(defun ay (x l g)
  (if (consp l)
      (if (equal (op x (car l) g) (op (car l) x g))
	  (ay x (cdr l) g)
	(list (car l)))
    ()))

(defun axy (l g)
  (if (consp l)
      (let ((ay (ay (car l) (elts g) g)))
        (if ay
	    (cons (car l) ay)
	  (axy (cdr l) g)))
    ()))

(defun abelianp-cex (g) (axy (elts g) g))

(defun abelianp (g) (null (abelianp-cex g)))


;;---------------------------------------------------------------------------------------------------
;; Group Properties
;;---------------------------------------------------------------------------------------------------

;; Closure:

(defthm group-closure
  (implies (and (groupp g)
                (in x g)
		(in y g))
	   (in (op x y g) g)))

;; Converse of group-closure, useful in establisshing closure of a proposed group::

(defthm not-closedp-cex
  (implies (and (dlistp (elts g))
                (not (closedp g)))
           (let* ((cex (closedp-cex g))
                  (x (car cex))
	          (y (cadr cex)))
             (and (in x g)
	          (in y g)
	          (not (in (op x y g) g))))))

;; Associativity:

(defthmd group-assoc
  (implies (and (groupp g)
                (in x g)
		(in y g)
		(in z g))
	   (equal (op x (op y z g) g)
	          (op (op x y g) z g))))

;; Converse of group-assoc, useful in establisshing associativity  of a proposed group::

(defthm not-assocp-cex
  (implies (and (dlistp (elts g))
                (not (assocp g)))
           (let* ((cex (assocp-cex g))
                  (x (car cex))
	          (y (cadr cex))
	          (z (caddr cex)))
	     (and (in x g)
	          (in y g)
	          (in z g)
		  (not (equal (op x (op y z g) g)
		              (op (op x y g) z g)))))))

;; Inverses:

(defthm group-left-inverse
  (implies (and (groupp g)
                (in x g))
	   (and (in (inv x g) g)
	        (equal (op (inv x g) x g)
		       (e g)))))

(defthm not-inv-cex
  (implies (and (dlistp (elts g))
                (not (in () g))
                (not (inversesp g)))
	   (and (in (inv-cex g) g)
	        (implies (in y g) (not (equal (op y (inv-cex g) g) (e g)))))))
			
;; Abelian groups:

(defthm group-abelianp
  (implies (and (groupp g)
                (abelianp g)
                (in x g)
		(in y g))
	   (equal (op x y g) (op y x g)))
  :hints (("Goal" :in-theory (enable groupp))))

;; Converse of group-closure:

(defthm not-abelianp-cex
  (implies (and (dlistp (elts g))
                (not (abelianp g)))
           (let* ((cex (abelianp-cex g))
                  (x (car cex))
	          (y (cadr cex)))
             (and (in x g)
	          (in y g)
	          (not (equal (op x y g) (op y x g)))))))

;; Some basic properties derived from the axioms:

(defthm idem-e
  (implies (and (groupp g)
		(in x g)
		(equal (op x x g) x))
	   (equal x (e g)))
  :rule-classes ())

(defthm group-right-inverse
  (implies (and (groupp g)
                (in x g))
	   (and (in (inv x g) g)
                (equal (op x (inv x g) g)
	               (e g)))))

(defthm group-right-identity
  (implies (and (groupp g)
                (in x g))
	   (equal (op x (e g) g)
	          x)))

(defthm left-cancel
  (implies (and (groupp g)
                (in x g) (in y g) (in a g)
		(equal (op a x g) (op a y g)))
	   (equal x y))
  :rule-classes ())

(defthm right-cancel
  (implies (and (groupp g)
                (in x g) (in y g) (in a g)
		(equal (op x a g) (op y a g)))
	   (equal x y))
  :rule-classes ())

(defthm inv-inv
  (implies (and (groupp g)
                (in x g))
           (equal (inv (inv x g) g)
	          x)))

(defthm inv-unique
  (implies (and (groupp g)
                (in x g)
		(in y g)
		(equal (op y x g) (e g)))
	   (equal (inv x g) y)))

(defthm inv-e
  (implies (groupp g)
           (equal (inv (e g) g) (e g)))
  :hints (("Goal" :use ((:instance inv-unique (x (e g)) (y (e g)))))))

(defthmd prod-inv
  (implies (and (groupp g)
                (in x g)
		(in y g))
	   (equal (inv (op x y g) g)
	          (op (inv y g) (inv x g) g))))


;;---------------------------------------------------------------------------------------------------
;; Subgroups
;;---------------------------------------------------------------------------------------------------

;; Subgrouphood is established by checking that the operations agree on every pair of elements:

(defun sy (x l h g)
  (if (consp l)
      (if (equal (op x (car l) h) (op x (car l) g))
	  (sy x (cdr l) h g)
	(list (car l)))
    ()))

(defun sxy (l h g)
  (if (consp l)
      (let ((sy (sy (car l) (elts h) h g)))
        (if sy
	    (cons (car l) sy)
	  (sxy (cdr l) h g)))
    ()))

(defun subgroupp-cex (h g) (sxy (elts h) h g))

(defun subgroupp (h g)
  (and (groupp g)
       (groupp h)
       (sublistp (elts h) (elts g))
       (not (subgroupp-cex h g))))

(defthm subgroupp-groupp
  (implies (subgroupp h g)
           (and (groupp g) (groupp h))))

(defthm subgroupp-sublistp
  (implies (subgroupp h g)
           (sublistp (elts h) (elts g))))

(defthm subgroupp-subsetp
  (implies (and (subgroupp h g)
		(in x h))
	   (in x g)))

(defthm subgroup-op
  (implies (and (subgroupp h g)
                (in x h)
		(in y h))
	   (equal (op x y h) (op x y g))))

;; Converse of subgroup-group-op

(defthm not-subgroupp-cex
  (implies (and (groupp g)
		(groupp h)
		(sublistp (elts h) (elts g))
		(not (subgroupp h g)))
           (let* ((cex (subgroupp-cex h g))
                  (x (car cex))
	          (y (cadr cex)))
             (and (in x h)
	          (in y h)
	          (not (equal (op x y h) (op x y g)))))))

(defthm subgroup-e
  (implies (subgroupp h g)
	   (equal (e h) (e g)))
  :hints (("Goal" :use ((:instance group-left-identity (x (e h)))
			(:instance group-left-identity (x (e h)) (g h))
			(:instance right-cancel (a (e h)) (x (e g)) (y (e h)))))))

(defthm subgroup-inv
  (implies (and (subgroupp h g)
		(in x h))
           (equal (inv x h) (inv x g))))

(defthm abelian-subgroup
  (implies (and (subgroupp h g)
                (abelianp g))
	   (abelianp h)))

;; Generate a subgroup from a list of its elements:

(defun oplist (x m g)
  (if (consp m)
      (cons (op x (car m) g)
	    (oplist x (cdr m) g))
    ()))

(defun subgroup-aux (l m g)
  (if (consp l)
      (cons (oplist (car l) m g)
            (subgroup-aux (cdr l) m g))
    ()))

(defun subgroup (l g)
  (subgroup-aux l l g))


;;---------------------------------------------------------------------------------------------------
;; Parametrized Groups
;;---------------------------------------------------------------------------------------------------

;; The macro defgroup is based on the following encapsulation, which constrains three functions
;; representing the list of elements of a group, the group operation, and its inverse operator.

(encapsulate (((glist) => *) ((gop * *) => *) ((ginv *) => *))
  (local (defun glist () (list 0)))
  (local (defun gop (x y) (+ x y)))
  (local (defun ginv (x) x))
  (defthm consp-glist (consp (glist)))
  (defthm dlistp-glist (dlistp (glist)))
  (defthm g-non-nil (not (member-equal () (glist))))
  (defthm g-identity
    (implies (member-equal x (glist))
             (equal (gop (car (glist)) x)
	            x)))
  (defthm g-closed
    (implies (and (member-equal x (glist))
                  (member-equal y (glist)))
	     (member-equal (gop x y) (glist))))
  (defthm g-assoc
    (implies (and (member-equal x (glist))
                  (member-equal y (glist))
		  (member-equal z (glist)))
	     (equal (gop x (gop y z))
	            (gop (gop x y) z))))
  (defthm g-inverse
    (implies (member-equal x (glist))
             (and (member-equal (ginv x) (glist))
	          (equal (gop (ginv x) x) (car (glist)))))))

;; Definition of the group g:

(defun g-row (x m)
  (if (consp m)
      (cons (gop x (car m))
            (g-row x (cdr m)))
    ()))

(defun g-aux (l m)
  (if (consp l)
      (cons (g-row (car l) m)
            (g-aux (cdr l) m))
    ()))

(defun g () (let ((l (glist))) (g-aux l l)))

;; Derived properties of g:

(defthm glist-elts
  (equal (elts (g))
         (glist)))
	 
(defthm op-g-rewrite
  (implies (and (in x (g))
		(in y (g)))
           (equal (op x y (g))
	          (gop x y))))

(defthm groupp-g
  (groupp (g)))

(defthmd inv-g-rewrite
  (implies (in x (g))
	   (equal (inv x (g)) (ginv x))))

;; The macro defgroup generates families of groups through functional instantiation of the above results.

;; Parameters of defgroup:

;; name: name of the generated group
;; args: a list of parameters
;; cond: a predicate that must be satisfied by args
;; elts: a list of the group elements as a function of args
;; op:   the product of group elements x and y as a function of x, y, and args
;; inv:  the inverse of x as a function of x and args

;; Prior to a call of defgroup, 7 rewrite rules corresponding to the theorems of the encapsulation must
;; be proved, as illustrated in the examples below.

(defmacro defgroup (name args cond elts op inv)
  (let ((op-name (intern$ (concatenate 'string "OP-" (symbol-name name)) "RTL"))
        (name-row (intern$ (concatenate 'string (symbol-name name) "-ROW") "RTL"))
	(name-aux (intern$ (concatenate 'string (symbol-name name) "-AUX") "RTL"))
	(groupp-name (intern$ (concatenate 'string "GROUPP-" (symbol-name name)) "RTL"))
	(name-elts (intern$ (concatenate 'string (symbol-name name) "-ELTS") "RTL"))
	(name-op-rewrite (intern$ (concatenate 'string (symbol-name name) "-OP-REWRITE") "RTL"))
	(name-inv-rewrite (intern$ (concatenate 'string (symbol-name name) "-INV-REWRITE") "RTL")))
    `(encapsulate ()
       (set-ignore-ok t)
       (set-irrelevant-formals-ok t)
       (defun ,op-name (x y ,@args) ,op)
       (defun ,name-row (x m ,@args)
         (if (consp m)
             (cons (,op-name x (car m) ,@args)
	           (,name-row x (cdr m) ,@args))
	   ()))
       (defun ,name-aux (l m ,@args)
         (if (consp l)
             (cons (,name-row (car l) m ,@args)
	           (,name-aux (cdr l) m ,@args))
           ()))
       (defun ,name ,args
         (let ((l ,elts))
           (,name-aux l l ,@args)))
       (defthm ,groupp-name
         (implies ,cond (groupp (,name ,@args)))
	 :hints (("Goal" :use ((:functional-instance groupp-g
	                         (glist (lambda () (if ,cond ,elts (glist))))
			         (gop (lambda (x y) (if ,cond ,op (gop x y))))
			         (ginv (lambda (x) (if ,cond ,inv (ginv x))))
			         (g-row (lambda (x m) (if ,cond (,name-row x m ,@args) (g-row x m))))
			         (g-aux (lambda (l m) (if ,cond (,name-aux l m ,@args) (g-aux l m))))
			         (g (lambda () (if ,cond (,name ,@args) (g)))))))))
       (defthm ,name-elts
         (implies ,cond
	          (equal (elts (,name ,@args))
	                 ,elts))
	 :hints (("Goal" :use ((:functional-instance glist-elts
	                         (glist (lambda () (if ,cond ,elts (glist))))
			         (gop (lambda (x y) (if ,cond ,op (gop x y))))
			         (ginv (lambda (x) (if ,cond ,inv (ginv x))))
			         (g-row (lambda (x m) (if ,cond (,name-row x m ,@args) (g-row x m))))
			         (g-aux (lambda (l m) (if ,cond (,name-aux l m ,@args) (g-aux l m))))
			         (g (lambda () (if ,cond (,name ,@args) (g)))))))))
       (defthm ,name-op-rewrite
         (implies (and ,cond
	               (in x (,name ,@args))
	       	       (in y (,name ,@args)))
                  (equal (op x y (,name ,@args))
	                 ,op))
	 :hints (("Goal" :use ((:functional-instance op-g-rewrite
	                         (glist (lambda () (if ,cond ,elts (glist))))
			         (gop (lambda (x y) (if ,cond ,op (gop x y))))
			         (ginv (lambda (x) (if ,cond ,inv (ginv x))))
			         (g-row (lambda (x m) (if ,cond (,name-row x m ,@args) (g-row x m))))
			         (g-aux (lambda (l m) (if ,cond (,name-aux l m ,@args) (g-aux l m))))
			         (g (lambda () (if ,cond (,name ,@args) (g)))))))))
       (defthm ,name-inv-rewrite
         (implies (and ,cond
	               (in x (,name ,@args)))
                  (equal (inv x (,name ,@args))
	                 ,inv))
	 :hints (("Goal" :use ((:functional-instance inv-g-rewrite
	                         (glist (lambda () (if ,cond ,elts (glist))))
			         (gop (lambda (x y) (if ,cond ,op (gop x y))))
			         (ginv (lambda (x) (if ,cond ,inv (ginv x))))
			         (g-row (lambda (x m) (if ,cond (,name-row x m ,@args) (g-row x m))))
			         (g-aux (lambda (l m) (if ,cond (,name-aux l m ,@args) (g-aux l m))))
			         (g (lambda () (if ,cond (,name ,@args) (g)))))))))
      (in-theory (disable ,name)))))

;; A version of defgroup that defines a family of groups but does not prove anything:

(defmacro defgroup-light (name args elts op)
  (let ((op-name (intern$ (concatenate 'string "OP-" (symbol-name name)) "RTL"))
        (name-row (intern$ (concatenate 'string (symbol-name name) "-ROW") "RTL"))
	(name-aux (intern$ (concatenate 'string (symbol-name name) "-AUX") "RTL")))
    `(encapsulate ()
       (defun ,op-name (x y ,@args) ,op)
       (defun ,name-row (x m ,@args)
         (if (consp m)
             (cons (,op-name x (car m) ,@args)
	           (,name-row x (cdr m) ,@args))
	   ()))
       (defun ,name-aux (l m ,@args)
         (if (consp l)
             (cons (,name-row (car l) m ,@args)
	           (,name-aux (cdr l) m ,@args))
           ()))
       (defun ,name ,args
         (let ((l ,elts))
           (,name-aux l l ,@args))))))


;;---------------------------------------------------------------------------------------------------
;; Integers Modulo n
;;---------------------------------------------------------------------------------------------------

;; Initial segment of natural numbers:

(defun ninit (n)
  (if (zp n)
      ()
    (append (ninit (1- n)) (list (1- n)))))

(defthm consp-ninit
  (implies (posp n)
           (consp (ninit n))))

(defthmd member-ninit
  (implies (posp n)
           (iff (member-equal x (ninit n))
	        (and (natp x)
	             (< x n)))))

(defthm dlistp-ninit
  (implies (posp n)
           (dlistp (ninit n))))

(defthm ninit-non-nil
  (implies (posp n)
           (not (member-equal () (ninit n)))))

(defthm car-ninit
  (implies (posp n)
           (equal (car (ninit n)) 0)))

;; Additive group of integers modulo n:

(defun z+-op (x y n) (mod (+ x y) n))

(defun z+-inv (x n) (mod (- x) n))

(defthm z+-identity
  (implies (and (posp n)
                (member-equal x (ninit n)))
	   (equal (z+-op 0 x n)
	          x)))

(defthm z+-closed
  (implies (and (posp n)
                (member-equal x (ninit n))
                (member-equal y (ninit n)))
           (member-equal (z+-op x y n) (ninit n))))

(defthm z+-assoc
  (implies (and (posp n)
                (member-equal x (ninit n))
                (member-equal y (ninit n))
                (member-equal z (ninit n)))
	   (equal (z+-op x (z+-op y z n) n)
	          (z+-op (z+-op x y n) z n))))

(defthm z+-inverse
  (implies (and (posp n)
                (member-equal x (ninit n)))
	   (and (member-equal (z+-inv x n) (ninit n))
	        (equal (z+-op (z+-inv x n) x n) 0))))

(defgroup z+ (n)
  (posp n)
  (ninit n)
  (z+-op x y n)
  (z+-inv x n))

;; Multiplicative group of integers modulo n:

(defun rel-primes-aux (k n)
  (if (zp k)
      ()
    (if (= (g-c-d k n) 1)
        (append (rel-primes-aux (1- k) n) (list k))
      (rel-primes-aux (1- k) n))))

(defun rel-primes (n)
  (rel-primes-aux n n))

(defthmd member-rel-primes
  (implies (and (posp n) (> n 1))
	   (iff (member k (rel-primes n))
	        (and (posp k)
		     (< k n)
		     (= (g-c-d k n) 1))))
  :hints (("Goal" :in-theory (disable member-rel-primes-aux-<=) :use (member-rel-primes-1))))

(defthm consp-rel-primes
  (implies (posp n)
           (consp (rel-primes n)))
  :hints (("Goal" :in-theory (disable rel-primes) :use (member-1-rel-primes))))

(defthm dlistp-rel-primes
  (implies (posp n)
           (dlistp (rel-primes n))))

(defthm rel-primes-non-nil
  (implies (posp n)
           (not (member-equal () (rel-primes n)))))

(defthm car-rel-primes
  (implies (posp n)
           (equal (car (rel-primes n)) 1)))

(in-theory (disable rel-primes))

(defun z*-op (x y n) (mod (* x y) n))

(defthm z*-identity
  (implies (and (and (posp n) (> n 1))
                (member-equal x (rel-primes n)))
	   (equal (z*-op 1 x n)
	          x))
  :hints (("Goal" :use ((:instance member-rel-primes (k x))))))

(defthm g-c-d-0
  (implies (posp n)
           (equal (g-c-d 0 n) n))
  :hints (("Goal" :in-theory (enable g-c-d))))

(defthm z*-closed
  (implies (and (posp n) (> n 1)
                (member-equal x (rel-primes n))
                (member-equal y (rel-primes n)))
           (member-equal (z*-op x y n) (rel-primes n)))
  :hints (("Goal" :use ((:instance member-rel-primes (k x))
                        (:instance member-rel-primes (k y))
                        (:instance member-rel-primes (k (z*-op x y n)))
			(:instance mod-prod-rel-prime (a x) (b y))
			(:instance g-c-d-divides (x (* x y)) (y n))))))

(defthm z*-assoc
  (implies (and (posp n)
                (member-equal x (rel-primes n))
                (member-equal y (rel-primes n))
                (member-equal z (rel-primes n)))
	   (equal (z*-op x (z*-op y z n) n)
	          (z*-op (z*-op x y n) z n)))
  :hints (("Goal" :use ((:instance member-rel-primes (k x))
                        (:instance member-rel-primes (k y))
                        (:instance member-rel-primes (k z))
			(:instance mod-mod-times (b x) (a (* y z)))
			(:instance mod-mod-times (b z) (a (* x y)))))))

;; The definition of z*-inv is based on the following lemma from books/projects/quadratic-reciprocity/euclid.lisp"

(defthm g-c-d-linear-combination
    (implies (and (integerp x)
		  (integerp y))
	     (= (+ (* (r-int x y) x)
		   (* (s-int x y) y))
		(g-c-d x y)))
    :rule-classes ())

(defun z*-inv (x n) (mod (r-int x n) n))

(defthm z*-inverse
  (implies (and (posp n) (> n 1)
                (member-equal x (rel-primes n)))
	   (and (member-equal (z*-inv x n) (rel-primes n))
	        (equal (z*-op (z*-inv x n) x n) 1)))
  :hints (("Goal" :use (z*-inverse-1 z*-inverse-5))))

(in-theory (disable z*-op z*-inv))

(defgroup z* (n)
  (and (posp n) (> n 1))
  (rel-primes n)
  (z*-op x y n)
  (z*-inv x n))

;; Memoization of op speeds it up considerably:

(memoize 'op)

(memoize 'op-guard)

(defthm assocp-z*-500
  (assocp (z* 500)))


;;---------------------------------------------------------------------------------------------------
;; Permutation Groups
;;---------------------------------------------------------------------------------------------------

;; A list of all permutations of a list:

(defun conses (x l)
  (if (consp l)
      (cons (cons x (car l)) (conses x (cdr l)))
    ()))

(defthm count-remove
  (implies (member-equal x l)
           (< (acl2-count (remove-equal x l))
	      (acl2-count l)))
  :rule-classes (:linear))
	   
(mutual-recursion

  (defun perms-aux (l m)
    (declare (xargs :measure (list (acl2-count m) (acl2-count l) 0)))
    (if (and (consp l) (member (car l) m))
        (append (conses (car l) (perms (remove-equal (car l) m)))
                (perms-aux (cdr l) m))
      ()))

  (defun perms (m)
    (declare (xargs :measure (list (acl2-count m) (acl2-count m) 1)))
    (if (consp m)
        (perms-aux m m)
      (list ())))
)

;; We focus on permutations of (0 1 ... n).

(defund slist (n) (perms (ninit n)))

;; The set of all such permutations form a group under the operation of composition,
;; which is defined as follows:

(defun comp-perm-aux (p r l)
  (if (consp l)
      (cons (nth (nth (car l) r) p)
            (comp-perm-aux p r (cdr l)))
    ()))

(defun comp-perm (p r n)
  (comp-perm-aux p r (ninit n)))

;; The inverse of a permutation:

(defun inv-perm-aux (p l)
  (if (consp l)
      (cons (index (car l) p)
            (inv-perm-aux p (cdr l)))
    ()))

(defun inv-perm (p n)
  (inv-perm-aux p (ninit n)))

(in-theory (disable comp-perm inv-perm))

;; Some work is needed here:
#|
(defthm consp-slist
  (implies (posp n)
           (consp (slist n))))

(defthm dlistp-slist
  (implies (posp n)
           (dlistp (slist n))))

(defthm slist-non-nil
  (implies (posp n)
           (not (member-equal () (slist n)))))

(defthm car-slist
  (implies (posp n)
           (equal (car (slist n)) (ninit n))))

(defthm sym-identity
  (implies (and (posp n)
                (member-equal x (slist n)))
	   (equal (comp-perm (ninit n) x n)
	          x)))

(defthm sym-closed
  (implies (and (posp n)
                (member-equal x (slist n))
                (member-equal y (slist n)))
           (member-equal (comp-perm x y n) (slist n))))

(defthm sym-assoc
  (implies (and (posp n)
                (member-equal x (slist n))
                (member-equal y (slist n))
                (member-equal z (slist n)))
	   (equal (comp-perm x (comp-perm y z n) n)
	          (comp-perm (comp-perm x y n) z n))))

(defthm sym-inverse
  (implies (and (posp n)
                (member-equal x (slist n)))
	   (and (member-equal (inv-perm x n) (slist n))
	        (equal (comp-perm (inv-perm x n) x n) (ninit n)))))

(defgroup sym (n)
  (posp n)
  (slist n)
  (comp-perm x y n)
  (inv-perm x n))
|#

;; So for now, we'll go light:

(defgroup-light sym (n)
  (slist n)
  (comp-perm x y n))

(defun s3 () (sym 3))

(defun s4 () (sym 4))

(defun s5 () (sym 5))

;; Representation of a permutation as a product of cycles

(defun cyc-aux (next done rest perm)
  (if (consp rest)
      (if (equal (nth (car rest) perm) (car rest))
          (cyc-aux next
		   done
		   (cdr rest)
	    	   perm)
        (if (member (nth (car next) perm) next)
            (cyc-aux (list (car rest))
                     (append done (list (reverse next)))
		     (cdr rest)
	    	     perm)
	  (if (member (nth (car next) perm) rest)
	      (cyc-aux (cons (nth (car next) perm) next)
	               done
	               (remove1-equal (nth (car next) perm) rest)
	               perm)
	    ())))
    (append done (list (reverse next)))))

(defun cyc (perm)
  (cyc-aux (list 0) () (cdr (ninit (len perm))) perm))

;; A permutation is even or odd according to whether it can be represented as a product of an even or
;; odd number of transpositions.  This may be determined by examining its cycle structure:

(defun even-cyc (cyc)
  (if (consp cyc)
      (if (evenp (len (car cyc)))
          (not (even-cyc (cdr cyc)))
	(even-cyc (cdr cyc)))
    t))

(defun even-perm (perm)
  (even-cyc (cyc perm)))

(defun even-perms (l)
  (if (consp l)
      (if (even-perm (car  l))
          (cons (car l) (even-perms (cdr l)))
	(even-perms (cdr l)))
    ()))

;; Alternating group:

;; Some work is required here:
#|
(defgroup alt (n)
  (posp n)
  (even-perms (slist n))
  (comp-perm x y n)
  (inv-perm x n))
|#

;; So for now, we'll go light:

(defgroup-light alt (n)
  (even-perms (slist n))
  (comp-perm x y n))  

(defun a3 () (alt 3))

(defun a4 () (alt 4))

(defun a5 () (alt 5))


;;---------------------------------------------------------------------------------------------------
;; Ordered Lists of Group Elements
;;---------------------------------------------------------------------------------------------------

;; A list of elements of G ordered according to group index:

(defun ordp (l g)
  (if (consp l)
      (and (in (car l) g)
           (if (consp (cdr l))
	       (and (< (ind (car l) g) (ind (cadr l) g))
	            (ordp (cdr l) g))
	     (null (cdr l))))
    (null l)))

(defthmd car-ordp-minimal
  (implies (and (ordp l g)
                (member x (cdr l)))
	   (> (ind x g) (ind (car l) g))))

(defthm ordp-dlistp
  (implies (ordp l g)
           (dlistp l)))

(defthm ordp-equal
  (implies (and (ordp x g)
                (ordp y g)
		(sublistp x y)
		(sublistp y x))
	   (equal x y))
  :rule-classes ())


;;---------------------------------------------------------------------------------------------------
;; Cosets
;;---------------------------------------------------------------------------------------------------

;; Informally, the left coset of a subgroup H of G determined by an element x of G is the set of
;; elements of G of the form xh, where h is in H.  In our formalization, we define a left coset
;; to be the ordered list of these elements: 

(defun insert (x l g)
  (if (consp l)
      (if (equal x (car l))
          l
	(if (< (ind x g) (ind (car l) g))
	    (cons x l)
	  (cons (car l) (insert x (cdr l) g))))
    (list x)))

(defun lcoset-aux (x h g)
  (if (consp h)
      (insert (op x (car h) g)
              (lcoset-aux x (cdr h) g)
	      g)
    ()))

(defund lcoset (x h g)
  (lcoset-aux x (elts h) g))

;; A coset is a list of group elements:

(defthmd sublistp-lcoset-g
  (implies (and (subgroupp h g)
		(in x g))
	   (sublistp (lcoset x h g) (elts g))))

(defthm member-lcoset-g
  (implies (and (subgroupp h g)
		(in x g)
		(member-equal y (lcoset x h g)))
	   (in y g)))

;; A coset is an ordered list of group elements:

(defthm ordp-lcoset
  (implies (and (subgroupp h g)
		(in x g))
	   (ordp (lcoset x h g) g)))

;;  The length of a coset is the order of the subgroup:

(defthm len-lcoset
  (implies (and (subgroupp h g)
		(in x g))
	   (equal (len (lcoset x h g))
		  (order h))))

;; A characterization of coset elements:

(defthm member-lcoset
  (implies (and (subgroupp h g)
		(in x g)
		(in y h))
	   (member-equal (op x y g) (lcoset x h g))))

(defthmd member-lcoset-iff
  (implies (and (subgroupp h g)
		(in x g)
		(in y g))
	   (iff (member-equal y (lcoset x h g))
	        (in (op (inv x g) y g) h))))

(defthm member-self-lcoset
  (implies (and (subgroupp h g)
		(in x g))
	   (member-equal x (lcoset x h g))))

;; Intersecting cosets are equal:

(defthm member-lcoset-symmetry
  (implies (and (subgroupp h g)
		(in x g)
		(in y g))
	   (implies (member-equal y (lcoset x h g))
	            (member-equal x (lcoset y h g)))))

(defthm lcosets-intersect
  (implies (and (subgroupp h g)
		(in x g)
		(in y g)
		(member-equal a (lcoset x h g))
		(member-equal a (lcoset y h g))
		(member-equal b (lcoset x h g)))
	   (member-equal b (lcoset y h g))))
			
(defthm sublistp-lcoset
  (implies (and (subgroupp h g)
		(in x g)
		(in y g)
		(member-equal y (lcoset x h g)))
	   (sublistp (lcoset y h g) (lcoset x h g))))
	   
(defthmd equal-lcoset
  (implies (and (subgroupp h g)
		(in x g)
		(in y g)
		(member-equal y (lcoset x h g)))
	   (equal (lcoset y h g) (lcoset x h g))))

(defthmd equal-lcoset-2
  (implies (and (subgroupp h g)
		(in x1 g)
		(in x2 g)
		(in y g)
		(member-equal y (lcoset x1 h g))
		(member-equal y (lcoset x2 h g)))
	   (equal (lcoset x1 h g) (lcoset x2 h g))))
	   

;;---------------------------------------------------------------------------------------------------
;; Lagrange's Theorem
;;---------------------------------------------------------------------------------------------------

;; A list of all left cosets of H:

(defun member-list (x l)
  (if (consp l)
      (or (member-equal x (car l))
	  (member-list x (cdr l)))
    ()))

(defun lcosets-aux (l h g)
  (if (consp l)
      (let ((cosets (lcosets-aux (cdr l) h g)))
	(if (member-list (car l) cosets)
	    cosets
	  (cons (lcoset (car l) h g) cosets)))
    ()))

(defund lcosets (h g)
  (lcosets-aux (elts g) h g))

(defun subgroup-index (h g) (len (lcosets h g)))

;; lcosets contains every lcoset:

(defthm member-lcoset-cosets
  (implies (and (subgroupp h g)
                (in x g))
	   (member (lcoset x h g) (lcosets h g))))

;; lcosets are distinct and non-nil:

(defthm member-member-list
  (implies (and (consp x) (member x l))
           (member-list (car x) l)))

(defthm dlistp-lcosets
  (implies (subgroupp h g)
           (dlistp (lcosets h g))))

(defthm lcosets-non-nil
  (implies (subgroupp h g)
           (not (member-equal () (lcosets h g)))))

;; The length of (append-list (lcosets h g)):

(defthm len-lcosets
  (implies (subgroupp h g)
	   (equal (len (append-list (lcosets h g)))
	          (* (order h) (subgroup-index h g)))))

;; append-list(lcosets(h,g)) is a dlist:

(defthm lcoset-car
  (implies (and (subgroupp h g)
		(in x g))
	   (and (in (car (lcoset x h g)) g)
	        (equal (lcoset (car (lcoset x h g)) h g)
	               (lcoset x h g)))))

(defthmd lcosets-cars
  (implies (and (subgroupp h g)
		(member c (lcosets h g)))
	   (and (in (car c ) g)
		(equal (lcoset (car c) h g)
		       c))))
	          
(defthm lcosets-disjointp-pairwise
  (implies (subgroupp h g)
	   (disjointp-pairwise (lcosets h g))))

(defthm dlistp-list-lcosets
  (implies (subgroupp h g)
	   (dlistp-list (lcosets h g))))

(defthm dlistp-append-list-lcosets
  (implies (subgroupp h g)
	   (dlistp (append-list (lcosets h g)))))

;; elts(g) is a sublist of (append-list (lcosets h g)):

(defthm sublistp-elts-lcosets
  (implies (subgroupp h g)
	   (sublistp (elts g) (append-list (lcosets h g)))))

;; (append-list (lcosets h g)) is a sublist of (elts g):

(defthm sublistp-lcosets-elts
  (implies (subgroupp h g)
	   (sublistp (append-list (lcosets h g))
	             (elts g))))

;; Thus, the two lists have the same length, and Lagrange's Theorem follows:

(defthmd len-append-list-lcosets
  (implies (subgroupp h g)
	   (equal (len (append-list (lcosets h g)))
	          (order g))))

(defthmd lagrange
  (implies (subgroupp h g)
           (equal (* (order h) (subgroup-index h g))
                  (order g))))


;;---------------------------------------------------------------------------------------------------
;; Normal Subgroups and Quotient Groups
;;---------------------------------------------------------------------------------------------------

;; The conjugate of x by a:

(defund conj (x a g)
  (op (op (inv a g) x g) a g))

(defthmd conj-commute
  (implies (and (groupp g)
                (in x g)
		(in y g))
	   (iff (equal (conj x y g) x)
	        (equal (op x y g) (op y x g)))))

;; h is normal in g if every conjugate of an element of h by an element of g is in h:

(defun normalp-elt (x l h g)
  (if (consp l)
      (and (in (conj x (car l) g) h)
           (normalp-elt x (cdr l) h g))
    t))

(defun normalp-aux (l h g)
  (if (consp l)
      (and (normalp-elt (car l) (elts g) h g)
           (normalp-aux (cdr l) h g))
    t))

(defun normalp (h g)
  (and (subgroupp h g)
       (normalp-aux (elts h) h g)))

(defthm normalp-subgroupp
  (implies (normalp h g)
           (subgroupp h g)))

(defthm normalp-groupp
  (implies (normalp h g)
           (and (groupp h) (groupp g))))

(defthm normalp-conj
  (implies (and (normalp h g)
                (in x h)
		(in y g))
	   (in (conj x y g) h)))

;; If h is not normal in g, then we can construct a counterexample to the definition:

(defun normalp-elt-cex (x l h g)
  (if (consp l)
      (if (in (conj x (car l) g) h)
          (normalp-elt-cex x (cdr l) h g)
	(car l))
    ()))

(defun normalp-aux-cex (l h g)
  (if (consp l)
      (if (normalp-elt (car l) (elts g) h g)
          (normalp-aux-cex (cdr l) h g)
	(list (car l) (normalp-elt-cex (car l) (elts g) h g)))
    ()))

(defun normalp-cex (h g)
  (normalp-aux-cex (elts h) h g))

(defthmd not-normalp-cex
  (let* ((cex (normalp-cex h g))
         (x (car cex))
	 (y (cadr cex)))
    (implies (and (subgroupp h g)
                  (not (normalp h g)))
	     (and (in x h)
	          (in y g)
		  (not (in (conj x y g) h))))))

;; A subgroup of an abelian group is normal:
  
(defthm abelianp-normalp
  (implies (and (abelianp g)
		(subgroupp h g))
	   (normalp h g)))

;; We shall use defgroup to define quotient groups.

;; Identity element of the quotient group:

(defun qe (h g) (lcoset (e g) h g))

(defthm car-qe
  (implies (normalp h g)
           (equal (car (lcoset (e g) h g))
	          (e g))))

(defthm qe-exists
  (implies (subgroupp h g)
           (member-equal (qe h g) (lcosets h g))))


;; The element list of the quotient group is the coset list with the identity moved to the front:

(defun qlist (h g)
  (cons (qe h g) (remove1-equal (qe h g) (lcosets h g))))

(defthm len-qlist
  (implies (normalp h g)
           (equal (len (qlist h g)) (subgroup-index h g))))

(defthm member-qlist-car
  (implies (and (normalp h g)
                (member x (qlist h g)))
	   (in (car x) g)))

(defthmd car-member-qlist
  (implies (and (normalp h g)
                (member x (qlist h g)))
	   (and (in (car x) g)
	        (equal (lcoset (car x) h g)
		       x))))

(defthm member-lcoset-qlist
  (implies (and (normalp h g)
                (member x (lcosets h g)))
           (member x (qlist h g))))

(defthm qe-car
  (equal (car (qlist h g))
         (qe h g)))

(defthm consp-qlist
  (consp (qlist h g)))


(defthm dlistp-qlist
  (implies (normalp h g)
           (dlistp (qlist h g))))

(defthm qlist-non-nil
  (implies (normalp h g)
           (not (member-equal () (qlist h g)))))

;; The quotient group operation and inverse operator:

(defun qop (x y h g)
  (lcoset (op (car x) (car y) g) h g))

(defun qinv (x h g)
  (lcoset (inv (car x) g) h g))

(defthm op-qop
  (implies (and (normalp h g)
                (member-equal x (qlist h g)) (member-equal y (qlist h g))
		(member-equal a x) (member-equal b y))
	   (member-equal (op a b g) (qop x y h g))))

(defthm q-identity
  (implies (and (normalp h g)
                (member-equal x (qlist h g)))
	   (equal (qop (qe h g) x h g)
	          x)))

(defthm q-closed
  (implies (and (normalp h g)
                (member-equal x (qlist h g))
                (member-equal y (qlist h g)))
           (member-equal (qop x y h g) (qlist h g))))

(defthm q-assoc
  (implies (and (normalp h g)
                (member-equal x (qlist h g))
                (member-equal y (qlist h g))
                (member-equal z (qlist h g)))
	   (equal (qop x (qop y z h g) h g)
	          (qop (qop x y h g) z h g))))

(defthm q-inverse
  (implies (and (normalp h g)
                (member-equal x (qlist h g)))
	   (and (member-equal (qinv x h g) (qlist h g))
	        (equal (qop (qinv x h g) x h g) (qe h g)))))
  
;; Quotient group:

(defgroup quotient (g h)
  (normalp h g)
  (qlist h g)
  (qop x y h g)
  (qinv x h g))

(defthm order-quotient
  (implies (normalp h g)
           (equal (order (quotient g h))
	          (subgroup-index h g))))

(defthm quotient-e
  (implies (normalp h g)
           (equal (e (quotient g h))
	          (lcoset (e g) h g))))

(defthm abelian-quotient
  (implies (and (subgroupp h g)
                (abelianp g))
	   (abelianp (quotient g h))))

;; In order to manage concrete quotient groups, the function quot remanes the elements of a quotient
;; group by replacing each coset with its car:

(defun collect-cars-aux (l)
  (if (consp l)
      (cons (caar l) (collect-cars-aux (cdr l)))
    ()))

(defun collect-cars (l)
  (if (consp l)
      (cons (collect-cars-aux (car l)) (collect-cars (cdr l)))
    ()))

(defun quot (g h)
  (collect-cars (quotient g h)))


;;----------------------------------------------------------------------------------------------------------
;; Parametrized Subgroups
;;----------------------------------------------------------------------------------------------------------

;; The macro defsubgroup calls defgroup to define a subgroup of a given group g, which is represented
;; by the last element of args.  The last two arguments of defgroup are not supplied to defsubgroup,
;; since they are always (op x y g) and (inv x g).  Before calling defsubgroup, the following rewrite
;; rule shoud be proved:
;;   `(implies ,cond (dlistp ,elts))
;;   `(implies ,cond (sublistp ,elts (elts ,(car (last args)))))
;;   `(implies ,cond (consp ,elts))
;;   `(implies ,cond (equal (car ,elts) (e ,(car last args))))
;;   `(implies (and .cond (member-equal x ,elts) (member-equal y ,elts))
;;             (member-equal (op x y ,(car (last args))) ,elts))
;;   `(implies (and .cond (member-equal x ,elts))
;;             (member-equal (inv x ,(car (last args))) ,elts))
;; The other prerequisites of defgroup are automatically generated by defsubgroup.

(defmacro defsubgroup (name args cond elts)
  (let ((g (car (last args)))
        (non-nil-name (intern$ (concatenate 'string (symbol-name name) "-NON-NIL") "RTL"))
        (identity-name (intern$ (concatenate 'string (symbol-name name) "-IDENTITY") "RTL"))
        (assoc-name (intern$ (concatenate 'string (symbol-name name) "-ASSOC") "RTL"))
        (inverse-name (intern$ (concatenate 'string (symbol-name name) "-INVERSE") "RTL"))
        (subgroupp-name (intern$ (concatenate 'string "SUBGROUPP-" (symbol-name name)) "RTL")))
    `(encapsulate ()
       (defthm ,non-nil-name
         (implies ,cond (not (member-equal () ,elts)))
	 :hints (("Goal" :use ((:instance member-sublist (x ()) (l ,elts) (m (elts ,g)))))))
       (defthm ,identity-name
         (implies (and ,cond (member-equal x ,elts))
	          (equal (op (car ,elts) x ,g) x)))
       (defthm ,inverse-name
         (implies (and ,cond (member-equal x ,elts))
	          (and (member-equal (inv x ,g) ,elts)
		       (equal (op (inv x ,g) x ,g) (car ,elts)))))
       (defthm ,assoc-name
         (implies (and ,cond (member-equal x ,elts) (member-equal y ,elts) (member-equal z ,elts))
	          (equal (op x (op y z ,g) ,g) (op (op x y ,g) z ,g)))
	 :hints (("Goal" :use (group-assoc))))
       (defgroup ,name ,args
         ,cond
	 ,elts
	 (op x y ,g)
	 (inv x ,g))
       (defthm ,subgroupp-name
         (implies ,cond (subgroupp (,name ,@args) ,g))
	 :hints (("Goal" :use ((:instance not-subgroupp-cex (g ,g) (h (,name ,@args))))))))))


;;----------------------------------------------------------------------------------------------------------
;; Centralizer of a Group Element
;;----------------------------------------------------------------------------------------------------------

;; The ordered list of the elements of g that commute with a:

(defun centizer-elts-aux (a l g)
  (if (consp l)
      (if (equal (op a (car l) g) (op (car l) a g))
          (cons (car l) (centizer-elts-aux a (cdr l) g))
	(centizer-elts-aux a (cdr l) g))
    ()))

(defund centizer-elts (a g) (centizer-elts-aux a (elts g) g))

(defthm sublistp-centizer-elts
  (implies (and (groupp g) (in a g))
           (sublistp (centizer-elts a g) (elts g))))

(defthm dlistp-centizer-elts
  (implies (and (groupp g) (in a g))
           (dlistp (centizer-elts a g))))

(defthm centizer-elts-identity
  (implies (and (groupp g) (in a g))
           (equal (car (centizer-elts a g)) (e g))))

(defthm consp-centizer-elts
  (implies (and (groupp g) (in a g))
           (consp (centizer-elts a g))))

(defthm centizer-elts-iff
  (implies (and (groupp g) (in a g))
           (iff (member-equal x (centizer-elts a g))
	        (and (in x g) (equal (op a x g) (op x a g))))))

(defthm centizer-elts-closed
  (implies (and (groupp g) (in a g)
                (member-equal x (centizer-elts a g))
		(member-equal y (centizer-elts a g)))
           (member-equal (op x y g) (centizer-elts a g))))

(defthm centizer-elts-inverse
  (implies (and (groupp g) (in a g)
                (member-equal x (centizer-elts a g)))
           (member-equal (inv x g) (centizer-elts a g))))

(defsubgroup centralizer (a g)
  (and (groupp g) (in a g))
  (centizer-elts a g))

(defthmd centralizer-iff
  (implies (and (groupp g) (in a g))
           (iff (in x (centralizer a g))
	        (and (in x g) (equal (op a x g) (op x a g)))))		
  :hints (("Goal" :in-theory (enable centizer-elts-iff))))

(defthmd centralizer-conj-iff
  (implies (and (groupp g) (in a g))
           (iff (in x (centralizer a g))
	        (and (in x g) (equal (conj a x g) a))))
  :hints (("Goal" :in-theory (enable centralizer-iff)
                  :use ((:instance conj-commute (x a) (y x))))))

(defthmd centralizer-op
  (implies (and (groupp g) (in a g) (in x g) (in y g))
           (iff (in (op x y g) (centralizer a g))
	        (equal (conj a (inv y g) g)
		       (conj a x g)))))


;;----------------------------------------------------------------------------------------------------------
;; Center of a Group
;;----------------------------------------------------------------------------------------------------------

;; Search for an element of g that does not commute with a:

(defun cent-cex-aux (a l g)
  (if (consp l)
      (if (equal (op a (car l) g) (op (car l) a g))
          (cent-cex-aux a (cdr l) g)
	(car l))
    ()))

(defund cent-cex (a g) (cent-cex-aux a (elts g) g))

; Ordered list of elements of g that commute with all elements:

(defun cent-elts-aux (l g)
  (if (consp l)
      (if (cent-cex (car l) g)
          (cent-elts-aux (cdr l) g)
	(cons (car l) (cent-elts-aux (cdr l) g)))
	
    ()))

(defund cent-elts (g) (cent-elts-aux (elts g) g))

(defthm sublistp-cent-elts
  (sublistp (cent-elts g) (elts g)))

(defthm dlistp-cent-elts
  (implies (groupp g)
           (dlistp (cent-elts g))))

(defthm cent-elts-1
  (implies (and (in a g)
                (not (member-equal a (cent-elts g))))
	   (and (in (cent-cex a g) g)
	        (not (equal (op a (cent-cex a g) g)
		            (op (cent-cex a g) a g))))))

(defthmd cent-elts-2
  (implies (and (groupp g)
                (in a g)
                (member-equal a (cent-elts g))
		(in x g))
	   (equal (op a x g) (op x a g))))

(defthm cent-elts-identity
  (implies (groupp g)
           (equal (car (cent-elts g)) (e g))))

(defthm consp-cent-elts
  (implies (groupp g)
           (consp (cent-elts g))))

(defthm cent-elts-closed
  (implies (and (groupp g)
                (member-equal x (cent-elts g))
		(member-equal y (cent-elts g)))
           (member-equal (op x y g) (cent-elts g))))

(defthm cent-elts-inverse
  (implies (and (groupp g)
                (member-equal x (cent-elts g)))
           (member-equal (inv x g) (cent-elts g))))

(defsubgroup center (g)
  (groupp g)
  (cent-elts g))

(defthmd center-commutes
  (implies (and (groupp g)
                (in a (center g))
		(in x g))
	   (equal (op a x g) (op x a g))))

(defthmd center-commutes-converse
  (implies (and (groupp g)
                (in a g)
                (not (in a (center g))))
	   (and (in (cent-cex a g) g)
	        (not (equal (op a (cent-cex a g) g)
		            (op (cent-cex a g) a g))))))

;; The center is an abelian subgroup:

(defthm abelianp-center
  (implies (groupp g)
           (abelianp (center g))))

;; The centralizer of a non-central element is a proper subgroup:

(defthmd order-proper-subgroup
  (implies (and (groupp g)
                (subgroupp h g)
		(in x g)
		(not (in x h)))
	   (< (order h) (order g))))

(defthmd order-centralizer-not-center
  (implies (and (groupp g)
                (in x g)
		(not (in x (center g))))
	   (< (order (centralizer x g)) (order g))))


;;---------------------------------------------------------------------------------------------------
;; Cyclic Subgroups
;;---------------------------------------------------------------------------------------------------

;; The powers of a group element:

(defun power (a n g)
  (if (zp n)
      (e g)
    (op a (power a (1- n) g) g)))

(defthm power-in-g
  (implies (and (groupp g) (in a g) (natp n))
	   (in (power a n g) g)))

(defthmd power+
  (implies (and (groupp g) (in a g) (natp n) (natp m))
           (equal (op (power a n g) (power a m g) g)
	          (power a (+ n m) g))))

(defthm power-e
  (implies (and (groupp g) (natp n))
           (equal (power (e g) n g) (e g))))

(defthmd power*
  (implies (and (groupp g) (in a g) (natp n) (natp m))
           (equal (power (power a n g) m g)
	          (power a (* n m) g))))

(defthm power-subgroup
  (implies (and (subgroupp h g)
                (in x h)
		(natp n))
	   (and (in (power x n g) h)
	        (equal (power x n h) (power x n g)))))

;; The order of a group element:

(defun ord-aux (a n g)
  (declare (xargs :measure (nfix (- (order g) n))))
  (if (equal (power a n g) (e g))
      n
    (if (and (natp n) (< n (order g)))
        (ord-aux a (1+ n) g)
      ())))

(defun ord (a g) (ord-aux a 1 g))

;; The element list of the cyclic subgroup generated by a is a list of all powers of a:

(defun powers-aux (a n g)
  (if (zp n)
      ()
    (append (powers-aux a (1- n) g) (list (power a (1- n) g)))))

(defun powers (a g) (powers-aux a (ord a g) g))

(defthm ord<=order
  (implies (and (groupp g) (in a g))
           (and (posp (ord a g)) (<= (ord a g) (order g))))
  :hints (("Goal" :use (ord-8 order-pos (:instance ord-9 (n 1))))))

(defthm ord-power
  (implies (and (groupp g) (in a g))
           (and (equal (power a (ord a g) g) (e g))
	        (implies (and (posp n) (< n (ord a g)))
		         (not (equal (power a n g) (e g)))))))

(defthmd power-mod
  (implies (and (groupp g) (in a g) (natp n))
           (equal (power a n g) (power a (mod n (ord a g)) g))))

(defthm divides-ord
  (implies (and (groupp g) (in a g) (natp n))
           (iff (equal (power a n g) (e g))
	        (divides (ord a g) n))))

(defthm ord-power-div
  (implies (and (groupp g)
                (in a g)
		(posp n)
		(divides n (ord a g)))
	   (equal (ord (power a n g) g)
	          (/ (ord a g) n))))

(defthm power-member
  (implies (and (groupp g) (in a g) (natp n))
           (member (power a n g) (powers a g))))

(defthm consp-powers
  (implies (and (groupp g) (in a g))
           (consp (powers a g))))

(defthm powers-non-nil
  (implies (and (groupp g) (in a g))
           (not (member-equal () (powers a g)))))

(defthm dlistp-powers
  (implies (and (groupp g) (in a g))
           (dlistp (powers a g))))

(defthm len-append
  (implies (natp n)
           (equal (nth n (append l m))
	          (if (< n (len l))
		      (nth n l)
		    (nth (- n (len l)) m)))))

(defthm len-powers
  (implies (and (groupp g) (in a g))
           (equal (len (powers a g)) (ord a g))))

(defthm member-powers
  (implies (and (groupp g) (in a g)
                (natp n) (< n (ord a g)))
	   (equal (nth n (powers a g))
	          (power a n g))))

(defthm car-powers
  (implies (and (groupp g) (in a g))
           (equal (car (powers a g))
                  (e g))))

(defthm powers-closed
  (implies (and (groupp g) (in a g)
                (member-equal x (powers a g))
                (member-equal y (powers a g)))
           (member-equal (op x y g) (powers a g))))

(defthm powers-id
  (implies (and (groupp g) (in a g)
                (member-equal x (powers a g)))
	   (equal (op (e g) x g)
	          x)))

(defthm inv-power
  (implies (and (groupp g) (in a g)
                (member-equal x (powers a g)))
	   (member-equal (inv x g) (powers a g))))

(defthm sublistp-powers
  (implies (and (groupp g) (in a g))
           (sublistp (powers a g) (elts g))))

(defsubgroup cyclic (a g)
  (and (groupp g) (in a g))
  (powers a g))

(in-theory (disable cyclic))

(defthm order-ord
  (implies (and (groupp g) (in a g))
	   (equal (order (cyclic a g))
	          (ord a g))))


;;---------------------------------------------------------------------------------------------------
;; Cauchy's Theorem for Abelian Groups
;;---------------------------------------------------------------------------------------------------

;; The witness function:

(defun elt-of-ord-aux (l n g)
  (if (consp l)
      (if (= (ord (car l) g) n)
          (car l)
	(elt-of-ord-aux (cdr l) n g))
    ()))

(defun elt-of-ord (n g) (elt-of-ord-aux (elts g) n g))

(defthm elt-of-ord-ord
  (implies (and (groupp g)
                (natp n)
                (elt-of-ord n g))
	   (and (in (elt-of-ord n g) g)
	        (equal (ord (elt-of-ord n g) g)
		       n))))

(defthm ord-elt-of-ord
  (implies (and (groupp g)
                (natp n)
		(in x g)
		(= (ord x g) n))
           (elt-of-ord n g)))

;; If there is an element of order divisible by n then there is an element of order n:

(defthm exists-elt-of-ord
  (implies (and (groupp g)
                (posp n)
		(in x g)
		(divides n (ord x g)))
	   (elt-of-ord n g)))

;; A consequence of lagrange and euclid:

(defthm divides-order-quotient
  (implies (and (groupp g)
                (abelianp g)
                (primep p)
		(divides p (order g))
                (not (elt-of-ord p g))
		(in a g))
	   (divides p (order (quotient g (cyclic a g))))))

;; Power of an element of the quotient group:

(defthmd lcoset-power
  (implies (and (normalp h g)
                (in x (quotient g h))
		(natp n))
	   (equal (power x n (quotient g h))
	          (lcoset (power (car x) n g) h g))))

(defthm divides-ord-quotient
  (implies (and (normalp h g)
                (in x (quotient g h)))
	   (divides (ord x (quotient g h))
	            (ord (car x) g))))

;; A critical lemma for the induction:

(defthm lift-elt-of-ord
  (implies (and (normalp h g)
                (posp m)
                (elt-of-ord m (quotient g h)))
           (elt-of-ord m g)))

(defun cauchy-abelian-induction (g)
  (declare (xargs :measure (order g) :hints (("Goal" :use order-quotient-cadr))))
  (if (and (groupp g)
           (abelianp g)
	   (> (order g) 1))
      (cauchy-abelian-induction (quotient g (cyclic (cadr (elts g)) g)))
    ()))

(defthmd cauchy-abelian
  (implies (and (groupp g)
                (abelianp g)
		(primep p)
		(divides p (order g)))
	   (and (in (elt-of-ord p g) g)
	        (equal (ord (elt-of-ord p g) g) p))))


;;----------------------------------------------------------------------------------------------------------
;; Conjugacy Classes
;;----------------------------------------------------------------------------------------------------------

;; Ordered list of conjugates of x:

(defun conjs-aux (x l g)
  (if (consp l)
      (if (member-equal (conj x (car l) g)
                        (conjs-aux x (cdr l) g))
	  (conjs-aux x (cdr l) g)
	(insert (conj x (car l) g)
	        (conjs-aux x (cdr l) g)
		g))
    ()))

(defund conjs (x g) (conjs-aux x (elts g) g))

(defthm conj-in-g
  (implies (and (groupp g) (in x g) (in a g))
           (in (conj x a g) g)))

(defthm ordp-conjs
  (implies (and (groupp g) (in x g))
           (ordp (conjs x g) g)))

(defthm dlistp-conjs
  (implies (and (groupp g) (in x g))
           (dlistp (conjs x g))))

(defthm conj-in-conjs
  (implies (and (groupp g) (in x g) (in a g))
           (member-equal (conj x a g) (conjs x g))))

;; Given a member y of that list, we would like to find the conjugator that put it there,
;; i.e., the element a such that y = (conj x a g):

(defun conjer-aux (y x l g)
  (if (consp l)
      (if (equal (conj x (car l) g) y)
          (car l)
	(conjer-aux y x (cdr l) g))
    ()))

(defund conjer (y x g) (conjer-aux y x (elts g) g))

(defthm conjs-conjer
  (implies (and (groupp g) (in x g) (member-equal y (conjs x g)))
           (let ((c (conjer y x g)))
	     (and (in c g)
	          (equal (conj x c g) y)))))

(defthm conjs-in-g
  (implies (and (groupp g) (in x g) (member-equal y (conjs x g)))
           (in y g)))

;; Conjugacy is an equivalence relation:

(defthm conj-reflexive
  (implies (and (groupp g) (in x g))
           (member-equal x (conjs x g))))

(defthmd conj-symmetric
  (implies (and (groupp g) (in x g) (in y g) (member-equal y (conjs x g)))
           (member-equal x (conjs y g))))

(defthmd conj-trans
  (implies (and (groupp g) (in x g) (in y g) (in z g)
                (member-equal y (conjs x g))
                (member-equal z (conjs y g)))
           (member-equal z (conjs x g))))

;; If two conjugacy classes intersect, then they are equal:

(defthm sublistp-conjs
  (implies (and (groupp g)
		(in x g)
		(in y g)
		(member-equal y (conjs x g)))
	   (sublistp (conjs y g) (conjs x g))))
	   
(defthmd equal-conjs
  (implies (and (groupp g)
		(in x g)
		(in y g)
		(member-equal y (conjs x g)))
	   (equal (conjs y g) (conjs x g))))

(defthmd equal-conjs-2
  (implies (and (groupp g)
		(in x1 g)
		(in x2 g)
		(in y g)
		(member-equal y (conjs x1 g))
		(member-equal y (conjs x2 g)))
	   (equal (conjs x1 g) (conjs x2 g))))

;; 1-1 map between (conjs x g) and (lcosets (centralizer x g) g):

(defund conj2coset (y x g)
  (lcoset (inv (conjer y x g) g) (centralizer x g) g))

(defund coset2conj (c x g)
  (conj x (inv (car c) g) g))

(defthm coset2conj-conj2coset
  (implies (and (groupp g) (in x g) (member-equal y (conjs x g)))
           (equal (coset2conj (conj2coset y x g) x g)
	          y)))

(defthm conj2coset-coset2conj
  (implies (and (groupp g) (in x g) (member-equal c (lcosets (centralizer x g) g)))
           (equal (conj2coset (coset2conj c x g) x g)
	          c)))

;; This is proved by functional instantiation of len-1-1-equal:

(defthm len-conjs-cosets
  (implies (and (groupp g) (in x g))
           (equal (len (conjs x g))
	          (subgroup-index (centralizer x g) g))))


;;----------------------------------------------------------------------------------------------------------
;; Class equation
;;----------------------------------------------------------------------------------------------------------

;; The nontrivial conjugacy classes of g together with its center form a partition of g.
;; This provides a useful expression for the order of g.

;; A list of the nontrivial conjugacy classes:

(defun conjs-list-aux (l g)
  (if (consp l)
      (let ((conjs (conjs-list-aux (cdr l) g)))
	(if (or (in (car l) (center g))
	        (member-list (car l) conjs))
	    conjs
	  (cons (conjs (car l) g) conjs)))
    ()))

(defund conjs-list (g)
  (conjs-list-aux (elts g) g))

;; We shall show that (append (center g) (append-list (conjs-list g))) is a permutation of (elts g).

;; (append-list (conjs-list g)) contains every non-central element:

(defthm member-lconjs-conjs-list
  (implies (and (groupp g)
                (in x g)
		(not (in x (center g))))
	   (member (conjs x g) (conjs-list g))))

(defthm member-append-list-conjs-list
  (implies (and (groupp g)
                (in x g)
		(not (in x (center g))))
	   (member x (append-list (conjs-list g)))))

;; (append-list (conjs-list g)) is disjoint from the center:

(defthm center-conjs
  (implies (and (groupp g)
                (in x g)
		(not (in x (center g)))
		(in c (center g)))
	   (not (member-equal c (conjs x g)))))

(defthm center-conjs-list
  (implies (and (groupp g)
		(in c (center g)))
	   (not (member-equal c (append-list (conjs-list g))))))

(defthm dlistp-conj-list
  (implies (groupp g)
           (dlistp (conjs-list g))))

;; (append (center g) (append-list (conjs-list g))) is a dlist:

(defthm conjs-car
  (implies (and (groupp g)
		(in x g))
	   (and (in (car (conjs x g)) g)
	        (equal (conjs (car (conjs x g)) g)
	               (conjs x g)))))

(defthmd conjs-list-cars
  (implies (and (groupp g)
		(member c (conjs-list g)))
	   (and (in (car c ) g)
		(equal (conjs (car c) g)
		       c))))

(defthm conjs-list-disjointp-pairwise
  (implies (groupp g)
	   (disjointp-pairwise (conjs-list g))))

(defthm dlistp-list-conjs-list
  (implies (groupp g)
	   (dlistp-list (conjs-list g))))

(defthm dlistp-append-list-conjs-list
  (implies (groupp g)
	   (dlistp (append-list (conjs-list g)))))

(defthm dijjointp-center-conjs-list
  (implies (groupp g)
           (disjointp (elts (center g))
	              (append-list (conjs-list g)))))

(defthm dlistp-big-list
  (implies (groupp g)
           (dlistp (append (elts (center g))
	                   (append-list (conjs-list g))))))

;; The two lists are sublists of each other:

(defthm sublistp-elts-big-list
  (implies (groupp g)
           (sublistp (elts g)
                     (append (elts (center g))
	                     (append-list (conjs-list g))))))

(defthm sublistp-conjs-list-elts
  (implies (groupp g)
	   (sublistp (append-list (conjs-list g))
	             (elts g))))

(defthm sublistp-big-list-elts
  (implies (groupp g)
	   (sublistp (append (elts (center g))
	                     (append-list (conjs-list g)))
	             (elts g))))

;; Thus, the two lists have the same length:

(defthmd class-equation
  (implies (groupp g)
	   (equal (len (append (elts (center g))
	                       (append-list (conjs-list g))))
	          (order g))))


;;----------------------------------------------------------------------------------------------------------
;; Cauchy's Theorem
;;----------------------------------------------------------------------------------------------------------

;; Search for a non-central group element the centralizer of which has order divisible by p:

(defun find-elt-aux (l g p)
  (if (consp l)
      (if (and (not (in (car l) (center g)))
               (divides p (order (centralizer (car l) g))))
	  (car l)
	(find-elt-aux (cdr l) g p))
    ()))

(defund find-elt (g p) (find-elt-aux (elts g) g p))

;; If such an element exists, then since it in not in the center, the order of its centralizer is
;; less than that of g:

(defthmd find-elt-centralizer
  (implies (and (groupp g)
                (primep p)
                (find-elt g p))
	   (let ((cent (centralizer (find-elt g p) g)))
	     (and (subgroupp cent g)
	          (< (order cent) (order g))
		  (divides p (order cent))))))

;; Assume that p divides the order of g.  If no such element exists, then the length of every nontrivial
;; cojugacy class is divisible by p, and according to the class equation, so is the order of the center:

(defthm find-elt-center
  (implies (and (groupp g)
                (primep p)
		(divides p (order g))
                (null (find-elt g p)))
	   (divides p (order (center g)))))

;; Clearly, if any subgroup of g has an element of order p, then so does g:

(defthmd ord-subgroup
  (implies (and (subgroupp h g)
                (in x h))
	   (equal (ord x h) (ord x g))))

(defthm elt-of-ord-subgroup
  (implies (and (groupp g)
                (natp n)
		(subgroupp h g)
		(elt-of-ord n h))
	   (elt-of-ord n g)))

;; The theorem follows by induction:

(defun cauchy-induction (g p)
  (declare (xargs :measure (order g) :hints (("Goal" :use find-elt-centralizer))))
  (if (and (groupp g)
           (primep p)
	   (find-elt g p))
      (cauchy-induction (centralizer (find-elt g p) g) p)
    t))

(defthmd cauchy
  (implies (and (groupp g)
		(primep p)
		(divides p (order g)))
	   (and (in (elt-of-ord p g) g)
	        (equal (ord (elt-of-ord p g) g) p))))
