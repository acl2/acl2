;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "DM")

(local (include-book "support/groups"))
(include-book "lists")
(include-book "rtl/rel11/lib/util" :dir :system)
(include-book "projects/numbers/euclid" :dir :system)

;;---------------------------------------------------------------------------------------------------
;; Fimite Groups
;;---------------------------------------------------------------------------------------------------

;; An mxn matrix is a proper list of m proper lists of length n:

(defund matrixp (l m n)
  (declare (xargs :guard (and (natp m) (natp n))))
  (if (consp l)
      (and (posp m)
           (true-listp (car l))
	   (= (len (car l)) n)
	   (matrixp (cdr l) (1- m) n))
    (and (zerop m) (null l))))

;; A group g of order n is represented by its operation table, an nxn matrix.  The first row of g,
;; (car g), is a list of the elements of g, beginning with its identity element e = x0:

;;   (x0 x1 x2 ... x(n-1))

;; For 0 <= k < n, the kth row, (nth k g), is

;;   (xkx0 xkx1 xkx2 ... xkx(n-1)).

;; The elements of a group:

(defmacro elts (g) `(car ,g))

;; Group membership:

(defmacro in (x g) `(member-equal ,x (elts ,g)))

;; Order of a group:

(defund order (g) (len (elts g)))

;; Left identity element:

(defund e (g) (caar g))

;; index of a group element:

(defmacro ind (x g) `(index ,x (elts ,g)))

;; Group operation:

(defun op-guard (g)
  (declare (xargs :guard t))
  (and (true-listp g) (matrixp g (len (car g)) (len (car g)))))

(defund op (x y g)
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

(defund closedp (g) (null (closedp-cex g)))

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

(defund inv (x g)
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

;; Definition of a group:

(defund groupp (g)
  (and (posp (order g))
       (matrixp g (order g) (order g))
       (dlistp (elts g))
       (not (in () g))
       (closedp g)
       (assocp g)
       (inversesp g)))

(defthm consp-groupp
  (implies (groupp g)
           (consp (elts g))))

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

(defund abelianp-cex (g) (axy (elts g) g))

(defund abelianp (g) (null (abelianp-cex g)))


;;---------------------------------------------------------------------------------------------------
;; Group Properties: Consequences of (groupp g)
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

;; Converse of group-assoc, useful in establisshing associativity of a purported group::

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

;; useful in establishing the inverse property:

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
	   (equal (op x y g) (op y x g))))

;; Useful in establishing that a group is abelian:

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

(defthmd inv-unique
  (implies (and (groupp g)
                (in x g)
		(in y g)
		(equal (op y x g) (e g)))
	   (equal (inv x g) y)))

(defthm inv-e
  (implies (groupp g)
           (equal (inv (e g) g) (e g))))

(defthmd prod-inv
  (implies (and (groupp g)
                (in x g)
		(in y g))
	   (equal (inv (op x y g) g)
	          (op (inv y g) (inv x g) g))))

;; If 2 groups have the same element list and their operations agree on all pairs of elements,
;; then they are the same group:

(defun diff-member (x y)
  (if (consp x)
      (if (equal (car x) (car y))
	  (1+ (diff-member (cdr x) (cdr y)))
	0)
    ()))

(defun diff-entry (x y)
  (let ((i (diff-member x y)))
    (cons i (diff-member (nth i x) (nth i y)))))

(defund diff-elt-1 (h k)
  (nth (car (diff-entry h k)) (elts h)))

(defund diff-elt-2 (h k)
  (nth (cdr (diff-entry h k)) (elts h)))

(defthmd diff-group-op
  (implies (and (groupp h)
                (groupp k)
		(equal (elts h) (elts k))
		(not (equal h k)))
	   (let ((x (diff-elt-1 h k)) (y (diff-elt-2 h k)))
	     (and (in x h)
	          (in y h)
		  (not (equal (op x y h) (op x y k)))))))


;;---------------------------------------------------------------------------------------------------
;; Ordered Lists of Group Elements
;;---------------------------------------------------------------------------------------------------

;; The advantage of working with ordered lists of group elements is that if 2 such lists have the same
;; elements (i.e., each is a sublist of the other), then they are equal.  This is an attempt to compensate
;; for the failure of ACL2 to represents sets.

;; An ordered list of elements of g is recognized by the following predicate:

(defun ordp (l g)
  (if (consp l)
      (and (in (car l) g)
           (if (consp (cdr l))
	       (and (< (ind (car l) g) (ind (cadr l) g))
	            (ordp (cdr l) g))
	     (null (cdr l))))
    (null l)))

(defthm ordp-sublistp
  (implies (and (groupp g) (ordp l g))
           (sublistp l (elts g))))

(defthmd car-ordp-minimal
  (implies (and (ordp l g)
                (member x (cdr l)))
	   (> (ind x g) (ind (car l) g))))

(defthmd car-ordp-e
  (implies (and (groupp g)
		(ordp l g)
		(member-equal (e g) l))
	   (equal (car l) (e g))))

(defthmd ordp<ind
  (implies (and (groupp g)
                (ordp l g)
		(member-equal x l)
		(member-equal y l))
           (iff (< (index x l) (index y l))
	        (< (ind x g) (ind y g)))))

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

;; Obviously (though not so easily proved), (elts g) is ordered with respect to g:

(defthm ordp-g
  (implies (groupp g)
           (ordp (elts g) g)))

;; (elts g) is the only ordered list that contains all elements of g:

(defthmd equal-l-elts
  (implies (and (groupp g)
                (ordp l g)
		(sublistp (elts g) l))
	   (equal (elts g) l)))

;; Insert an element into an ordered list:

(defun insert (x l g)
  (if (consp l)
      (if (equal x (car l))
          l
	(if (< (ind x g) (ind (car l) g))
	    (cons x l)
	  (cons (car l) (insert x (cdr l) g))))
    (list x)))

(defthm ordp-insert
  (implies (and (ordp l g) (in x g))
           (ordp (insert x l g) g)))

(defthm sublistp-insert
  (implies (and (sublistp l m)
                (member-equal x m))
	   (sublistp (insert x l g) m)))

(defthmd member-insert
  (iff (member-equal y (insert x l g))
       (or (equal y x) (member-equal y l))))

(defthm len-insert
  (implies (not (member x l))
	   (equal (len (insert x l g))
		  (1+ (len l)))))


;;---------------------------------------------------------------------------------------------------
;; Subgroups
;;---------------------------------------------------------------------------------------------------

;; A group h is a subgroup of a group g if every element of H is an element of G and the group 
;; operations agree on all pairs of elements of h.  Note that the element list of a subgroup of g
;; neen not be ordered with respect to g.  Although we shall ebdeavor to construct ordered subgroups,
;; this is not always convenient (e.g., the elements of a cyclic subgroup have a different natural
;; ordering) or even possible (e.g., the intersection of 2 groups cannot in general be ordered with
;; respect to both groups).

;; The definition is based on a function that searches for a counterexample to closure:

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

(defund subgroupp (h g)
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

(defthm subgroup-e
  (implies (subgroupp h g)
	   (equal (e h) (e g))))

(defthm subgroup-inv
  (implies (and (subgroupp h g)
		(in x h))
           (equal (inv x h) (inv x g))))

(defthm abelian-subgroup
  (implies (and (subgroupp h g)
                (abelianp g))
	   (abelianp h)))

(defthmd subgroup-order-<=
  (implies (subgroupp h g)
           (<= (order h) (order g))))

;; Converse of subgroup-group-op, used to establish subgrouphood:

(defthmd not-subgroupp-cex
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

;; Every group is a subgroup of itself:

(defthm subgroupp-g-g
  (implies (groupp g)
           (subgroupp g g)))

;; Subgroups of subgroups:

(defthmd subgroup-subgroup
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(sublistp (elts h) (elts k)))
	   (subgroupp h k)))

(defthmd subgroupp-transitive
  (implies (and (subgroupp h k) (subgroupp k g)) (subgroupp h g)))

;; If 2 subgroups of a group have the same element list, then there are the same group:

(defthm subgroups-equal-elts
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(equal (elts h) (elts k)))
	   (equal h k))
  :rule-classes ())

;; As a consequence of subgroups-equal-elts and equal-l-elts, g is the only ordered subgroup of itself with the same order:

(defthm ordp-subgroup-equal
  (implies (and (subgroupp h g)
                (equal (order h) (order g))
		(ordp (elts h) g))
	   (equal h g))
  :rule-classes ())

;; If a sublist of (elts g) is the element list of a subgroup, then the subgroup is generated by
;; the following function:

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

(defund subgroup (l g)
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

(defthm groupp-g
  (groupp (g)))

(defthm glist-elts
  (equal (elts (g))
         (glist)))
	 
(defthm op-g-rewrite
  (implies (and (in x (g))
		(in y (g)))
           (equal (op x y (g))
	          (gop x y))))

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
  (let ((op-name (intern$ (concatenate 'string "OP-" (symbol-name name)) "DM"))
        (name-row (intern$ (concatenate 'string (symbol-name name) "-ROW") "DM"))
	(name-aux (intern$ (concatenate 'string (symbol-name name) "-AUX") "DM"))
	(groupp-name (intern$ (concatenate 'string "GROUPP-" (symbol-name name)) "DM"))
	(name-elts (intern$ (concatenate 'string (symbol-name name) "-ELTS") "DM"))
	(name-op-rewrite (intern$ (concatenate 'string (symbol-name name) "-OP-REWRITE") "DM"))
	(name-inv-rewrite (intern$ (concatenate 'string (symbol-name name) "-INV-REWRITE") "DM")))
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
  (let ((op-name (intern$ (concatenate 'string "OP-" (symbol-name name)) "DM"))
        (name-row (intern$ (concatenate 'string (symbol-name name) "-ROW") "DM"))
	(name-aux (intern$ (concatenate 'string (symbol-name name) "-AUX") "DM")))
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

(defthm len-ninit
  (implies (natp n)
           (equal (len (ninit n)) n)))

(defthm nth-ninit
  (implies (and (posp n) (natp k) (< k n))
           (equal (nth k (ninit n))
	          k)))

(defthmd member-ninit
  (implies (posp n)
           (iff (member-equal x (ninit n))
	        (and (natp x)
	             (< x n)))))

;; Additive group of integers modulo n:

(defun z+-op (x y n) (mod (+ x y) n))

(defun z+-inv (x n) (mod (- x) n))

;; Rewrite rules required by defgroup:

(defthm consp-ninit
  (implies (posp n)
           (consp (ninit n))))

(defthm dlistp-ninit
  (implies (posp n)
           (dlistp (ninit n))))

(defthm ninit-non-nil
  (implies (posp n)
           (not (member-equal () (ninit n)))))

(defthm car-ninit
  (implies (posp n)
           (equal (car (ninit n)) 0)))

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

;; List of integers less than n and relatively prime to n:

(defun rel-primes-aux (k n)
  (if (zp k)
      ()
    (if (= (gcd k n) 1)
        (append (rel-primes-aux (1- k) n) (list k))
      (rel-primes-aux (1- k) n))))

(defund rel-primes (n)
  (rel-primes-aux n n))

(defthmd member-rel-primes
  (implies (and (posp n) (> n 1))
	   (iff (member k (rel-primes n))
	        (and (posp k)
		     (< k n)
		     (= (gcd k n) 1)))))

;; Multiplicative group of integers modulo n:

(defund z*-op (x y n) (mod (* x y) n))

;; The definition of z*-inv is based on the following lemma from books/projects/numbers/euclid.lisp"

(defthm gcd-linear-combination
    (implies (and (integerp x)
		  (integerp y))
	     (= (+ (* (r x y) x)
		   (* (s x y) y))
		(gcd x y)))
    :rule-classes ())

(defund z*-inv (x n) (mod (r x n) n))

;; Rewrite rules required by defgroup:

(defthm consp-rel-primes
  (implies (posp n)
           (consp (rel-primes n))))

(defthm dlistp-rel-primes
  (implies (posp n)
           (dlistp (rel-primes n))))

(defthm rel-primes-non-nil
  (implies (posp n)
           (not (member-equal () (rel-primes n)))))

(defthm car-rel-primes
  (implies (posp n)
           (equal (car (rel-primes n)) 1)))

(defthm z*-identity
  (implies (and (and (posp n) (> n 1))
                (member-equal x (rel-primes n)))
	   (equal (z*-op 1 x n)
	          x)))

(defthm z*-closed
  (implies (and (posp n) (> n 1)
                (member-equal x (rel-primes n))
                (member-equal y (rel-primes n)))
           (member-equal (z*-op x y n) (rel-primes n))))

(defthm z*-assoc
  (implies (and (posp n)
                (member-equal x (rel-primes n))
                (member-equal y (rel-primes n))
                (member-equal z (rel-primes n)))
	   (equal (z*-op x (z*-op y z n) n)
	          (z*-op (z*-op x y n) z n))))

(defthm z*-inverse
  (implies (and (posp n) (> n 1)
                (member-equal x (rel-primes n)))
	   (and (member-equal (z*-inv x n) (rel-primes n))
	        (equal (z*-op (z*-inv x n) x n) 1))))

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


;;----------------------------------------------------------------------------------------------------------
;; Parametrized Subgroups
;;----------------------------------------------------------------------------------------------------------

;; The macro call

;;   (defsubgroup name args grp cond elts)

;; calls defgroup to define a subgroup of a given group, grp, which may be either of the following:
;;   (1) A symbol representing an arbitrary group, in which case grp is added to args and
;;       (groupp grp) is added to cond in the defgroup call.  This applies to all of the examples below.
;;   (2) a previously defined group.  In the case of a parametrized group or an instantiation thereof,
;;       every variable that occurs in the parameter list must be an element of args.  An example of
;;       this case is the alternating group (alt n), defined as a sybgroup of the symmetric group
;;       (sym n) in symmetric.lisp.

;; The last two arguments of defgroup are not supplied to defsubgroup, since they are always 
;; (op x y grp) and (inv x grp).

;; Before calling defsubgroup, the following rewrite rules should be proved:
;;   `(implies ,cond (dlistp ,elts))
;;   `(implies ,cond (sublistp ,elts (elts ,grp)))
;;   `(implies ,cond (consp ,elts))
;;   `(implies ,cond (equal (car ,elts) (e ,grp)))
;;   `(implies (and ,cond (member-equal x ,elts) (member-equal y ,elts))
;;             (member-equal (op x y ,grp) ,elts))
;;   `(implies (and ,cond (member-equal x ,elts))
;;             (member-equal (inv x ,grp) ,elts))
;; The other prerequisites of defgroup are automatically proved by defsubgroup.

(defmacro defsubgroup (name args grp cond elts)
  (let ((non-nil-name (intern$ (concatenate 'string (symbol-name name) "-NON-NIL") "DM"))
        (identity-name (intern$ (concatenate 'string (symbol-name name) "-IDENTITY") "DM"))
        (assoc-name (intern$ (concatenate 'string (symbol-name name) "-ASSOC") "DM"))
        (inverse-name (intern$ (concatenate 'string (symbol-name name) "-INVERSE") "DM"))
        (subgroupp-name (intern$ (concatenate 'string "SUBGROUPP-" (symbol-name name)) "DM"))
	(cond (if (symbolp grp) `(and (groupp ,grp) ,cond) cond))
	(args (if (symbolp grp) (append args (list grp)) args)))
    `(encapsulate ()
       (local-defthm ,non-nil-name
         (implies ,cond (not (member-equal () ,elts)))
	 :hints (("Goal" :use ((:instance member-sublist (x ()) (l ,elts) (m (elts ,grp)))))))
       (local-defthm ,identity-name
         (implies (and ,cond (member-equal x ,elts))
	          (equal (op (car ,elts) x ,grp) x)))
       (local-defthm ,inverse-name
         (implies (and ,cond (member-equal x ,elts))
	          (and (member-equal (inv x ,grp) ,elts)
		       (equal (op (inv x ,grp) x ,grp) (car ,elts)))))
       (local-defthm ,assoc-name
         (implies (and ,cond (member-equal x ,elts) (member-equal y ,elts) (member-equal z ,elts))
	          (equal (op x (op y z ,grp) ,grp) (op (op x y ,grp) z ,grp)))
         :hints (("Goal" :use ((:instance group-assoc (g ,grp))))))
       (defgroup ,name ,args
         ,cond
	 ,elts
	 (op x y ,grp)
	 (inv x ,grp))
       (defthm ,subgroupp-name
         (implies ,cond (subgroupp (,name ,@args) ,grp))
	 :hints (("Goal" :use ((:instance not-subgroupp-cex (g ,grp) (h (,name ,@args))))))))))

;; A trivial example:

(defsubgroup trivial-subgroup () g t (list (e g)))

(defthmd iff-trivial-order-1
  (implies (subgroupp h g)
           (iff (equal (trivial-subgroup g) h)
	        (equal (order h) 1))))

(defthmd in-trivial-subgroup
  (implies (and (groupp g)
                (in x (trivial-subgroup g)))
	   (equal (e g) x)))

(defthm trivial-subgroup-subgroup
  (implies (subgroupp h g)
           (equal (trivial-subgroup h)
	          (trivial-subgroup g))))

;; A non-trivial subgroup has a non-trivial element:

(defthmd not-trivial-elt
  (implies (and (subgroupp h g)
                (not (equal h (trivial-subgroup g))))
	   (and (in (cadr (elts h)) h)
	        (not (equal (cadr (elts h)) (e g))))))


;;----------------------------------------------------------------------------------------------------------
;; Intersection of Subgroups
;;----------------------------------------------------------------------------------------------------------

(defthm dlistp-int-elts
  (implies (subgroupp h g)
	   (dlistp (intersection-equal (elts h) (elts k)))))

(defthm sublistp-int-elts
  (implies (subgroupp h g)
	   (and (sublistp (intersection-equal (elts h) (elts k)) (elts g))
		(sublistp (intersection-equal (elts h) (elts k)) (elts h))
		(sublistp (intersection-equal (elts h) (elts k)) (elts k)))))

(defthm car-int-elts
  (implies (and (subgroupp h g) (subgroupp k g))
	   (and (consp (intersection-equal (elts h) (elts k)))
		(equal (car (intersection-equal (elts h) (elts k))) (e g)))))

(defthm int-elts-closed
  (implies (and (subgroupp h g) (subgroupp k g)
		(member-equal x (intersection-equal (elts h) (elts k)))
		(member-equal y (intersection-equal (elts h) (elts k))))
	   (member-equal (op x y g) (intersection-equal (elts h) (elts k)))))

(defthm int-elts-inv
  (implies (and (subgroupp h g) (subgroupp k g)
		(member-equal x (intersection-equal (elts h) (elts k))))
	   (member-equal (inv x g) (intersection-equal (elts h) (elts k)))))

(defsubgroup group-intersection (h k) g
  (and (subgroupp h g) (subgroupp k g))
  (intersection-equal (elts h) (elts k)))

(defthm subgroupp-int-both
  (implies (and (subgroupp h g)
		(subgroupp k g))
	   (and (subgroupp (group-intersection h k g) h)
		(subgroupp (group-intersection h k g) k))))

;; The elements of the intersection are ordered according to the first parameter:

(defthmd ordp-int-elts
  (implies (groupp h)
           (ordp (intersection-equal (elts h) l)
                 h)))

;; An intersection with the trivial group is trivial:

(defthm trivial-subgroup-intersection
  (implies (subgroupp h g)
           (and (equal (group-intersection h (trivial-subgroup g) g)
	               (trivial-subgroup g))
	        (equal (group-intersection (trivial-subgroup g) h g)
	               (trivial-subgroup g)))))


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

(defthm ordp-centizer-elts
  (implies (groupp g)
	   (ordp (centizer-elts a g) g)))

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

(defsubgroup centralizer (a) g (in a g) (centizer-elts a g))

(defthmd centralizer-iff
  (implies (and (groupp g) (in a g))
           (iff (in x (centralizer a g))
	        (and (in x g) (equal (op a x g) (op x a g))))))


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

(defthm ordp-cent-elts
  (implies (groupp g)
	   (ordp (cent-elts g) g)))

(defthm sublistp-cent-elts
  (sublistp (cent-elts g) (elts g)))

(defthm dlistp-cent-elts
  (implies (groupp g)
           (dlistp (cent-elts g))))

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

(defsubgroup center () g t (cent-elts g))

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

;; An abelian group is its own center:

(defthm abelian-group-center
  (implies (and (groupp g)
		(abelianp g))
	   (equal (center g) g)))

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

(defthmd power-
  (implies (and (groupp g) (in a g) (natp n) (natp m) (>= n m))
           (equal (op (power a n g) (power (inv a g) m g) g)
	          (power a (- n m) g))))

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

(defthmd power-abelian
  (implies (and (groupp g)
                (abelianp g)
		(in x g)
		(in y g)
		(natp n))
	   (equal (op (power x n g) (power y n g) g)
	          (power (op x y g) n g))))

(defthmd power-inv
  (implies (and (groupp g)
                (in x g)
		(natp n))
	   (equal (power (inv x g) n g)
	          (inv (power x n g) g))))

;; The order of a group element:

(defun ord-aux (a n g)
  (declare (xargs :measure (nfix (- (order g) n))))
  (if (equal (power a n g) (e g))
      n
    (if (and (natp n) (< n (order g)))
        (ord-aux a (1+ n) g)
      ())))

(defund ord (a g) (ord-aux a 1 g))

(defthmd ord>1
  (implies (and (groupp g) (in a g))
	   (and (posp (ord a g))
	        (iff (equal (ord a g) 1)
		     (equal a (e g))))))

;; The element list of the cyclic subgroup generated by a is a list of all powers of a:

(defun powers-aux (a n g)
  (if (zp n)
      ()
    (append (powers-aux a (1- n) g) (list (power a (1- n) g)))))

(defund powers (a g) (powers-aux a (ord a g) g))

(defthmd member-powers-power
  (implies (and (groupp g) (in a g) (member x (powers a g)))
	   (equal (power a (index x (powers a g)) g)
		  x)))

(defthmd ord<=order
  (implies (and (groupp g) (in a g))
           (and (posp (ord a g)) (<= (ord a g) (order g)))))

(defthmd ord-power
  (implies (and (groupp g) (in a g))
           (and (equal (power a (ord a g) g) (e g))
	        (implies (and (posp n) (< n (ord a g)))
		         (not (equal (power a n g) (e g)))))))

(defthmd ord-power-gcd
  (implies (and (groupp g)
                (in a g)
		(posp n))
	   (equal (ord (power a n g) g)
	          (/ (ord a g) (gcd (ord a g) n)))))

(defthm equal-ord-subgroup
  (implies (and (subgroupp h g)
                (in a h))
	   (equal (ord a h) (ord a g))))


(defthmd ord-inv
  (implies (and (groupp g)
                (in x g))
	   (equal (ord (inv x g) g)
	          (ord x g))))

(defthmd ord-divides-lcm
  (implies (and (groupp g)
                (abelianp g)
		(in x g)
		(in y g))
	   (divides (ord (op x y g) g)
	            (lcm (ord x g) (ord y g)))))

(defthmd power-mod
  (implies (and (groupp g) (in a g) (natp n))
           (equal (power a n g) (power a (mod n (ord a g)) g))))

(defthmd divides-ord
  (implies (and (groupp g) (in a g) (natp n))
           (iff (equal (power a n g) (e g))
	        (divides (ord a g) n))))

(defthmd ord-power-div
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

(defthmd len-powers
  (implies (and (groupp g) (in a g))
           (equal (len (powers a g)) (ord a g))))

(defthmd member-powers
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

(defsubgroup cyclic (a) g (in a g) (powers a g))

(defthm order-ord
  (implies (and (groupp g) (in a g))
	   (equal (order (cyclic a g))
	          (ord a g))))

(defthmd abelianp-cyclic
  (implies (and (groupp g)
                (in a g))
	   (abelianp (cyclic a g))))

;; The witness function:

(defun elt-of-ord-aux (l n g)
  (if (consp l)
      (if (= (ord (car l) g) n)
          (car l)
	(elt-of-ord-aux (cdr l) n g))
    ()))

;; Search g for an element of ord n:

(defund elt-of-ord (n g) (elt-of-ord-aux (elts g) n g))

(defthmd elt-of-ord-ord
  (implies (and (groupp g)
                (natp n)
                (elt-of-ord n g))
	   (and (in (elt-of-ord n g) g)
	        (equal (ord (elt-of-ord n g) g)
		       n))))

(defthmd ord-elt-of-ord
  (implies (and (groupp g)
                (natp n)
		(in x g)
		(= (ord x g) n))
           (elt-of-ord n g)))

;; An element of ord (order g) is a generator of g:

(defund group-gen (g)
  (elt-of-ord (order g) g))

(defthmd order-group-gen
  (implies (and (groupp g)
                (group-gen g))
	   (and (in (group-gen g) g)
	        (equal (ord (group-gen g) g)
		       (order g)))))

;; A group is cyclic if it has a generator:

(defund cyclicp (g)
  (and (groupp g)
       (group-gen g)))

(defthm cyclicp-groupp
  (implies (cyclicp g)
           (and (groupp g)
	        (group-gen g))))

;; Once we have defined isomorphism, we shall prove that if (cyclicp g), then (cyclic (group-gen g) g)
;; is isomorphic to g.  For now, we have this:

(defthmd cyclicp-order
  (implies (cyclicp g)
	   (equal (order (cyclic (group-gen g) g))
		  (order g))))

(defthmd permp-cyclic
  (implies (cyclicp g)
           (permp (elts (cyclic (group-gen g) g))
	          (elts g))))

(defthmd member-cyclicp-power
  (implies (and (cyclicp g)
                (in x g))
	   (in x (cyclic (group-gen g) g))))

(defthm cyclic-cyclicp
  (implies (and (groupp g)
                (in a g))
	   (cyclicp (cyclic a g))))

