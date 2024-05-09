(in-package "DM")

(include-book "perms")
(include-book "rtl/rel11/lib/util" :dir :system)

;; This file contains all of the results in the top-level books lists, groups, quotients, and cauchy
;; and is included by those books.  Most of these results are proved in support/groups.lisp.  That file
;; is a mess.  (Someday I hope to clean it up.)  When it is included, a lot of proofs that that should
;; be easy don't go through.  That is why it lives in its own subdirectory and is included only in this
;; file, locally inside of an encapsulation, in which all of its desired lemmas are proved redundantly.
;; Then, outside of the encapsulation, I can prove additional lemmas for those 4 top-level books as the
;; need arises.

(encapsulate ()
	     
(local (include-book "support/groups"))

;;---------------------------------------------------------------------------------------------------
;; Fimite Groups
;;---------------------------------------------------------------------------------------------------

;; An mxn matrix is a proper list of m proper lists of length n:

(defun matrixp (l m n)
  (declare (xargs :guard (and (natp m) (natp n))))
  (if (consp l)
      (and (posp m)
           (true-listp (car l))
	   (= (len (car l)) n)
	   (matrixp (cdr l) (1- m) n))
    (and (zerop m) (null l))))

;; A group g of order n is represented by its operation table, an nxn matrix.  The first row of g,
;; car(g), is a list of the elements of g, beginning with its identity element e = x0:

;;   (x0 x1 x2 ... x(n-1))

;; For 0 <= k < n, the kth row, (nth k g), is

;;   (xkx0 xkx1 xkx2 ... xkx(n-1)).

;; The elements of a group:

(defmacro elts (g) `(car ,g))

;; Group membership:

(defmacro in (x g) `(member-equal ,x (elts ,g)))

;; Order of a group:

(defun order (g) (len (elts g)))

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

(defun abelianp-cex (g) (axy (elts g) g))

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

(defthm inv-unique
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


;;---------------------------------------------------------------------------------------------------
;; Ordered Lists of Group Elements
;;---------------------------------------------------------------------------------------------------

;; An ordered list of elements of G is recognized by the following predicate:

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

;; (elts g) is ordered with respect to g:

(defthm dlistp-ordp
  (implies (dlistp (car g))
           (ordp (elts g) g)))

(defthm ordp-g
  (implies (groupp g)
           (ordp (elts g) g)))

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

(defthm member-insert
  (iff (member-equal y (insert x l g))
       (or (equal y x) (member-equal y l))))

(defthm len-insert
  (implies (not (member x l))
	   (equal (len (insert x l g))
		  (1+ (len l)))))

;;---------------------------------------------------------------------------------------------------
;; Subgroups
;;---------------------------------------------------------------------------------------------------

;; A group H is a subgroup of a group G if every element of H is an element of G and the group 
;; operations agree on pairs of elements of H:

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

;; Converse of subgroup-group-op, used to establish subgrouphood:

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

(defthm subgroupp-g-g
  (implies (groupp g)
           (subgroupp g g)))

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

(defthm celt-elts-abelian
  (implies (and (groupp g)
                (abelianp g))
	   (equal (cent-elts g) (elts g))))
	   
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

(defund ord (a g) (ord-aux a 1 g))

;; The element list of the cyclic subgroup generated by a is a list of all powers of a:

(defun powers-aux (a n g)
  (if (zp n)
      ()
    (append (powers-aux a (1- n) g) (list (power a (1- n) g)))))

(defund powers (a g) (powers-aux a (ord a g) g))

(defthm ord<=order
  (implies (and (groupp g) (in a g))
           (and (posp (ord a g)) (<= (ord a g) (order g)))))

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

(defthm nth-append
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

(defsubgroup cyclic (a) g (in a g) (powers a g))

(defthm order-ord
  (implies (and (groupp g) (in a g))
	   (equal (order (cyclic a g))
	          (ord a g))))


;;---------------------------------------------------------------------------------------------------
;; Cosets
;;---------------------------------------------------------------------------------------------------

;; Informally, the left coset of a subgroup H of G determined by an element x of G is the set of
;; elements of G of the form xh, where h is in H.  In our formalization, we define a left coset
;; to be the list of these elements ordered according to group index.  This ensures that intersecting
;; cosets are equal.

;; The coset xH:

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
		(in y g)
	        (member-equal y (lcoset x h g)))
	   (member-equal x (lcoset y h g))))

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

;; THEOREM: If H is a subgroup of G, the the order of G is the product of the order of H and the
;; number of left cosets of H in G.

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

;; The index of a subgroup:

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

(defthmd subgroup-index-pos
  (implies (subgroupp h g)
           (posp (subgroup-index h g))))

(defthmd order-subgroup-divides
  (implies (subgroupp h g)
           (divides (order h) (order g))))

(defthmd ord-divides-order
  (implies (and (groupp g)
		(in x g))
	   (divides (ord x g) (order g))))


;;---------------------------------------------------------------------------------------------------
;; Normal Subgroups and Quotient Groups
;;---------------------------------------------------------------------------------------------------

;; The conjugate of x by a:

(defund conj (x a g)
  (op (op a x g) (inv a g) g))

(defthm conj-in-g
  (implies (and (groupp g) (in x g) (in a g))
           (in (conj x a g) g)))

(defthmd conj-op
  (implies (and (groupp g)
                (in x g)
		(in y g)
		(in a g))
	   (equal (conj (op x y g) a g)
	          (op (conj x a g) (conj y a g) g))))

(defthmd inv-conj
  (implies (and (groupp g)
                (in x g)
		(in a g))
	   (equal (conj (inv x g) a g)
	          (inv (conj x a g) g))))


(defthmd conj-commute
  (implies (and (groupp g)
                (in x g)
		(in y g))
	   (iff (equal (conj x y g) x)
	        (equal (op x y g) (op y x g)))))

(defthmd subgroup-conj
  (implies (and (subgroupp h g)
                (in x h)
		(in y h))
	   (equal (conj y x h)
	          (conj y x g))))

(defthmd centralizer-conj-iff
  (implies (and (groupp g) (in a g))
           (iff (in x (centralizer a g))
	        (and (in x g) (equal (conj a x g) a)))))

(defthm conj-e
  (implies (and (groupp g) (in x g))
           (equal (conj x (e g) g)
	          x))
  :hints (("Goal" :in-theory (enable conj))))

(defthm conj-conj
  (implies (and (groupp g) (in x g) (in a g) (in b g))
           (equal (conj (conj x b g) a g)
	          (conj x (op a b g) g)))
  :hints (("Goal" :in-theory (enable conj)
                  :use ((:instance group-assoc (x a) (y (op b x g)) (z (inv b g)))
		        (:instance group-assoc (x (op a (op b x g) g)) (y (inv b g)) (z (inv a g)))
		        (:instance group-assoc (x a) (y b) (z x))
			(:instance prod-inv (x a) (y b))))))

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

(defund normalp (h g)
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

(defund normalp-cex (h g)
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
  (implies (and (normalp h g) (member x (lcosets h g)))
           (member x (qlist h g))))
                

(defthmd member-lcoset-qlist-iff
  (implies (normalp h g)
           (iff (member x (qlist h g))
                (member x (lcosets h g)))))

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
  (declare (xargs :measure (order g)))
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

(defun conj2coset (y x g)
  (lcoset (conjer y x g) (centralizer x g) g))

(defun coset2conj (c x g)
  (conj x (car c) g))

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
;; Class Equation
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
  (declare (xargs :measure (order g)))
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

) ;encapsulate


;---------------------------------------------------------------------------------------------------------------

(defun diff-member (x y)
  (if (consp x)
      (if (equal (car x) (car y))
	  (1+ (diff-member (cdr x) (cdr y)))
	0)
    ()))

(defthm diff-member-diff
  (implies (and (true-listp x) (true-listp y) (equal (len x) (len y)) (not (equal x y)))
	   (let ((n (diff-member x y)))
	     (and (natp n)
		  (< n (len x))
		  (not (equal (nth n x) (nth n y)))))))

(defun diff-entry (x y)
  (let ((i (diff-member x y)))
    (cons i (diff-member (nth i x) (nth i y)))))

(defthmd diff-row-diff
  (implies (and (natp m) (natp n) (matrixp x m n) (matrixp y m n) (not (equal x y)))
           (let ((i (diff-member x y)))
	     (and (natp i)
		  (< i m)
		  (not (equal (nth i x) (nth i y)))))))

(defthmd nth-row
  (implies (and (natp m) (natp n) (matrixp x m n) (natp i) (< i m))
	   (and (true-listp (nth i x))
		(equal (len (nth i x)) n))))
	   
(defthmd diff-entry-diff
  (implies (and (natp m) (natp n) (matrixp x m n) (matrixp y m n) (not (equal x y)))
	   (let* ((entry (diff-entry x y)) (i (car entry)) (j (cdr entry)))
	     (and (natp i) (< i m)
		  (natp j) (< j n)
		  (not (equal (nth j (nth i x)) (nth j (nth i y)))))))
  :hints (("Goal" :use (diff-row-diff
			(:instance nth-row (i (diff-member x y)))
			(:instance nth-row (i (diff-member x y)) (x y))
			(:instance diff-member-diff (x (nth (diff-member x y) x)) (y (nth (diff-member x y) y)))))))

(defthmd diff-group-diff
  (implies (and (groupp h)
                (groupp k)
		(equal (order h) (order k))
		(not (equal h k)))
	   (let* ((entry (diff-entry h k)) (i (car entry)) (j (cdr entry)))
	     (and (natp i) (< i (order h))
		  (natp j) (< j (order h))
		  (not (equal (nth j (nth i h)) (nth j (nth i k)))))))
  :hints (("Goal" :in-theory (enable groupp)
                  :use ((:instance diff-entry-diff (x h) (y k) (m (order h)) (n (order h)))))))

(defun diff-elt-1 (h k)
  (nth (car (diff-entry h k)) (elts h)))

(defun diff-elt-2 (h k)
  (nth (cdr (diff-entry h k)) (elts h)))

(defthmd diff-group-op
  (implies (and (groupp h)
                (groupp k)
		(equal (elts h) (elts k))
		(not (equal h k)))
	   (let ((x (diff-elt-1 h k)) (y (diff-elt-2 h k)))
	     (and (in x h)
	          (in y h)
		  (not (equal (op x y h) (op x y k))))))
  :hints (("Goal" :in-theory (enable op)
                  :use (diff-group-diff))))

(defthm subgroups-equal-elts
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(equal (elts h) (elts k)))
	   (equal h k))
  :rule-classes ()
  :hints (("Goal" :use (diff-group-op))))

(defthm abelian-group-center
  (implies (and (groupp g)
		(abelianp g))
	   (equal (center g) g))
  :hints (("Goal" :use ((:instance subgroups-equal-elts (h (center g)) (k g))))))

;-----------------------------------------------------------------------------------------------------------------------	   

(defthmd lcoset-member-lcoset
  (implies (and (subgroupp h g)
		(member-equal c (lcosets h g))
		(member-equal x c))
	   (equal (lcoset x h g) c))
  :hints (("Goal" :use (lcosets-cars
                        (:instance equal-lcoset (y x) (x (car c)))))))

(defthmd op-quotient-lcoset
  (implies (and (normalp h g)
                (in x (quotient g h ))
                (in y (quotient g h))
		(member-equal a x)
		(member-equal b y))
	   (equal (op x y (quotient g h))
	          (lcoset (op a b g) h g)))
  :hints (("Goal" :use (op-qop
                        (:instance lcoset-member-lcoset (x (op a b g)) (c (qop x y h g)))))))

(defthmd normalp-reverse
  (implies (and (normalp h g)
                (in x g)
		(in y g)
		(in (op x y g) h))
	   (in (op y x g) h))
  :hints (("Goal" :in-theory (enable conj)
                  :use ((:instance normalp-conj (x (op x y g)) (y (inv x g)))
		        (:instance group-assoc (x (inv x g)) (y x) (z y))))))

(defthmd sublistp-elts-quotient-lcosets
  (implies (normalp h g)
           (sublistp (elts (quotient g h)) (lcosets h g))))

(in-theory (disable qlist))

(defthmd sublistp-subgroup-lcosets
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (sublistp (elts h) (lcosets n g)))
  :hints (("Goal" :use ((:instance sublistp-elts-quotient-lcosets (h n))
                        (:instance subgroupp-sublistp (g (quotient g n)))
			(:instance sublistp-sublistp (l (elts h)) (m (elts (quotient g n))) (n (lcosets n g)))))))

(defthmd inv-quotient-lcoset
  (implies (and (normalp h g)
                (in x (quotient g h))
		(member-equal a x))
	   (equal (inv x (quotient g h))
	          (lcoset (inv a g) h g)))
  :hints (("Goal" :use (sublistp-elts-quotient-lcosets
                        (:instance normalp-reverse (x (inv (car x) g)) (y a))
                        (:instance lcosets-cars (c x))
			(:instance sublistp-lcoset-g (x (car x)))
			(:instance member-lcoset-iff (y a) (x (car x)))
			(:instance member-lcoset-iff (y (inv (car x) g)) (x (inv a g)))
			(:instance equal-lcoset (y (inv a g)) (x (inv (car x) g)))))))

(defthmd subgroup-subgroup
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(sublistp (elts h) (elts k)))
	   (subgroupp h k))
  :hints (("Goal" :use ((:instance not-subgroupp-cex (g k))))))

(defthmd subgroupp-transitive
  (implies (and (subgroupp h k) (subgroupp k g)) (subgroupp h g))
  :hints (("Goal" :in-theory (e/d (sublistp-sublistp subgroupp) (not-subgroupp-cex subgroupp-cex))
                  :use (not-subgroupp-cex
		        (:instance subgroup-op (x (car (subgroupp-cex h g))) (y (cadr (subgroupp-cex h g))) (g k))
		        (:instance subgroup-op (x (car (subgroupp-cex h g))) (y (cadr (subgroupp-cex h g))) (h k))))))

(defthmd subgroup-order-<=
  (implies (subgroupp h g)
           (<= (order h) (order g)))
  :hints (("Goal" :in-theory (enable subgroupp groupp)
                  :use ((:instance sublistp-<=-len (l (elts h)) (m (elts g)))))))

(defthmd power-in-quotient
  (implies (and (normalp h g)
                (in x (quotient g h))
		(natp n))
	   (in (power x n (quotient g h)) (quotient g h))))

(defthmd member-member-quotient
  (implies (and (normalp h g)
                (in x (quotient g h))
		(member-equal a x))
	   (in a g))
  :hints (("Goal" :use (car-member-qlist  
                        (:instance member-lcoset-g (x (car x)) (y a))))))

(defthmd power-lcoset
  (implies (and (normalp h g)
                (in x (quotient g h))
		(member-equal a x)
		(natp n))
	   (equal (power x n (quotient g h))
	          (lcoset (power a n g) h g)))
  :hints (("Subgoal *1/4" :in-theory (disable qop)
                          :use (member-member-quotient
			        (:instance power-in-quotient (n (1- n)))
			        (:instance member-self-lcoset (x (power a (1- n) g)))
			        (:instance op-quotient-lcoset (y (lcoset (power a (1- n) g) h g))
					   (b (power a (1- n) g)))))))

(defthmd ord-lcoset-divides
  (implies (and (normalp h g)
                (in x (quotient g h))
		(member-equal a x))
	   (divides (ord x (quotient g h))
		    (ord a g)))
  :hints (("Goal" :in-theory (disable member-lcoset-qlist)
                  :use (ord-power member-lcoset-qlist-iff ord<=order
                        (:instance lcosets-cars (c x))
			(:instance member-lcoset-g (x (car x)) (y a))
                        (:instance power-lcoset (n (ord a g)))
                        (:instance divides-ord (a x) (g (quotient g h)) (n (ord a g)))))))


(defthmd lcoset-member-lcoset
  (implies (and (subgroupp h g)
		(member-equal c (lcosets h g))
		(member-equal x c))
	   (equal (lcoset x h g) c)))

(defthm equal-ord-subgroup
  (implies (and (subgroupp h g)
                (in a h))
	   (equal (ord a h) (ord a g)))
  :hints (("Goal" :in-theory (e/d (divides) (ord-power))
                  :use ((:instance ord-power (n (ord a h)))
                        (:instance ord-power (g h) (n (ord a g)))))))

(defthmd equal-lcoset-lcoset-e
  (implies (and (subgroupp h g) (in x g)
                (equal (lcoset x h g) (lcoset (e g) h g)))
	   (in x h))
  :hints (("Goal" :use ((:instance member-lcoset-iff (y x))
                        (:instance member-lcoset-iff (y x) (x (e g)))))))

(defthmd prod-indices
  (implies (and (subgroupp h k)
                (subgroupp k g))
	   (equal (subgroup-index h g)
	          (* (subgroup-index k g)
		     (subgroup-index h k))))
  :hints (("Goal" :use (lagrange subgroupp-transitive order-pos
                        (:instance order-pos (g h))
                        (:instance order-pos (g k))
                        (:instance lagrange (g k))
			(:instance lagrange (h k))))))


;-----------------------------------------------------------------------------------------------------------------------

(defthmd member-powers-power
  (implies (and (groupp g) (in a g) (member x (powers a g)))
	   (equal (power a (index x (powers a g)) g)
		  x))
  :hints (("Goal" :in-theory (disable nth-ind)
	          :use ((:instance nth-ind (l (powers a g)))		  
			(:instance ind<len (l (powers a g)))
			(:instance member-powers (n (index x (powers a g))))))))
			
(defthmd abelianp-cyclic
  (implies (and (groupp g)
                (in a g))
	   (abelianp (cyclic a g)))
  :hints (("Goal" :use ((:instance not-abelianp-cex (g (cyclic a g)))
                        (:instance member-powers-power (x (car (abelianp-cex (cyclic a g)))))
                        (:instance member-powers-power (x (cadr (abelianp-cex (cyclic a g)))))
	                (:instance power+ (n (index (car (abelianp-cex (cyclic a g))) (powers a g)))
	                                  (m (index (cadr (abelianp-cex (cyclic a g))) (powers a g))))
	                (:instance power+ (n (index (cadr (abelianp-cex (cyclic a g))) (powers a g)))
	                                  (m (index (car (abelianp-cex (cyclic a g))) (powers a g))))))))

(defund group-gen (g)
  (elt-of-ord (order g) g))

(defthmd order-group-gen
  (implies (and (groupp g)
                (group-gen g))
	   (and (in (group-gen g) g)
	        (equal (ord (group-gen g) g)
		       (order g))))
  :hints (("Goal" :in-theory (enable group-gen)
                  :use ((:instance elt-of-ord-ord (n (order g)))))))

(defund cyclicp (g)
  (and (groupp g)
       (group-gen g)))

;; Once we have defined isomorphism, we shall prove that if (cyclicp g), then (cyclic (group-gen g) g)
;; is isomorphic to g.  For now, we have this:

(defthmd cyclicp-order
  (implies (cyclicp g)
	   (equal (order (cyclic (group-gen g) g))
		  (order g)))
  :hints (("Goal" :in-theory (enable group-gen cyclicp)
                  :use ((:instance elt-of-ord-ord (n (order g)))
                        (:instance order-ord (a (group-gen g)))))))

(defthmd member-cyclicp-power
  (implies (and (cyclicp g)
                (in x g))
	   (in x (cyclic (group-gen g) g)))
  :hints (("Goal" :in-theory (e/d (cyclicp permp) (permp-eq-len))
                  :use (order-group-gen
		        (:instance permp-eq-len (l (elts (cyclic (group-gen g) g))) (m (elts g)))))))

(defthm cyclic-cyclicp
  (implies (and (groupp g)
                (in a g))
	   (cyclicp (cyclic a g)))
  :hints (("Goal" :in-theory (e/d (group-gen cyclicp) (power-member))
                  :expand ((power a 1 g))
                  :use ((:instance ord-elt-of-ord (g (cyclic a g)) (n (ord a g)) (x a))
		        (:instance power-member (n 1))
		        (:instance ord-subgroup (x a) (h (cyclic a g)))))))

(defthm cyclicp-groupp
  (implies (cyclicp g)
           (and (groupp g)
	        (group-gen g)))
  :hints (("Goal" :in-theory (enable cyclicp))))

(defthmd permp-cyclic
  (implies (cyclicp g)
           (permp (elts (cyclic (group-gen g) g))
	          (elts g)))
  :hints (("Goal" :use (cyclicp-order order-group-gen))))

(local-defthmd ord-aux>=n
  (implies (and (posp n)
                (posp (ord-aux a n g)))
	   (>= (ord-aux a n g) n)))

(defthmd ord>1
  (implies (and (groupp g) (in a g))
	   (and (posp (ord a g))
	        (iff (equal (ord a g) 1)
		     (equal a (e g)))))
  :hints (("Goal" :in-theory (e/d (ord power) (divides-ord ord-aux))
                  :expand ((power a 1 g))
                  :use (ord<=order
		        (:instance ord-aux (n 1))
		        (:instance ord-aux>=n (n 2))))))

(local-defthmd cadr-not-e
  (implies (groupp g)
           (not (equal (cadr (elts g)) (e g))))
  :hints (("Goal" :in-theory (e/d (e) (in-e-g dlistp-elts non-nil-elts))
                  :use (in-e-g dlistp-elts non-nil-elts))))

;; Since this requires ord-divides-order, it should go into ../quotients.lisp:

(defthm primep-cyclicp
  (implies (and (groupp g)
		(primep (order g)))
	   (cyclicp g))
  :hints (("Goal" :in-theory (e/d (e group-gen cyclicp) (non-nil-elts))
                  :use (cadr-not-e
		        (:instance ord-elt-of-ord (x (cadr (elts g))) (n (order g)))
                        (:instance primep-no-divisor (p (order g)) (d (ord (cadr (elts g)) g)))
			(:instance ord<=order (a (cadr (elts g))))
			(:instance ord>1 (a (cadr (elts g))))
			(:instance ord-divides-order (x (cadr (elts g))))))))
			
(defthmd power-abelian
  (implies (and (groupp g)
                (abelianp g)
		(in x g)
		(in y g)
		(natp n))
	   (equal (op (power x n g) (power y n g) g)
	          (power (op x y g) n g)))		  
  :hints (("Subgoal *1/2" :use ((:instance group-assoc (y (power x (1- n) g)) (z (power y n g)))
                                (:instance group-assoc (x (power x (1- n) g)) (z (power y (1- n) g)))
				(:instance group-abelianp (x (power x (1- n) g)))
				(:instance group-assoc (x y) (y (power x (1- n) g)) (z (power y (1- n) g)))
				(:instance group-assoc (z (power (op x y g) (1- n) g)))))))

(defthmd power-inv
  (implies (and (groupp g)
                (in x g)
		(natp n))
	   (equal (power (inv x g) n g)
	          (inv (power x n g) g)))
  :hints (("Subgoal *1/2" :use ((:instance prod-inv (x (power x (1- n) g)) (y x))
                                (:instance power+ (a x) (n (1- n)) (m 1))))))


(local-defthmd power-lcm
  (implies (and (groupp g)
                (abelianp g)
		(in x g)
		(in y g))
	   (equal (power (op x y g) (lcm (ord x g) (ord y g)) g)
		  (e g)))
  :hints (("Goal" :use ((:instance power-abelian (n (lcm (ord x g) (ord y g))))
                        (:instance lcm-is-common-multiple (x (ord x g)) (y (ord y g)))
			(:instance ord>1 (a x))
			(:instance ord>1 (a x))
			(:instance divides-ord (a x) (n (lcm (ord x g) (ord y g))))
			(:instance divides-ord (a y) (n (lcm (ord x g) (ord y g))))))))

(defthmd ord-divides-lcm
  (implies (and (groupp g)
                (abelianp g)
		(in x g)
		(in y g))
	   (divides (ord (op x y g) g)
	            (lcm (ord x g) (ord y g))))
  :hints (("Goal" :use (power-lcm posp-lcm
			(:instance ord>1 (a x))
			(:instance ord>1 (a x))
			(:instance divides-ord (a (op x y g)) (n (lcm (ord x g) (ord y g))))))))

(defthmd power-
  (implies (and (groupp g) (in a g) (natp n) (natp m) (>= n m))
           (equal (op (power a n g) (power (inv a g) m g) g)
	          (power a (- n m) g)))
  :hints (("Goal" :use ((:instance power+ (n (- n m)))
                        (:instance power-inv (x a) (n m))
			(:instance group-assoc (x (power a (- n m) g)) (y (power a m g)) (z (power (inv a g) m g)))))))


;;------------------------------------------------------------------------------------------------------------------

;; Recognizer of powers of an integer greater than 1:

(in-theory (enable divides))

(defun powerp (n p)
  (if (and (natp p) (> p 1) (posp n) (divides p n))
      (powerp (/ n p) p)
    (equal n 1)))

(defthmd p-divides-power-p
  (implies (and (powerp n p)
                (not (equal n 1)))
	   (divides p n)))

(defun log (n p)
  (if (and (natp p) (> p 1) (posp n) (integerp (/ n p)))
      (1+ (log (/ n p) p))
    0))

(local-defthmd max-power-p-dividing-1
  (implies (and (primep p) (posp n))
           (and (divides (expt p (log n p)) n)
	        (not (divides (expt p (1+ (log n p))) n)))))

(defthmd max-power-p-dividing
  (implies (and (primep p)
                (posp n)
		(natp k))
	   (iff (divides (expt p k) n)
	        (<= k (log n p))))	   
  :hints (("Goal" :use (max-power-p-dividing-1
                        (:instance divides-transitive (x (expt p k)) (y (expt p (log n p))) (z n))
                        (:instance divides-transitive (y (expt p k)) (x (expt p (1+ (log n p)))) (z n))))))

(defthmd powerp-log
  (implies (and (natp p) (> p 1) (powerp n p))
           (equal (expt p (log n p)) n)))

(defthm powerp*p
  (implies (and (natp p) (> p 1) (powerp n p))
           (powerp (* p n) p))
  :hints (("Goal" :in-theory (enable powerp))))

(defthm powerp-power
  (implies (and (natp p) (> p 1) (natp n))
           (powerp (expt p n) p))
  :hints (("Goal" :induct (fact n))))

(local-defthmd divides-power-1
  (implies (and (primep p) (posp k) (posp m) (divides m (expt p k)))
           (or (divides p m)
	       (divides m (expt p (1- k)))))
  :hints (("Goal" :use ((:instance euclid (a m) (b (/ (expt p k) m)))))))

(local-defun divides-power-induct (p m k)
  (if (and (primep p) (posp m) (posp k))
      (list (divides-power-induct p m (1- k))
            (divides-power-induct p (/ m p) (1- k)))
    ()))

(defthmd divides-power
  (implies (and (primep p) (natp k) (posp m) (divides m (expt p k)))
           (powerp m p))	   
  :hints (("Goal" :induct (divides-power-induct p m k))
          ("Subgoal *1/1" :use (divides-power-1))))

(defthmd powerp-divides
  (implies (and (primep p) (powerp n p) (posp m) (divides m n))
           (powerp m p))
  :hints (("Goal" :use (powerp-log (:instance divides-power (k (log n p)))))))

(defthm not-powerp-prime
  (implies (and (primep q) (posp n) (powerp q n))
           (equal q n))
  :rule-classes ()
  :hints (("Goal" :use ((:instance primep-no-divisor (p q) (d n))))))

(defthm powerp-prime-divisor
  (implies (and (primep p)
                (primep q)
		(powerp n p)
		(divides q n))
           (equal p q))
  :rule-classes ()
  :hints (("Goal" :use ((:instance powerp-divides (m q))
                        (:instance p-divides-power-p (n q))
		        (:instance primep-no-divisor (d p) (p q))))))

(defthmd least-prime-divisor-powerp
  (implies (and (powerp n p)
                (primep p)                
                (> n 1))
	   (equal (least-prime-divisor n)
	          p))
  :hints (("Goal" :use (primep-least-divisor
                        (:instance least-divisor-divides (k 2))
                        (:instance powerp-prime-divisor (q (least-prime-divisor n)))))))

(defun least-divisor-not-p (n p)
  (declare (xargs :measure (nfix n)))
  (if (and (natp n) (> n 1))
      (let ((q (least-prime-divisor n)))
        (if (= q p)
	    (least-divisor-not-p (/ n p) p)
	  q))
    ()))

(local-defthmd hack-1
  (implies (and (posp n) (posp q) (<= q n) (<= (/ n q) 1))
           (equal (/ n q) 1))
  :hints (("Goal" :nonlinearp t)))

(local-defthmd hack-2
  (implies (and (integerp a) (integerp b))
           (integerp (* a b))))

(local-defthmd hack-3
  (implies (and (primep p) (primep q) (natp n) (divides q (/ n p)))
           (divides q n))
  :hints (("Goal" :use ((:instance hack-2 (a (/ (/ n p) q)) (b p))))))

;; In n is not a power of prime p, then n has a prime divisor other than p:

(defthmd primep-least-divisor-not-p
  (implies (and (natp n)
                (> n 1)
                (primep p)
		(not (powerp n p)))
	   (let ((q (least-divisor-not-p n p)))
	     (and (primep q)
	          (not (= q p))
	          (divides q n))))
  :hints (("Subgoal *1/2" :use (primep-least-divisor (:instance least-divisor-divides (k 2))))
          ("Subgoal *1/1" :use ((:instance least-divisor-divides (k 2))
	                        (:instance powerp-power (n 0) (p (least-prime-divisor n))))
			  :expand ((least-divisor-not-p n p)))
	  ("Subgoal *1/1.2" :use ((:instance least-divisor-divides (k 2) (n p))
	                          (:instance hack-1 (q (least-prime-divisor n)))))
	  ("subgoal *1/1.1" :use ((:instance hack-3 (p (least-prime-divisor n))
	                                            (q (least-divisor-not-p (* n (/ (least-prime-divisor n))) (least-prime-divisor n))))))))

;; Recognizer of p-groups:

(defund p-groupp (g p)
  (and (primep p)
       (groupp g)
       (powerp (order g) p)))

(defthm p-groupp-groupp
  (implies (p-groupp g p)
           (groupp g))
  :hints (("Goal" :in-theory (enable p-groupp))))

(defthmd p-groupp-ord-powerp
  (implies (and (p-groupp g p)
		(in x g))
	   (powerp (ord x g) p))
  :hints (("Goal" :in-theory (enable p-groupp)
                  :use (ord-divides-order (:instance powerp-divides (m (ord x g)) (n (order g)))))))

(defthmd not-p-groupp-divisor
  (implies (and (primep p)
                (groupp g)
		(> (order g) 1)
		(not (p-groupp g p)))
	   (let ((q (least-divisor-not-p (order g) p)))
	     (and (primep q)
	          (not (= q p))
	          (divides q (order g)))))
  :hints (("Goal" :in-theory (enable p-groupp)
                  :use ((:instance primep-least-divisor-not-p (n (order g)))))))

(defthmd not-p-groupp-ord-prime
  (implies (and (primep p)
                (groupp g)
		(> (order g) 1)
		(not (p-groupp g p)))
	   (let* ((q (least-divisor-not-p (order g) p))
	          (x (elt-of-ord q g)))
	     (and (primep q)
	          (not (= q p))
		  (in x g)
	          (equal (ord x g) q))))
  :hints (("Goal" :in-theory (enable p-groupp)
                  :use (not-p-groupp-divisor
		        (:instance cauchy (p (least-divisor-not-p (order g) p)))))))

(defthmd not-p-groupp-not-powerp-ord
  (implies (and (primep p)
                (groupp g)
		(> (order g) 1)
		(not (p-groupp g p)))
	   (let* ((q (least-divisor-not-p (order g) p))
	          (x (elt-of-ord q g)))
	     (not (powerp (ord x g) p))))
  :hints (("Goal" :in-theory (enable p-groupp)
                  :use (not-p-groupp-ord-prime
		        (:instance not-powerp-prime (n p) (q (least-divisor-not-p (order g) p)))))))


;-----------------------------------------------------------------------------------------------------------------------	   

(local-defthmd center-p-group-1
  (implies (and (primep p)
                (p-groupp g p)
                (in x g)
		(not (in x (center g))))
	   (divides p (subgroup-index (centralizer x g) g)))
  :hints (("Goal" :in-theory (enable p-groupp)
                  :use (order-centralizer-not-center
                        (:instance powerp-divides (m (subgroup-index (centralizer x g) g))
			                           (n (order g)))
			(:instance lagrange (h (centralizer x g)))
			(:instance p-divides-power-p (n (subgroup-index (centralizer x g) g)))))))

(local-defthmd center-p-group-2
  (implies (and (groupp g)
		(member c (conjs-list g)))
	   (and (in (car c) g)
	        (equal (conjs (car c) g) c)
	        (not (in (car c) (center g)))))
  :hints (("Goal" :use (conjs-list-cars
                        (:instance member-append-list (x (car c)) (l c) (m (conjs-list g)))))))

(local-defthmd center-p-group-3
  (implies (and (primep p)
                (p-groupp g p)
		(member c (conjs-list g)))
	   (divides p (len c)))
  :hints (("Goal" :use (center-p-group-2
                        (:instance center-p-group-1 (x (car c)))
			(:instance len-conjs-cosets (x (car c)))))))

(local-defthmd center-p-group-4
  (implies (and (primep p)
                (p-groupp g p)
		(sublistp l (conjs-list g)))
	   (divides p (len (append-list l))))
  :hints (("Subgoal *1/2" :use ((:instance center-p-group-3 (c (car l)))
                                (:instance divides-sum (x p) (y (len (car l))) (z (len (append-list (cdr l)))))))))

(local-defthmd center-p-group-5
  (implies (and (primep p)
                (p-groupp g p))
	   (divides p (len (append-list (conjs-list g)))))
  :hints (("Goal" :use ((:instance center-p-group-4 (l (conjs-list g)))))))

(defthmd center-p-group
  (implies (and (primep p)
                (p-groupp g p)                
		(> (order g) 1))
	   (divides p (order (center g))))
  :hints (("Goal" :in-theory (enable p-groupp)
                  :use (class-equation center-p-group-5
                        (:instance divides-sum (x p) (y (order g)) (z (- (len (append-list (conjs-list g))))))
			(:instance divides-minus (x p) (y (len (append-list (conjs-list g)))))))))

(defthmd subgroup-index-rewrite
  (implies (subgroupp h g)
           (equal (subgroup-index h g)
                  (/ (order g) (order h))))
  :hints (("Goal" :use (lagrange (:instance order-pos (g h))))))


;-----------------------------------------------------------------------------------------------------------------------	   

(defthm normalp-center
  (implies (groupp g)
	   (normalp (center g) g))
  :hints (("Goal" :use ((:instance not-normalp-cex (h (center g)))
                        (:instance center-commutes (a (car (normalp-cex (center g) g))) (x (cadr (normalp-cex (center g) g))))
			(:instance conj-commute (x (car (normalp-cex (center g) g))) (y (cadr (normalp-cex (center g) g))))))))

(local-defund inx (x g)
  (index (lcoset x (center g) g)
         (powers (group-gen (quotient g (center g)))
	         (quotient g (center g)))))

(local-defthmd natp-inx
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g))
           (natp (inx x g)))
  :hints (("Goal" :in-theory (enable inx)
                  :use ((:instance member-lcoset-cosets (h (center g)))))))

(local-defund gen (g)
  (car (group-gen (quotient g (center g)))))

(local-defthm in-gen-g
  (implies (and (groupp g)
                (cyclicp (quotient g (center g))))
	   (in (gen g) g))
  :hints (("Goal" :in-theory (enable cyclicp gen)
                  :use ((:instance order-group-gen (g (quotient g (center g))))
		        (:instance member-qlist-car (h (center g)) (x (group-gen (quotient g (center g)))))))))

(local-defund pow (x g)
  (power (gen g) (inx x g) g))

(local-defthmd in-pow-g
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g))
           (in (pow x g) g))
  :hints (("Goal" :in-theory (enable gen pow cyclicp)
                  :use (natp-inx in-gen-g
                        (:instance order-group-gen (g (quotient g (center g))))))))
  
(local-defund zelt (x g)
  (op (inv (pow x g) g) x g))

(local-defthmd in-zelt-g
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g))
	   (in (zelt x g) g))
  :hints (("Goal" :in-theory (enable zelt)
                  :use (in-pow-g))))

(local-defthmd x-pow-zelt
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g))
	   (equal (op (pow x g) (zelt x g) g)
	          x))
  :hints (("Goal" :in-theory (enable in-pow-g group-assoc zelt))))

(local-defthmd zelt-center-1
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g))
           (member-equal (lcoset x (center g) g)
	                 (powers (group-gen (quotient g (center g)))
			         (quotient g (center g)))))
  :hints (("Goal" :in-theory (enable cyclicp)
                  :use ((:instance member-lcoset-cosets (h (center g)))
                        (:instance order-group-gen (g (quotient g (center g))))
                        (:instance member-cyclicp-power (g (quotient g (center g))) (x (lcoset x (center g) g)))))))

(local-defthmd zelt-center-2
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g))
           (equal (lcoset x (center g) g)
	          (power (group-gen (quotient g (center g)))
		         (inx x g)
			 (quotient g (center g)))))
  :hints (("Goal" :in-theory (enable inx cyclicp)
                  :use (zelt-center-1
                        (:instance order-group-gen (g (quotient g (center g))))
                        (:instance member-powers-power (g (quotient g (center g)))
			                               (a (group-gen (quotient g (center g))))
			                               (x (lcoset x (center g) g)))))))

(local-defthmd zelt-center-3
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g))
           (equal (lcoset x (center g) g)
	          (lcoset (pow x g) (center g) g)))
  :hints (("Goal" :in-theory (enable gen pow cyclicp)
                  :use (zelt-center-2
                        (:instance order-group-gen (g (quotient g (center g))))
                        (:instance lcoset-power (h (center g))
			                        (x (group-gen (quotient g (center g))))
						(n (inx x g)))))))

(local-defthmd zelt-center
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g))
           (in (zelt x g) (center g)))
  :hints (("Goal" :in-theory (enable pow zelt)
                  :use (zelt-center-3 natp-inx in-pow-g
                        (:instance order-group-gen (g (quotient g (center g))))
			(:instance member-self-lcoset (h (center g)))
                        (:instance member-lcoset-iff (h (center g)) (x (pow x g)) (y x))))))

(local-defthmd xy-pow-zelt-1
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g)
		(in y g))
           (equal (op x y g)
	          (op (op (pow x g) (zelt x g) g)
		      (op (pow y g) (zelt y g) g)
		      g)))
  :hints (("Goal" :use (x-pow-zelt (:instance x-pow-zelt (x y))))))

(local-defthmd xy-pow-zelt-2
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g)
		(in y g))
           (equal (op x y g)
	          (op (pow x g)
		      (op (op (zelt x g) (pow y g) g)
		          (zelt y g)
		          g)
		      g)))
  :hints (("Goal" :in-theory (enable group-assoc)
                  :use (xy-pow-zelt-1 in-pow-g in-zelt-g
                        (:instance in-pow-g (x y))
                        (:instance in-zelt-g (x y))))))

(local-defthmd xy-pow-zelt-3
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g)
		(in y g))
           (equal (op x y g)
	          (op (pow x g)
		      (op (op (pow y g) (zelt x g) g)
		          (zelt y g)
		          g)
		      g)))
  :hints (("Goal" :in-theory (enable group-assoc)
                  :use (xy-pow-zelt-2 zelt-center
                        (:instance in-pow-g (x y))
                        (:instance center-commutes (a (zelt x g)) (x (pow y g)))))))

(local-defthmd xy-pow-zelt-4
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g)
		(in y g))
           (equal (op x y g)
	          (op (op (pow x g) (pow y g) g)
		      (op (zelt x g) (zelt y g) g)
		      g)))
  :hints (("Goal" :in-theory (enable group-assoc)
                  :use (xy-pow-zelt-3 in-pow-g in-zelt-g
                        (:instance in-pow-g (x y))
                        (:instance in-zelt-g (x y))))))

(local-defthmd xy-pow-zelt-5
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g)
		(in y g))
           (equal (op (pow x g) (pow y g) g)
	          (op (pow y g) (pow x g) g)))
  :hints (("Goal" :in-theory (enable gen pow cyclicp)
                  :use (natp-inx in-gen-g
                        (:instance order-group-gen (g (quotient g (center g))))
			(:instance power+ (a (gen g)) (n (inx x g)) (m (inx y g)))
			(:instance power+ (a (gen g)) (n (inx y g)) (m (inx x g)))))))

(defthmd quotient-center-cyclic-commute
  (implies (and (groupp g)
                (cyclicp (quotient g (center g)))
		(in x g)
		(in y g))
	   (equal (op x y g) (op y x g)))
  :hints (("Goal" :use (xy-pow-zelt-4 xy-pow-zelt-5 zelt-center
                        (:instance xy-pow-zelt-4 (x y) (y x))			
                        (:instance center-commutes (a (zelt x g)) (x (zelt y g)))
	                (:instance in-zelt-g (x y))))))

(defthmd quotient-center-cyclic-abelian
  (implies (and (groupp g)
                (cyclicp (quotient g (center g))))
	   (abelianp g))
  :hints (("Goal" :use (not-abelianp-cex 
                        (:instance quotient-center-cyclic-commute (x (car (abelianp-cex g))) (y (cadr (abelianp-cex g))))))))

	   
;-----------------------------------------------------------------------------------------------------------------------	   

(defthm ordp-sublistp
  (implies (and (groupp g) (ordp l g))
           (sublistp l (elts g))))

(local-defthm ordp-nthcdr
  (implies (and (groupp g) (natp n))
           (ordp (nthcdr n (elts g)) g)))

(local-defthm sublistp-cdr
  (implies (and (sublistp l m) (not (member-equal (car m) l)))
           (sublistp l (cdr m))))

(local-defun cdr+1-induct (n l)
  (if (consp l)
      (list n (cdr+1-induct (1+ n) (cdr l)))
    ()))
    
(local-defthmd equal-l-elts-1
  (implies (and (groupp g)
                (ordp l g)
		(natp n)
		(permp l (nthcdr n (elts g))))
	   (equal (nthcdr n (elts g)) l))
  :hints (("Goal" :induct (cdr+1-induct n l))
          ("Subgoal *1/1" :in-theory (enable permp)
	                  :use ((:instance car-ordp-minimal (x (car (nthcdr n (elts g)))))
			        (:instance car-ordp-minimal (x (car l)) (l (nthcdr n (elts g))))))
          ("Subgoal *1/2" :in-theory (enable permp))))

(local-defthmd equal-l-elts-2
  (implies (and (groupp g)
                (ordp l g)
		(permp l (elts g)))
	   (equal (elts g) l))
  :hints (("Goal" :use ((:instance equal-l-elts-1 (n 0))))))

(defthmd equal-l-elts
  (implies (and (groupp g)
                (ordp l g)
		(sublistp (elts g) l))
	   (equal (elts g) l))
  :hints (("Goal" :in-theory (enable permp)
                  :use (equal-l-elts-2))))

(defthm ordp-subgroup-equal
  (implies (and (subgroupp h g)
                (equal (order h) (order g))
		(ordp (elts h) g))
	   (equal h g))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (permp) (permp-eq-len))
                  :use ((:instance subgroups-equal-elts (k g))
                        (:instance equal-l-elts (l (elts h)))
			(:instance permp-eq-len (l (elts h)) (m (elts g)))))))

;; A non-trivial subgroup has a non-trivial element:

(defthmd order-1-trivial
  (implies (and (subgroupp h g)
                (equal (order h) 1))
           (equal (trivial-subgroup g) h))
  :hints (("Goal" :in-theory (e/d (e) (subgroup-e))
                  :use (subgroup-e
                        (:instance subgroups-equal-elts (k (trivial-subgroup g)))
                        (:instance dlistp-len-1 (l (elts h)))))))

(defthmd not-trivial-elt
  (implies (and (subgroupp h g)
                (not (equal h (trivial-subgroup g))))
	   (and (in (cadr (elts h)) h)
	        (not (equal (cadr (elts h)) (e g)))))
  :hints (("Goal" :in-theory (e/d (e) (dlistp-elts subgroup-e))
                  :use (subgroup-e order-1-trivial
		        (:instance dlistp-elts (g h))))))

(defthmd iff-trivial-order-1
  (implies (subgroupp h g)
           (iff (equal (trivial-subgroup g) h)
	        (equal (order h) 1)))
  :hints (("Goal" :use (order-1-trivial not-trivial-elt))))

(defthm normalp-trivial-subgroup
  (implies (groupp g)
           (normalp (trivial-subgroup g) g))
  :hints (("Goal" :in-theory (enable conj)
	          :use ((:instance not-normalp-cex (h (trivial-subgroup g)))))))

(defthm trivial-subgroup-subgroup
  (implies (subgroupp h g)
           (equal (trivial-subgroup h)
	          (trivial-subgroup g)))
  :hints (("Goal" :in-theory (e/d (trivial-subgroup) (subgroup-e))
                  :use (subgroup-e))))


;;-----------------------------------------------------------------------------------------------------------------------

(defthm dlistp-int-elts
  (implies (subgroupp h g)
	   (dlistp (intersection-equal (elts h) (elts k)))))


(local-defthm sublistp-int-elts-1
  (implies (and (subgroupp h g) (sublistp l (elts h)))
	   (and (sublistp (intersection-equal l (elts k)) (elts g))
		(sublistp (intersection-equal l (elts k)) (elts h))
		(sublistp (intersection-equal l (elts k)) (elts k))))
  :hints (("Subgoal *1/3" :expand ((intersection-equal l (car k))))
	  ("Subgoal *1/1" :expand ((intersection-equal l (car k))))))

(defthm sublistp-int-elts
  (implies (subgroupp h g)
	   (and (sublistp (intersection-equal (elts h) (elts k)) (elts g))
		(sublistp (intersection-equal (elts h) (elts k)) (elts h))
		(sublistp (intersection-equal (elts h) (elts k)) (elts k)))))

(defthm car-int-elts
  (implies (and (subgroupp h g) (subgroupp k g))
	   (and (consp (intersection-equal (elts h) (elts k)))
		(equal (car (intersection-equal (elts h) (elts k))) (e g))))
  :hints (("Goal" :expand ((intersection-equal (elts h) (elts k)))
	          :in-theory (e/d (e) (subgroup-e in-e-g non-nil-elts))
		  :use (in-e-g non-nil-elts subgroup-e
		        (:instance non-nil-elts (g h))
			(:instance in-e-g (g h))
		        (:instance non-nil-elts (g k))
			(:instance in-e-g (g k))
		        (:instance subgroup-e (h k))))))

(defthm int-elts-closed
  (implies (and (subgroupp h g) (subgroupp k g)
		(member-equal x (intersection-equal (elts h) (elts k)))
		(member-equal y (intersection-equal (elts h) (elts k))))
	   (member-equal (op x y g) (intersection-equal (elts h) (elts k))))
  :hints (("Goal" :in-theory (disable group-closure subgroup-op)
                  :use (subgroup-op
		        (:instance subgroup-op (h k))
			(:instance group-closure (g h))
			(:instance group-closure (g k))))))

(defthm int-elts-inv
  (implies (and (subgroupp h g) (subgroupp k g)
		(member-equal x (intersection-equal (elts h) (elts k))))
	   (member-equal (inv x g) (intersection-equal (elts h) (elts k))))
  :hints (("Goal" :in-theory (disable group-left-inverse subgroup-inv)
                  :use (subgroup-inv
		        (:instance subgroup-inv (h k))
			(:instance group-left-inverse (g h))
			(:instance group-left-inverse (g k))))))

(defsubgroup group-intersection (h k) g
  (and (subgroupp h g) (subgroupp k g))
  (intersection-equal (elts h) (elts k)))

(defthm subgroupp-int-both
  (implies (and (subgroupp h g)
		(subgroupp k g))
	   (and (subgroupp (group-intersection h k g) h)
		(subgroupp (group-intersection h k g) k)))
  :hints (("Goal" :use ((:instance subgroup-subgroup (h (group-intersection h k g)))
                        (:instance subgroup-subgroup (h (group-intersection h k g)) (k h))))))

(local-defthm ordp-int-elts-1
  (implies (and (sublistp l (elts h)) (ordp l h))
	   (and (ordp (intersection-equal l m) h)
	        (or (endp (intersection-equal l m))
		    (<= (ind (car l) h) (ind (car (intersection-equal l m)) h)))))
  :hints (("Subgoal *1/5" :expand ((intersection-equal () m)))
          ("Subgoal *1/3" :expand ((intersection-equal () m) (intersection-equal l m)))
          ("Subgoal *1/1" :expand ((intersection-equal l m)))))

(defthmd ordp-int-elts
  (implies (groupp h)
           (ordp (intersection-equal (elts h) l)
                 h)))

(defthm trivial-subgroup-intersection
  (implies (subgroupp h g)
           (and (equal (group-intersection h (trivial-subgroup g) g)
	               (trivial-subgroup g))
	        (equal (group-intersection (trivial-subgroup g) h g)
	               (trivial-subgroup g))))
  :hints (("Goal" :use ((:instance not-trivial-elt (h (group-intersection h (trivial-subgroup g) g)))
                        (:instance not-trivial-elt (h (group-intersection (trivial-subgroup g) h g)))))))

(defthmd in-trivial-subgroup
  (implies (and (groupp g)
                (in x (trivial-subgroup g)))
	   (equal (e g) x))
  :hints (("Goal" :in-theory (e/d (e) (TRIVIAL-SUBGROUP-ELTS))
                  :use (TRIVIAL-SUBGROUP-ELTS))))



;;-----------------------------------------------------------------------------------------------------------------------

(defthmd p-squared-divisors
  (implies (and (primep p)
                (posp a)
		(divides a (* p p)))
	   (member-equal a (list 1 p (* p p))))
  :hints (("Goal" :expand ((powerp a p) (POWERP (* A (/ P)) P))
                  :use ((:instance divides-power (k 2) (m a))
		        (:instance divides-leq (x a) (y (* p p)))
		        (:instance divides-leq (x a) (y p))))))

(defthmd powerp-p-squared
  (implies (and (groupp g)
                (primep p)
		(equal (order g) (* p p)))
           (p-groupp g p))
  :hints (("Goal" :in-theory (enable p-groupp))))

(defthmd p-squared-abelian
  (implies (and (groupp g)
		(primep p)
		(equal (order g) (* p p)))
	   (abelianp g))
  :hints (("Goal" :in-theory (disable abelianp-center)
                  :use (center-p-group quotient-center-cyclic-abelian abelianp-center powerp-p-squared
                        (:instance p-squared-divisors (a (order (center g))))
			(:instance lagrange (h (center g)))
			(:instance primep-cyclicp (g (quotient g (center g))))
			(:instance ordp-subgroup-equal (h (center g)))))))


;;-----------------------------------------------------------------------------------------------------------------------

(defthmd equal-lcosets-iff
  (implies (and (subgroupp h g)
                (in x g)
		(in y g))
           (iff (equal (lcoset x h g) (lcoset y h g))
	        (in (op (inv x g) y g) h)))
  :hints (("Goal" :use (member-lcoset-iff equal-lcoset
                        (:instance member-self-lcoset (x y))))))

(defthmd inverse-cancel
  (implies (and (groupp g)
                (in x g)
		(in y g)
		(in z g))
	   (equal (op (inv (op x z g) g) (op x y g) g)
	          (op (inv z g) y g)))
  :hints (("Goal" :in-theory (enable prod-inv)
                  :use ((:instance group-assoc (x (inv z g)) (y (inv x g)) (z (op x y g)))
		        (:instance group-assoc (x (inv x g)) (y x) (z y))))))

(defthmd equal-lcosets-cancel
  (implies (and (subgroupp h g)
                (in x g)
		(in y g)
		(in z g))
           (iff (equal (lcoset (op x y g) h g) (lcoset (op x z g) h g))
	        (equal (lcoset y h g) (lcoset z h g))))
  :hints (("Goal" :use (inverse-cancel
                        (:instance equal-lcosets-iff (x z))
			(:instance equal-lcosets-iff (x (op x z g)) (y (op x y g)))))))


;;-----------------------------------------------------------------------------------------------------------------------

(defthmd permp-normalp
  (implies (and (normalp h g)
                (subgroupp k g)
		(permp (elts h) (elts k)))
	   (normalp k g))
  :hints (("Goal" :in-theory (e/d (permp) (normalp-conj))
                  :use ((:instance not-normalp-cex (h k))
                        (:instance normalp-conj (x (car (normalp-cex k g))) (y (cadr (normalp-cex k g))))))))


;;-----------------------------------------------------------------------------------------------------------------------

;; Given a subgroup h of a quotient group g/n, we construct a corresponding subgroup (lift h n g) of g.
;; Its element list is constructed by appending the elements of h:

(defund append-elts (h)
  (append-list (elts h)))

(defthm car-append-elts
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (and (consp (append-elts h))
	        (equal (car (append-elts h))
		       (e g))))
  :hints (("Goal" :in-theory (e/d (e append-elts) (non-nil-elts))
                  :expand ((APPEND-LIST (CAR H))
		           (APPEND (CAR (CAR H)) (APPEND-LIST (CDR (CAR H)))))
		  :use (non-nil-elts in-e-g order-pos
		        (:instance subgroup-e (g (quotient g n)))
		        (:instance car-qe (h n))))))

;; Move to lists.lisp:

(defthmd sublistp-append-list
  (implies (and (sublistp l m)
                (sublistp (append-list m) n))
           (sublistp (append-list l) n)))

(defthmd sublistp-dlistp-list
  (implies (and (dlistp-list m)
                (sublistp l m))
	   (dlistp-list l)))

(local-defthm sublistp-append-elts
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (sublistp (append-elts h) (elts g)))
  :hints (("Goal" :in-theory (enable append-elts)
                  :use (sublistp-subgroup-lcosets
                        (:instance sublistp-append-list (l (elts h)) (m (lcosets n g)) (n (elts g)))
                        (:instance sublistp-lcosets-elts (h n))))))

(defthm dlistp-append-elts
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (dlistp (append-elts h)))
  :hints (("Goal" :in-theory (enable append-elts)
                  :use (sublistp-subgroup-lcosets
                        (:instance disjointp-pairwise-sublistp (l (elts h)) (m (lcosets n g)))
			(:instance sublistp-dlistp-list (l (elts h)) (m (lcosets n g)))
			(:instance dlistp-append-list (l (elts h)))))))

(defthm member-append
  (implies (or (member-equal x l) (member-equal x m))
           (member-equal x (append l m))))

(local-defthmd member-append-elts-1
  (implies (and (normalp n g)
                (sublistp l (lcosets n g))
		(in x g)
		(member-equal (lcoset x n g) l))
	   (member x (append-list l)))
  :hints (("Subgoal *1/2" :use ((:instance member-self-lcoset (h n))))))

(defthmd member-append-iff
  (iff (or (member-equal x l) (member-equal x m))
       (member-equal x (append l m))))

(local-defthmd member-append-elts-2
  (implies (and (normalp n g)
                (sublistp l (lcosets n g))
		(in x g)
		(member x (append-list l)))
	   (member-equal (lcoset x n g) l))	   
  :hints (("Subgoal *1/3" :use ((:instance lcosets-cars (c (car l)) (h n))
                                (:instance equal-lcoset (y x) (h n) (x (caar l)))
				(:instance member-append-iff (l (car l)) (m (append-list (cdr l))))))))

(local-defthmd member-append-elts
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(in x g))
           (iff (member x (append-elts h))
	        (member-equal (lcoset x n g) (elts h))))	   
  :hints (("Goal" :in-theory (enable append-elts)
                  :use (sublistp-subgroup-lcosets
		        (:instance member-append-elts-1 (l (elts h)))
                        (:instance member-append-elts-2 (l (elts h)))))))

(local-defthmd append-elts-closed-1
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(member-equal x (append-elts h))
		(member-equal y (append-elts h)))
           (in (qop (lcoset x n g) (lcoset y n g) n g) h))
  :hints (("Goal" :in-theory (disable lcoset-member-lcoset group-closure)
                  :use (member-append-elts sublistp-subgroup-lcosets sublistp-append-elts
                        (:instance member-append-elts (x y))
			(:instance member-self-lcoset (h n))
			(:instance member-self-lcoset (h n) (x y))
			(:instance group-closure (g h) (x (lcoset x n g)) (y (lcoset y n g)))))))

(defthm append-elts-closed
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(member-equal x (append-elts h))
		(member-equal y (append-elts h)))
           (member-equal (op x y g) (append-elts h)))
  :hints (("Goal" :use (append-elts-closed-1 member-append-elts sublistp-append-elts
                        (:instance member-append-elts (x y))
                        (:instance member-append-elts (x (op x y g)))
			(:instance op-quotient-lcoset (h n) (x (lcoset x n g)) (y (lcoset y n g)) (a x) (b y))))))

(local-defthmd append-elts-inv-1
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(member-equal x (append-elts h)))
           (in (qinv (lcoset x n g) n g) h))
  :hints (("Goal" :in-theory (disable lcoset-member-lcoset group-left-inverse)
                  :use (member-append-elts sublistp-subgroup-lcosets sublistp-append-elts
			(:instance member-self-lcoset (h n))
			(:instance group-left-inverse (g h) (x (lcoset x n g)))))))

(defthm append-elts-inv
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(member-equal x (append-elts h)))
           (member-equal (inv x g) (append-elts h)))
  :hints (("Goal" :use (append-elts-inv-1 member-append-elts sublistp-append-elts
                        (:instance member-append-elts (x (inv x g)))
			(:instance inv-quotient-lcoset (h n) (x (lcoset x n g)) (a x))))))

(defthm append-elts-non-nil
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (not (member-equal () (append-elts h))))
  :hints (("Goal" :in-theory (disable non-nil-elts)
                  :use (non-nil-elts sublistp-append-elts))))                        

(local (in-theory (enable sublistp-append-elts)))

(defsubgroup lift (h n) g
  (and (normalp n g)
       (subgroupp h (quotient g n)))
  (append-elts h))

(defthmd car-elts-h
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (equal (e h) (lcoset (e g) n g))))

(local-defthmd sublistp-n-append-elts-1
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(sublistp l (elts n)))
	   (sublistp l (lcoset (e g) n g)))
  :hints (("Subgoal *1/2" :use ((:instance member-lcoset-iff (h n) (y (car l)) (x (e g)))))))

(local-defthmd sublistp-n-append-elts-2
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (sublistp (elts n) (lcoset (e g) n g)))
  :hints (("Goal" :in-theory (enable sublistp-n-append-elts-1))))

(defthmd sublistp-append-2
  (implies (sublistp l m)
           (sublistp l (append m n))))

(defthmd sublistp-n-append-elts
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (sublistp (elts n) (append-elts h)))
  :hints (("Goal" :in-theory (e/d (e append-elts) (QUOTIENT-E))
                  :use (sublistp-n-append-elts-2 car-elts-h
                        (:instance sublistp-append-2 (l (elts n)) (m (car (elts h))) (n (append-list (cdr (elts h)))))))))

(defthmd lift-subgroup
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (subgroupp n (lift h n g)))
  :hints (("Goal" :use (sublistp-n-append-elts
                        (:instance subgroup-subgroup (h n) (k (lift h n g)))))))

(local-defthmd lift-order-1
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(sublistp l (elts h)))
	   (equal (len (append-list l))
		  (* (len l) (order n))))
  :hints (("Subgoal *1/1" :use (sublistp-subgroup-lcosets
                                (:instance lcosets-cars (c (car l)) (h n))
				(:instance len-lcoset (x (caar l)) (h n))))))

(defthmd lift-order
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (equal (order (lift h n g))
		  (* (order h) (order n))))
  :hints (("Goal" :use ((:instance lift-order-1 (l (elts h))))
	   :in-theory (enable append-elts))))

(local-defthm in-lift-subgroup-1
  (implies (and (subgroupp n g)
                (sublistp l (lcosets n g))
		(in x g))
	   (iff (member-equal x (append-list l))
	        (member-equal (lcoset x n g) l)))
  :hints (("Subgoal *1/3" :use ((:instance lcoset-member-lcoset (h n) (c (car l)))))))

(defthmd in-lift-subgroup-iff
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(in x g))
	   (iff (in x (lift h n g))
	        (in (lcoset x n g) h)))
  :hints (("Goal" :in-theory (enable subgroupp append-elts)
                  :use ((:instance member-lcoset-qlist-iff (h n) (x (scex1 (qlist n g) (lcosets n g))))
		        (:instance scex1-lemma (l (qlist n g)) (m (lcosets n g)))
			(:instance sublistp-sublistp (l (elts h)) (m (qlist n g)) (n (lcosets n g)))
                        (:instance in-lift-subgroup-1 (l (elts h)))))))


;;-----------------------------------------------------------------------------------------------------------------------

(local-defthmd ord-inv-divides
  (implies (and (groupp g)
                (in x g))
	   (divides (ord (inv x g) g)
	            (ord x g)))
  :hints (("Goal" :use ((:instance power-inv (n (ord x g)))
			(:instance divides-ord (a (inv x g)) (n (ord x g)))
			(:instance ord>1 (a x))
			(:instance ord>1 (a (inv x g)))))))

(defthmd ord-inv
  (implies (and (groupp g)
                (in x g))
	   (equal (ord (inv x g) g)
	          (ord x g)))
  :hints (("Goal" :use (ord-inv-divides
                        (:instance ord-inv-divides (x (inv x g)))
			(:instance ord>1 (a x))
			(:instance ord>1 (a (inv x g)))
			(:instance divides-leq (x (ord x g)) (y (ord (inv x g) g)))
			(:instance divides-leq (y (ord x g)) (x (ord (inv x g) g)))))))


;;-----------------------------------------------------------------------------------------------------------------------

(defthmd car-ordp-e
  (implies (and (groupp g)
		(ordp l g)
		(member-equal (e g) l))
	   (equal (car l) (e g)))
  :hints (("Goal" :in-theory (enable e)
	   :use ((:instance car-ordp-minimal (x (e g)))))))

(defthmd ordp<ind
  (implies (and (groupp g)
                (ordp l g)
		(member-equal x l)
		(member-equal y l))
           (iff (< (index x l) (index y l))
	        (< (ind x g) (ind y g))))
  :hints (("Subgoal *1/2" :use (car-ordp-minimal
                                (:instance car-ordp-minimal (x y))))
	  ("Subgoal *1/1" :use (car-ordp-minimal
                                (:instance car-ordp-minimal (x y))))))

(defthmd ord-power-gcd-1
  (implies (and (groupp g)
                (in a g)
		(posp n)
		(posp m))
	   (iff (equal (power (power a n g) m g)
	               (e g))
		(divides (/ (ord a g) (gcd (ord a g) n))
		         (* m (/ n (gcd (ord a g) n))))))
  :hints (("Goal" :use (power* ord>1
                        (:instance divides-ord (n (* m n)))
			(:instance gcd-pos (x (ord a g)) (y n))))))

(defthmd ord-power-gcd-2
  (implies (and (groupp g)
                (in a g)
		(posp n)
		(posp m))
	   (iff (equal (power (power a n g) m g)
	               (e g))
		(divides (/ (ord a g) (gcd (ord a g) n))
		         m)))
  :hints (("Goal" :use (ord>1 ord-power-gcd-1
                        (:instance gcd-divides (x (ord a g)) (y n))
			(:instance gcd-quotient-2 (x (ord a g)) (y n) (d (gcd (ord a g) n)))
			(:instance divides-transitive (x (ord a g)) (y (* m (gcd (ord a g) n))) (z (* m n)))
			(:instance divides-product-divides-factor (d (/ (ord a g) (gcd (ord a g) n))) (m (/ n (gcd (ord a g) n))) (n m))
			(:instance gcd-pos (x (ord a g)) (y n))))))

(defthmd ord-power-gcd-3
  (implies (and (groupp g)
                (in a g)
		(posp n)
		(posp m))
	   (iff (divides (ord (power a n g) g)
	                 m)
		(divides (/ (ord a g) (gcd (ord a g) n))
		         m)))
  :hints (("Goal" :use (ord>1 ord-power-gcd-2
			(:instance gcd-pos (x (ord a g)) (y n))
			(:instance divides-ord (a (power a n g)) (n m))))))

(defthmd ord-power-gcd
  (implies (and (groupp g)
                (in a g)
		(posp n))
	   (equal (ord (power a n g) g)
	          (/ (ord a g) (gcd (ord a g) n))))
  :hints (("Goal" :use (ord>1
                        (:instance ord>1 (a (power a n g)))
                        (:instance gcd-divides (x (ord a g)) (y n))
                        (:instance ord-power-gcd-3 (m (ord (power a n g) g)))
                        (:instance ord-power-gcd-3 (m (/ (ord a g) (gcd (ord a g) n))))
			(:instance gcd-pos (x (ord a g)) (y n))
			(:instance divides-leq (x (ord (power a n g) g)) (y (/ (ord a g) (gcd (ord a g) n))))
			(:instance divides-leq (y (ord (power a n g) g)) (x (/ (ord a g) (gcd (ord a g) n))))))))

;;-----------------------------------------------------------------------------------------------------------------------

(defthmd power-order
  (implies (and (groupp g)
                (in x g))
	   (equal (power x (order g) g)
	          (e g)))
  :hints (("Goal" :use (ord-divides-order
                        (:instance divides-ord (a x))))))
