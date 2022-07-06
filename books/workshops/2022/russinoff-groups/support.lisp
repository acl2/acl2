(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "projects/quadratic-reciprocity/euclid" :dir :system)

;;---------------------------------------------------------------------------------------------------
;; Properties of Lists
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

(defthm sublistp-remove1
  (implies (and (sublistp l m)
                (not (member x l)))
	   (sublistp l (remove1-equal x m))))

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

(defthm sublistp-append
  (implies (and (sublistp l g)
                (sublistp m g))
	   (sublistp (append l m) g)))

(defthm len-remove1-equal
  (implies (member x l)
           (equal (len (remove1-equal x l))
	          (1- (len l)))))

(defun sublistp-induct (l m)
  (declare (irrelevant m))
  (if (consp l)
      (sublistp-induct (cdr l) (remove1-equal (car l) m))
    ()))

(defthmd sublistp-<=-len
  (implies (and (dlistp l)
		(sublistp l m))
	   (<= (len l) (len m)))
  :hints (("Goal" :induct (sublistp-induct l m))))

(defthmd sublistp-equal-len
  (implies (and (dlistp l)
                (dlistp m)
		(sublistp l m)
		(sublistp m l))
	   (equal (len l) (len m)))
  :hints (("Goal" :use (sublistp-<=-len (:instance sublistp-<=-len (l m) (m l))))))

(defthmd len-proper-sublist
  (implies (and (sublistp l m)
                (dlistp l)
		(member-equal x m)
		(not (member-equal x l)))
	   (< (len l) (len m)))
  :hints (("Goal" :use ((:instance sublistp-<=-len (m (remove1-equal x m)))))))

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
	        (member-equal (common-member l m) m)))
  :hints (("Goal" :induct (true-listp l))))

;; The lemma len-x-y below may be functionally instantiated to show that two list have the same length:

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

(local-defun xy-in (x y)
  (if (consp x)
      (and (member-equal (xy (car x)) y)
           (xy-in (cdr x) y))
    t))

(local-defun yx-in (y x)
  (if (consp y)
      (and (member-equal (yx (car y)) x)
           (yx-in (cdr y) x))
    t))

(local-defthm xy-inj
  (implies (and (member-equal x1 (x))
                (member-equal x2 (x))
		(equal (xy x1) (xy x2)))
	   (equal x1 x2))
  :rule-classes ()
  :hints (("Goal" :use ((:instance yx-xy (a x1))
                        (:instance yx-xy (a x2))))))

(local-defthm yx-inj
  (implies (and (member-equal y1 (y))
                (member-equal y2 (y))
		(equal (yx y1) (yx y2)))
	   (equal y1 y2))
  :rule-classes ()
  :hints (("Goal" :use ((:instance xy-yx (a y1))
                        (:instance xy-yx (a y2))))))

(local-defthm xy-in-remove-1
  (implies (and (dlistp x)
                (sublistp x (x))
		(xy-in x y)
		(member-equal x1 (x))
		(not (member-equal x1 x)))
	   (xy-in x (remove1-equal (xy x1) y)))
  :hints (("Goal" :induct (dlistp x))
          ("Subgoal *1/1" :use ((:instance xy-inj (x2 (car x)))))))

(local-defthm xy-in-remove
  (implies (and (dlistp x)
                (dlistp y)
                (sublistp x (x))
		(xy-in x y))
	   (xy-in (cdr x) (remove1-equal (xy (car x)) y)))
  :hints (("Goal" :use ((:instance xy-in-remove-1 (x (cdr x)))))))

(local-defthm yx-in-cdr-1
  (implies (and (dlistp y)
                (sublistp y (y))
		(yx-in y x)
		(member-equal y1 (y))
		(not (member-equal (xy (car x)) y)))
	   (yx-in y (cdr x))))

(local-defthm yx-in-cdr
  (implies (and (dlistp y)
                (sublistp y (y))
		(yx-in y x))
	   (yx-in (remove1-equal (xy (car x)) y) (cdr x)))
  :hints (("Goal" :use ((:instance yx-in-cdr-1 (y (remove1-equal (xy (car x)) y)))))))

(local-defun xy-induct (x y)
  (declare (irrelevant y))
  (if (consp x)
      (xy-induct (cdr x) (remove1-equal (xy (car x)) y))
    ()))

(local-defthmd sublistp-trans
  (implies (and (sublistp l m)
                (sublistp m p))
	   (sublistp l p)))

(local-defthmd len-x-y
  (implies (and (dlistp x)
                (dlistp y)
		(sublistp x (x))
		(sublistp y (y))
		(xy-in x y)
		(yx-in y x))
	   (equal (len x) (len y)))
  :hints (("Goal" :induct (xy-induct x y))
          ("Subgoal *1/1" :use ((:instance sublistp-trans (l (remove1-equal (xy (car x)) y)) (m y) (p (y)))))))

(local-defthm xy-in-x-y
  (implies (sublistp x (x))
           (xy-in x (y))))

(local-defthm yx-in-y-x
  (implies (sublistp y (y))
           (yx-in y (x))))

(defthmd len-1-1-equal
  (equal (len (x)) (len (y)))
  :hints (("Goal" :use ((:instance len-x-y (x (x)) (y (y)))))))


;;---------------------------------------------------------------------------------------------------
;; Fimite Groups
;;---------------------------------------------------------------------------------------------------

;; A group of g order n is represented by its operation table, a list of n rows of length n.  The first
;; row of g, car(g), is a list of the elements of g, beginning with its identity element e = x0:

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

(defthm matrixp-1
  (implies (matrixp g m n)
           (true-listp (nth k g))))

(defthm matrixp-2
  (implies (matrixp g m n)
           (true-listp (nth (index x (car g)) g))))

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

(in-theory (disable e op))

;; Closure is established by checking every pair of group elements:

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

(defun check-inverses (l g)
  (if (consp l)
      (if (inv (car l) g)
          (check-inverses (cdr l) g)
	(car l))
    ()))

(defun inv-cex (g) (check-inverses (elts g) g))

(defun inversesp (g) (null (inv-cex g)))

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
           (dlistp (elts g)))
  :hints (("Goal" :in-theory (enable groupp))))

(defthm non-nil-elts
  (implies (groupp g)
           (not (in () g)))
  :hints (("Goal" :in-theory (enable groupp))))

(defthm in-e-g
  (implies (groupp g)
           (in (e g) g))
  :hints (("Goal" :in-theory (enable e groupp))))

(defthmd order-pos
  (implies (groupp g)
           (posp (order g)))
  :hints (("Goal" :in-theory (disable in-e-g) :use (in-e-g) :expand ((len (car g))))))

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

(local-defthm cy-0
  (implies (cy x l g)
           (member (car (cy x l g)) l)))

(local-defthm cy-1
  (implies (and (dlistp l)
                (cy x l g))
           (and (member-equal (car (cy x l g)) l)
	        (not (in (op x (car (cy x l g)) g) g)))))

(local-defthm cy-2
  (implies (and (null (cy x l g))
                (member y l))
	   (in (op x y g) g)))

(local-defthm cxy-1
  (let* ((cex (cxy l g))
         (x (car cex))
	 (y (cadr cex)))
    (implies (and (dlistp l)
                  (dlistp (elts g))
		  cex)
            (and (member-equal x l)
	         (in y g)
		 (not (in (op x y g) g))))))

(local-defthm cxy-2
  (implies (and (not (cxy l g))
                (member-equal x l)
		(in y g))
	   (in (op x y g) g)))

(local-defthm closedp-no-cex
  (implies (and (dlistp (elts g))
                (closedp g)
                (in x g)
		(in y g))
	   (in (op x y g) g)))

(defthm group-closure
  (implies (and (groupp g)
                (in x g)
		(in y g))
	   (in (op x y g) g))
  :hints (("Goal" :in-theory (enable groupp))))

;; Converse of group-closure:

(defthm not-closedp-cex
  (implies (and (dlistp (elts g))
                (not (closedp g)))
           (let* ((cex (closedp-cex g))
                  (x (car cex))
	          (y (cadr cex)))
             (and (in x g)
	          (in y g)
	          (not (in (op x y g) g))))))

(in-theory (disable closedp-cex))

;; Associativity:

(local-defthm az-0
  (implies (az x y l g)
           (member-equal (car (az x y l g)) l)))

(local-defthm az-1
  (implies (and (dlistp l)
                (az x y l g))
           (and (member-equal (car (az x y l g)) l)
	        (not (equal (op x (op y (car (az x y l g)) g) g)
		            (op (op x y g) (car (az x y l g)) g))))))

(local-defthm az-2
  (implies (and (null (az x y l g))
                (member-equal z l))
	   (equal (op x (op y z g) g)
		  (op (op x y g) z g))))

(local-defthm ayz-1
  (let* ((ayz (ayz x l g))
         (y (car ayz))
	 (z (cadr ayz)))
    (implies (and (dlistp l)
                  (dlistp (elts g))
		  ayz)
            (and (member-equal y l)
	         (in z g)
		 (not (equal (op x (op y z g) g)
		             (op (op x y g) z g)))))))

(local-defthm ayz-2
  (implies (and (null (ayz x l g))
                (member-equal y l)
		(in z g))
	   (equal (op x (op y z g) g)
		  (op (op x y g) z g))))

(local-defthm axyz-1
  (let* ((axyz (axyz l g))
         (x (car axyz))
         (y (cadr axyz))
	 (z (caddr axyz)))
    (implies (and (dlistp l)
                  (dlistp (elts g))
		  axyz)
            (and (member-equal x l)
	         (in y g)
	         (in z g)
		 (not (equal (op x (op y z g) g)
		             (op (op x y g) z g)))))))

(local-defthm axyz-2
  (implies (and (dlistp l)
                (null (axyz l g))
                (member-equal x l)
		(in y g)
		(in z g))
	   (equal (op x (op y z g) g)
		  (op (op x y g) z g))))

(local-defthm assocp-no-cex
  (implies (and (dlistp (elts g))
                (assocp g)
                (in x g)
		(in y g)
		(in z g))
	   (equal (op x (op y z g) g)
		  (op (op x y g) z g))))

(defthmd group-assoc
  (implies (and (groupp g)
                (in x g)
		(in y g)
		(in z g))
	   (equal (op x (op y z g) g)
	          (op (op x y g) z g)))
  :hints (("Goal" :in-theory (enable groupp))))

;; Converse of group-assoc:

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

(in-theory (disable assocp-cex))

;; Inverses:

(in-theory (disable inv))

(local-defthm check-inverses-0
  (implies (check-inverses l g)
           (member-equal (check-inverses l g) l)))

(local-defthm check-inverses-1
  (implies (check-inverses l g)
           (and (member-equal (check-inverses l g) l)
	        (null (inv (check-inverses l g) g)))))

(local-defthm check-inverses-2
  (implies (and (dlistp l)
                (not (member-equal () l))
                (null (check-inverses l g))
                (member-equal x l))
           (inv x g)))

(local-defthm inv-aux-1
  (let ((y (inv-aux x l g)))
    (implies y (and (member-equal y l) (equal (op y x g) (e g))))))

(local-defthm inv-aux-2
  (implies (and (dlistp l)
                (not (member-equal () l))
                (null (inv-aux x l g))
                (member-equal y l))
	   (not (equal (op y x g) (e g)))))

(local-defthm inv-1
  (implies (inv x g)
           (and (in (inv x g) g)
	        (equal (op (inv x g) x g) (e g))))
  :hints (("Goal" :in-theory (enable inv))))

(defthm group-left-inverse
  (implies (and (groupp g)
                (in x g))
	   (and (in (inv x g) g)
	        (equal (op (inv x g) x g)
		       (e g))))
  :hints (("Goal" :in-theory (enable groupp inv)
	   :use ((:instance check-inverses-2 (l (elts g)))))))

(defthm not-inv-cex
  (implies (and (dlistp (elts g))
                (not (in () g))
                (not (inversesp g)))
	   (and (in (inv-cex g) g)
	        (implies (in y g) (not (equal (op y (inv-cex g) g) (e g))))))
  :hints (("Goal" :in-theory (enable inv)
                  :use ((:instance check-inverses-1 (l (elts g)))
                        (:instance inv-aux-2 (x (inv-cex g)) (l (elts g)))))))

(in-theory (disable inv-cex))

;; Abelian groups:

(local-defthm ay-0
  (implies (ay x l g)
           (member (car (ay x l g)) l)))

(local-defthm ay-1
  (implies (and (dlistp l)
                (ay x l g))
           (and (member-equal (car (ay x l g)) l)
	        (not (equal (op x (car (ay x l g)) g)
		            (op (car (ay x l g)) x g))))))

(local-defthm ay-2
  (implies (and (null (ay x l g))
                (member y l))
	   (equal (op x y g) (op y x g))))

(local-defthm axy-1
  (let* ((cex (axy l g))
         (x (car cex))
	 (y (cadr cex)))
    (implies (and (dlistp l)
                  (dlistp (elts g))
		  cex)
            (and (member-equal x l)
	         (in y g)
		 (not (equal (op x y g) (op y x g)))))))

(local-defthm axy-2
  (implies (and (not (axy l g))
                (member-equal x l)
		(in y g))
	   (equal (op x y g) (op y x g))))

(local-defthm abelianp-no-cex
  (implies (and (dlistp (elts g))
                (abelianp g)
                (in x g)
		(in y g))
	   (equal (op x y g) (op y x g))))

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

(in-theory (disable group-abelianp not-abelianp-cex abelianp-cex))

;; Some basic properties derived from the axioms:

(defthm idem-e
  (implies (and (groupp g)
		(in x g)
		(equal (op x x g) x))
	   (equal x (e g)))
  :rule-classes ()
  :hints (("Goal" :use (group-left-inverse
			(:instance group-assoc (x (inv x g)) (y x) (z x))))))

(defthm group-right-inverse
  (implies (and (groupp g)
                (in x g))
	   (and (in (inv x g) g)
                (equal (op x (inv x g) g)
	               (e g))))
  :hints (("Goal" :use (group-left-inverse
			(:instance group-assoc (y (inv x g)) (z (op x (inv x g) g)))
			(:instance group-assoc (x (inv x g)) (y x) (z (inv x g)))
			(:instance group-left-identity (x (inv x g)))
			(:instance idem-e (x (op x (inv x g) g)))))))

(defthm group-right-identity
  (implies (and (groupp g)
                (in x g))
	   (equal (op x (e g) g)
	          x))
  :hints (("Goal" :use (group-left-inverse group-right-inverse
                        (:instance group-assoc (y (inv x g)) (z x))))))

(defthm left-cancel
  (implies (and (groupp g)
                (in x g) (in y g) (in a g)
		(equal (op a x g) (op a y g)))
	   (equal x y))
  :rule-classes ()
  :hints (("Goal" :use (group-left-identity
                        (:instance group-left-identity (x y))
			(:instance group-assoc (x (inv a g)) (y a) (z x))
			(:instance group-assoc (x (inv a g)) (y a) (z y))
                        (:instance group-left-inverse (x a))))))

(defthm right-cancel
  (implies (and (groupp g)
                (in x g) (in y g) (in a g)
		(equal (op x a g) (op y a g)))
	   (equal x y))
  :rule-classes ()
  :hints (("Goal" :use (group-right-identity
                        (:instance group-right-identity (x y))
			(:instance group-assoc (y a) (z (inv a g)))
			(:instance group-assoc (x y) (y a) (z (inv a g)))
                        (:instance group-right-inverse (x a))))))

(defthm inv-inv
  (implies (and (groupp g)
                (in x g))
           (equal (inv (inv x g) g)
	          x))
  :hints (("Goal" :use (group-right-inverse
                        (:instance group-left-inverse (x (inv x g)))
			(:instance right-cancel (y (inv (inv x g) g)) (a (inv x g)))))))

(defthm inv-unique
  (implies (and (groupp g)
                (in x g)
		(in y g)
		(equal (op y x g) (e g)))
	   (equal (inv x g) y))
  :hints (("Goal" :use (group-left-inverse
                        (:instance right-cancel (x y) (y (inv x g)) (a x))))))

(defthm inv-e
  (implies (groupp g)
           (equal (inv (e g) g) (e g)))
  :hints (("Goal" :use ((:instance inv-unique (x (e g)) (y (e g)))))))

(defthmd prod-inv
  (implies (and (groupp g)
                (in x g)
		(in y g))
	   (equal (inv (op x y g) g)
	          (op (inv y g) (inv x g) g)))
  :hints (("Goal" :use (group-left-inverse
                        (:instance group-assoc (x (inv y g)) (y (inv x g)) (z (op x y g)))
                        (:instance group-assoc (x (inv x g)) (y x) (z y))
			(:instance group-left-inverse (x y))
			(:instance inv-unique (x (op x y g)) (y (op (inv y g) (inv x g) g)))))))


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

(local-defthm sy-0
  (implies (sy x l h g)
           (member (car (sy x l h g)) l)))

(local-defthm sy-1
  (implies (and (dlistp l)
                (sy x l h g))
           (and (member-equal (car (sy x l h g)) l)
	        (not (equal (op x (car (sy x l h g)) h)
			    (op x (car (sy x l h g)) g))))))

(local-defthm sy-2
  (implies (and (null (sy x l h g))
                (member y l))
	   (equal (op x y h) (op x y g))))

(local-defthm sxy-1
  (let* ((cex (sxy l h g))
         (x (car cex))
	 (y (cadr cex)))
    (implies (and (dlistp (elts h))
		  cex)
            (and (member-equal x l)
	         (in y h)
		 (not (equal (op x y h) (op x y g)))))))

(local-defthm sxy-2
  (implies (and (not (sxy l h g))
                (member-equal x l)
		(in y h))
	   (equal (op x y h) (op x y g))))

(local-defthm subgroupp-no-cex
  (implies (and (not (subgroupp-cex h g))
                (in x h)
		(in y h))
	   (equal (op x y h) (op x y g))))

(defthm subgroup-op
  (implies (and (subgroupp h g)
                (in x h)
		(in y h))
	   (equal (op x y h) (op x y g)))
  :hints (("Goal" :in-theory (enable subgroupp))))

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

(in-theory (disable subgroupp subgroupp-cex))

(defthm subgroup-e
  (implies (subgroupp h g)
	   (equal (e h) (e g)))
  :hints (("Goal" :use ((:instance group-left-identity (x (e h)))
			(:instance group-left-identity (x (e h)) (g h))
			(:instance right-cancel (a (e h)) (x (e g)) (y (e h)))))))

(defthm subgroup-inv
  (implies (and (subgroupp h g)
		(in x h))
           (equal (inv x h) (inv x g)))
  :hints (("Goal" :use (group-right-inverse
                        (:instance group-right-inverse (g h))
			(:instance left-cancel (a x) (x (inv x h)) (y (inv x g)))))))

(defthm abelian-subgroup
  (implies (and (subgroupp h g)
                (abelianp g))
	   (abelianp h))
  :hints (("Goal" :use ((:instance not-abelianp-cex (g h))
		        (:instance member-sublist (x (car (abelianp-cex h))) (l (car h)) (m (car g)))
		        (:instance member-sublist (x (cadr (abelianp-cex h))) (l (car h)) (m (car g)))
		        (:instance group-abelianp (x (car (abelianp-cex h))) (y (cadr (abelianp-cex h))))))))

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

(local-defthm g-row-1
  (and (true-listp (g-row x m))
       (equal (len (g-row c m)) (len m))))

(local-defthm g-row-2
  (implies (and (true-listp m)
                (sublistp m (glist)))
           (equal (g-row (car (glist)) m)
	          m)))

(local-defthm g-row-3
  (implies (and (natp j)
                (< j (len m)))
	   (equal (nth j (g-row x m))
	          (gop x (nth j m)))))

(local-defthm g-aux-1
  (matrixp (g-aux l m) (len l) (len m)))

(local-defthm g-aux-2
  (implies (consp l)
           (equal (car (g-aux l m))
	          (g-row (car l) m))))

(local-defthm g-aux-3
  (implies (and (natp i)
                (< i (len l)))
	   (equal (nth i (g-aux l m))
	          (g-row (nth i l) m))))

(local-defthm matrixp-g
  (matrixp (g) (order (g)) (order (g))))

(defthm glist-elts
  (equal (elts (g))
         (glist)))

(defthm op-g-rewrite
  (implies (and (in x (g))
		(in y (g)))
           (equal (op x y (g))
	          (gop x y)))
  :hints (("Goal" :in-theory (enable op))))

(in-theory (disable g (g)))

(local-defthm closedp-g
  (closedp (g))
  :hints (("Goal" :use ((:instance not-closedp-cex (g (g)))))))

(local-defthm assocp-g
  (assocp (g))
  :hints (("Goal" :use ((:instance not-assocp-cex (g (g)))))))

(local-defthm inversep-g
  (inversesp (g))
  :hints (("Goal" :in-theory (enable e)
                  :use ((:instance not-inv-cex (g (g)) (y (ginv (inv-cex (g)))))))))

(local-defthmd posp-order-g
  (posp (len (car (g))))
  :hints (("Goal" :use (consp-glist glist-elts) :in-theory (disable consp-glist glist-elts) :expand ((len (glist))))))

(defthm groupp-g
  (groupp (g))
  :hints (("Goal" :in-theory (enable groupp)
	   :use (posp-order-g matrixp-g))))

(defthmd inv-g-rewrite
  (implies (in x (g))
	   (equal (inv x (g)) (ginv x)))
  :hints (("Goal" :in-theory (enable e) :use ((:instance inv-unique (g (g)) (y (ginv x)))))))

(in-theory (enable g))

;; args: a list of parameters
;; elts: a list of the group elements as a function of args
;; op: the product of group elements x and y as a function of args

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
           (dlistp (ninit n)))
  :hints (("Subgoal *1/4" :use ((:instance member-ninit (x (1- n)) (n (1- n)))
                                (:instance dlistp-append (l (ninit (1- n))) (m (list (1- n))))))))

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
	          x))
  :hints (("Goal" :use (member-ninit))))

(defthm z+-closed
  (implies (and (posp n)
                (member-equal x (ninit n))
                (member-equal y (ninit n)))
           (member-equal (z+-op x y n) (ninit n)))
  :hints (("Goal" :use (member-ninit (:instance member-ninit (x y)) (:instance member-ninit (x (z+-op x y n)))))))

(defthm z+-assoc
  (implies (and (posp n)
                (member-equal x (ninit n))
                (member-equal y (ninit n))
                (member-equal z (ninit n)))
	   (equal (z+-op x (z+-op y z n) n)
	          (z+-op (z+-op x y n) z n)))
  :hints (("Goal" :use (member-ninit
                        (:instance member-ninit (x y))
			(:instance member-ninit (x z))
                        (:instance mod-sum (a x) (b (+ y z)))
                        (:instance mod-sum (a z) (b (+ x y)))))))

(defthm z+-inverse
  (implies (and (posp n)
                (member-equal x (ninit n)))
	   (and (member-equal (z+-inv x n) (ninit n))
	        (equal (z+-op (z+-inv x n) x n) 0)))
  :hints (("Goal" :use (member-ninit
                        (:instance member-ninit (x (z+-inv x n)))
			(:instance mod-sum (a x) (b (- x)))))))

(in-theory (disable z+-op z+-inv))

(defgroup z+ (n)
  (posp n)
  (ninit n)
  (z+-op x y n)
  (z+-inv x n))

;; Multiplicative group of integers modulo n:

;; Move these to euclid.lisp?

(defthmd least-divisor-prime-divides
  (implies (and (natp n) (> n 1))
	   (and (primep (least-divisor 2 n))
		(divides (least-divisor 2 n) n)))
  :hints (("Goal" :use (primep-least-divisor (:instance least-divisor-divides (k 2))))))

(defthmd g-c-d-symmetry
  (implies (and (natp x) (natp y))
           (equal (g-c-d x y) (g-c-d y x)))
  :hints (("Goal" :in-theory (enable g-c-d))))

(defthmd prod-rel-prime
  (implies (and (posp n)
		(integerp a)
		(integerp b)
		(= (g-c-d a n) 1)
		(= (g-c-d b n) 1))
	   (equal (g-c-d (* a b) n) 1))
  :hints (("Goal" :use ((:instance least-divisor-prime-divides (n (g-c-d (* a b) n)))
                        (:instance euclid (p (least-divisor 2 (g-c-d (* a b) n))))
			(:instance divides-leq (x (least-divisor 2 (g-c-d (* a b) n))) (y 1))
			(:instance g-c-d-pos (x (* a b)) (y n))
			(:instance g-c-d-symmetry (x a) (y n))
			(:instance g-c-d-symmetry (x b) (y n))
			(:instance g-c-d-divides (x (* a b)) (y n))
			(:instance divides-transitive (x (least-divisor 2 (g-c-d (* a b) n))) (y (g-c-d (* a b) n)) (z (* a b)))
			(:instance divides-transitive (x (least-divisor 2 (g-c-d (* a b) n))) (y (g-c-d (* a b) n)) (z n))
			(:instance divides-g-c-d (d (least-divisor 2 (g-c-d (* a b) n))) (x a) (y n))
			(:instance divides-g-c-d (d (least-divisor 2 (g-c-d (* a b) n))) (x b) (y n))))))

(local-defthm divides-mod-n
  (implies (and (posp n) (integerp m) (posp k) (divides k n) (divides k (mod m n)))
           (divides k m))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable divides)
                  :use ((:instance mod-def (x m) (y n))))))

(local-defthmd mod-prod-rel-prime
  (implies (and (posp n)
		(posp a)
		(posp b)
		(= (g-c-d a n) 1)
		(= (g-c-d b n) 1))
	   (equal (g-c-d (mod (* a b) n) n) 1))
  :hints (("Goal" :in-theory (enable divides)
                  :use (prod-rel-prime
		        (:instance g-c-d-pos (x (* a b)) (y n))
		        (:instance g-c-d-pos (x (mod (* a b) n)) (y n))
		        (:instance divides-mod-n (k (g-c-d (mod (* a b) n) n)) (m (* a b)))
                        (:instance g-c-d-divides (x (mod (* a b) n)) (y n))
			(:instance divides-g-c-d (d (g-c-d (mod (* a b) n) n)) (x (* a b)) (y n))
			(:instance divides-leq (x (g-c-d (mod (* a b) n) n)) (y 1))))))

(defun rel-primes-aux (k n)
  (if (zp k)
      ()
    (if (= (g-c-d k n) 1)
        (append (rel-primes-aux (1- k) n) (list k))
      (rel-primes-aux (1- k) n))))

(defun rel-primes (n)
  (rel-primes-aux n n))

(local-defthm member-rel-primes-aux-<=
  (implies (and (natp k)
                (natp j)
		(member j (rel-primes-aux k n)))
	   (<= j k)))

(local-defthmd member-rel-primes-aux-1
  (implies (and (posp k)
                (posp j)
		(<= j k))
	   (iff (member j (rel-primes-aux k n))
	        (= (g-c-d j n) 1))))

(local-defthmd member-rel-primes-aux-2
  (implies (and (posp k)
                (member j (rel-primes-aux k n)))
	   (and (posp j)
		(<= j k))))

(local-defthmd member-rel-primes-aux
  (implies (posp k)
	   (iff (member j (rel-primes-aux k n))
	        (and (posp j)
		     (<= j k)
		     (= (g-c-d j n) 1))))
  :hints (("Goal" :use (member-rel-primes-aux-1 member-rel-primes-aux-2))))

(local-defthmd member-rel-primes-1
  (implies (and (posp n) (> n 1))
	   (iff (member k (rel-primes n))
	        (and (posp k)
		     (<= k n)
		     (= (g-c-d k n) 1))))
  :hints (("Goal" :use ((:instance member-rel-primes-aux (k n) (j k))))))

(defthm g-c-d-n-n
  (implies (posp n)
           (equal (g-c-d n n) n))
  :hints (("Goal" :in-theory (enable g-c-d))))

(defthmd member-rel-primes
  (implies (and (posp n) (> n 1))
	   (iff (member k (rel-primes n))
	        (and (posp k)
		     (< k n)
		     (= (g-c-d k n) 1))))
  :hints (("Goal" :in-theory (disable member-rel-primes-aux-<=) :use (member-rel-primes-1))))

(defthm g-c-d-1
  (implies (posp n)
           (equal (g-c-d 1 n)
	          1))
  :hints (("Goal" :use ((:instance g-c-d-divides (x 1) (y n))
                        (:instance g-c-d-pos (x 1) (y n))
                        (:instance divides-leq (x (g-c-d 1 n)) (y 1))))))

(local-defthm member-1-rel-primes-aux
  (implies (and (posp n) (posp k) (<= k n))
           (member 1 (rel-primes-aux k n))))

(defthmd member-1-rel-primes
  (implies (posp n)
           (member 1 (rel-primes n))))

(defthm consp-rel-primes
  (implies (posp n)
           (consp (rel-primes n)))
  :hints (("Goal" :in-theory (disable rel-primes) :use (member-1-rel-primes))))

(local-defthm not-member-dlistp-append
  (implies (and (dlistp l) (not (member x l)))
           (dlistp (append l (list x)))))

(local-defthm dlist-rel-primes-aux
  (implies (and (posp n) (posp j) (<= j n))
	   (dlistp (rel-primes-aux j n)))
  :hints (("Subgoal *1/5" :in-theory (disable member-rel-primes-aux-<=)
                          :use ((:instance member-rel-primes-aux-<= (k (1- j)))))))

(defthm dlistp-rel-primes
  (implies (posp n)
           (dlistp (rel-primes n))))

(local-defthm rel-primes-aux-non-nil
  (implies (posp n)
           (not (member-equal () (rel-primes-aux k n)))))

(defthm rel-primes-non-nil
  (implies (posp n)
           (not (member-equal () (rel-primes n)))))

(local-defthm car-rel-primes-aux
  (implies (and (posp n) (posp k) (<= k n))
           (equal (car (rel-primes-aux  k n)) 1)))

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

(local-defthm hack
  (implies (and (integerp x)
                (integerp n)
                (equal (+ (* n (s-int x n)) (* x (r-int x n)))
                       1))
           (equal (+ 1 (- (* n (s-int x n))))
	          (* x (r-int x n)))))

(local-defthmd z*-inverse-1
  (implies (and (posp n) (> n 1)
                (member-equal x (rel-primes n)))
	   (equal (z*-op (z*-inv x n) x n) 1))
  :hints (("Goal" :use (hack
		        (:instance g-c-d-linear-combination (y n))
                        (:instance member-rel-primes (k x))
			(:instance mod-mod-times (a (r-int x n)) (b x))
                        (:instance mod-mult (m 1) (a (- (s-int x n))))))))

(local-defthmd z*-inverse-2
  (implies (and (posp n) (> n 1)
                (member-equal x (rel-primes n))
		(posp k)
		(divides k (z*-inv x n))
		(divides k n))
	  (and (divides k (* (r-int x n) x))
	       (divides k (* (s-int x n) n))))
  :hints (("Goal" :in-theory (enable divides)
                  :use ((:instance member-rel-primes (k x))
                        (:instance divides-mod-n (m (r-int x n)))))))

(local-defthmd z*-inverse-3
  (implies (and (posp n) (> n 1)
                (member-equal x (rel-primes n))
		(posp k)
		(divides k (z*-inv x n))
		(divides k n))
	  (divides k 1))
  :hints (("Goal" :use (z*-inverse-2
		        (:instance divides-sum (x k) (y (* (r-int x n) x)) (z (* (s-int x n) n)))
		        (:instance member-rel-primes (k x))
			(:instance g-c-d-linear-combination (y n))
                        (:instance divides-mod-n (m (r-int x n)))))))

(local-defthmd z*-inverse-4
  (implies (and (posp n) (> n 1)
                (member-equal x (rel-primes n)))
	   (equal (g-c-d (z*-inv x n) n) 1))
  :hints (("Goal" :use ((:instance z*-inverse-3 (k (g-c-d (z*-inv x n) n)))
                        (:instance divides-leq (x (g-c-d (z*-inv x n) n)) (y 1))
		        (:instance g-c-d-pos (x (z*-inv x n)) (y n))
		        (:instance member-rel-primes (k x))
			(:instance g-c-d-divides (x (z*-inv x n)) (y n))))))

(local-defthmd z*-inverse-5
  (implies (and (posp n) (> n 1)
                (member-equal x (rel-primes n)))
	   (member-equal (z*-inv x n) (rel-primes n)))
  :hints (("Goal" :use (z*-inverse-4
		        (:instance member-rel-primes (k (z*-inv x n)))))))

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

(comp t) ; added by Matt K. 7/3/2022 for Allegro CL proof of assocp-z*-500

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


(encapsulate ()

  (local (include-book "ordinals/lexicographic-book" :dir :system))

  (set-well-founded-relation acl2::l<)

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
(defthm consp-slidt
  (implies (posp n)
           (consp (slist n))))

(defthm dlistp-slidt
  (implies (posp n)
           (dlistp (slist n))))

(defthm slidt-non-nil
  (implies (posp n)
           (not (member-equal () (slist n)))))

(defthm car-slidt
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
;; odd number of transpositions.  This may be determied by examining its cycle structure:

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
           (dlistp l))
  :hints (("Subgoal *1/3" :use ((:instance car-ordp-minimal (x (car l)))))))

(local-defthm sublistp-cdr
  (implies (and (sublistp x y)
                (not (member-equal (car y) x)))
	   (sublistp x (cdr y))))

(local-defun ordp-equal-induct (x y)
  (if (and (consp x) (consp y))
      (1+ (ordp-equal-induct (cdr x) (cdr y)))
    0))

(defthm ordp-equal
  (implies (and (ordp x g)
                (ordp y g)
		(sublistp x y)
		(sublistp y x))
	   (equal x y))
  :rule-classes ()
  :hints (("Goal" :induct (ordp-equal-induct x y))
          ("Subgoal *1/1" :use (sublistp-cdr
	                        (:instance sublistp-cdr (x y) (y x))
				(:instance car-ordp-minimal (x (car x)) (l (cdr y)))
				(:instance car-ordp-minimal (x (car y)) (l (cdr x)))))))


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

(local-defthmd sublistp-insert
  (implies (and (sublistp l m)
                (member-equal x m))
	   (sublistp (insert x l g) m)))

(local-defthm sublistp-lcoset-aux-g
  (implies (and (groupp g)
                (sublistp h (elts g))
		(in x g))
	   (sublistp (lcoset-aux x h g) (elts g)))
  :hints (("Subgoal *1/1" :in-theory (disable group-closure)
                          :use ((:instance group-closure (y (car h)))))))

(defthmd sublistp-lcoset-g
  (implies (and (subgroupp h g)
		(in x g))
	   (sublistp (lcoset x h g) (elts g)))
  :hints (("Goal" :in-theory (enable subgroupp lcoset))))

(defthm member-lcoset-g
  (implies (and (subgroupp h g)
		(in x g)
		(member-equal y (lcoset x h g)))
	   (in y g))
  :hints (("Goal" :use (sublistp-lcoset-g))))

;; A coset is an ordered list of group elements:

(defthm ordp-insert
  (implies (and (ordp l g) (in x g))
           (ordp (insert x l g) g))
  :hints (("Subgoal *1/3" :use ((:instance index-1-to-1 (y (car l)) (l (car g)))))))

(local-defthm ordp-lcoset-aux
  (implies (and (groupp g)
                (in x g)
                (sublistp h (car g)))
	   (ordp (lcoset-aux x h g) g)))

(defthm ordp-lcoset
  (implies (and (subgroupp h g)
		(in x g))
	   (ordp (lcoset x h g) g))
  :hints (("Goal" :in-theory (enable lcoset subgroupp))))

;;  The length of a coset is the order of the subgroup:

(defthm member-insert
  (implies (and (member-equal y (insert x l g))
                (not (equal y x)))
           (member-equal y l)))

(local-defthm not-member-lcoset-aux
  (implies (and (groupp g)
		(sublistp l (elts g))
		(in x g)
		(in y g)
		(not (member y l)))
	   (not (member (op x y g) (lcoset-aux x l g))))
  :hints (("Subgoal *1/1" :use ((:instance left-cancel (a x) (x (car l)))))))

(defthm len-insert
  (implies (not (member x l))
	   (equal (len (insert x l g))
		  (1+ (len l)))))

(local-defthm len-lcoset-aux
  (implies (and (groupp g)
		(in x g)
		(sublistp l (elts g))
		(dlistp l))
	   (equal (len (lcoset-aux x l g))
		  (len l))))

(defthm len-lcoset
  (implies (and (subgroupp h g)
		(in x g))
	   (equal (len (lcoset x h g))
		  (order h)))
  :hints (("Goal" :in-theory (enable lcoset subgroupp groupp))))

;; A characterization of coset elements:

(local-defthm member-lcoset-aux
  (implies (member-equal y h)
	   (member-equal (op x y g) (lcoset-aux x h g))))

(defthm member-lcoset
  (implies (and (subgroupp h g)
		(in x g)
		(in y h))
	   (member-equal (op x y g) (lcoset x h g)))
  :hints (("Goal" :in-theory (enable lcoset))))

(local-defthm member-lcoset-aux-inv
  (implies (and (subgroupp h g)
		(sublistp l (elts h))
                (in x g)
                (member-equal y (lcoset-aux x l g)))
	   (member-equal (op (inv x g) y g) (elts h)))
  :hints (("Subgoal *1/1" :use (group-left-inverse
                                (:instance member-insert (x (op x (car l) g)) (l (lcoset-aux x (cdr l) g)))
                                (:instance group-assoc (x (inv x g)) (y x) (z (car l)))
				(:instance group-left-identity (x (car l)))))))

(local-defthmd member-lcoset-iff-1
  (implies (and (subgroupp h g)
		(in x g)
		(in y g))
	   (implies (in (op (inv x g) y g) h)
	            (member-equal y (lcoset x h g))))
  :hints (("Goal" :use (group-right-inverse
                        (:instance group-assoc (y (inv x g)) (z y))
			(:instance member-lcoset (y (op (inv x g) y g)))))))

(local-defthmd member-lcoset-iff-2
  (implies (and (subgroupp h g)
		(in x g)
		(in y g))
	   (implies (member-equal y (lcoset x h g))
	            (in (op (inv x g) y g) h)))
  :hints (("Goal" :in-theory (enable lcoset groupp subgroupp)
                  :use ((:instance member-lcoset-aux-inv (l (elts h)))))))

(defthmd member-lcoset-iff
  (implies (and (subgroupp h g)
		(in x g)
		(in y g))
	   (iff (member-equal y (lcoset x h g))
	        (in (op (inv x g) y g) h)))
  :hints (("Goal" :use (member-lcoset-iff-1 member-lcoset-iff-2))))

;; Intersecting cosets are equal:

(defthm member-self-lcoset
  (implies (and (subgroupp h g)
		(in x g))
	   (member-equal x (lcoset x h g)))
  :hints (("Goal" :in-theory (disable subgroup-e)
                  :use (group-left-inverse subgroup-e
                       (:instance group-left-identity (g h))
                       (:instance member-lcoset-iff (y x))))))

(defthm member-lcoset-symmetry
  (implies (and (subgroupp h g)
		(in x g)
		(in y g))
	   (implies (member-equal y (lcoset x h g))
	            (member-equal x (lcoset y h g))))
  :hints (("Goal" :use (group-left-inverse member-lcoset-iff
                        (:instance group-left-inverse (x (op (inv x g) y g)) (g h))
                        (:instance member-lcoset-iff (x y) (y x))
			(:instance prod-inv (x (inv x g)))))))

(local-defthm lcosets-intersect-1
  (implies (and (subgroupp h g)
		(in x g)
		(in y g)
		(member-equal a (lcoset x h g))
		(member-equal a (lcoset y h g))
		(member-equal b (lcoset x h g)))
	   (in (op (op (op (inv y g) a g) (op (inv a g) x g) g) (op (inv x g) b g) g) h))
  :hints (("Goal" :use ((:instance member-lcoset-symmetry (y a))
                        (:instance member-lcoset-iff (x y) (y a))
                        (:instance member-lcoset-iff (y b))
                        (:instance member-lcoset-iff (x a) (y x))
			(:instance group-closure (g h) (x (op (op (inv y g) a g) (op (inv a g) x g) g))
			                               (y (op (inv x g) b g)))
			(:instance group-closure (g h) (x (op (inv y g) a g)) (y (op (inv a g) x g)))))))

(local-defthm lcosets-intersect-2
  (implies (and (groupp g)
		(in x g)
		(in y g)
		(in a g)
		(in b g))
	   (equal (op (op (inv y g) a g) (op (inv a g) x g) g)
	          (op (inv y g) x g)))
  :hints (("Goal" :use (group-left-identity
                        (:instance group-left-inverse (x y))
                        (:instance group-assoc (x (inv y g)) (y a) (z (op (inv a g) x g)))
                        (:instance group-assoc (x a) (y (inv a g)) (z x))
                        (:instance group-right-inverse (x a))))))

(local-defthm lcosets-intersect-3
  (implies (and (groupp g)
		(in x g)
		(in y g)
		(in a g)
		(in b g))
	   (equal (op (op (op (inv y g) a g) (op (inv a g) x g) g) (op (inv x g) b g) g)
	          (op (inv y g) b g)))
  :hints (("Goal" :use (lcosets-intersect-2
                        (:instance lcosets-intersect-2 (a x) (x b))))))

(defthm lcosets-intersect
  (implies (and (subgroupp h g)
		(in x g)
		(in y g)
		(member-equal a (lcoset x h g))
		(member-equal a (lcoset y h g))
		(member-equal b (lcoset x h g)))
	   (member-equal b (lcoset y h g)))
  :hints (("Goal" :use (lcosets-intersect-1 lcosets-intersect-3
                        (:instance member-lcoset-iff (x y) (y b))))))

(local-defthm sublistp-lcoset-1
  (implies (and (subgroupp h g)
		(in x g)
		(in y g)
		(member-equal y (lcoset x h g))
		(sublistp l (lcoset y h g)))
	   (sublistp l (lcoset x h g)))
  :hints (("Subgoal *1/2" :use ((:instance lcosets-intersect (a y) (b (car l)) (x y) (y x))))))

(defthm sublistp-lcoset
  (implies (and (subgroupp h g)
		(in x g)
		(in y g)
		(member-equal y (lcoset x h g)))
	   (sublistp (lcoset y h g) (lcoset x h g)))
  :hints (("Goal" :use ((:instance sublistp-lcoset-1 (l (lcoset y h g)))))))

(defthmd equal-lcoset
  (implies (and (subgroupp h g)
		(in x g)
		(in y g)
		(member-equal y (lcoset x h g)))
	   (equal (lcoset y h g) (lcoset x h g)))
  :hints (("Goal" :use (member-lcoset-iff sublistp-lcoset
                        (:instance ordp-equal (x (lcoset x h g)) (y (lcoset y h g)))
                        (:instance sublistp-lcoset (x y) (y x))))))

(defthmd equal-lcoset-2
  (implies (and (subgroupp h g)
		(in x1 g)
		(in x2 g)
		(in y g)
		(member-equal y (lcoset x1 h g))
		(member-equal y (lcoset x2 h g)))
	   (equal (lcoset x1 h g) (lcoset x2 h g)))
  :hints (("Goal" :use ((:instance equal-lcoset (x x1))
                        (:instance equal-lcoset (x x2))))))


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

(local-defthm member-lcoset-cosets-aux-1
  (implies (and (subgroupp h g)
                (sublistp l (elts g))
		(in x g)
		(member-list x (lcosets-aux l h g)))
	   (member (lcoset x h g) (lcosets-aux l h g)))
  :hints (("Subgoal *1/2" :use ((:instance equal-lcoset (x (car l)) (y x))))))

(local-defthm member-lcoset-cosets-aux
  (implies (and (subgroupp h g)
                (sublistp l (elts g))
		(member x l))
	   (member (lcoset x h g) (lcosets-aux l h g))))

(defthm member-lcoset-cosets
  (implies (and (subgroupp h g)
                (in x g))
	   (member (lcoset x h g) (lcosets h g)))
  :hints (("Goal" :in-theory (enable lcosets))))

;; lcosets are distinct and non-nil:

(defthm member-member-list
  (implies (and (consp x) (member x l))
           (member-list (car x) l)))

(local-defthm dlistp-lcosets-aux
  (implies (and (subgroupp h g)
                (sublistp l (elts g)))
           (dlistp (lcosets-aux l h g))))

(defthm dlistp-lcosets
  (implies (subgroupp h g)
           (dlistp (lcosets h g)))
  :hints (("Goal" :in-theory (enable lcosets))))

(local-defthm lcosets-aux-non-nil
  (implies (and (subgroupp h g)
                (sublistp l (elts g)))
           (not (member-equal () (lcosets-aux l h g))))
  :hints (("Subgoal *1/2" :use ((:instance member-self-lcoset (x (car l)))))))

(defthm lcosets-non-nil
  (implies (subgroupp h g)
           (not (member-equal () (lcosets h g))))
  :hints (("Goal" :in-theory (enable lcosets))))

;; The length of append-list(lcosets(h,g)):

(local-defthm len-lcosets-aux
  (implies (and (subgroupp h g)
		(sublistp l (car g)))
	   (equal (len (append-list (lcosets-aux l h g)))
	          (* (order h) (len (lcosets-aux l h g))))))

(defthm len-lcosets
  (implies (subgroupp h g)
	   (equal (len (append-list (lcosets h g)))
	          (* (order h) (subgroup-index h g))))
  :hints (("Goal" :in-theory (enable lcosets))))

;; append-list(lcosets(h,g)) is a dlist:

(defthm lcoset-car
  (implies (and (subgroupp h g)
		(in x g))
	   (and (in (car (lcoset x h g)) g)
	        (equal (lcoset (car (lcoset x h g)) h g)
	               (lcoset x h g))))
  :hints (("Goal" :in-theory (disable member-self-lcoset)
                  :use (ordp-lcoset member-self-lcoset
                        (:instance member-lcoset-g (y (car (lcoset x h g))))
                        (:instance equal-lcoset (y (car (lcoset x h g))))))))

(local-defthm lcosets-aux-cars
  (implies (and (subgroupp h g)
		(sublistp l (elts g))
		(member c (lcosets-aux l h g)))
	   (and (in (car c ) g)
		(equal (lcoset (car c) h g)
		       c)))
  :hints (("Subgoal *1/2" :use ((:instance lcoset-car (x (car l)))))))

(defthmd lcosets-cars
  (implies (and (subgroupp h g)
		(member c (lcosets h g)))
	   (and (in (car c ) g)
		(equal (lcoset (car c) h g)
		       c)))
  :hints (("Goal" :use ((:instance lcosets-aux-cars (l (elts g))))
                  :in-theory (enable lcosets))))

(defthm lcosets-aux-disjointp-list
  (implies (and (subgroupp h g)
		(sublistp l (elts g))
		(in x g)
		(not (member-list x (lcosets-aux l h g))))
	   (disjointp-list (lcoset x h g) (lcosets-aux l h g)))
  :hints (("Subgoal *1/2" :use ((:instance common-member-shared (l (lcoset x h g)) (m (lcoset (car l) h g)))
                                (:instance lcosets-intersect (a (common-member (lcoset x h g) (lcoset (car l) h g)))
				                             (y (car l))
							     (b x))))))

(defthm lcosets-aux-disjointp-pairwise
  (implies (and (subgroupp h g)
		(sublistp l (elts g)))
	   (disjointp-pairwise (lcosets-aux l h g))))

(defthm lcosets-disjointp-pairwise
  (implies (subgroupp h g)
	   (disjointp-pairwise (lcosets h g)))
  :hints (("Goal" :in-theory (enable lcosets))))

(local-defthm dlistp-list-lcosets-aux
  (implies (and (subgroupp h g)
		(sublistp l (car g)))
	   (dlistp-list (lcosets-aux l h g)))
  :hints (("Subgoal *1/2" :use ((:instance ordp-lcoset (x (car l)))))))

(defthm dlistp-list-lcosets
  (implies (subgroupp h g)
	   (dlistp-list (lcosets h g)))
  :hints (("Goal" :in-theory (enable lcosets))))

(defthm dlistp-append-list-lcosets
  (implies (subgroupp h g)
	   (dlistp (append-list (lcosets h g)))))

;; elts(g) is a sublist of append-list(lcosets(h,g):

(local-defthm sublistp-elts-lcosets-aux
  (implies (and (subgroupp h g)
		(sublistp l (car g)))
	   (sublistp l (append-list (lcosets-aux l h g)))))

(defthm sublistp-elts-lcosets
  (implies (subgroupp h g)
	   (sublistp (elts g) (append-list (lcosets h g))))
  :hints (("Goal" :in-theory (enable lcosets))))

;; append-list(lcosets(h,g) is a sublist of elts(g):

(local-defthm sublistp-lcosets-aux-elts
  (implies (and (subgroupp h g)
		(sublistp l (car g)))
	   (sublistp (append-list (lcosets-aux l h g))
	             (elts g)))
  :hints (("Goal" :in-theory (enable sublistp-lcoset-g))))

(defthm sublistp-lcosets-elts
  (implies (subgroupp h g)
	   (sublistp (append-list (lcosets h g))
	             (elts g)))
  :hints (("Goal" :in-theory (enable lcosets))))

;; Thus, the two lists have the same length, and Lagrange's Theorem follows:

(defthmd len-append-list-lcosets
  (implies (subgroupp h g)
	   (equal (len (append-list (lcosets h g)))
	          (order g)))
  :hints (("Goal" :use ((:instance sublistp-equal-len (l (elts g)) (m (append-list (lcosets h g)))))
                  :in-theory (enable subgroupp groupp))))

(defthmd lagrange
  (implies (subgroupp h g)
           (equal (* (order h) (subgroup-index h g))
                  (order g)))
  :hints (("Goal" :use (len-append-list-lcosets))))


;;---------------------------------------------------------------------------------------------------
;; Normal Subgroups and Quotient Groups
;;---------------------------------------------------------------------------------------------------

(defund conj (x a g)
  (op (op (inv a g) x g) a g))

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
           (and (groupp h) (groupp g)))
  :hints (("Goal" :in-theory (enable subgroupp))))

(local-defthm normalp-elt-1
  (implies (and (member-equal y l)
		(normalp-elt x l h g))
	   (in (conj x y g) h)))

(local-defthm normalp-aux-1
  (implies (and (in x g)
                (member-equal y l)
                (normalp-aux l h g))
	   (in (conj y x g) h)))

(defthm normalp-conj
  (implies (and (normalp h g)
                (in x h)
		(in y g))
	   (in (conj x y g) h)))

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

(local-defthm normalp-elt-2
  (let ((cex (normalp-elt-cex x l h g)))
    (implies (not (normalp-elt x l h g))
             (and (member-equal cex l)
	          (not (in (conj x cex g) h))))))

(local-defthm normalp-aux-2
  (let ((cex (normalp-aux-cex l h g)))
    (implies (not (normalp-aux l h g))
             (and (member-equal (car cex) l)
	          (in (cadr cex) g)
		  (not (in (conj (car cex) (cadr cex) g) h))))))

(defthmd not-normalp-cex
  (let* ((cex (normalp-cex h g))
         (x (car cex))
	 (y (cadr cex)))
    (implies (and (subgroupp h g)
                  (not (normalp h g)))
	     (and (in x h)
	          (in y g)
		  (not (in (conj x y g) h))))))

(defthmd conj-commute
  (implies (and (groupp g)
                (in x g)
		(in y g))
	   (iff (equal (conj x y g) x)
	        (equal (op x y g) (op y x g))))
  :hints (("Goal" :expand ((conj x y g))
                  :use ((:instance group-assoc (x (inv y g)) (y x) (z y))
			(:instance group-assoc (x y) (y (inv y g)) (z (op x y g)))
                        (:instance left-cancel (a y) (y (op (inv y g) (op x y g) g)))
                        (:instance group-right-inverse (x y))))))

(defthm abelianp-normalp
  (implies (and (abelianp g)
		(subgroupp h g))
	   (normalp h g))
  :hints (("Goal" :use (not-normalp-cex
                        (:instance group-abelianp (x (car (normalp-cex h g))) (y (cadr (normalp-cex h g))))
			(:instance conj-commute (x (car (normalp-cex h g))) (y (cadr (normalp-cex h g))))))))

(in-theory (disable normalp))

;; Identity element:

(defun qe (h g) (lcoset (e g) h g))

(defthm car-qe
  (implies (normalp h g)
           (equal (car (lcoset (e g) h g))
	          (e g)))
  :hints (("Goal" :in-theory (e/d (e) (member-self-lcoset in-e-g))
                  :use (in-e-g
                        (:instance ordp-lcoset (x (e g)))
                        (:instance lcoset-car (x (e g)))
			(:instance member-self-lcoset (x (e g)))
			(:instance car-ordp-minimal (x (e g)) (l (lcoset (e g) h g)))))))

(defthm qe-exists
  (implies (subgroupp h g)
           (member-equal (qe h g) (lcosets h g))))


;; Move the identity element to the front of the list of cosets:

(defun qlist (h g)
  (cons (qe h g) (remove1-equal (qe h g) (lcosets h g))))

(defthm len-qlist
  (implies (normalp h g)
           (equal (len (qlist h g)) (subgroup-index h g))))

(defthm member-qlist-car
  (implies (and (normalp h g)
                (member x (qlist h g)))
	   (in (car x) g))
  :hints (("Goal" :in-theory (enable normalp)
                  :use ((:instance lcosets-cars (c x))))))

(defthmd car-member-qlist
  (implies (and (normalp h g)
                (member x (qlist h g)))
	   (and (in (car x) g)
	        (equal (lcoset (car x) h g)
		       x)))
  :hints (("Goal" :in-theory (enable normalp)
                  :use ((:instance lcosets-cars (c x))))))

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
           (not (member-equal () (qlist h g))))
  :hints (("Goal" :in-theory (disable member-self-lcoset)
                  :use (in-e-g (:instance member-self-lcoset (x (e g)))))))

(in-theory (disable qlist))

(defun qop (x y h g)
  (lcoset (op (car x) (car y) g) h g))

(defun qinv (x h g)
  (lcoset (inv (car x) g) h g))

(local-defthmd op-qop-1
  (implies (and (normalp h g)
                (member-equal x (qlist h g)) (member-equal y (qlist h g))
		(member-equal a x) (member-equal b y))
	   (and (in (car x) g)
	        (in (car y) g)
	        (in a g)
	        (in b g)
		(in (op (inv (car x) g) a g) h)
	        (in (op (inv (car y) g) b g) h)))
  :hints (("Goal" :in-theory (disable member-lcoset-g)
	          :use (car-member-qlist
			(:instance car-member-qlist (x y))
			(:instance member-lcoset-iff (x (car x)) (y a))
			(:instance member-lcoset-iff (x (car y)) (y b))
			(:instance member-lcoset-g (x (car x)) (y a))
			(:instance member-lcoset-g (x (car y)) (y b))))))

(local-defthmd op-qop-2
  (implies (and (groupp g) (in cx g) (in cy g) (in a g) (in b g))
	   (equal (op (inv (op cx cy g) g) (op a b g) g)
		  (op (inv cy g) (op (op (inv cx g) a g) b g) g)))
  :hints (("Goal" :use ((:instance prod-inv (x cx) (y cy))
			(:instance group-assoc (x (inv cy g)) (y (inv cx g)) (z (op a b g)))
			(:instance group-assoc (x (inv cx g)) (y a) (z b))))))

(local-defthmd op-qop-3
  (implies (and (normalp h g) (in h1 h) (in b g))
	   (and (in (conj h1 b g) h)
		(equal (op h1 b g)
		       (op b (conj h1 b g) g))))
  :hints (("Goal" :in-theory (enable conj)
	          :use ((:instance normalp-conj (x h1) (y b))
		        (:instance group-right-inverse (x b))
			(:instance group-left-identity (x h1))
			(:instance group-assoc (x b) (y (inv b g)) (z h1))
			(:instance group-assoc (x b) (y (op (inv b g) h1 g)) (z b))))))

(local-defthmd op-qop-4
  (implies (and (normalp h g)
                (member-equal x (qlist h g)) (member-equal y (qlist h g))
		(member-equal a x) (member-equal b y))
	   (and (in (op (inv (car y) g) b g) h)
	        (in (conj (op (inv (car x) g) a g) b g) h)
	        (equal (op (inv (op (car x) (car y) g) g) (op a b g) g)
	               (op (op (inv (car y) g) b g) (conj (op (inv (car x) g) a g) b g) g))))
  :hints (("Goal" :in-theory (disable normalp-conj lcoset-car acl2::subsetp-car-member)
                  :use (op-qop-1
                        (:instance op-qop-2 (cx (car x)) (cy (car y)))
			(:instance op-qop-3 (h1 (op (inv (car x) g) a g)))
			(:instance normalp-conj (x (op (inv (e g) g) a g)) (y b))
			(:instance group-assoc (x (inv (car y) g)) (y b) (z (conj (op (inv (car x) g) a g) b g)))))))

(local-defthmd op-qop-5
  (implies (and (normalp h g)
                (member-equal x (qlist h g)) (member-equal y (qlist h g))
		(member-equal a x) (member-equal b y))
	   (in (op (inv (op (car x) (car y) g) g) (op a b g) g) h))
  :hints (("Goal" :in-theory (enable normalp)
                  :use (op-qop-4 subgroup-e
                        (:instance group-closure (x (op (inv (car y) g) b g)) (y (conj (op (inv (car x) g) a g) b g)) (g h))))))

(defthm op-qop
  (implies (and (normalp h g)
                (member-equal x (qlist h g)) (member-equal y (qlist h g))
		(member-equal a x) (member-equal b y))
	   (member-equal (op a b g) (qop x y h g)))
  :hints (("Goal" :use (op-qop-1 op-qop-5
                        (:instance member-lcoset-iff (x (op (car x) (car y) g)) (y (op a b g)))))))

(defthm q-identity
  (implies (and (normalp h g)
                (member-equal x (qlist h g)))
	   (equal (qop (qe h g) x h g)
	          x))
  :hints (("Goal" :use (car-member-qlist))))

(defthm q-closed
  (implies (and (normalp h g)
                (member-equal x (qlist h g))
                (member-equal y (qlist h g)))
           (member-equal (qop x y h g) (qlist h g))))

(in-theory (disable qop))

(local-defthm q-assoc-1
  (implies (and (normalp h g)
                (member x (qlist h g)))
	   (car x))
  :hints (("Goal" :in-theory (enable subgroupp groupp normalp)
                  :use (member-qlist-car))))

(local-defthm q-assoc-2
  (implies (and (normalp h g)
                (member x (qlist h g)))
	   (consp x))
  :hints (("Goal" :use (q-assoc-1))))

(local-defthmd q-assoc-3
  (implies (and (normalp h g)
                (member-equal x (qlist h g))
                (member-equal y (qlist h g))
                (member-equal z (qlist h g)))
	   (and (member-equal (op (car x) (op (car y) (car z) g) g)
	                      (qop x (qop y z h g) h g))
	        (member-equal (op (op (car x) (car y) g) (car z) g)
	                      (qop (qop x y h g) z h g)))))

(defthm q-assoc
  (implies (and (normalp h g)
                (member-equal x (qlist h g))
                (member-equal y (qlist h g))
                (member-equal z (qlist h g)))
	   (equal (qop x (qop y z h g) h g)
	          (qop (qop x y h g) z h g)))
  :hints (("Goal" :in-theory (enable qop)
                  :use (q-assoc-3
                        (:instance group-assoc (x (car x)) (y (car y)) (z (car z)))
                        (:instance equal-lcoset-2 (x1 (op (car (lcoset (op (car x) (car y) g) h g)) (car z) g))
			                          (x2 (op (car x) (car (lcoset (op (car y) (car z) g) h g)) g))
						  (y (op (op (car x) (car y) g) (car z) g)))))))

(local-defthm q-inverse-1
  (implies (and (normalp h g)
                (member-equal x (qlist h g)))
	   (member-equal (qinv x h g) (qlist h g)))
  :hints (("Goal" :use (car-member-qlist))))

(local-defthm q-inverse-2
  (implies (and (normalp h g)
                (member-equal x (qlist h g)))
	   (member-equal (e g) (qop (qinv x h g) x h g)))
  :hints (("Goal" :in-theory (disable op-qop)
                  :use (car-member-qlist
		        (:instance car-member-qlist (x (qinv x h g)))
			(:instance op-qop (x (qinv x h g)) (y x) (b (car x)) (a (inv (car x) g)))))))

(defthm q-inverse
  (implies (and (normalp h g)
                (member-equal x (qlist h g)))
	   (and (member-equal (qinv x h g) (qlist h g))
	        (equal (qop (qinv x h g) x h g) (qe h g))))
  :hints (("Goal" :use (q-inverse-1 q-inverse-2
                        (:instance car-member-qlist (x (qop (qinv x h g) x h g)))
                        (:instance equal-lcoset (x (car (qop (qinv x h g) x h g))) (y (e g)))))))

(in-theory (disable qe qlist qop qinv))

;; Quotient group:

(defgroup quotient (g h)
  (normalp h g)
  (qlist h g)
  (qop x y h g)
  (qinv x h g))

(in-theory (disable quotient))

(defthm order-quotient
  (implies (normalp h g)
           (equal (order (quotient g h))
	          (subgroup-index h g))))

(defthm quotient-e
  (implies (normalp h g)
           (equal (e (quotient g h))
	          (lcoset (e g) h g)))
  :hints (("Goal" :in-theory (enable qe e))))

(defthm abelian-quotient
  (implies (and (subgroupp h g)
                (abelianp g))
	   (abelianp (quotient g h)))
  :hints (("Goal" :in-theory (enable qop)
                  :use ((:instance group-abelianp (x (caar (abelianp-cex (quotient g h)))) (y (caadr (abelianp-cex (quotient g h)))))
                        (:instance not-abelianp-cex (g (quotient g h)))
			(:instance car-member-qlist (x (car (abelianp-cex (quotient g h)))))
			(:instance car-member-qlist (x (cadr (abelianp-cex (quotient g h)))))))))

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

;; The macro defsubgroup calls defgroup to define a subgroup of a given group, which is represented
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

(defun centizer-elts-aux (a l g)
  (if (consp l)
      (if (equal (op a (car l) g) (op (car l) a g))
          (cons (car l) (centizer-elts-aux a (cdr l) g))
	(centizer-elts-aux a (cdr l) g))
    ()))

(defund centizer-elts (a g) (centizer-elts-aux a (elts g) g))

(local-defthm sublistp-centizer-elts-aux
  (implies (and (groupp g) (in a g))
           (sublistp (centizer-elts-aux a l g) l)))

(defthm sublistp-centizer-elts
  (implies (and (groupp g) (in a g))
           (sublistp (centizer-elts a g) (elts g)))
  :hints (("Goal" :in-theory (enable centizer-elts))))

(local-defthm dlistp-centizer-elts-aux
  (implies (and (groupp g) (in a g) (dlistp l))
           (dlistp (centizer-elts-aux a l g))))

(defthm dlistp-centizer-elts
  (implies (and (groupp g) (in a g))
           (dlistp (centizer-elts a g)))
  :hints (("Goal" :in-theory (enable centizer-elts))))

(defthm centizer-elts-identity
  (implies (and (groupp g) (in a g))
           (equal (car (centizer-elts a g)) (e g)))
  :hints (("Goal" :in-theory (enable e centizer-elts)
                  :use ((:instance group-left-identity (x a))
		        (:instance group-right-identity (x a)))
                  :expand ((centizer-elts-aux a (car g) g)))))

(defthm consp-centizer-elts
  (implies (and (groupp g) (in a g))
           (consp (centizer-elts a g)))
  :hints (("Goal" :in-theory (enable e centizer-elts)
                  :use ((:instance group-left-identity (x a))
		        (:instance group-right-identity (x a)))
                  :expand ((centizer-elts-aux a (car g) g)))))

(local-defthm centizer-elts-aux-iff
  (implies (and (groupp g) (in a g) (sublistp l (elts g)))
           (iff (member-equal x (centizer-elts-aux a l g))
	        (and (member x l) (equal (op a x g) (op x a g))))))

(defthm centizer-elts-iff
  (implies (and (groupp g) (in a g))
           (iff (member-equal x (centizer-elts a g))
	        (and (in x g) (equal (op a x g) (op x a g)))))
  :hints (("Goal" :in-theory (enable centizer-elts))))

(defthm centizer-elts-closed
  (implies (and (groupp g) (in a g)
                (member-equal x (centizer-elts a g))
		(member-equal y (centizer-elts a g)))
           (member-equal (op x y g) (centizer-elts a g)))
  :hints (("Goal" :use ((:instance group-assoc (z a))
                        (:instance group-assoc (y a) (z y))
                        (:instance group-assoc (x a) (y x) (z y))))))

(defthm centizer-elts-inverse
  (implies (and (groupp g) (in a g)
                (member-equal x (centizer-elts a g)))
           (member-equal (inv x g) (centizer-elts a g)))
  :hints (("Goal" :use (group-right-inverse group-left-inverse
                        (:instance group-right-identity (x a))
                        (:instance group-assoc (x a) (y x) (z (inv x g)))
                        (:instance group-assoc (x (inv x g)) (y (op a x g)) (z (inv x g)))
                        (:instance group-assoc (x (inv x g)) (y x) (z a))
			(:instance group-left-identity (x a))))))

(in-theory (disable centizer-elts-iff))

(defsubgroup centralizer (a g)
  (and (groupp g) (in a g))
  (centizer-elts a g))

(defthmd centralizer-iff
  (implies (and (groupp g) (in a g))
           (iff (in x (centralizer a g))
	        (and (in x g) (equal (op a x g) (op x a g)))))
  :hints (("Goal" :in-theory (enable centizer-elts-iff))))

(in-theory (disable centralizer-elts))

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
		       (conj a x g))))
  :hints (("Goal" :in-theory (enable conj centralizer-conj-iff)
                  :use (prod-inv
		        (:instance group-assoc (x (inv y g)) (y (inv x g)) (z a))
			(:instance group-assoc (x (inv y g)) (y (op (inv x g) a g)) (z (op x y g)))
			(:instance group-assoc (x (op (inv x g) a g)) (y x) (z y))
			(:instance group-assoc (x y) (y (inv y g)) (z (op (conj a x g) y g)))
			(:instance group-assoc (x (conj a x g)) (z (inv y g)))
			(:instance left-cancel (a y) (x (op (inv y g) (op (conj a x g) y g) g)) (y a))
			(:instance right-cancel (a (inv y g)) (x (op (conj a x g) y g)) (y (op y a g)))))))


;;----------------------------------------------------------------------------------------------------------
;; Center of a Group
;;----------------------------------------------------------------------------------------------------------

;; Our second application of defsubgroup is the center of a group:

(defun cent-cex-aux (a l g)
  (if (consp l)
      (if (equal (op a (car l) g) (op (car l) a g))
          (cent-cex-aux a (cdr l) g)
	(car l))
    ()))

(defun cent-cex (a g) (cent-cex-aux a (elts g) g))

(defun cent-elts-aux (l g)
  (if (consp l)
      (if (cent-cex (car l) g)
          (cent-elts-aux (cdr l) g)
	(cons (car l) (cent-elts-aux (cdr l) g)))

    ()))

(defun cent-elts (g) (cent-elts-aux (elts g) g))


(local-defthm sublistp-cent-elts-aux
  (sublistp (cent-elts-aux l g) l))

(defthm sublistp-cent-elts
  (sublistp (cent-elts g) (elts g)))

(local-defthm dlistp-cent-elts-aux
  (implies (dlistp l)
           (dlistp (cent-elts-aux l g))))

(defthm dlistp-cent-elts
  (implies (groupp g)
           (dlistp (cent-elts g))))

(local-defthm cent-cex-aux-1
  (implies (and (in a g)
                (sublistp l (elts g))
                (cent-cex-aux a l g))
	   (and (in (cent-cex-aux a l g) g)
	        (not (equal (op a (cent-cex-aux a l g) g)
		            (op (cent-cex-aux a l g) a g))))))

(local-defthm cent-cex-1
  (implies (and (in a g)
                (cent-cex a g))
	   (and (in (cent-cex a g) g)
	        (not (equal (op a (cent-cex a g) g)
		            (op (cent-cex a g) a g))))))

(local-defthm cent-elts-aux-1
  (implies (and (member-equal a l)
                (sublistp l (elts g))
                (not (member-equal a (cent-elts-aux l g))))
	   (and (in (cent-cex a g) g)
	        (not (equal (op a (cent-cex a g) g)
		            (op (cent-cex a g) a g))))))

(defthm cent-elts-1
  (implies (and (in a g)
                (not (member-equal a (cent-elts g))))
	   (and (in (cent-cex a g) g)
	        (not (equal (op a (cent-cex a g) g)
		            (op (cent-cex a g) a g)))))
  :hints (("Goal" :use ((:instance cent-elts-aux-1 (l (elts g)))))))

(local-defthmd cent-cex-aux-2
  (implies (and (in a g)
                (sublistp l (elts g))
                (not (cent-cex-aux a l g))
		(not (member-equal () l))
		(member-equal x l))
	   (equal (op a x g) (op x a g))))

(local-defthm cent-cex-2
  (implies (and (groupp g)
                (in a g)
                (not (cent-cex a g))
		(in x g))
	   (equal (op a x g) (op x a g)))
  :hints (("Goal" :use (:instance cent-cex-aux-2 (l (elts g))))))

(local-defthm cent-elts-aux-2
  (implies (and (groupp g)
                (member-equal a l)
                (sublistp l (elts g))
                (member-equal a (cent-elts-aux l g))
		(in x g))
	   (equal (op a x g) (op x a g))))

(defthmd cent-elts-2
  (implies (and (groupp g)
                (in a g)
                (member-equal a (cent-elts g))
		(in x g))
	   (equal (op a x g) (op x a g)))
  :hints (("Goal" :use ((:instance cent-elts-aux-2 (l (elts g)))))))

(in-theory (disable cent-cex))

(defthm cent-elts-identity
  (implies (groupp g)
           (equal (car (cent-elts g)) (e g)))
  :hints (("Goal" :in-theory (enable e)
                  :use ((:instance cent-elts-1 (a (e g)))
		        (:instance cent-cex-1 (a (e g)))
		        (:instance group-left-identity (x (cent-cex (e g) g)))
		        (:instance group-right-identity (x (cent-cex (e g) g))))
                  :expand ((cent-elts-aux (car g) g)))))

(defthm consp-cent-elts
  (implies (groupp g)
           (consp (cent-elts g)))
  :hints (("Goal" :in-theory (enable groupp e) :use (cent-elts-identity))))

(defthm cent-elts-closed
  (implies (and (groupp g)
                (member-equal x (cent-elts g))
		(member-equal y (cent-elts g)))
           (member-equal (op x y g) (cent-elts g)))
  :hints (("Goal" :in-theory (disable cent-elts-1)
                  :use ((:instance cent-elts-1 (a (op x y g)))
                        (:instance cent-elts-2 (a x) (x (cent-cex (op x y g) g)))
                        (:instance cent-elts-2 (a y) (x (cent-cex (op x y g) g)))
                        (:instance group-assoc (z (cent-cex (op x y g) g)))
                        (:instance group-assoc (y (cent-cex (op x y g) g)) (z y))
                        (:instance group-assoc (x (cent-cex (op x y g) g)) (y x) (z y))))))

(defthm cent-elts-inverse
  (implies (and (groupp g)
                (member-equal x (cent-elts g)))
           (member-equal (inv x g) (cent-elts g)))
  :hints (("Goal" :use ((:instance cent-elts-1 (a (inv x g)))
                        (:instance cent-elts-2 (a x) (x (inv (cent-cex (inv x g) g) g)))
			(:instance prod-inv (x (inv (cent-cex (inv x g) g) g)) (y x))
                        (:instance prod-inv (y (inv (cent-cex (inv x g) g) g)))))))

(local (in-theory (disable cent-elts cent-elts-aux-2 cent-elts-2)))

(defsubgroup center (g)
  (groupp g)
  (cent-elts g))

(defthmd center-commutes
  (implies (and (groupp g)
                (in a (center g))
		(in x g))
	   (equal (op a x g) (op x a g)))
  :hints (("Goal" :use (cent-elts-2))))

(defthmd center-commutes-converse
  (implies (and (groupp g)
                (in a g)
                (not (in a (center g))))
	   (and (in (cent-cex a g) g)
	        (not (equal (op a (cent-cex a g) g)
		            (op (cent-cex a g) a g))))))

(in-theory (disable cent-elts-1))

(defthm abelianp-center
  (implies (groupp g)
           (abelianp (center g)))
  :hints (("Goal" :use ((:instance not-abelianp-cex (g (center g)))
                        (:instance center-commutes (a (car (abelianp-cex (center g)))) (x (cadr (abelianp-cex (center g)))))))))

(defthmd order-proper-subgroup
  (implies (and (groupp g)
                (subgroupp h g)
		(in x g)
		(not (in x h)))
	   (< (order h) (order g)))
  :hints (("Goal" :in-theory (enable groupp subgroupp)
                  :use ((:instance len-proper-sublist (l (elts h)) (m (elts g)))))))

(defthmd order-centralizer-not-center
  (implies (and (groupp g)
                (in x g)
		(not (in x (center g))))
	   (< (order (centralizer x g)) (order g)))
  :hints (("Goal" :use ((:instance center-commutes-converse (a x))
                        (:instance centralizer-iff (a x) (x (cent-cex x g)))
			(:instance  order-proper-subgroup (h (centralizer x g)) (x (cent-cex x g)))))))


;;---------------------------------------------------------------------------------------------------
;; Cyclic Subgroups
;;---------------------------------------------------------------------------------------------------

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
	          (power a (+ n m) g)))
  :hints (("Subgoal *1/2" :use ((:instance group-assoc (x a) (y (power a (1- n) g)) (z (power a m g)))))))

(defthm power-e
  (implies (and (groupp g) (natp n))
           (equal (power (e g) n g) (e g))))

(defthmd power*
  (implies (and (groupp g) (in a g) (natp n) (natp m))
           (equal (power (power a n g) m g)
	          (power a (* n m) g)))
  :hints (("Goal" :induct (fact m))
          ("Subgoal *1/2" :use ((:instance power+ (m (* n (1- m))))))))

(defun ord-aux (a n g)
  (declare (xargs :measure (nfix (- (order g) n))))
  (if (equal (power a n g) (e g))
      n
    (if (and (natp n) (< n (order g)))
        (ord-aux a (1+ n) g)
      ())))

(defun ord (a g) (ord-aux a 1 g))

(defun powers-aux (a n g)
  (if (zp n)
      ()
    (append (powers-aux a (1- n) g) (list (power a (1- n) g)))))

(defun powers (a g) (powers-aux a (ord a g) g))

(local-defthmd ord-1
  (implies (and (groupp g)
                (in a g)
		(posp n)
		(not (ord-aux a n g))
		(natp k)
		(<= n k)
		(<= k (order g)))
	   (not (equal (power a k g) (e g)))))

(local-defthmd ord-2
  (implies (and (groupp g)
                (in a g)
		(not (ord a g))
		(posp k)
		(<= k (order g)))
	   (not (equal (power a k g) (e g))))
  :hints (("Goal" :use ((:instance ord-1 (n 1))))))

(local-defthmd ord-3
  (implies (and (groupp g)
                (in a g)
		(not (ord a g))
		(natp k)
		(natp j)
		(< j k)
		(<= k (order g)))
	   (not (equal (power a k g) (power a j g))))
  :hints (("Goal" :use ((:instance ord-2 (k (- k j)))
                        (:instance power+ (n (- k j)) (m j))
			(:instance right-cancel (a (power a j g)) (x (power a (- k j) g)) (y (e g)))))))

(local-defthmd ord-4
  (implies (and (groupp g)
                (in a g)
		(not (ord a g))
		(natp k)
		(natp j)
		(<= j k)
		(<= k (order g)))
	   (not (member-equal (power a k g) (powers-aux a j g))))
  :hints (("Goal" :induct (powers-aux a j g))
          ("Subgoal *1/2" :use ((:instance ord-3 (j (1- j)))))))

(local-defthmd ord-5
  (implies (and (groupp g)
                (in a g)
		(not (ord a g))
		(natp k)
		(<= k (1+ (order g))))
	   (dlistp (powers-aux a k g)))
  :hints (("Subgoal *1/2" :use ((:instance dlistp-append (l (powers-aux a (1- k) k)) (m (list (power a (1- k) g))))
                                (:instance ord-4 (k (1- k)) (j (1- k)))))))

(local-defthmd ord-6
  (implies (and (groupp g)
                (in a g)
		(natp n))
	   (sublistp (powers-aux a n g) (elts g))))

(local-defthmd ord-7
  (implies (and (groupp g)
                (in a g)
		(natp n))
	   (equal (len (powers-aux a n g)) n)))

(local-defthmd ord-8
  (implies (and (groupp g)
                (in a g))
           (ord a g))
  :hints (("Goal" :use ((:instance ord-6 (n (1+ (order g))))
                        (:instance ord-7 (n (1+ (order g))))
                        (:instance ord-5 (k (1+ (order g))))
			(:instance sublistp-<=-len (l (powers-aux a (1+ (order g)) g)) (m (elts g)))))))

(local-defthmd ord-9
  (implies (and (groupp g)
                (in a g)
		(posp n)
		(<= n (order g))
		(ord-aux a n g))
	   (and (posp (ord-aux a n g))
	        (equal (power a (ord-aux a n g) g) (e g))
		(implies (and (posp k) (<= n k) (< k (ord-aux a n g)))
		         (not (equal (power a k g) (e g))))
	        (<= (ord-aux a n g) (order g)))))

(defthm ord<=order
  (implies (and (groupp g) (in a g))
           (and (posp (ord a g)) (<= (ord a g) (order g))))
  :hints (("Goal" :use (ord-8 order-pos (:instance ord-9 (n 1))))))

(defthm ord-power
  (implies (and (groupp g) (in a g))
           (and (equal (power a (ord a g) g) (e g))
	        (implies (and (posp n) (< n (ord a g)))
		         (not (equal (power a n g) (e g))))))
  :hints (("Goal" :use (ord-8 (:instance ord-9 (n 1) (k n))))))

(defthmd power-mod
  (implies (and (groupp g) (in a g) (natp n))
           (equal (power a n g) (power a (mod n (ord a g)) g)))
  :hints (("Goal" :use (ord<=order ord-power
                        (:instance mod-def (x n) (y (ord a g)))
			(:instance power* (n (ord a g)) (m (fl (/ n (ord a g)))))
			(:instance power+ (m (* (ord a g) (fl (/ n (ord a g))))) (n (mod n (ord a g))))))))

(defthm divides-ord
  (implies (and (groupp g) (in a g) (natp n))
           (iff (equal (power a n g) (e g))
	        (divides (ord a g) n)))
  :hints (("Goal" :in-theory (enable divides) :use (ord<=order power-mod ord-power))))

(in-theory (disable ord))

(defthm ord-power-div
  (implies (and (groupp g)
                (in a g)
		(posp n)
		(divides n (ord a g)))
	   (equal (ord (power a n g) g)
	          (/ (ord a g) n)))
  :hints (("Goal" :in-theory (enable divides)
                  :nonlinearp t
                  :use (ord<=order
		        (:instance ord-power (n (* n (ord (power a n g) g))))
		        (:instance ord<=order (a (power a n g)))
		        (:instance ord-power (a (power a n g)) (n (/ (ord a g) n)))
			(:instance power* (m (ord (power a n g) g)))
			(:instance power* (m (/ (ord a g) n)))))))

(local-defthm power-member-1
  (implies (and (groupp g) (in a g) (natp n) (natp m) (< n m))
           (member (power a n g) (powers-aux a m g)))
  :hints (("Goal" :induct (powers-aux a m g))))

(defthm power-member
  (implies (and (groupp g) (in a g) (natp n))
           (member (power a n g) (powers a g)))
  :hints (("Goal" :use (ord<=order power-mod (:instance power-member-1 (m (ord a g)) (n (mod n (ord a g))))))))

(local-defthm consp-powers-aux
  (implies (and (groupp g) (in a g) (posp n))
           (consp (powers-aux a n g))))

(defthm consp-powers
  (implies (and (groupp g) (in a g))
           (consp (powers a g)))
  :hints (("Goal" :use (ord<=order))))

(local-defthm powers-aux-non-nil
  (implies (and (groupp g) (in a g) (natp n))
           (not (member-equal () (powers-aux a n g))))
  :hints (("Subgoal *1/2" :in-theory (e/d (groupp) ( power-in-g))
                          :use ((:instance power-in-g (n (1- n)))))))

(defthm powers-non-nil
  (implies (and (groupp g) (in a g))
           (not (member-equal () (powers a g))))
  :hints (("Goal" :use (ord<=order))))

(local-defthmd dlistp-powers-1
  (implies (and (groupp g)
                (in a g)
		(natp k)
		(natp j)
		(< j k)
		(< k (ord a g)))
	   (not (equal (power a k g) (power a j g))))
  :hints (("Goal" :use ((:instance ord-power (n (- k j)))
                        (:instance power+ (n (- k j)) (m j))
			(:instance right-cancel (a (power a j g)) (x (power a (- k j) g)) (y (e g)))))))

(local-defthmd dlistp-powers-2
  (implies (and (groupp g)
                (in a g)
		(natp k)
		(natp j)
		(<= j k)
		(< k (ord a g)))
	   (not (member-equal (power a k g) (powers-aux a j g))))
  :hints (("Goal" :induct (powers-aux a j g))
          ("Subgoal *1/2" :use ((:instance dlistp-powers-1 (j (1- j)))))))

(local-defthmd dlistp-powers-3
  (implies (and (groupp g)
                (in a g)
		(natp k)
		(<= k (ord a g)))
	   (dlistp (powers-aux a k g)))
  :hints (("Subgoal *1/2" :use ((:instance dlistp-append (l (powers-aux a (1- k) k)) (m (list (power a (1- k) g))))
                                (:instance dlistp-powers-2 (k (1- k)) (j (1- k)))))))

(defthm dlistp-powers
  (implies (and (groupp g) (in a g))
           (dlistp (powers a g)))
  :hints (("Goal" :use (ord<=order))))

(defthm len-append
  (implies (natp n)
           (equal (nth n (append l m))
	          (if (< n (len l))
		      (nth n l)
		    (nth (- n (len l)) m)))))

(local-defthm len-powers-aux
  (implies (natp m)
           (equal (len (powers-aux a m g)) m)))

(defthm len-powers
  (implies (and (groupp g) (in a g))
           (equal (len (powers a g)) (ord a g)))
  :hints (("Goal" :use (ord<=order))))

(local-defthm member-powers-aux
  (implies (and (groupp g) (in a g)
                (natp n) (natp m) (< n m))
	   (equal (nth n (powers-aux a m g))
	          (power a n g)))
  :hints (("Goal" :induct (powers-aux a m g))))

(defthm member-powers
  (implies (and (groupp g) (in a g)
                (natp n) (< n (ord a g)))
	   (equal (nth n (powers a g))
	          (power a n g)))
  :hints (("Goal" :use (ord<=order))))


(defthm power-index
  (implies (and (groupp g) (in a g)
                (member-equal x (powers a g)))
	   (and (natp (index x (powers a g)))
	        (< (index x (powers a g)) (ord a g))
		(equal (power a (index x (powers a g)) g)
	               x)))
  :hints (("Goal" :use ((:instance ind<len (l (powers a g)))
                        (:instance member-powers (n (index x (powers a g))))))))

(local-defthm car-powers-aux-1
  (equal (car (powers-aux a 1 g))
         (e g))
  :hints (("Goal" :expand ((powers-aux a 1 g)))))

(local-defthm car-powers-aux
  (implies (posp n)
           (equal (car (powers-aux a n g))
                  (e g))))

(defthm car-powers
  (implies (and (groupp g) (in a g))
           (equal (car (powers a g))
                  (e g)))
  :hints (("Goal" :use (ord<=order))))

(in-theory (disable powers))

(defthm powers-closed
  (implies (and (groupp g) (in a g)
                (member-equal x (powers a g))
                (member-equal y (powers a g)))
           (member-equal (op x y g) (powers a g)))
  :hints (("Goal" :use (power-index
                        (:instance power-index (x y))
			(:instance power+ (n (index x (powers a g))) (m (index y (powers a g))))))))

(local-defthm member-powers-in-g
  (implies (and (groupp g) (in a g) (member-equal x (powers a g)))
           (in x g))
  :hints (("Goal" :use (ord<=order power-index
                        (:instance power-in-g (n (INDEX X (POWERS A G)))))
                  :in-theory (disable ord<=order power-in-g power-index))))

(defthm powers-id
  (implies (and (groupp g) (in a g)
                (member-equal x (powers a g)))
	   (equal (op (e g) x g)
	          x)))

(defthm c-assoc
  (implies (and (groupp g) (in a g)
                (member-equal x (powers a g))
                (member-equal y (powers a g))
                (member-equal z (powers a g)))
	   (equal (op x (op y z g) g)
	          (op (op x y g) z g)))
  :hints (("Goal" :use (group-assoc))))


(defun cinv (x a g)
  (power a (- (ord a g) (index x (powers a g))) g))

(defthmd c-inverse
  (implies (and (groupp g) (in a g)
                (member-equal x (powers a g)))
           (and (member-equal (cinv x a g) (powers a g))
	        (equal (op (cinv x a g) x g) (e g))))
  :hints (("Goal" :in-theory (e/d (natp) (power-index ord<=order))
                  :use (ord<=order power-index
		        (:instance power+ (n (- (ord a g) (index x (powers a g))))
			                  (m (index x (powers a g))))))))

(in-theory (disable ord<=order))

(in-theory (disable cinv))

(defthm inv-power
  (implies (and (groupp g) (in a g)
                (member-equal x (powers a g)))
	   (member-equal (inv x g) (powers a g)))
  :hints (("Goal" :use (c-inverse (:instance inv-unique (y (cinv x a g)))))))

(local-defthm sublistp-powers-aux
  (implies (and (groupp g) (in a g) (natp n))
           (sublistp (powers-aux a n g) (elts g))))

(defthm sublistp-powers
  (implies (and (groupp g) (in a g))
           (sublistp (powers a g) (elts g)))
  :hints (("Goal" :in-theory (e/d (powers) (ord<=order))
                  :use (ord<=order))))

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

(defun elt-of-ord-aux (l n g)
  (if (consp l)
      (if (= (ord (car l) g) n)
          (car l)
	(elt-of-ord-aux (cdr l) n g))
    ()))

(defun elt-of-ord (n g) (elt-of-ord-aux (elts g) n g))

(local-defthm elt-of-ord-aux-ord
  (implies (and (groupp g)
                (natp n)
		(sublistp l (elts g))
                (elt-of-ord-aux l n g))
	   (and (in (elt-of-ord-aux l n g) g)
	        (equal (ord (elt-of-ord-aux l n g) g)
		       n))))

(defthm elt-of-ord-ord
  (implies (and (groupp g)
                (natp n)
                (elt-of-ord n g))
	   (and (in (elt-of-ord n g) g)
	        (equal (ord (elt-of-ord n g) g)
		       n))))

(local-defthm ord-elt-of-ord-aux
  (implies (and (groupp g)
                (natp n)
		(sublistp l (elts g))
		(member-equal x l)
		(= (ord x g) n))
           (elt-of-ord-aux l n g))
  :hints (("Subgoal *1/1" :in-theory (enable groupp))))

(defthm ord-elt-of-ord
  (implies (and (groupp g)
                (natp n)
		(in x g)
		(= (ord x g) n))
           (elt-of-ord n g)))

(in-theory (disable elt-of-ord))

(in-theory (disable ord-power-div))

(defthm exists-elt-of-ord
  (implies (and (groupp g)
                (posp n)
		(in x g)
		(divides n (ord x g)))
	   (elt-of-ord n g))
  :hints (("Goal" :in-theory (enable divides)
                  :use ((:instance ord<=order (a x))
		        (:instance power-in-g (a x) (n (/ (ord a g) n)))
                        (:instance ord-power-div (a x) (n (/ (ord x g) n)))
                        (:instance ord-elt-of-ord (x (power x (/ (ord x g) n) g)))))))

(in-theory (disable abelianp))

(defthm divides-order-quotient
  (implies (and (groupp g)
                (abelianp g)
                (primep p)
		(divides p (order g))
                (not (elt-of-ord p g))
		(in a g))
	   (divides p (order (quotient g (cyclic a g)))))
  :hints (("Goal" :use ((:instance order-quotient (h (cyclic a g)))
                        (:instance exists-elt-of-ord (n p) (x a))
			(:instance euclid (a (ord a g)) (b (len (lcosets (cyclic a g) g))))
                        (:instance lagrange (h (cyclic a g)))))))

(local-defthmd lcoset-power-1
  (implies (and (normalp h g)
                (in x (quotient g h))
		(natp n))
	   (and (in (power x n (quotient g h)) (quotient g h))
	        (member-equal (power (car x) n g) (power x n (quotient g h))))	   )
  :hints (("Subgoal *1/2" :use ((:instance op-qop (y (power x (1- n) (quotient g h)))
                                                  (a (car x))
						  (b (power (car x) (1- n) g)))
				(:instance power-in-g (a x) (n (1- n)) (g (quotient g h)))))
	  ("Subgoal *1/1" :in-theory (enable qe e)
	                  :use (in-e-g (:instance member-self-lcoset (x (e g)))))))

(defthmd lcoset-power
  (implies (and (normalp h g)
                (in x (quotient g h))
		(natp n))
	   (equal (power x n (quotient g h))
	          (lcoset (power (car x) n g) h g)))
  :hints (("Goal" ;:in-theory (e/d () (car-member-qlist))
                  :use (lcoset-power-1
		        (:instance car-member-qlist (x (power x n (quotient g h))))
		        (:instance power-in-g (a (car x)))
                        (:instance equal-lcoset (y (power (car x) n g)) (x (car (power x n (quotient g h)))))))))

(local-defthm lcoset-ord-1
  (implies (and (normalp h g)
                (in x (quotient g h)))
	   (equal (power x (ord (car x) g) (quotient g h))
	          (e (quotient g h))));(lcoset (e g) h g)))
  :hints (("Goal" :use ((:instance lcoset-power (n (ord (car x) g)))
                        (:instance ord<=order (a (car x)))
                        (:instance ord-power (a (car x)))))))

(defthm divides-ord-quotient
  (implies (and (normalp h g)
                (in x (quotient g h)))
	   (divides (ord x (quotient g h))
	            (ord (car x) g)))
  :hints (("Goal" :use (lcoset-ord-1
                        (:instance ord<=order (a (car x)))
			(:instance divides-ord (n (ord (car x) g)) (g (quotient g h)) (a x))))))

(defthm lift-elt-of-ord
  (implies (and (normalp h g)
                (posp m)
                (elt-of-ord m (quotient g h)))
           (elt-of-ord m g))
  :hints (("Goal" :use ((:instance elt-of-ord-ord (n m) (g (quotient g h)))
                        (:instance divides-ord-quotient (x (elt-of-ord m (quotient g h))))
			(:instance exists-elt-of-ord (n m) (x (car (elt-of-ord m (quotient g h)))))))))

(local-defthmd ord>1
  (implies (and (groupp g) (in a g) (not (equal a (e g))))
           (> (ord a g) 1))
  :hints (("Goal" :in-theory (disable divides-ord ord-power)
                  :expand ((power a 1 g))
                  :use (ord<=order ord-power))))

(local-defthmd ord-cadr
  (implies (and (groupp g)
                (> (order g) 1))
           (and (in (cadr (elts g)) g)
	        (> (ord (cadr (elts g)) g) 1)))
  :hints (("Goal" :in-theory (enable e groupp)
                  :use ((:instance ord>1 (a (cadr (elts g))))
		        (:instance ord<=order (a (e g)))))))

(local-defthmd order-quotient-bound
  (implies (and (groupp g)
                (abelianp g)
		(in a g)
		(> (ord a g) 1))
	   (< (order (quotient g (cyclic a g)))
	      (order g)))
  :hints (("Goal" :in-theory (disable order-quotient)
                  :use (ord<=order
		        (:instance order-quotient (h (cyclic a g)))
		        (:instance lagrange (h (cyclic a g)))))))

(local-defthmd order-quotient-cadr
  (implies (and (groupp g)
                (abelianp g)
		(> (order g) 1))
	   (< (order (quotient g (cyclic (cadr (car g)) g)))
	      (order g)))
  :hints (("Goal" :use (ord-cadr
                        (:instance order-quotient-bound (a (cadr (elts g))))))))

(defun cauchy-abelian-induction (g)
  (declare (xargs :measure (order g) :hints (("Goal" :use order-quotient-cadr))))
  (if (and (groupp g)
           (abelianp g)
	   (> (order g) 1))
      (cauchy-abelian-induction (quotient g (cyclic (cadr (elts g)) g)))
    ()))

(defthmd cauchy-abelian-lemma
  (implies (and (groupp g)
                (abelianp g)
		(primep p)
		(divides p (order g)))
	   (elt-of-ord p g))
  :hints (("Goal" :induct (cauchy-abelian-induction g))
          ("Subgoal *1/2" :nonlinearp t :in-theory (enable groupp primep divides))
	  ("Subgoal *1/1" :use ((:instance divides-order-quotient (a (cadr (elts g))))
	                        (:instance lift-elt-of-ord (m p) (h (cyclic (cadr (elts g)) g)))))))

(defthmd cauchy-abelian
  (implies (and (groupp g)
                (abelianp g)
		(primep p)
		(divides p (order g)))
	   (and (in (elt-of-ord p g) g)
	        (equal (ord (elt-of-ord p g) g) p)))
  :hints (("Goal" :use (cauchy-abelian-lemma))))


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

(defun conjs (x g) (conjs-aux x (elts g) g))

(defthm conj-in-g
  (implies (and (groupp g) (in x g) (in a g))
           (in (conj x a g) g))
  :hints (("Goal" :in-theory (enable conj))))

(local-defthm ordp-conjs-aux
  (implies (and (groupp g) (in x g) (sublistp l (elts g)))
           (ordp (conjs-aux x l g) g)))

(defthm ordp-conjs
  (implies (and (groupp g) (in x g))
           (ordp (conjs x g) g)))

(defthm dlistp-conjs
  (implies (and (groupp g) (in x g))
           (dlistp (conjs x g)))
  :hints (("Goal" :use (ordp-conjs) :in-theory (disable conjs ordp-conjs))))

(local-defthm member-insert-self
  (member-equal x (insert x l g)))

(local-defthm conj-in-conjs-aux
  (implies (and (groupp g) (in x g) (sublistp l (elts g)) (member-equal a l))
           (member-equal (conj x a g) (conjs-aux x l g))))

(defthm conj-in-conjs
  (implies (and (groupp g) (in x g) (in a g))
           (member-equal (conj x a g) (conjs x g))))

(in-theory (disable conjs))

;; Search for a such that y = (conj x a g):

(defun conjer-aux (y x l g)
  (if (consp l)
      (if (equal (conj x (car l) g) y)
          (car l)
	(conjer-aux y x (cdr l) g))
    ()))

(defun conjer (y x g) (conjer-aux y x (elts g) g))

(local-defthmd conjs-conjer-aux
  (implies (and (groupp g) (in x g) (sublistp l (elts g)) (member-equal y (conjs-aux x l g)))
           (let ((c (conjer-aux y x l g)))
	     (and (member-equal c l)
	          (equal (conj x c g) y)))))

(defthm conjs-conjer
  (implies (and (groupp g) (in x g) (member-equal y (conjs x g)))
           (let ((c (conjer y x g)))
	     (and (in c g)
	          (equal (conj x c g) y))))
  :hints (("Goal" :expand ((conjs x g)) :use ((:instance conjs-conjer-aux (l (elts g)))))))

(in-theory (disable conjer))

(defthm conjs-in-g
  (implies (and (groupp g) (in x g) (member-equal y (conjs x g)))
           (in y g))
  :hints (("Goal" :in-theory (disable conj-in-g conjs-conjer)
                  :use (conjs-conjer
		        (:instance conj-in-g (a (conjer y x g)))))))

;;----------------------------------------------------------------------------------------------------------

(defthm conj-reflexive
  (implies (and (groupp g) (in x g))
           (member-equal x (conjs x g)))
  :hints (("Goal" :in-theory (e/d (conj) (conj-in-conjs))
                  :use ((:instance conj-in-conjs (a (e g)))))))

(local-defthmd conj-symmetric-1
  (implies (and (groupp g) (in x g) (in a g))
           (equal (conj (conj x a g) (inv a g) g)
	          x))
  :hints (("Goal" :in-theory (enable conj)
                  :use ((:instance group-assoc (x a) (y (op (inv a g) x g)) (z a))
		        (:instance group-assoc (x a) (y (inv a g)) (z x))
		        (:instance group-assoc (y a) (z (inv a g)))))))

(defthmd conj-symmetric
  (implies (and (groupp g) (in x g) (in y g) (member-equal y (conjs x g)))
           (member-equal x (conjs y g)))
  :hints (("Goal" :use (conjs-conjer
                        (:instance conj-symmetric-1 (a (conjer y x g)))
			(:instance conj-in-conjs (x y) (a (inv (conjer y x g) g)))))))

(local-defthmd conj-trans-1
  (implies (and (groupp g) (in x g) (in a g) (in b g))
           (equal (conj (conj x a g) b g)
	          (conj x (op a b g) g)))
  :hints (("Goal" :in-theory (enable conj)
                  :use ((:instance group-assoc (x (inv b g)) (y (op (inv a g) x g)) (z a))
		        (:instance group-assoc (x (inv b g)) (y (inv a g)) (z x))
		        (:instance group-assoc (x (op (inv (op a b g) g) x g)) (y a) (z b))
			(:instance prod-inv (x a) (y b))))))

(defthmd conj-trans
  (implies (and (groupp g) (in x g) (in y g) (in z g)
                (member-equal y (conjs x g))
                (member-equal z (conjs y g)))
           (member-equal z (conjs x g)))
  :hints (("Goal" :use (conjs-conjer
                        (:instance conjs-conjer (x y) (y z))
                        (:instance conj-trans-1 (a (conjer y x g)) (b (conjer z y g)))
			(:instance conj-in-conjs (a (op (conjer y x g) (conjer z y g) g)))))))

(local-defthm sublistp-conjs-1
  (implies (and (groupp g)
		(in x g)
		(in y g)
		(member-equal y (conjs x g))
		(sublistp l (conjs y g)))
	   (sublistp l (conjs x g)))
  :hints (("Subgoal *1/2" :in-theory (disable conj-in-g conjs-conjer)
                          :use ((:instance conj-trans (z (car l)))
			        (:instance conj-in-g (x y) (a (conjer (car l) y g)))
                                (:instance conjs-conjer (x y) (y (car l)))))))

(defthm sublistp-conjs
  (implies (and (groupp g)
		(in x g)
		(in y g)
		(member-equal y (conjs x g)))
	   (sublistp (conjs y g) (conjs x g)))
  :hints (("Goal" :use ((:instance sublistp-conjs-1 (l (conjs y g)))))))

(defthmd equal-conjs
  (implies (and (groupp g)
		(in x g)
		(in y g)
		(member-equal y (conjs x g)))
	   (equal (conjs y g) (conjs x g)))
  :hints (("Goal" :use (conj-symmetric
                        (:instance ordp-equal (x (conjs x g)) (y (conjs y g)))))))

(defthmd equal-conjs-2
  (implies (and (groupp g)
		(in x1 g)
		(in x2 g)
		(in y g)
		(member-equal y (conjs x1 g))
		(member-equal y (conjs x2 g)))
	   (equal (conjs x1 g) (conjs x2 g)))
  :hints (("Goal" :use ((:instance equal-conjs (x x1))
                        (:instance equal-conjs (x x2))))))

;;----------------------------------------------------------------------------------------------------------

;; 1-1 map between (conjs x g) and (lcosets (centralizer x g) g):

(defun conj2coset (y x g)
  (lcoset (inv (conjer y x g) g) (centralizer x g) g))

(defun coset2conj (c x g)
  (conj x (inv (car c) g) g))

(local-defthmd conj-comp-1
  (implies (and (groupp g) (in x g) (member-equal y (conjs x g)))
           (in (op (conjer y x g)
	           (car (lcoset (inv (conjer y x g) g) (centralizer x g) g))
		   g)
	       (centralizer x g)))
  :hints (("Goal" :use ((:instance lcoset-car (h (centralizer x g)) (x (inv (conjer y x g) g)))
                        (:instance member-lcoset-iff (h (centralizer x g))
			                             (x (inv (conjer y x g) g))
						     (y (car (lcoset (inv (conjer y x g) g) (centralizer x g) g))))))))

(local-defthm conj-comp-2
  (implies (and (groupp g) (in x g) (member-equal y (conjs x g)))
           (equal (conj x (inv (car (lcoset (inv (conjer y x g) g) (centralizer x g) g)) g) g)
	          (conj x (conjer y x g) g)))
  :hints (("Goal" :use (conj-comp-1) :in-theory (enable centralizer-op))))

(defthm coset2conj-conj2coset
  (implies (and (groupp g) (in x g) (member-equal y (conjs x g)))
           (equal (coset2conj (conj2coset y x g) x g)
	          y)))

(local-defthmd conj-comp-4
  (implies (and (groupp g) (in x g) (member-equal c (lcosets (centralizer x g) g)))
           (and (in (car c) g)
	        (in (conjer (conj x (inv (car c) g) g) x g) g)
	        (in (op (conjer (conj x (inv (car c) g) g) x g)
	                (car c)
		        g)
	            (centralizer x g))))
  :hints (("Goal" :in-theory (enable centralizer-op)
                  :use ((:instance conjs-conjer (y (conj x (inv (car c) g) g)))
		        (:instance lcosets-cars (h (centralizer x g)))
			(:instance conj-in-conjs (a (inv (car c) g)))))))

(local-defthmd conj-comp-5
  (implies (and (groupp g) (in x g) (member-equal c (lcosets (centralizer x g) g)))
           (equal (lcoset (inv (conjer (conj x (inv (car c) g) g) x g) g) (centralizer x g) g)
	          c))
  :hints (("Goal" :use (conj-comp-4
		        (:instance lcosets-cars (h (centralizer x g)))
                        (:instance member-lcoset-iff (h (centralizer x g))
			                             (x (inv (conjer (conj x (inv (car c) g) g) x g) g))
						     (y (car c)))
			(:instance equal-lcoset (h (centralizer x g))
			                        (x (inv (conjer (conj x (inv (car c) g) g) x g) g))
						(y (car c)))))))

(defthm conj2coset-coset2conj
  (implies (and (groupp g) (in x g) (member-equal c (lcosets (centralizer x g) g)))
           (equal (conj2coset (coset2conj c x g) x g)
	          c))
  :hints (("Goal" :use (conj-comp-5))))

(local-defthm conj-comp-7
  (implies (and (groupp g) (in x g) (member-equal y (conjs x g)))
           (member-equal (conj2coset y x g)
	                 (lcosets (centralizer x g) g))))

(local-defthm conj-comp-8
  (implies (and (groupp g) (in x g) (member-equal c (lcosets (centralizer x g) g)))
           (member-equal (coset2conj c x g)
	                 (conjs x g)))
  :hints (("Goal" :use ((:instance lcosets-cars (h (centralizer x g)))))))

(in-theory (disable coset2conj conj2coset))

(defthm len-conjs-cosets
  (implies (and (groupp g) (in x g))
           (equal (len (conjs x g))
	          (subgroup-index (centralizer x g) g)))
  :hints (("Goal" :use ((:functional-instance len-1-1-equal
                         (x (lambda () (if (and (groupp g) (in x g)) (conjs x g) (x))))
			 (y (lambda () (if (and (groupp g) (in x g)) (lcosets (centralizer x g) g) (y))))
			 (xy (lambda (a) (if (and (groupp g) (in x g)) (conj2coset a x g) (xy a))))
			 (yx (lambda (c) (if (and (groupp g) (in x g)) (coset2conj c x g) (yx c)))))))))


;;----------------------------------------------------------------------------------------------------------
;; Class equation
;;----------------------------------------------------------------------------------------------------------

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

(local-defthm member-conjs-conjs-list-aux-1
  (implies (and (groupp g)
                (sublistp l (elts g))
		(in x g)
		(member-list x (conjs-list-aux l g)))
	   (member (conjs x g) (conjs-list-aux l g)))
  :hints (("Subgoal *1/2" :use ((:instance equal-conjs (x (car l)) (y x))))))

(local-defthm member-conjs-conjs-list-aux
  (implies (and (groupp g)
                (not (in x (center g)))
                (sublistp l (elts g))
		(member x l))
	   (member (conjs x g) (conjs-list-aux l g))))

(defthm member-lconjs-conjs-list
  (implies (and (groupp g)
                (in x g)
		(not (in x (center g))))
	   (member (conjs x g) (conjs-list g)))
  :hints (("Goal" :in-theory (enable conjs-list))))

(defthm member-append-list-conjs-list
  (implies (and (groupp g)
                (in x g)
		(not (in x (center g))))
	   (member x (append-list (conjs-list g))))
  :hints (("Goal" :use ((:instance member-append-list (l (conjs x g)) (m (conjs-list g)))))))

(defthm center-conjs
  (implies (and (groupp g)
                (in x g)
		(not (in x (center g)))
		(in c (center g)))
	   (not (member-equal c (conjs x g))))
  :hints (("Goal" :use ((:instance conj-symmetric (y c))
                        (:instance conj-commute (x c) (y (conjer x c g)))
			(:instance center-commutes (a c) (x (conjer x c g)))
			(:instance conjs-conjer (y x) (x c))))))

(local-defthm center-conjs-list-aux
  (implies (and (groupp g)
		(in c (center g))
		(sublistp l (elts g)))
	   (not (member-equal c (append-list (conjs-list-aux l g))))))

(defthm center-conjs-list
  (implies (and (groupp g)
		(in c (center g)))
	   (not (member-equal c (append-list (conjs-list g)))))
  :hints (("Goal" :in-theory (enable conjs-list))))

(local-defthm dlistp-conjs-list-aux
  (implies (and (groupp g)
                (sublistp l (elts g)))
           (dlistp (conjs-list-aux l g))))

(defthm dlistp-conj-list
  (implies (groupp g)
           (dlistp (conjs-list g)))
  :hints (("Goal" :in-theory (enable conjs-list))))

(defthm conjs-car
  (implies (and (groupp g)
		(in x g))
	   (and (in (car (conjs x g)) g)
	        (equal (conjs (car (conjs x g)) g)
	               (conjs x g))))
  :hints (("Goal" :in-theory (disable conj-reflexive)
                  :use (ordp-conjs conj-reflexive
		        (:instance conj-in-g (a (conjer (car (conjs x g)) x g)))
                        (:instance conjs-conjer (y (car (conjs x g))))
                        (:instance equal-conjs (y (car (conjs x g))))))))

(local-defthm conjs-list-aux-cars
  (implies (and (groupp g)
		(sublistp l (elts g))
		(member c (conjs-list-aux l g)))
	   (and (in (car c ) g)
		(equal (conjs (car c) g)
		       c)))
  :hints (("Subgoal *1/2" :use ((:instance conjs-car (x (car l)))))))

(defthmd conjs-list-cars
  (implies (and (groupp g)
		(member c (conjs-list g)))
	   (and (in (car c ) g)
		(equal (conjs (car c) g)
		       c)))
  :hints (("Goal" :use ((:instance conjs-list-aux-cars (l (elts g))))
                  :in-theory (enable conjs-list))))

(local-defthm conjs-list-aux-disjointp-list
  (implies (and (groupp g)
		(sublistp l (elts g))
		(in x g)
		(not (member-list x (conjs-list-aux l g))))
	   (disjointp-list (conjs x g) (conjs-list-aux l g)))
  :hints (("Subgoal *1/2" :use ((:instance common-member-shared (l (conjs x g)) (m (conjs (car l) g)))
                                (:instance equal-conjs-2 (y (common-member (conjs x g) (conjs (car l) g)))
				                          (x1 (car l))
							  (x2 x))))))

(local-defthm conjs-list-aux-disjointp-pairwise
  (implies (and (groupp g)
		(sublistp l (elts g)))
	   (disjointp-pairwise (conjs-list-aux l g))))

(defthm conjs-list-disjointp-pairwise
  (implies (groupp g)
	   (disjointp-pairwise (conjs-list g)))
  :hints (("Goal" :in-theory (enable conjs-list))))

(local-defthm dlistp-list-conjs-list-aux
  (implies (and (groupp g)
		(sublistp l (car g)))
	   (dlistp-list (conjs-list-aux l g)))
  :hints (("Subgoal *1/2" :use ((:instance ordp-conjs (x (car l)))))))

(defthm dlistp-list-conjs-list
  (implies (groupp g)
	   (dlistp-list (conjs-list g)))
  :hints (("Goal" :in-theory (enable conjs-list))))

(defthm dlistp-append-list-conjs-list
  (implies (groupp g)
	   (dlistp (append-list (conjs-list g)))))

(local-defthm dijjointp-center-conjs-list-1
  (implies (and (groupp g) (sublistp l (elts (center g))))
           (disjointp l
	              (append-list (conjs-list g)))))

(defthm dijjointp-center-conjs-list
  (implies (groupp g)
           (disjointp (elts (center g))
	              (append-list (conjs-list g)))))

(defthm dlistp-big-list
  (implies (groupp g)
           (dlistp (append (elts (center g))
	                   (append-list (conjs-list g))))))

(local-defthm sublistp-elts-big-list-1
  (implies (and (groupp g) (sublistp l (elts g)))
           (sublistp l
                     (append (elts (center g))
	                     (append-list (conjs-list g))))))

(defthm sublistp-elts-big-list
  (implies (groupp g)
           (sublistp (elts g)
                     (append (elts (center g))
	                     (append-list (conjs-list g)))))
  :hints (("Goal" :use ((:instance sublistp-elts-big-list-1 (l (elts g)))))))

(local-defthm sublistp-center-elts
  (implies (groupp g)
	   (sublistp (elts (center g))
	             (elts g))))

(local-defthm sublistp-conjs-list-elts-1
  (implies (and (groupp g) (in x g) (sublistp l (conjs x g)))
	   (sublistp l (elts g))))

(local-defthm sublistp-conjs-list-elts-2
  (implies (and (groupp g)
		(member c (conjs-list g)))
	   (sublistp c (elts g)))
  :hints (("Goal" :use (conjs-list-cars))))

(local-defthm sublistp-conjs-list-elts-3
  (implies (and (groupp g) (sublistp l (conjs-list g)))
	   (sublistp (append-list l)
	             (elts g))))

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
	          (order g)))
  :hints (("Goal" :use (sublistp-elts-big-list
                        (:instance sublistp-equal-len (l (elts g))
                                                      (m (append (elts (center g))
	                                                         (append-list (conjs-list g)))))))))


;;----------------------------------------------------------------------------------------------------------
;; Cauchy's lemma
;;----------------------------------------------------------------------------------------------------------

;; Search for a non-central group element the centralizer of which has order divisible by p:

(defun find-elt-aux (l g p)
  (if (consp l)
      (if (and (not (in (car l) (center g)))
               (divides p (order (centralizer (car l) g))))
	  (car l)
	(find-elt-aux (cdr l) g p))
    ()))

(defun find-elt (g p) (find-elt-aux (elts g) g p))

(local-defthmd find-elt-aux-centralizer
  (implies (and (groupp g)
                (primep p)
		(sublistp l (elts g))
                (find-elt-aux l g p))
	   (let ((cent (centralizer (find-elt-aux l g p) g)))
	     (and (subgroupp cent g)
	          (< (order cent) (order g))
		  (divides p (order cent)))))
  :hints (("Subgoal *1/1" :use ((:instance order-centralizer-not-center (x (car l)))))))

(defthmd find-elt-centralizer
  (implies (and (groupp g)
                (primep p)
                (find-elt g p))
	   (let ((cent (centralizer (find-elt g p) g)))
	     (and (subgroupp cent g)
	          (< (order cent) (order g))
		  (divides p (order cent)))))
  :hints (("Goal" :use ((:instance find-elt-aux-centralizer (l (elts g)))))))

(local-defthmd find-elt-center-1
  (implies (and (groupp g)
                (primep p)
		(sublistp l (elts g))
                (null (find-elt-aux l g p))
		(member-equal x l)
		(not (in x (center g))))
	   (not (divides p (order (centralizer x g))))))

(local-defthmd find-elt-center-2
  (implies (and (groupp g)
                (primep p)
                (null (find-elt g p))
		(in x g)
		(not (in x (center g))))
	   (not (divides p (order (centralizer x g)))))
  :hints (("Goal" :use ((:instance find-elt-center-1 (l (elts g)))))))

(local-defthmd find-elt-center-3
  (implies (and (groupp g)
		(member c (conjs-list g)))
	   (and (in (car c) g)
	        (equal (conjs (car c) g) c)
	        (not (in (car c) (center g)))))
  :hints (("Goal" :use (conjs-list-cars
                        (:instance member-append-list (x (car c)) (l c) (m (conjs-list g)))))))

(local-defthmd find-elt-center-4
  (implies (and (groupp g)
                (primep p)
		(divides p (order g))
                (null (find-elt g p))
		(member c (conjs-list g)))
	   (divides p (len c)))
  :hints (("Goal" :use (find-elt-center-3
                        (:instance find-elt-center-2 (x (car c)))
			(:instance len-conjs-cosets (x (car c)))
			(:instance lagrange (h (centralizer (car c) g)))
			(:instance euclid (a (subgroup-index (centralizer (car c) g) g))
			                  (b (order (centralizer (car c) g))))))))

(local-defthmd find-elt-center-5
  (implies (and (groupp g)
                (primep p)
		(divides p (order g))
                (null (find-elt g p))
		(sublistp l (conjs-list g)))
	   (divides p (len (append-list l))))
  :hints (("Subgoal *1/1" :use ((:instance find-elt-center-4 (c (car l)))
                                (:instance divides-sum (x p) (y (len (car l))) (z (len (append-list (cdr l)))))))))

(local-defthmd find-elt-center-6
  (implies (and (groupp g)
                (primep p)
		(divides p (order g))
                (null (find-elt g p)))
	   (divides p (len (append-list (conjs-list g)))))
  :hints (("Goal" :use ((:instance find-elt-center-5 (l (conjs-list g)))))))

(defthm find-elt-center
  (implies (and (groupp g)
                (primep p)
		(divides p (order g))
                (null (find-elt g p)))
	   (divides p (order (center g))))
  :hints (("Goal" :use (class-equation find-elt-center-6
                        (:instance divides-sum (x p) (y (order g)) (z (- (len (append-list (conjs-list g))))))
			(:instance divides-minus (x p) (y (len (append-list (conjs-list g)))))))))

(defthm power-subgroup
  (implies (and (subgroupp h g)
                (in x h)
		(natp n))
	   (and (in (power x n g) h)
	        (equal (power x n h) (power x n g))))
  :hints (("Subgoal *1/1" :in-theory (e/d (e) (subgroup-e)) :use (subgroup-e))
          ("Subgoal *1/2" :in-theory (disable subgroup-op)
	                  :use ((:instance subgroup-op (y (power x (1- n) g)))
			        (:instance group-closure (g h) (y (power x (1- n) g)))))))

(defthmd ord-subgroup
  (implies (and (subgroupp h g)
                (in x h))
	   (equal (ord x h) (ord x g)))
  :hints (("Goal" :in-theory (disable ord<=order ord-power)
                  :use ((:instance ord-power (a x) (n (ord x h)))
		        (:instance ord-power (a x) (g h) (n (ord x g)))
			(:instance ord<=order (a x))
			(:instance ord<=order (a x) (g h))))))

(defthm elt-of-ord-subgroup
  (implies (and (groupp g)
                (natp n)
		(subgroupp h g)
		(elt-of-ord n h))
	   (elt-of-ord n g))
  :hints (("Goal" :use ((:instance ord-elt-of-ord (x (elt-of-ord n h)))
                        (:instance elt-of-ord-ord (g h))
			(:instance ord-subgroup (x (elt-of-ord n h)))))))

(defun cauchy-induction (g p)
  (declare (xargs :measure (order g) :hints (("Goal" :use find-elt-centralizer))))
  (if (and (groupp g)
           (primep p)
	   (find-elt g p))
      (cauchy-induction (centralizer (find-elt g p) g) p)
    t))

(in-theory (disable center-elts find-elt))

(defthm cauchy-lemma
  (implies (and (groupp g)
                (primep p)
		(divides p (order g)))
	   (elt-of-ord p g))
  :hints (("Goal" :induct (cauchy-induction g p))
          ("Subgoal *1/2" :use (find-elt-center
	                        (:instance elt-of-ord-subgroup (n p) (h (center g)))
	                        (:instance cauchy-abelian-lemma (g (center g)))))
	  ("Subgoal *1/1" :use (find-elt-centralizer))))

(defthmd cauchy
  (implies (and (groupp g)
		(primep p)
		(divides p (order g)))
	   (and (in (elt-of-ord p g) g)
	        (equal (ord (elt-of-ord p g) g) p)))
  :hints (("Goal" :use (cauchy-lemma))))

