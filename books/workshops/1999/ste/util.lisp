(in-package "ACL2")
;;(include-book "books/data-structures/utilities")
;;(include-book "books/data-structures/list-theory")
;;(include-book "books/data-structures/alist-theory")
;;(include-book "books/data-structures/set-theory")
;;(include-book "books/arithmetic/top-with-meta")

(include-book "../../../data-structures/utilities")
(include-book "../../../data-structures/list-theory")
(include-book "../../../arithmetic/top-with-meta")

(defun defuntypedlemmaname (name type)
  (let ((namestr (symbol-name name))
	(typestr (symbol-name type)))
    (let ((lemmaname (concatenate 'string namestr "-IS-" typestr)))
      (intern lemmaname "ACL2"))))
(defun defuntypedformals (args)
  (if (consp args)
      (cons (if (symbolp (first args)) (first args) (second (first args)))
	    (defuntypedformals (rest args)))
    nil))
(defun defuntypedfiltertypedargs (args)
  (if (consp args)
      (if (consp (first args))
	  (cons (first args) (defuntypedfiltertypedargs (rest args)))
	(defuntypedfiltertypedargs (rest args)))
    nil))
(defmacro typethm (name &rest thm)
  `(defthm ,name ,@thm :rule-classes (:type-prescription :rewrite)))
;;;
;;;
;;;

(defun defuntypedmeasure (hints)
  (if (member ':measure hints)
      `(:measure ,(second (member ':measure hints)))
    nil))

(defmacro defuntyped (name args guard type default result &rest hints)
  `(progn
     (defun ,name (,@(defuntypedformals args))
       (declare (xargs
		 :guard (and ,@(defuntypedfiltertypedargs args) ,guard)
		 ,@(defuntypedmeasure hints)
		 ))
       (if (and ,@(defuntypedfiltertypedargs args) ,guard)
	   ,result
	 ,default))
     (typethm ,(defuntypedlemmaname name type)
       (,type (,name ,@(defuntypedformals args))))
     ))
(defmacro deflisttyped (lname ename)
  (let ((lnamestr (symbol-name lname))
	(enamestr (symbol-name ename)))
    `(progn
       (deflist ,lname (l)
	 (declare (xargs :guard t))
	 ,ename)
       (defthm ,(intern (concatenate 'string lnamestr "-NTH-IS-" enamestr) "ACL2")
	 (implies (and (,lname lst)
		       (<= 0 n)
		       (< n (length lst)))
		  (,ename (nth n lst))))
       (defthm ,(intern (concatenate 'string lnamestr "-NTHCDR-IS-" lnamestr) "ACL2")
	 (implies (,lname lst)
		  (,lname (nthcdr n lst))))
       )))

;;
;;
;;
(defmacro naturalp(n)  `(and (integerp ,n) (<= 0 ,n)))
(defmacro positivep(n) `(and (integerp ,n) (< 0  ,n)))

(defuntyped nat-induct ((naturalp n)) t
  booleanp t
  (if (equal n 0)
      t
    (nat-induct (1- n))))


(defuntyped nat-induct2 ((naturalp n)) t
  booleanp t
  (if (equal n 0)
      t
    (if (equal n 1)
	t
      (nat-induct2 (1- n)))))

(defthm update-nth-collapse
  (implies (and (true-listp s)
		(naturalp i)
		(< i (len s))
		(equal (nth i s) b))
	   (equal (update-nth i b s)
		  s)))

;;
;;
;;

;;(defuntyped eqlenp ((true-listp l1) (true-listp l2)) t
;;  booleanp nil
;;  (equal (len l1) (len l2)))

;;(defuntyped extend ((true-listp lst) (naturalp n) x) t
;;  true-listp nil
;;  (append lst (make-list n :initial-element x)))

;;(defuntyped memeqlenp ((true-listp l1) (true-listp l2)) (eqlenp l1 l2)
;;  booleanp nil
;;  (if (and (consp l1) (consp l2))
;;      (if (and (true-listp (car l1)) (true-listp (car l2)));
;;	  (and (eqlenp (car l1) (car l2))
;;	       (memeqlenp (cdr l1) (cdr l2)))
;;	nil)
;;    nil))

(defthm len-minus-one
  (implies (and (true-listp r)
		(< 0 (len r)))
	   (equal (+ -1 (len r))
		  (len (cdr r)))))


(defthm consp-len-positive
  (implies (and (true-listp lst)
		(consp lst))
	   (< 0 (len lst))))

(defthm true-listp-len-0-equal-nil
  (implies (and (true-listp lst)
		(equal (len lst) 0))
	   (not lst))
  :rule-classes :forward-chaining)


(defuntyped list-nat-induct ((true-listp lst) (naturalp n)) t
  booleanp t
  (if (consp lst)
      (if (< 0 n)
	  (list-nat-induct (cdr lst) (1- n))
	nil)
    nil)
  )

